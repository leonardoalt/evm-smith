import EvmSmith.Demos.Weth.Solvency
import EvmSmith.Demos.Weth.Dispatch

/-!
# WETH — the formal spec (v1, human-readable)

This file is **the spec**: the single place an auditor or Solidity dev
needs to read to know *what* the WETH contract guarantees, without
reading any of the proof machinery, EVMYulLean internals, or the
bytecode walk.

Everything here is plain Lean `def`s and `theorem`s with English names.
The hard work — proving the bytecode actually obeys the spec — lives in
the other files and is reached through exactly one line: the headline
theorem `weth_is_always_solvent` is *proved by* the engine theorem
`weth_solvency_invariant`. So the chain you must trust is:

    read this file  ──►  weth_is_always_solvent
                              │  (proof term)
                              ▼
                    weth_solvency_invariant   (Solvency.lean)
                              │
                              ▼
                  the bytecode walk + EVMYulLean semantics

The spec vocabulary below (`ethBalance`, `recordedTokenSupply`,
`Solvent`, …) is *definitionally equal* to the predicates the proofs
use (`balanceOf`, `storageSum`, `WethInv`). The `*_iff_*` bridge
lemmas, each proved by `rfl`, witness that equality — so "the spec is
what the theorems use" is not a claim, it is checked by Lean.

## How to read it

1. **The contract** — `wethBytecode`, and what the two entry points do
   (`deposit` / `withdraw`), summarised in prose below.
2. **The vocabulary** — `ethBalance`, `tokenBalanceSlot`,
   `tokenBalanceOf`, `recordedTokenSupply`.
3. **The property** — `Solvent`.
4. **Running a transaction** — `ExecContext`, `runTx`, `SolventAfter`.
5. **The assumptions** — `SolvencyAssumptions`, the real-world /
   chain-state facts the guarantee is conditional on.
6. **The guarantee** — `weth_is_always_solvent`.
7. **Entry points (behavioural)** — what the dispatcher and functions
   *do*, established by executing the bytecode. Every theorem here starts
   at the genuine call entry (`pc = 0`, empty stack); the function-body
   entry points (PC 32 / 42 / 61) are *derived* from dispatch, not
   assumed.
   - `weth_computes_function_selector` — the dispatcher computes the ABI selector;
   - `weth_deposit_selector_dispatches` / `weth_withdraw_selector_dispatches` — each selector routes to the right body;
   - `weth_unknown_selector_reverts` — any other selector reverts with no state change (no fallback/receive);
   - `weth_deposit_credits_from_call` — a deposit call adds `msg.value` to the caller's balance (dispatch + body composed);
   - `weth_withdraw_decrements_from_call` — a withdraw call subtracts `x` from the caller's balance;
   - `weth_withdraw_sends_from_call` — a withdraw call issues a bare `x`-wei transfer to the caller.

## What the contract does (86 bytes of runtime code)

| Selector     | Solidity                | Behaviour                                   |
|--------------|-------------------------|---------------------------------------------|
| `0xd0e30db0` | `deposit() payable`     | `balance[msg.sender] += msg.value`          |
| `0x2e1a7d4d` | `withdraw(uint256 x)`   | require `balance[msg.sender] ≥ x`; subtract `x`; then `CALL` `x` wei back to `msg.sender` |

`withdraw` updates storage **before** the external call
(checks-effects-interactions), so a reentrant `withdraw` sees the
already-decremented balance and cannot double-spend.

The token-balance map uses a deliberately simplified storage layout:
user `a`'s balance is stored at the slot key equal to `a`'s own address
(the 20-byte address zero-extended to a 32-byte word), via
`tokenBalanceSlot`. This is **not** Solidity's `mapping(address =>
uint256)` layout — real Solidity stores the value at
`keccak256(key ‖ slot)`. This contract skips the hashing and uses the
address directly as the slot key. The spec relies only on distinct
users getting distinct slots (`addressSlot_injective`).
-/

namespace EvmSmith.Weth

open EvmYul EvmYul.EVM EvmYul.Frame Batteries EvmSmith.Layer1

/-! ## The contract -/

/-- An on-chain account / contract address. (Alias of EVMYulLean's
`AccountAddress`, renamed for readability of the spec below.) -/
abbrev Address := AccountAddress

/-- WETH's runtime bytecode — the 86 bytes whose behaviour this spec
constrains. `weth` (the address argument throughout the spec) is the
account at which this code is installed. -/
def wethBytecode : ByteArray := bytecode

/-! ## Vocabulary

Readable wrappers over the EVMYulLean state projections. Each is a
one-liner so that the property and the theorem below read in plain
words. All values are interpreted in `ℕ` (an unbounded natural number),
matching the underlying `balanceOf` / `storageSum` convention. -/

/-- WETH's actual on-chain ETH balance (in wei), as held by the EVM
account map `σ` at address `weth`. Unknown account ⇒ `0`. -/
def ethBalance (σ : AccountMap .EVM) (weth : Address) : ℕ :=
  balanceOf σ weth

/-- The storage slot that records `user`'s WETH token balance.

The contract uses the user's address directly as the slot key (the
20-byte address zero-extended to a 32-byte word) — a deliberate
simplification. Real Solidity would hash the key
(`keccak256(key ‖ slot)`); this contract does not. All the proof needs
is that distinct users map to distinct slots (`addressSlot_injective`),
so their balances never collide. -/
def tokenBalanceSlot (user : Address) : UInt256 :=
  addressSlot user

/-- User `user`'s WETH token balance as *recorded in storage* (in wei).
Reads the slot `tokenBalanceSlot user` from `weth`'s storage; a missing
slot or account reads as `0`. -/
def tokenBalanceOf (σ : AccountMap .EVM) (weth user : Address) : ℕ :=
  ((σ.find? weth).map
      (fun acc => (acc.storage.findD (tokenBalanceSlot user) ⟨0⟩).toNat)).getD 0

/-- User `user`'s WETH token balance as a 256-bit word (the raw slot
value). This is the `UInt256`-valued sibling of `tokenBalanceOf`; using
it lets the postconditions below state balance changes in faithful
256-bit arithmetic (`UInt256.add`/`UInt256.sub`, which wrap) rather than
in `ℕ`. -/
def recordedBalance (σ : AccountMap .EVM) (weth user : Address) : UInt256 :=
  ((σ.find? weth).map (fun acc => acc.lookupStorage (tokenBalanceSlot user))).getD ⟨0⟩

/-- The `msg.sender` of the call executing in state `s`. -/
def msgSender (s : EVM.State) : Address := s.executionEnv.source

/-- The `msg.value` (wei sent) of the call executing in state `s`. -/
def msgValue (s : EVM.State) : UInt256 := s.executionEnv.weiValue

/-- `withdraw`'s `uint256` argument: the requested amount, ABI-decoded
from `calldata[4:36]`. -/
def withdrawArg (s : EVM.State) : UInt256 :=
  EvmYul.State.calldataload s.toState (UInt256.ofNat 4)

/-! ### Storage readback (used to state balance deltas)

Reading back a slot after `updateStorage`: the written slot reads as the
written value; every other slot is unchanged. The `v = 0` branch of
`updateStorage` erases the key, handled via `rbmap_erase_toList_filter`. -/

private theorem uint256_eq_of_beq {a b : UInt256} (h : (a == b) = true) : a = b := by
  obtain ⟨a⟩ := a; obtain ⟨b⟩ := b
  exact congrArg UInt256.mk (eq_of_beq (a := a) (b := b) h)

private theorem storage_find?_erase_self (s : Storage) (k : UInt256) :
    (s.erase k).find? k = none := by
  cases h : (s.erase k).find? k with
  | none => rfl
  | some w =>
    obtain ⟨y, hMem, hEq⟩ := RBMap.find?_some_mem_toList h
    rw [rbmap_erase_toList_filter, List.mem_filter] at hMem
    exact absurd hEq (by simpa using hMem.2)

private theorem storage_find?_erase_ne (s : Storage) (k k' : UInt256) (hne : k' ≠ k) :
    (s.erase k).find? k' = s.find? k' := by
  unfold RBMap.find?
  congr 1
  ext y
  rw [RBMap.findEntry?_some, RBMap.findEntry?_some]
  have hfilter : y ∈ (s.erase k).toList ↔ y ∈ s.toList ∧ compare k y.1 ≠ .eq := by
    rw [rbmap_erase_toList_filter]; simp [List.mem_filter]
  constructor
  · rintro ⟨hMem, hEq⟩; rw [hfilter] at hMem; exact ⟨hMem.1, hEq⟩
  · rintro ⟨hMem, hEq⟩
    refine ⟨hfilter.mpr ⟨hMem, ?_⟩, hEq⟩
    intro hky
    exact hne ((Std.LawfulEqCmp.compare_eq_iff_eq.mp hEq).trans
      (Std.LawfulEqCmp.compare_eq_iff_eq.mp hky).symm)

theorem lookupStorage_updateStorage_self (acc : Account .EVM) (k v : UInt256) :
    (acc.updateStorage k v).lookupStorage k = v := by
  unfold Account.updateStorage Account.lookupStorage
  by_cases h : (v == default) = true
  · rw [if_pos h]
    show ((acc.storage.erase k).find? k).getD ⟨0⟩ = v
    rw [storage_find?_erase_self]
    exact (uint256_eq_of_beq h).symm
  · rw [if_neg h]
    show ((acc.storage.insert k v).find? k).getD ⟨0⟩ = v
    rw [RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]; rfl

theorem lookupStorage_updateStorage_ne (acc : Account .EVM) (k k' v : UInt256) (h : k' ≠ k) :
    (acc.updateStorage k v).lookupStorage k' = acc.lookupStorage k' := by
  have hcmp : compare k' k ≠ .eq := fun hc => h (Std.LawfulEqCmp.compare_eq_iff_eq.mp hc)
  unfold Account.updateStorage Account.lookupStorage
  by_cases hv : (v == default) = true
  · rw [if_pos hv]
    show ((acc.storage.erase k).find? k').getD ⟨0⟩ = (acc.storage.find? k').getD ⟨0⟩
    rw [storage_find?_erase_ne _ _ _ h]
  · rw [if_neg hv]
    show ((acc.storage.insert k v).find? k').getD ⟨0⟩ = (acc.storage.find? k').getD ⟨0⟩
    rw [RBMap.find?_insert_of_ne _ hcmp]

/-- After a deposit/withdraw `SSTORE` (which `insert`s the codeOwner's
account with the caller's slot updated to `v`), reading back that slot
gives `v`. -/
theorem recordedBalance_insert_self
    (σ : AccountMap .EVM) (C a : Address) (v : UInt256) (acc : Account .EVM) :
    recordedBalance (σ.insert C (acc.updateStorage (tokenBalanceSlot a) v)) C a = v := by
  unfold recordedBalance
  rw [find?_insert_self]
  simpa using lookupStorage_updateStorage_self acc (tokenBalanceSlot a) v

/-- When `C`'s account is `acc`, `recordedBalance` reads back through it. -/
theorem recordedBalance_of_find
    (σ : AccountMap .EVM) (C a : Address) (acc : Account .EVM)
    (hfind : σ.find? C = some acc) :
    recordedBalance σ C a = acc.lookupStorage (tokenBalanceSlot a) := by
  unfold recordedBalance; rw [hfind]; rfl

/-- The same `SSTORE` leaves every *other* user's balance slot unchanged. -/
theorem recordedBalance_insert_ne
    (σ : AccountMap .EVM) (C a b : Address) (v : UInt256) (acc : Account .EVM)
    (hfind : σ.find? C = some acc) (hb : b ≠ a) :
    recordedBalance (σ.insert C (acc.updateStorage (tokenBalanceSlot a) v)) C b
      = recordedBalance σ C b := by
  unfold recordedBalance
  rw [find?_insert_self, hfind]
  have hslot : tokenBalanceSlot b ≠ tokenBalanceSlot a := fun he => hb (addressSlot_injective he)
  simpa using lookupStorage_updateStorage_ne acc (tokenBalanceSlot a) (tokenBalanceSlot b) v hslot

/-- The total WETH token supply *recorded in storage*: the sum, over
every user, of their recorded token balance. (Equivalently: the sum of
all values stored at `weth`'s storage slots — see `storageSum`.) -/
def recordedTokenSupply (σ : AccountMap .EVM) (weth : Address) : ℕ :=
  storageSum σ weth

/-! ## The property -/

/-- **Solvency.** WETH is *solvent* in state `σ` when the total token
supply it has recorded in storage is at most the actual ETH it holds:

  `recordedTokenSupply σ weth ≤ ethBalance σ weth`.

In words: WETH never owes its users more ETH than it actually has —
every wei of WETH token is backed by a wei of real ETH in the
contract. (The relation is `≤`, not `=`: external sources such as
`SELFDESTRUCT` or block rewards can add ETH to the contract without
minting tokens, so the contract may be *over*-collateralised, never
under.) -/
def Solvent (σ : AccountMap .EVM) (weth : Address) : Prop :=
  recordedTokenSupply σ weth ≤ ethBalance σ weth

/-! ### Bridge to the proven predicates

`Solvent` is, *by definition*, the predicate the proofs preserve. These
`rfl` lemmas make the connection explicit and machine-checked: the
auditor does not have to take "same thing, different name" on faith. -/

/-- `Solvent` is definitionally the proof-side invariant `WethInv`. -/
theorem solvent_iff_wethInv (σ : AccountMap .EVM) (weth : Address) :
    Solvent σ weth ↔ WethInv σ weth := Iff.rfl

/-- `Solvent` is definitionally the framework's `StorageSumLeBalance`
(the predicate the EVMYulLean closure threads through every step). -/
theorem solvent_iff_storageSumLeBalance (σ : AccountMap .EVM) (weth : Address) :
    Solvent σ weth ↔ StorageSumLeBalance σ weth := Iff.rfl

/-! ## Running a transaction

EVMYulLean's transaction-level driver is `EVM.Υ`: it runs one whole
transaction and returns either the post-state (`.ok`) or an error
(`.error` — a reverted or otherwise failed transaction). The wrappers
here bundle its plumbing arguments and hide the `Except`/tuple shape, so
the guarantee at the bottom reads in plain words. -/

/-- The ambient EVM context for running a transaction: everything `Υ`
needs besides the pre-state and the transaction itself. None of it is
WETH-specific — it is the surrounding chain/block plumbing.

* `fuel`    — interpreter step budget (large enough to run to completion).
* `baseFee` — the block's base fee per gas (`H_f` in `Υ`).
* `block`   — the current block header (`H`).
* `genesis` — the genesis block header.
* `history` — the previously processed blocks. -/
structure ExecContext where
  fuel    : ℕ
  baseFee : ℕ
  block   : BlockHeader
  genesis : BlockHeader
  history : ProcessedBlocks

/-- Run one transaction `tx`, sent by `S_T`, on pre-state `σ` in context
`ctx`. Thin wrapper over EVMYulLean's `EVM.Υ`; returns `.ok` with the
post-state or `.error`. -/
def runTx (ctx : ExecContext) (σ : AccountMap .EVM)
    (tx : Transaction) (S_T : Address) :=
  EVM.Υ ctx.fuel σ ctx.baseFee ctx.block ctx.genesis ctx.history tx S_T

/-- **WETH is solvent after running `tx`.** Holds when the post-state of
`runTx` is `Solvent`; vacuously true when the transaction reverts
(`.error`), since then no state changed. -/
def SolventAfter (ctx : ExecContext) (σ : AccountMap .EVM)
    (tx : Transaction) (S_T weth : Address) : Prop :=
  match runTx ctx σ tx S_T with
  | .ok (σ', _, _, _) => Solvent σ' weth
  | .error _ => True

/-! ## The assumptions

The guarantee is conditional on a small bundle of facts that are *not*
derivable from WETH's bytecode alone — they are facts about the
deployment, the rest of the chain, and the surrounding transaction.
`SolvencyAssumptions` is exactly the proof-side `WethAssumptions`
bundle; the five fields, in plain terms, are:

* `deployed`     — WETH's exact bytecode is installed at `weth`, and no
                   frame can replace it (WETH has no
                   `CREATE`/`CREATE2`/`SELFDESTRUCT`).
* `sd_excl`      — no `SELFDESTRUCT` anywhere in the transaction targets
                   `weth` (follows from `deployed`: only WETH's
                   code, which has no `SELFDESTRUCT`, runs at `weth`).
* `dead_at_σP`   — `weth` still has non-empty code after the call
                   dispatch (it is not a "dead" account).
* `inv_at_σP`    — solvency still holds at the post-dispatch state
                   `σ_P` (the propagation step into the call tree).
* `call_no_wrap` — at `withdraw`'s outbound `CALL`, the recipient's
                   balance plus the transferred value stays below
                   `2^256`. The only contract-specific assumption: a
                   chain-state bound on `UInt256` arithmetic, guaranteed
                   in practice by the finite total ETH supply.

See `Solvency.lean` and `REPORT_WETH.md` for the full justification of
each. -/
abbrev SolvencyAssumptions (ctx : ExecContext) (σ : AccountMap .EVM)
    (tx : Transaction) (S_T weth : Address) : Prop :=
  WethAssumptions σ ctx.fuel ctx.baseFee ctx.block ctx.genesis ctx.history tx S_T weth

/-! ## The guarantee

The headline result, stated entirely in the spec vocabulary above. -/

/-- **WETH is always solvent.**

If WETH is solvent before a transaction, then after running *any*
Ethereum transaction through the EVM it is still solvent (or the
transaction reverted, in which case nothing changed).

Pre-conditions, in plain terms:
* `hWellFormed`   — the pre-state is well-formed.
* `hSolventBefore`— WETH is solvent before the transaction.
* `hNotSender`    — WETH is not the transaction's sender (it has no
                    private key).
* `hNotMiner`     — WETH is not the block's fee beneficiary.
* `hTxValid`      — the transaction is valid (sender can pay gas+value).
* `hAssumptions`  — the deployment / chain-state bundle above.

Conclusion: on a successful run the post-state is `Solvent`; on a
reverted run there is nothing to prove.

The proof is a single application of `weth_solvency_invariant` — the
engine that does the instruction-by-instruction bytecode walk. That one
line is the entire bridge between this spec and the bytecode. -/
theorem weth_is_always_solvent
    (ctx : ExecContext) (σ : AccountMap .EVM)
    (tx : Transaction) (S_T weth : Address)
    (hWellFormed     : StateWF σ)
    (hSolventBefore  : Solvent σ weth)
    (hNotSender      : weth ≠ S_T)
    (hNotMiner       : weth ≠ ctx.block.beneficiary)
    (hTxValid        : TxValid σ S_T tx ctx.block ctx.baseFee)
    (hAssumptions    : SolvencyAssumptions ctx σ tx S_T weth) :
    SolventAfter ctx σ tx S_T weth :=
  weth_solvency_invariant ctx.fuel σ ctx.baseFee ctx.block ctx.genesis ctx.history
    tx S_T weth hWellFormed hSolventBefore hNotSender hNotMiner hTxValid hAssumptions

/-! ## Entry points (behavioural)

What WETH's dispatcher and functions *do*, established by **executing the
bytecode** through the EVM semantics (proofs in `Dispatch.lean`), rather
than by inspecting opcodes at fixed program counters. Properties are
surfaced here as they are proved; the engine lemmas live in
`Dispatch.lean`.

`functionSelector` is the ABI selector a call carries. Each step
hypothesis `hN` below runs `decode s.executionEnv.code s.pc` — the
instruction the EVM interpreter fetches from the contract's bytecode at
the current program counter — with the code pinned to `wethBytecode` and
the entry `pc` fixed. So the opcodes are not hand-supplied; they are
forced by the bytecode and the threaded program counter (whether a step
succeeds depends on gas, which is orthogonal to what it computes). -/

/-- The ABI **function selector** of a call: the high 4 bytes of the
first calldata word, `calldataload(0) >> 224`. -/
def functionSelector (calldata : ByteArray) : UInt256 :=
  selectorOf calldata

/-- **The dispatcher computes the ABI selector.** From the entry state
(running WETH's bytecode at `pc = 0`, empty stack), the dispatcher's
selector-extraction instructions leave exactly `functionSelector calldata`
on the stack — the value the two entry-point branches are compared
against. -/
theorem weth_computes_function_selector
    (s0 s1 s2 s3 s4 : EVM.State) (f c0 c1 c2 c3 : ℕ)
    (hcode : s0.executionEnv.code = wethBytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4) :
    s4.stack = [functionSelector s0.executionEnv.calldata] :=
  (weth_dispatcher_computes_selector s0 s1 s2 s3 s4 f c0 c1 c2 c3 hcode hpc0 hstk0 h0 h1 h2 h3).1

/-- **A `deposit` selector routes to the deposit body.** Running WETH's
bytecode from `pc = 0`, if the call's `functionSelector` is `deposit`'s,
the dispatcher lands execution at the deposit body (`depositLbl`, PC 32)
with the selector on the stack. -/
theorem weth_deposit_selector_dispatches
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : EVM.State) (f c0 c1 c2 c3 c4 c5 c6 c7 c8 : ℕ)
    (hcode : s0.executionEnv.code = wethBytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (hsel : functionSelector s0.executionEnv.calldata = depositSelector)
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4)
    (h4 : EVM.step (f + 1) c4 (decode s4.executionEnv.code s4.pc) s4 = .ok s5)
    (h5 : EVM.step (f + 1) c5 (decode s5.executionEnv.code s5.pc) s5 = .ok s6)
    (h6 : EVM.step (f + 1) c6 (decode s6.executionEnv.code s6.pc) s6 = .ok s7)
    (h7 : EVM.step (f + 1) c7 (decode s7.executionEnv.code s7.pc) s7 = .ok s8)
    (h8 : EVM.step (f + 1) c8 (decode s8.executionEnv.code s8.pc) s8 = .ok s9) :
    s9.pc = depositLbl ∧ s9.stack = [depositSelector] := by
  obtain ⟨hp, hs, _, _⟩ := weth_routes_deposit s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
    f c0 c1 c2 c3 c4 c5 c6 c7 c8 hcode hpc0 hstk0 hsel h0 h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨hp, hs⟩

/-- **A `withdraw` selector routes to the withdraw body.** Running WETH's
bytecode from `pc = 0`, if the call's `functionSelector` is `withdraw`'s,
the dispatcher (after the deposit comparison falls through) lands
execution at the withdraw body (`withdrawLbl`, PC 42) with an empty
stack. -/
theorem weth_withdraw_selector_dispatches
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 : EVM.State)
    (f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : ℕ)
    (hcode : s0.executionEnv.code = wethBytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (hsel : functionSelector s0.executionEnv.calldata = withdrawSelector)
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4)
    (h4 : EVM.step (f + 1) c4 (decode s4.executionEnv.code s4.pc) s4 = .ok s5)
    (h5 : EVM.step (f + 1) c5 (decode s5.executionEnv.code s5.pc) s5 = .ok s6)
    (h6 : EVM.step (f + 1) c6 (decode s6.executionEnv.code s6.pc) s6 = .ok s7)
    (h7 : EVM.step (f + 1) c7 (decode s7.executionEnv.code s7.pc) s7 = .ok s8)
    (h8 : EVM.step (f + 1) c8 (decode s8.executionEnv.code s8.pc) s8 = .ok s9)
    (h9 : EVM.step (f + 1) c9 (decode s9.executionEnv.code s9.pc) s9 = .ok s10)
    (h10 : EVM.step (f + 1) c10 (decode s10.executionEnv.code s10.pc) s10 = .ok s11)
    (h11 : EVM.step (f + 1) c11 (decode s11.executionEnv.code s11.pc) s11 = .ok s12)
    (h12 : EVM.step (f + 1) c12 (decode s12.executionEnv.code s12.pc) s12 = .ok s13) :
    s13.pc = withdrawLbl ∧ s13.stack = [] := by
  obtain ⟨hp, hs, _, _⟩ := weth_routes_withdraw s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13
    f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 hcode hpc0 hstk0 hsel
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact ⟨hp, hs⟩

/-- **A withdraw call sends `x` to the caller (end to end).** From the
call entry (`pc = 0`, empty stack, running WETH's bytecode) with the
withdraw selector and sufficient balance, after dispatch (PCs 0–26), the
state-update block (PCs 42–60) and the call-setup (PCs 61–71), the seven
`CALL` arguments come out as `value = x = calldata[4:36]`, recipient = the
caller, empty calldata (`argsSize = 0`) and ignored return data
(`retSize = 0`) — a bare ETH transfer of `x` to the caller. The PC-61
call-setup point is reached by dispatch + the body, not assumed. (The
balance movement itself is the EVM's `CALL` semantics.) -/
theorem weth_withdraw_sends_from_call
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22
      s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 s34 s35 s36 : EVM.State)
    (f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
      c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 : ℕ)
    (C : Address) (acc : Account .EVM)
    (hcode : s0.executionEnv.code = wethBytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (hsel : functionSelector s0.executionEnv.calldata = withdrawSelector)
    (hCo : s0.executionEnv.codeOwner = C)
    (hfind : s0.accountMap.find? C = some acc)
    (hle : (EvmYul.State.calldataload s0.toState (UInt256.ofNat 4)).toNat
            ≤ (acc.lookupStorage (tokenBalanceSlot s0.executionEnv.source)).toNat)
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4)
    (h4 : EVM.step (f + 1) c4 (decode s4.executionEnv.code s4.pc) s4 = .ok s5)
    (h5 : EVM.step (f + 1) c5 (decode s5.executionEnv.code s5.pc) s5 = .ok s6)
    (h6 : EVM.step (f + 1) c6 (decode s6.executionEnv.code s6.pc) s6 = .ok s7)
    (h7 : EVM.step (f + 1) c7 (decode s7.executionEnv.code s7.pc) s7 = .ok s8)
    (h8 : EVM.step (f + 1) c8 (decode s8.executionEnv.code s8.pc) s8 = .ok s9)
    (h9 : EVM.step (f + 1) c9 (decode s9.executionEnv.code s9.pc) s9 = .ok s10)
    (h10 : EVM.step (f + 1) c10 (decode s10.executionEnv.code s10.pc) s10 = .ok s11)
    (h11 : EVM.step (f + 1) c11 (decode s11.executionEnv.code s11.pc) s11 = .ok s12)
    (h12 : EVM.step (f + 1) c12 (decode s12.executionEnv.code s12.pc) s12 = .ok s13)
    (h13 : EVM.step (f + 1) c13 (decode s13.executionEnv.code s13.pc) s13 = .ok s14)
    (h14 : EVM.step (f + 1) c14 (decode s14.executionEnv.code s14.pc) s14 = .ok s15)
    (h15 : EVM.step (f + 1) c15 (decode s15.executionEnv.code s15.pc) s15 = .ok s16)
    (h16 : EVM.step (f + 1) c16 (decode s16.executionEnv.code s16.pc) s16 = .ok s17)
    (h17 : EVM.step (f + 1) c17 (decode s17.executionEnv.code s17.pc) s17 = .ok s18)
    (h18 : EVM.step (f + 1) c18 (decode s18.executionEnv.code s18.pc) s18 = .ok s19)
    (h19 : EVM.step (f + 1) c19 (decode s19.executionEnv.code s19.pc) s19 = .ok s20)
    (h20 : EVM.step (f + 1) c20 (decode s20.executionEnv.code s20.pc) s20 = .ok s21)
    (h21 : EVM.step (f + 1) c21 (decode s21.executionEnv.code s21.pc) s21 = .ok s22)
    (h22 : EVM.step (f + 1) c22 (decode s22.executionEnv.code s22.pc) s22 = .ok s23)
    (h23 : EVM.step (f + 1) c23 (decode s23.executionEnv.code s23.pc) s23 = .ok s24)
    (h24 : EVM.step (f + 1) c24 (decode s24.executionEnv.code s24.pc) s24 = .ok s25)
    (h25 : EVM.step (f + 1) c25 (decode s25.executionEnv.code s25.pc) s25 = .ok s26)
    (h26 : EVM.step (f + 1) c26 (decode s26.executionEnv.code s26.pc) s26 = .ok s27)
    (h27 : EVM.step (f + 1) c27 (decode s27.executionEnv.code s27.pc) s27 = .ok s28)
    (h28 : EVM.step (f + 1) c28 (decode s28.executionEnv.code s28.pc) s28 = .ok s29)
    (h29 : EVM.step (f + 1) c29 (decode s29.executionEnv.code s29.pc) s29 = .ok s30)
    (h30 : EVM.step (f + 1) c30 (decode s30.executionEnv.code s30.pc) s30 = .ok s31)
    (h31 : EVM.step (f + 1) c31 (decode s31.executionEnv.code s31.pc) s31 = .ok s32)
    (h32 : EVM.step (f + 1) c32 (decode s32.executionEnv.code s32.pc) s32 = .ok s33)
    (h33 : EVM.step (f + 1) c33 (decode s33.executionEnv.code s33.pc) s33 = .ok s34)
    (h34 : EVM.step (f + 1) c34 (decode s34.executionEnv.code s34.pc) s34 = .ok s35)
    (h35 : EVM.step (f + 1) c35 (decode s35.executionEnv.code s35.pc) s35 = .ok s36) :
    ∃ g, s36.stack =
      [g, UInt256.ofNat s0.executionEnv.source.val,
       EvmYul.State.calldataload s0.toState (UInt256.ofNat 4),
       UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0,
       EvmYul.State.calldataload s0.toState (UInt256.ofNat 4)] :=
  weth_withdraw_sends_from_entry s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16
    s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 s34 s35 s36
    f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
    c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 C acc hcode hpc0 hstk0 hsel hCo hfind hle
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
    h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35

/-- **An unknown selector reverts with no state change.** Running WETH's
bytecode from `pc = 0`, if the call's `functionSelector` is neither
`deposit`'s nor `withdraw`'s, both dispatch comparisons fall through
(`s9.pc = s8.pc + 1` ≠ `depositLbl`; `s13.pc = s12.pc + 1` ≠
`withdrawLbl`), so no function body is entered, and the account map is
unchanged throughout the dispatch (`s15.accountMap = s0.accountMap`) —
execution proceeds to the dispatcher's `REVERT` having modified nothing.
So WETH has no fallback or receive function; a stray/empty call reverts
as a no-op. -/
theorem weth_unknown_selector_reverts
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : EVM.State)
    (f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : ℕ)
    (hcode : s0.executionEnv.code = wethBytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (hne_dep : functionSelector s0.executionEnv.calldata ≠ depositSelector)
    (hne_wd : functionSelector s0.executionEnv.calldata ≠ withdrawSelector)
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4)
    (h4 : EVM.step (f + 1) c4 (decode s4.executionEnv.code s4.pc) s4 = .ok s5)
    (h5 : EVM.step (f + 1) c5 (decode s5.executionEnv.code s5.pc) s5 = .ok s6)
    (h6 : EVM.step (f + 1) c6 (decode s6.executionEnv.code s6.pc) s6 = .ok s7)
    (h7 : EVM.step (f + 1) c7 (decode s7.executionEnv.code s7.pc) s7 = .ok s8)
    (h8 : EVM.step (f + 1) c8 (decode s8.executionEnv.code s8.pc) s8 = .ok s9)
    (h9 : EVM.step (f + 1) c9 (decode s9.executionEnv.code s9.pc) s9 = .ok s10)
    (h10 : EVM.step (f + 1) c10 (decode s10.executionEnv.code s10.pc) s10 = .ok s11)
    (h11 : EVM.step (f + 1) c11 (decode s11.executionEnv.code s11.pc) s11 = .ok s12)
    (h12 : EVM.step (f + 1) c12 (decode s12.executionEnv.code s12.pc) s12 = .ok s13)
    (h13 : EVM.step (f + 1) c13 (decode s13.executionEnv.code s13.pc) s13 = .ok s14)
    (h14 : EVM.step (f + 1) c14 (decode s14.executionEnv.code s14.pc) s14 = .ok s15) :
    s9.pc = s8.pc + ⟨1⟩ ∧ s13.pc = s12.pc + ⟨1⟩ ∧ s15.accountMap = s0.accountMap :=
  weth_unknown_selector_no_state_change s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
    f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 hcode hpc0 hstk0 hne_dep hne_wd
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

/-! ### End-to-end: dispatch composed with the function body

The two theorems above split a call into "routing" and "body". These
compose them, so the entry point and stack at PC 32 / PC 42 are *derived*
from dispatch rather than assumed — the only entry assumption is `pc = 0`
with an empty stack. -/

/-- **A deposit call credits the caller by `msg.value` (end to end).**
From the call entry (`pc = 0`, empty stack, running WETH's bytecode) with
the deposit selector, after the dispatch (PCs 0–16) *and* the deposit body
(PCs 32–40), the caller's token-balance slot has increased by `msg.value`
and nothing else changed. Reaching the deposit body is part of what's
proved — there is no assumption that we start at PC 32. -/
theorem weth_deposit_credits_from_call
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 : EVM.State)
    (f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 : ℕ)
    (C : Address) (acc : Account .EVM)
    (hcode : s0.executionEnv.code = wethBytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (hsel : functionSelector s0.executionEnv.calldata = depositSelector)
    (hCo : s0.executionEnv.codeOwner = C)
    (hfind : s0.accountMap.find? C = some acc)
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4)
    (h4 : EVM.step (f + 1) c4 (decode s4.executionEnv.code s4.pc) s4 = .ok s5)
    (h5 : EVM.step (f + 1) c5 (decode s5.executionEnv.code s5.pc) s5 = .ok s6)
    (h6 : EVM.step (f + 1) c6 (decode s6.executionEnv.code s6.pc) s6 = .ok s7)
    (h7 : EVM.step (f + 1) c7 (decode s7.executionEnv.code s7.pc) s7 = .ok s8)
    (h8 : EVM.step (f + 1) c8 (decode s8.executionEnv.code s8.pc) s8 = .ok s9)
    (h9 : EVM.step (f + 1) c9 (decode s9.executionEnv.code s9.pc) s9 = .ok s10)
    (h10 : EVM.step (f + 1) c10 (decode s10.executionEnv.code s10.pc) s10 = .ok s11)
    (h11 : EVM.step (f + 1) c11 (decode s11.executionEnv.code s11.pc) s11 = .ok s12)
    (h12 : EVM.step (f + 1) c12 (decode s12.executionEnv.code s12.pc) s12 = .ok s13)
    (h13 : EVM.step (f + 1) c13 (decode s13.executionEnv.code s13.pc) s13 = .ok s14)
    (h14 : EVM.step (f + 1) c14 (decode s14.executionEnv.code s14.pc) s14 = .ok s15)
    (h15 : EVM.step (f + 1) c15 (decode s15.executionEnv.code s15.pc) s15 = .ok s16)
    (h16 : EVM.step (f + 1) c16 (decode s16.executionEnv.code s16.pc) s16 = .ok s17)
    (h17 : EVM.step (f + 1) c17 (decode s17.executionEnv.code s17.pc) s17 = .ok s18) :
    recordedBalance s18.accountMap C (msgSender s0)
        = UInt256.add (msgValue s0) (recordedBalance s0.accountMap C (msgSender s0))
    ∧ ∀ b, b ≠ msgSender s0 →
        recordedBalance s18.accountMap C b = recordedBalance s0.accountMap C b := by
  simp only [msgSender, msgValue]
  have hb := weth_deposit_from_entry s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18
    f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 C acc
    hcode hpc0 hstk0 hsel hCo hfind
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  rw [show (UInt256.ofNat s0.executionEnv.source.val)
        = tokenBalanceSlot s0.executionEnv.source from rfl] at hb
  refine ⟨?_, ?_⟩
  · rw [hb, recordedBalance_insert_self, recordedBalance_of_find s0.accountMap C s0.executionEnv.source acc hfind]
  · intro b hbne
    rw [hb]
    exact recordedBalance_insert_ne s0.accountMap C s0.executionEnv.source b _ acc hfind hbne

/-- **A withdraw call decrements the caller by `x` (end to end).** From
the call entry (`pc = 0`, empty stack, running WETH's bytecode) with the
withdraw selector and sufficient balance (`x ≤ balance`), after the
dispatch (PCs 0–26) *and* the withdraw body (PCs 42–60), the caller's
token-balance slot has decreased by `x = calldata[4:36]` and nothing else
changed. Reaching the withdraw body is part of what's proved. -/
theorem weth_withdraw_decrements_from_call
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22
      s23 s24 s25 s26 s27 s28 s29 : EVM.State)
    (f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
      c23 c24 c25 c26 c27 c28 : ℕ)
    (C : Address) (acc : Account .EVM)
    (hcode : s0.executionEnv.code = wethBytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (hsel : functionSelector s0.executionEnv.calldata = withdrawSelector)
    (hCo : s0.executionEnv.codeOwner = C)
    (hfind : s0.accountMap.find? C = some acc)
    (hle : (EvmYul.State.calldataload s0.toState (UInt256.ofNat 4)).toNat
            ≤ (acc.lookupStorage (tokenBalanceSlot s0.executionEnv.source)).toNat)
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4)
    (h4 : EVM.step (f + 1) c4 (decode s4.executionEnv.code s4.pc) s4 = .ok s5)
    (h5 : EVM.step (f + 1) c5 (decode s5.executionEnv.code s5.pc) s5 = .ok s6)
    (h6 : EVM.step (f + 1) c6 (decode s6.executionEnv.code s6.pc) s6 = .ok s7)
    (h7 : EVM.step (f + 1) c7 (decode s7.executionEnv.code s7.pc) s7 = .ok s8)
    (h8 : EVM.step (f + 1) c8 (decode s8.executionEnv.code s8.pc) s8 = .ok s9)
    (h9 : EVM.step (f + 1) c9 (decode s9.executionEnv.code s9.pc) s9 = .ok s10)
    (h10 : EVM.step (f + 1) c10 (decode s10.executionEnv.code s10.pc) s10 = .ok s11)
    (h11 : EVM.step (f + 1) c11 (decode s11.executionEnv.code s11.pc) s11 = .ok s12)
    (h12 : EVM.step (f + 1) c12 (decode s12.executionEnv.code s12.pc) s12 = .ok s13)
    (h13 : EVM.step (f + 1) c13 (decode s13.executionEnv.code s13.pc) s13 = .ok s14)
    (h14 : EVM.step (f + 1) c14 (decode s14.executionEnv.code s14.pc) s14 = .ok s15)
    (h15 : EVM.step (f + 1) c15 (decode s15.executionEnv.code s15.pc) s15 = .ok s16)
    (h16 : EVM.step (f + 1) c16 (decode s16.executionEnv.code s16.pc) s16 = .ok s17)
    (h17 : EVM.step (f + 1) c17 (decode s17.executionEnv.code s17.pc) s17 = .ok s18)
    (h18 : EVM.step (f + 1) c18 (decode s18.executionEnv.code s18.pc) s18 = .ok s19)
    (h19 : EVM.step (f + 1) c19 (decode s19.executionEnv.code s19.pc) s19 = .ok s20)
    (h20 : EVM.step (f + 1) c20 (decode s20.executionEnv.code s20.pc) s20 = .ok s21)
    (h21 : EVM.step (f + 1) c21 (decode s21.executionEnv.code s21.pc) s21 = .ok s22)
    (h22 : EVM.step (f + 1) c22 (decode s22.executionEnv.code s22.pc) s22 = .ok s23)
    (h23 : EVM.step (f + 1) c23 (decode s23.executionEnv.code s23.pc) s23 = .ok s24)
    (h24 : EVM.step (f + 1) c24 (decode s24.executionEnv.code s24.pc) s24 = .ok s25)
    (h25 : EVM.step (f + 1) c25 (decode s25.executionEnv.code s25.pc) s25 = .ok s26)
    (h26 : EVM.step (f + 1) c26 (decode s26.executionEnv.code s26.pc) s26 = .ok s27)
    (h27 : EVM.step (f + 1) c27 (decode s27.executionEnv.code s27.pc) s27 = .ok s28)
    (h28 : EVM.step (f + 1) c28 (decode s28.executionEnv.code s28.pc) s28 = .ok s29) :
    recordedBalance s29.accountMap C (msgSender s0)
        = UInt256.sub (recordedBalance s0.accountMap C (msgSender s0)) (withdrawArg s0)
    ∧ ∀ b, b ≠ msgSender s0 →
        recordedBalance s29.accountMap C b = recordedBalance s0.accountMap C b := by
  simp only [msgSender, withdrawArg]
  have hb := weth_withdraw_from_entry s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18
    s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29
    f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
    c23 c24 c25 c26 c27 c28 C acc hcode hpc0 hstk0 hsel hCo hfind hle
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
    h23 h24 h25 h26 h27 h28
  rw [show (UInt256.ofNat s0.executionEnv.source.val)
        = tokenBalanceSlot s0.executionEnv.source from rfl] at hb
  refine ⟨?_, ?_⟩
  · rw [hb, recordedBalance_insert_self, recordedBalance_of_find s0.accountMap C s0.executionEnv.source acc hfind]
  · intro b hbne
    rw [hb]
    exact recordedBalance_insert_ne s0.accountMap C s0.executionEnv.source b _ acc hfind hbne

/-! ### A gas-free "big-step" run

`wethRun` iterates the **real** `EVM.step` (decoding each instruction from
the contract's own code at the current pc, exactly as the interpreter
does) until it reaches a halting instruction, returning the final state
and the return data. It is the EVM's frame loop `EVM.X` **with gas
ignored** (`gasCost = 0`, ample step fuel) — the one modelling
assumption. (The genuine `EVM.X` form would additionally require the
framework's gas/halt fuel-induction, which is currently an open
`sorry`-staged obligation in `XFrame.lean`.) The point: the spec
theorems below take a *single* `wethRun … = some (s', o)` hypothesis,
hiding the per-step chain, and can talk about the return data `o`. -/

/-- The halting opcodes (where `EVM.X` stops the frame). -/
def isHaltOp : Operation .EVM → Bool
  | .STOP => true
  | .REVERT => true
  | .RETURN => true
  | _ => false

/-- The frame's return data at a halt (matching `EVM.X`'s `H`): the
returned memory slice for `RETURN`/`REVERT`, empty for `STOP`. -/
def haltOutput (s : EVM.State) : Operation .EVM → ByteArray
  | .RETURN => s.toMachineState.H_return
  | .REVERT => s.toMachineState.H_return
  | _ => .empty

/-- Run the contract gas-free from `s`: fetch-and-`EVM.step` until a halt
opcode, returning the (pre-halt) state and the halt's return data.
`callFuel` bounds any nested call; the outer `ℕ` bounds the number of
instructions. -/
def wethRun (callFuel : ℕ) : ℕ → EVM.State → Option (EVM.State × ByteArray)
  | 0, _ => none
  | n + 1, s =>
    match decode s.executionEnv.code s.pc with
    | none => none
    | some (op, arg) =>
      if isHaltOp op then some (s, haltOutput s op)
      else
        match EVM.step (callFuel + 1) 0 (some (op, arg)) s with
        | .ok s' => wethRun callFuel n s'
        | .error _ => none

/-- One non-halting `wethRun` step: peel off the `EVM.step` fact and the
remaining run. -/
theorem wethRun_succ_step
    (callFuel n : ℕ) (s : EVM.State) (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (res : EVM.State × ByteArray)
    (hdec : decode s.executionEnv.code s.pc = some (op, arg))
    (hnh : isHaltOp op = false)
    (hrun : wethRun callFuel (n + 1) s = some res) :
    ∃ s1, EVM.step (callFuel + 1) 0 (some (op, arg)) s = .ok s1
        ∧ wethRun callFuel n s1 = some res := by
  rw [wethRun, hdec] at hrun
  simp only [hnh] at hrun
  cases hstep : EVM.step (callFuel + 1) 0 (some (op, arg)) s with
  | error e => rw [hstep] at hrun; simp at hrun
  | ok s1 => rw [hstep] at hrun; exact ⟨s1, rfl, hrun⟩

/-- `SSTORE` advances the pc by one and preserves the execution
environment (the post-`pc` is needed to reach the trailing `STOP`). -/
theorem step_SSTORE_pc_ee
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (slot newVal : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = slot :: newVal :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SSTORE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧ s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryStateOp EVM.binaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨?_, ?_⟩
  · simp only [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
  · show (EvmYul.State.sstore s.toState slot newVal).executionEnv = s.executionEnv
    rw [sstore_preserves_executionEnv]

/-- `ISZERO` preserves the account map (a pure stack op). Needed to carry
the recorded balance through the post-`CALL` success check. -/
theorem step_ISZERO_am
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.ISZERO, arg)) s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnary EVM.execUnOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  simp only [accountMap_replaceStackAndIncrPC]

/-- A halting `wethRun` step returns the current state and the halt
output. -/
theorem wethRun_halt_step
    (callFuel n : ℕ) (s : EVM.State) (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (res : EVM.State × ByteArray)
    (hdec : decode s.executionEnv.code s.pc = some (op, arg))
    (hh : isHaltOp op = true)
    (hrun : wethRun callFuel (n + 1) s = some res) :
    res = (s, haltOutput s op) := by
  rw [wethRun, hdec] at hrun
  simp only [hh, if_true] at hrun
  exact (Option.some.inj hrun).symm

/-- **The withdraw tail through the external CALL preserves the recorded
balance.** From the post-`SSTORE` state (pc 61, stack `[x]`), running the
gas-free interpreter to its halt — the call-setup, the outbound `CALL`
itself, and the success check — leaves `recordedBalance` for `(C, u)`
unchanged at `T`. The `CALL`'s effect on `C`'s storage is the explicit
no-reentrancy / codeless-recipient hypothesis `hcallKeep`. Both the
success (→ `STOP`) and failure (→ `REVERT`) branches of the post-call
`JUMPI` are covered, so no call-success assumption is needed. -/
theorem wethRun_withdraw_tail
    (s : EVM.State) (callFuel N : ℕ) (res : EVM.State × ByteArray)
    (C : Address) (u : AccountAddress) (x T : UInt256)
    (hcode : s.executionEnv.code = bytecode)
    (hpc : s.pc = UInt256.ofNat 61)
    (hstk : s.stack = [x])
    (hrb : recordedBalance s.accountMap C u = T)
    (hcallKeep : ∀ (sa sb : EVM.State),
        EVM.step (callFuel + 1) 0 (some (.CALL, none)) sa = .ok sb →
        recordedBalance sb.accountMap C u = recordedBalance sa.accountMap C u)
    (hrun : wethRun callFuel N s = some res) :
    recordedBalance res.1.accountMap C u = T := by
  -- 61: PUSH1 0
  have hd0 : decode s.executionEnv.code s.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
    rw [hcode, hpc]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s1, hst0, hrun⟩ := wethRun_succ_step callFuel N s _ _ _ hd0 (by decide) hrun
  obtain ⟨h1pc, h1stk, h1ee, h1am⟩ := step_PUSH1_shape_strong s s1 callFuel 0 (UInt256.ofNat 0) hst0
  rw [hstk] at h1stk
  have hc1 : s1.executionEnv.code = bytecode := by rw [h1ee]; exact hcode
  have hp1 : s1.pc = UInt256.ofNat 63 := by rw [h1pc, hpc]; decide
  have hrb1 : recordedBalance s1.accountMap C u = T := by rw [h1am]; exact hrb
  -- 63: PUSH1 0
  have hd1 : decode s1.executionEnv.code s1.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
    rw [hc1, hp1]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s2, hst1, hrun⟩ := wethRun_succ_step callFuel N s1 _ _ _ hd1 (by decide) hrun
  obtain ⟨h2pc, h2stk, h2ee, h2am⟩ := step_PUSH1_shape_strong s1 s2 callFuel 0 (UInt256.ofNat 0) hst1
  rw [h1stk] at h2stk
  have hc2 : s2.executionEnv.code = bytecode := by rw [h2ee]; exact hc1
  have hp2 : s2.pc = UInt256.ofNat 65 := by rw [h2pc, hp1]; decide
  have hrb2 : recordedBalance s2.accountMap C u = T := by rw [h2am]; exact hrb1
  -- 65: PUSH1 0
  have hd2 : decode s2.executionEnv.code s2.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
    rw [hc2, hp2]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s3, hst2, hrun⟩ := wethRun_succ_step callFuel N s2 _ _ _ hd2 (by decide) hrun
  obtain ⟨h3pc, h3stk, h3ee, h3am⟩ := step_PUSH1_shape_strong s2 s3 callFuel 0 (UInt256.ofNat 0) hst2
  rw [h2stk] at h3stk
  have hc3 : s3.executionEnv.code = bytecode := by rw [h3ee]; exact hc2
  have hp3 : s3.pc = UInt256.ofNat 67 := by rw [h3pc, hp2]; decide
  have hrb3 : recordedBalance s3.accountMap C u = T := by rw [h3am]; exact hrb2
  -- 67: PUSH1 0
  have hd3 : decode s3.executionEnv.code s3.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
    rw [hc3, hp3]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s4, hst3, hrun⟩ := wethRun_succ_step callFuel N s3 _ _ _ hd3 (by decide) hrun
  obtain ⟨h4pc, h4stk, h4ee, h4am⟩ := step_PUSH1_shape_strong s3 s4 callFuel 0 (UInt256.ofNat 0) hst3
  rw [h3stk] at h4stk
  have hc4 : s4.executionEnv.code = bytecode := by rw [h4ee]; exact hc3
  have hp4 : s4.pc = UInt256.ofNat 69 := by rw [h4pc, hp3]; decide
  have hrb4 : recordedBalance s4.accountMap C u = T := by rw [h4am]; exact hrb3
  -- 69: DUP5
  have hd4 : decode s4.executionEnv.code s4.pc = some (.DUP5, none) := by
    rw [hc4, hp4]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s5, hst4, hrun⟩ := wethRun_succ_step callFuel N s4 _ _ _ hd4 (by decide) hrun
  obtain ⟨h5pc, h5stk, h5ee, h5am⟩ :=
    step_DUP5_shape_strong s4 s5 callFuel 0 none (UInt256.ofNat 0) (UInt256.ofNat 0)
      (UInt256.ofNat 0) (UInt256.ofNat 0) x [] h4stk hst4
  rw [h4stk] at h5stk
  have hc5 : s5.executionEnv.code = bytecode := by rw [h5ee]; exact hc4
  have hp5 : s5.pc = UInt256.ofNat 70 := by rw [h5pc, hp4]; decide
  have hrb5 : recordedBalance s5.accountMap C u = T := by rw [h5am]; exact hrb4
  -- 70: CALLER
  have hd5 : decode s5.executionEnv.code s5.pc = some (.CALLER, none) := by
    rw [hc5, hp5]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s6, hst5, hrun⟩ := wethRun_succ_step callFuel N s5 _ _ _ hd5 (by decide) hrun
  obtain ⟨h6pc, h6stk, h6ee, h6am⟩ := step_CALLER_value s5 s6 callFuel 0 none hst5
  rw [h5stk] at h6stk
  have hc6 : s6.executionEnv.code = bytecode := by rw [h6ee]; exact hc5
  have hp6 : s6.pc = UInt256.ofNat 71 := by rw [h6pc, hp5]; decide
  have hrb6 : recordedBalance s6.accountMap C u = T := by rw [h6am]; exact hrb5
  -- 71: GAS
  have hd6 : decode s6.executionEnv.code s6.pc = some (.GAS, none) := by
    rw [hc6, hp6]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s7, hst6, hrun⟩ := wethRun_succ_step callFuel N s6 _ _ _ hd6 (by decide) hrun
  obtain ⟨h7pc, ⟨g, h7stk⟩, h7ee, h7am⟩ := step_GAS_shape_strong s6 s7 callFuel 0 none hst6
  rw [h6stk] at h7stk
  have hc7 : s7.executionEnv.code = bytecode := by rw [h7ee]; exact hc6
  have hp7 : s7.pc = UInt256.ofNat 72 := by rw [h7pc, hp6]; decide
  have hrb7 : recordedBalance s7.accountMap C u = T := by rw [h7am]; exact hrb6
  -- 72: CALL (the external send; effect on C's slot given by hcallKeep)
  have hd7 : decode s7.executionEnv.code s7.pc = some (.CALL, none) := by
    rw [hc7, hp7]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s8, hst7, hrun⟩ := wethRun_succ_step callFuel N s7 _ _ _ hd7 (by decide) hrun
  obtain ⟨h8pc, ⟨flag, h8stk⟩, h8ee⟩ :=
    step_CALL_shape s7 s8 callFuel 0 none _ _ _ _ _ _ _ [x] h7stk hst7
  have hc8 : s8.executionEnv.code = bytecode := by rw [h8ee]; exact hc7
  have hp8 : s8.pc = UInt256.ofNat 73 := by rw [h8pc, hp7]; decide
  have hrb8 : recordedBalance s8.accountMap C u = T := by rw [hcallKeep s7 s8 hst7]; exact hrb7
  -- 73: ISZERO
  have hd8 : decode s8.executionEnv.code s8.pc = some (.ISZERO, none) := by
    rw [hc8, hp8]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s9, hst8, hrun⟩ := wethRun_succ_step callFuel N s8 _ _ _ hd8 (by decide) hrun
  obtain ⟨h9pc, ⟨v2, h9stk⟩, h9ee⟩ := step_ISZERO_shape s8 s9 callFuel 0 none flag [x] h8stk hst8
  have h9am : s9.accountMap = s8.accountMap := step_ISZERO_am s8 s9 callFuel 0 none flag [x] h8stk hst8
  have hc9 : s9.executionEnv.code = bytecode := by rw [h9ee]; exact hc8
  have hp9 : s9.pc = UInt256.ofNat 74 := by rw [h9pc, hp8]; decide
  have hrb9 : recordedBalance s9.accountMap C u = T := by rw [h9am]; exact hrb8
  -- 74: PUSH2 revertLbl
  have hd9 : decode s9.executionEnv.code s9.pc = some (.Push .PUSH2, some (revertLbl, 2)) := by
    rw [hc9, hp9]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s10, hst9, hrun⟩ := wethRun_succ_step callFuel N s9 _ _ _ hd9 (by decide) hrun
  obtain ⟨h10pc, h10stk, h10ee, h10am⟩ :=
    step_PUSH_shape_strong s9 s10 callFuel 0 .PUSH2 (by decide) revertLbl 2 hst9
  rw [h9stk] at h10stk
  have hc10 : s10.executionEnv.code = bytecode := by rw [h10ee]; exact hc9
  have hp10 : s10.pc = UInt256.ofNat 77 := by rw [h10pc, hp9]; decide
  have hrb10 : recordedBalance s10.accountMap C u = T := by rw [h10am]; exact hrb9
  -- 77: JUMPI — success check (case-split on the CALL flag)
  have hd10 : decode s10.executionEnv.code s10.pc = some (.JUMPI, none) := by
    rw [hc10, hp10]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s11, hst10, hrun⟩ := wethRun_succ_step callFuel N s10 _ _ _ hd10 (by decide) hrun
  obtain ⟨h11pc, h11stk, h11ee, h11am⟩ :=
    step_JUMPI_shape_strong s10 s11 callFuel 0 none revertLbl v2 [x] h10stk hst10
  have hc11 : s11.executionEnv.code = bytecode := by rw [h11ee]; exact hc10
  have hrb11 : recordedBalance s11.accountMap C u = T := by rw [h11am]; exact hrb10
  by_cases hv2 : v2 != ⟨0⟩
  · -- CALL failed: JUMPI taken → revert block (PCs 80–85)
    have hp11' : s11.pc = revertLbl := by rw [h11pc, if_pos hv2]
    -- 80: JUMPDEST
    have hd11 : decode s11.executionEnv.code s11.pc = some (.JUMPDEST, none) := by
      rw [hc11, hp11']; native_decide
    obtain _ | N := N
    · simp [wethRun] at hrun
    obtain ⟨s12, hst11, hrun⟩ := wethRun_succ_step callFuel N s11 _ _ _ hd11 (by decide) hrun
    obtain ⟨h12pc, _, h12ee, h12am⟩ := step_JUMPDEST_shape_strong s11 s12 callFuel 0 none hst11
    have hc12 : s12.executionEnv.code = bytecode := by rw [h12ee]; exact hc11
    have hp12 : s12.pc = UInt256.ofNat 81 := by rw [h12pc, hp11']; decide
    have hrb12 : recordedBalance s12.accountMap C u = T := by rw [h12am]; exact hrb11
    -- 81: PUSH1 0
    have hd12 : decode s12.executionEnv.code s12.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
      rw [hc12, hp12]; native_decide
    obtain _ | N := N
    · simp [wethRun] at hrun
    obtain ⟨s13, hst12, hrun⟩ := wethRun_succ_step callFuel N s12 _ _ _ hd12 (by decide) hrun
    obtain ⟨h13pc, _, h13ee, h13am⟩ := step_PUSH1_shape_strong s12 s13 callFuel 0 (UInt256.ofNat 0) hst12
    have hc13 : s13.executionEnv.code = bytecode := by rw [h13ee]; exact hc12
    have hp13 : s13.pc = UInt256.ofNat 83 := by rw [h13pc, hp12]; decide
    have hrb13 : recordedBalance s13.accountMap C u = T := by rw [h13am]; exact hrb12
    -- 83: PUSH1 0
    have hd13 : decode s13.executionEnv.code s13.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
      rw [hc13, hp13]; native_decide
    obtain _ | N := N
    · simp [wethRun] at hrun
    obtain ⟨s14, hst13, hrun⟩ := wethRun_succ_step callFuel N s13 _ _ _ hd13 (by decide) hrun
    obtain ⟨h14pc, _, h14ee, h14am⟩ := step_PUSH1_shape_strong s13 s14 callFuel 0 (UInt256.ofNat 0) hst13
    have hc14 : s14.executionEnv.code = bytecode := by rw [h14ee]; exact hc13
    have hp14 : s14.pc = UInt256.ofNat 85 := by rw [h14pc, hp13]; decide
    have hrb14 : recordedBalance s14.accountMap C u = T := by rw [h14am]; exact hrb13
    -- 85: REVERT — halt
    have hd14 : decode s14.executionEnv.code s14.pc = some (.REVERT, none) := by
      rw [hc14, hp14]; native_decide
    obtain _ | N := N
    · simp [wethRun] at hrun
    have hres := wethRun_halt_step callFuel N s14 _ _ _ hd14 (by decide) hrun
    rw [show res.1 = s14 from by rw [hres]]; exact hrb14
  · -- CALL succeeded: JUMPI not taken → POP; STOP (PCs 78–79)
    have hp11 : s11.pc = UInt256.ofNat 78 := by
      rw [h11pc, if_neg hv2, hp10]; decide
    -- 78: POP
    have hd11 : decode s11.executionEnv.code s11.pc = some (.POP, none) := by
      rw [hc11, hp11]; native_decide
    obtain _ | N := N
    · simp [wethRun] at hrun
    obtain ⟨s12, hst11, hrun⟩ := wethRun_succ_step callFuel N s11 _ _ _ hd11 (by decide) hrun
    obtain ⟨h12pc, _, h12ee, h12am⟩ := step_POP_shape_strong s11 s12 callFuel 0 none x [] h11stk hst11
    have hc12 : s12.executionEnv.code = bytecode := by rw [h12ee]; exact hc11
    have hp12 : s12.pc = UInt256.ofNat 79 := by rw [h12pc, hp11]; decide
    have hrb12 : recordedBalance s12.accountMap C u = T := by rw [h12am]; exact hrb11
    -- 79: STOP — halt
    have hd12 : decode s12.executionEnv.code s12.pc = some (.STOP, none) := by
      rw [hc12, hp12]; native_decide
    obtain _ | N := N
    · simp [wethRun] at hrun
    have hres := wethRun_halt_step callFuel N s12 _ _ _ hd12 (by decide) hrun
    rw [show res.1 = s12 from by rw [hres]]; exact hrb12

/-- **deposit, as a single big-step over the gas-free interpreter.**
From a call entry (`pc = 0`, empty stack, running WETH's bytecode) whose
ABI selector is `deposit`'s, *running the contract to its halt*
(`wethRun … = some (s', o)`) credits `msg.value` to the caller's recorded
balance, leaves every other balance untouched, and returns empty data.
The whole per-instruction chain — dispatch routing *and* the deposit
body — is hidden inside the single `wethRun` hypothesis. -/
theorem weth_deposit_run
    (s0 : EVM.State) (callFuel N : ℕ) (res : EVM.State × ByteArray)
    (C : Address) (acc : Account .EVM)
    (hcode : s0.executionEnv.code = wethBytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (hsel : functionSelector s0.executionEnv.calldata = depositSelector)
    (hCo : s0.executionEnv.codeOwner = C)
    (hfind : s0.accountMap.find? C = some acc)
    (hrun : wethRun callFuel N s0 = some res) :
    recordedBalance res.1.accountMap C (msgSender s0)
        = UInt256.add (msgValue s0) (recordedBalance s0.accountMap C (msgSender s0))
    ∧ (∀ b, b ≠ msgSender s0 →
        recordedBalance res.1.accountMap C b = recordedBalance s0.accountMap C b)
    ∧ res.2 = ByteArray.empty := by
  have hcodeB : s0.executionEnv.code = bytecode := hcode
  have hselB : selectorOf s0.executionEnv.calldata = depositSelector := hsel
  -- === DISPATCH (PCs 0–16): peel h0..h8, threading the pc ===
  -- 0: PUSH1 0 @ 0
  have hd0 : decode s0.executionEnv.code s0.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
    rw [hcodeB, hpc0]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s1, hst0, hrun⟩ := wethRun_succ_step callFuel N s0 _ _ _ hd0 (by decide) hrun
  have h0 : EVM.step (callFuel + 1) 0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1 := by
    rw [hd0]; exact hst0
  obtain ⟨h1pc, h1stk, h1ee, h1am⟩ := step_PUSH1_shape_strong s0 s1 callFuel 0 (UInt256.ofNat 0) hst0
  rw [hstk0] at h1stk
  have hc1 : s1.executionEnv.code = bytecode := by rw [h1ee]; exact hcodeB
  have hp1 : s1.pc = UInt256.ofNat 2 := by rw [h1pc, hpc0]; decide
  -- 1: CALLDATALOAD @ 2
  have hd1 : decode s1.executionEnv.code s1.pc = some (.CALLDATALOAD, none) := by
    rw [hc1, hp1]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s2, hst1, hrun⟩ := wethRun_succ_step callFuel N s1 _ _ _ hd1 (by decide) hrun
  have h1 : EVM.step (callFuel + 1) 0 (decode s1.executionEnv.code s1.pc) s1 = .ok s2 := by
    rw [hd1]; exact hst1
  obtain ⟨h2pc, h2stk, h2ee, h2am⟩ :=
    step_CALLDATALOAD_value s1 s2 callFuel 0 none (UInt256.ofNat 0) [] h1stk hst1
  have hc2 : s2.executionEnv.code = bytecode := by rw [h2ee]; exact hc1
  have hp2 : s2.pc = UInt256.ofNat 3 := by rw [h2pc, hp1]; decide
  -- 2: PUSH1 0xe0 @ 3
  have hd2 : decode s2.executionEnv.code s2.pc = some (.Push .PUSH1, some (UInt256.ofNat 0xe0, 1)) := by
    rw [hc2, hp2]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s3, hst2, hrun⟩ := wethRun_succ_step callFuel N s2 _ _ _ hd2 (by decide) hrun
  have h2 : EVM.step (callFuel + 1) 0 (decode s2.executionEnv.code s2.pc) s2 = .ok s3 := by
    rw [hd2]; exact hst2
  obtain ⟨h3pc, h3stk, h3ee, h3am⟩ := step_PUSH1_shape_strong s2 s3 callFuel 0 (UInt256.ofNat 0xe0) hst2
  rw [h2stk] at h3stk
  have hc3 : s3.executionEnv.code = bytecode := by rw [h3ee]; exact hc2
  have hp3 : s3.pc = UInt256.ofNat 5 := by rw [h3pc, hp2]; decide
  -- 3: SHR @ 5
  have hd3 : decode s3.executionEnv.code s3.pc = some (.SHR, none) := by
    rw [hc3, hp3]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s4, hst3, hrun⟩ := wethRun_succ_step callFuel N s3 _ _ _ hd3 (by decide) hrun
  have h3 : EVM.step (callFuel + 1) 0 (decode s3.executionEnv.code s3.pc) s3 = .ok s4 := by
    rw [hd3]; exact hst3
  obtain ⟨h4pc, h4stk, h4ee, h4am⟩ :=
    step_SHR_value s3 s4 callFuel 0 none (UInt256.ofNat 0xe0)
      (EvmYul.State.calldataload s1.toState (UInt256.ofNat 0)) [] h3stk hst3
  have hc4 : s4.executionEnv.code = bytecode := by rw [h4ee]; exact hc3
  have hp4 : s4.pc = UInt256.ofNat 6 := by rw [h4pc, hp3]; decide
  -- 4: DUP1 @ 6
  have hd4 : decode s4.executionEnv.code s4.pc = some (.DUP1, none) := by
    rw [hc4, hp4]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s5, hst4, hrun⟩ := wethRun_succ_step callFuel N s4 _ _ _ hd4 (by decide) hrun
  have h4 : EVM.step (callFuel + 1) 0 (decode s4.executionEnv.code s4.pc) s4 = .ok s5 := by
    rw [hd4]; exact hst4
  obtain ⟨h5pc, h5stk, h5ee, h5am⟩ :=
    step_DUP1_shape_strong s4 s5 callFuel 0 none _ [] h4stk hst4
  rw [h4stk] at h5stk
  have hc5 : s5.executionEnv.code = bytecode := by rw [h5ee]; exact hc4
  have hp5 : s5.pc = UInt256.ofNat 7 := by rw [h5pc, hp4]; decide
  -- 5: PUSH4 depositSelector @ 7
  have hd5 : decode s5.executionEnv.code s5.pc = some (.Push .PUSH4, some (depositSelector, 4)) := by
    rw [hc5, hp5]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s6, hst5, hrun⟩ := wethRun_succ_step callFuel N s5 _ _ _ hd5 (by decide) hrun
  have h5 : EVM.step (callFuel + 1) 0 (decode s5.executionEnv.code s5.pc) s5 = .ok s6 := by
    rw [hd5]; exact hst5
  obtain ⟨h6pc, h6stk, h6ee, h6am⟩ :=
    step_PUSH_shape_strong s5 s6 callFuel 0 .PUSH4 (by decide) depositSelector 4 hst5
  rw [h5stk] at h6stk
  have hc6 : s6.executionEnv.code = bytecode := by rw [h6ee]; exact hc5
  have hp6 : s6.pc = UInt256.ofNat 12 := by rw [h6pc, hp5]; decide
  -- 6: EQ @ 12
  have hd6 : decode s6.executionEnv.code s6.pc = some (.EQ, none) := by
    rw [hc6, hp6]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s7, hst6, hrun⟩ := wethRun_succ_step callFuel N s6 _ _ _ hd6 (by decide) hrun
  have h6 : EVM.step (callFuel + 1) 0 (decode s6.executionEnv.code s6.pc) s6 = .ok s7 := by
    rw [hd6]; exact hst6
  obtain ⟨h7pc, h7stk, h7ee, h7am⟩ :=
    step_EQ_value s6 s7 callFuel 0 none depositSelector _ _ h6stk hst6
  have hc7 : s7.executionEnv.code = bytecode := by rw [h7ee]; exact hc6
  have hp7 : s7.pc = UInt256.ofNat 13 := by rw [h7pc, hp6]; decide
  -- 7: PUSH2 depositLbl @ 13
  have hd7 : decode s7.executionEnv.code s7.pc = some (.Push .PUSH2, some (depositLbl, 2)) := by
    rw [hc7, hp7]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s8, hst7, hrun⟩ := wethRun_succ_step callFuel N s7 _ _ _ hd7 (by decide) hrun
  have h7 : EVM.step (callFuel + 1) 0 (decode s7.executionEnv.code s7.pc) s7 = .ok s8 := by
    rw [hd7]; exact hst7
  obtain ⟨h8pc, h8stk, h8ee, h8am⟩ :=
    step_PUSH_shape_strong s7 s8 callFuel 0 .PUSH2 (by decide) depositLbl 2 hst7
  have hc8 : s8.executionEnv.code = bytecode := by rw [h8ee]; exact hc7
  have hp8 : s8.pc = UInt256.ofNat 16 := by rw [h8pc, hp7]; decide
  -- 8: JUMPI @ 16 (branch logic delegated to weth_routes_deposit)
  have hd8 : decode s8.executionEnv.code s8.pc = some (.JUMPI, none) := by
    rw [hc8, hp8]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s9, hst8, hrun⟩ := wethRun_succ_step callFuel N s8 _ _ _ hd8 (by decide) hrun
  have h8 : EVM.step (callFuel + 1) 0 (decode s8.executionEnv.code s8.pc) s8 = .ok s9 := by
    rw [hd8]; exact hst8
  obtain ⟨h9pc, h9stk, h9ee, h9am⟩ :=
    weth_routes_deposit s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 callFuel 0 0 0 0 0 0 0 0 0
      hcodeB hpc0 hstk0 hselB h0 h1 h2 h3 h4 h5 h6 h7 h8
  have hc9 : s9.executionEnv.code = bytecode := by rw [h9ee]; exact hcodeB
  -- === DEPOSIT BODY (PCs 32–40): peel h9..h17 ===
  -- 9: JUMPDEST @ 32
  have hd9 : decode s9.executionEnv.code s9.pc = some (.JUMPDEST, none) := by
    rw [hc9, h9pc]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s10, hst9, hrun⟩ := wethRun_succ_step callFuel N s9 _ _ _ hd9 (by decide) hrun
  have h9 : EVM.step (callFuel + 1) 0 (decode s9.executionEnv.code s9.pc) s9 = .ok s10 := by
    rw [hd9]; exact hst9
  obtain ⟨h10pc, h10stk, h10ee, h10am⟩ := step_JUMPDEST_shape_strong s9 s10 callFuel 0 none hst9
  rw [h9stk] at h10stk
  have hc10 : s10.executionEnv.code = bytecode := by rw [h10ee]; exact hc9
  have hp10 : s10.pc = UInt256.ofNat 33 := by rw [h10pc, h9pc]; decide
  -- 10: POP @ 33
  have hd10 : decode s10.executionEnv.code s10.pc = some (.POP, none) := by
    rw [hc10, hp10]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s11, hst10, hrun⟩ := wethRun_succ_step callFuel N s10 _ _ _ hd10 (by decide) hrun
  have h10 : EVM.step (callFuel + 1) 0 (decode s10.executionEnv.code s10.pc) s10 = .ok s11 := by
    rw [hd10]; exact hst10
  obtain ⟨h11pc, h11stk, h11ee, h11am⟩ :=
    step_POP_shape_strong s10 s11 callFuel 0 none depositSelector [] h10stk hst10
  have hc11 : s11.executionEnv.code = bytecode := by rw [h11ee]; exact hc10
  have hp11 : s11.pc = UInt256.ofNat 34 := by rw [h11pc, hp10]; decide
  -- 11: CALLER @ 34
  have hd11 : decode s11.executionEnv.code s11.pc = some (.CALLER, none) := by
    rw [hc11, hp11]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s12, hst11, hrun⟩ := wethRun_succ_step callFuel N s11 _ _ _ hd11 (by decide) hrun
  have h11 : EVM.step (callFuel + 1) 0 (decode s11.executionEnv.code s11.pc) s11 = .ok s12 := by
    rw [hd11]; exact hst11
  obtain ⟨h12pc, h12stk, h12ee, h12am⟩ := step_CALLER_value s11 s12 callFuel 0 none hst11
  rw [h11stk] at h12stk
  have hc12 : s12.executionEnv.code = bytecode := by rw [h12ee]; exact hc11
  have hp12 : s12.pc = UInt256.ofNat 35 := by rw [h12pc, hp11]; decide
  -- 12: DUP1 @ 35
  have hd12 : decode s12.executionEnv.code s12.pc = some (.DUP1, none) := by
    rw [hc12, hp12]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s13, hst12, hrun⟩ := wethRun_succ_step callFuel N s12 _ _ _ hd12 (by decide) hrun
  have h12 : EVM.step (callFuel + 1) 0 (decode s12.executionEnv.code s12.pc) s12 = .ok s13 := by
    rw [hd12]; exact hst12
  obtain ⟨h13pc, h13stk, h13ee, h13am⟩ :=
    step_DUP1_shape_strong s12 s13 callFuel 0 none _ [] h12stk hst12
  rw [h12stk] at h13stk
  have hc13 : s13.executionEnv.code = bytecode := by rw [h13ee]; exact hc12
  have hp13 : s13.pc = UInt256.ofNat 36 := by rw [h13pc, hp12]; decide
  -- 13: SLOAD @ 36
  have hd13 : decode s13.executionEnv.code s13.pc = some (.SLOAD, none) := by
    rw [hc13, hp13]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s14, hst13, hrun⟩ := wethRun_succ_step callFuel N s13 _ _ _ hd13 (by decide) hrun
  have h13 : EVM.step (callFuel + 1) 0 (decode s13.executionEnv.code s13.pc) s13 = .ok s14 := by
    rw [hd13]; exact hst13
  obtain ⟨h14pc, h14stk, h14ee, h14am⟩ :=
    step_SLOAD_shape_strong s13 s14 callFuel 0 none _ _ h13stk hst13
  have hc14 : s14.executionEnv.code = bytecode := by rw [h14ee]; exact hc13
  have hp14 : s14.pc = UInt256.ofNat 37 := by rw [h14pc, hp13]; decide
  -- 14: CALLVALUE @ 37
  have hd14 : decode s14.executionEnv.code s14.pc = some (.CALLVALUE, none) := by
    rw [hc14, hp14]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s15, hst14, hrun⟩ := wethRun_succ_step callFuel N s14 _ _ _ hd14 (by decide) hrun
  have h14 : EVM.step (callFuel + 1) 0 (decode s14.executionEnv.code s14.pc) s14 = .ok s15 := by
    rw [hd14]; exact hst14
  obtain ⟨h15pc, h15stk, h15ee, h15am⟩ := step_CALLVALUE_value s14 s15 callFuel 0 none hst14
  rw [h14stk] at h15stk
  have hc15 : s15.executionEnv.code = bytecode := by rw [h15ee]; exact hc14
  have hp15 : s15.pc = UInt256.ofNat 38 := by rw [h15pc, hp14]; decide
  -- 15: ADD @ 38
  have hd15 : decode s15.executionEnv.code s15.pc = some (.ADD, none) := by
    rw [hc15, hp15]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s16, hst15, hrun⟩ := wethRun_succ_step callFuel N s15 _ _ _ hd15 (by decide) hrun
  have h15 : EVM.step (callFuel + 1) 0 (decode s15.executionEnv.code s15.pc) s15 = .ok s16 := by
    rw [hd15]; exact hst15
  obtain ⟨h16pc, h16stk, h16ee, h16am⟩ :=
    step_ADD_value s15 s16 callFuel 0 none _ _ _ h15stk hst15
  have hc16 : s16.executionEnv.code = bytecode := by rw [h16ee]; exact hc15
  have hp16 : s16.pc = UInt256.ofNat 39 := by rw [h16pc, hp15]; decide
  -- 16: SWAP1 @ 39
  have hd16 : decode s16.executionEnv.code s16.pc = some (.SWAP1, none) := by
    rw [hc16, hp16]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s17, hst16, hrun⟩ := wethRun_succ_step callFuel N s16 _ _ _ hd16 (by decide) hrun
  have h16 : EVM.step (callFuel + 1) 0 (decode s16.executionEnv.code s16.pc) s16 = .ok s17 := by
    rw [hd16]; exact hst16
  obtain ⟨h17pc, h17stk, h17ee, h17am⟩ :=
    step_SWAP1_shape_strong s16 s17 callFuel 0 none _ _ [] h16stk hst16
  have hc17 : s17.executionEnv.code = bytecode := by rw [h17ee]; exact hc16
  have hp17 : s17.pc = UInt256.ofNat 40 := by rw [h17pc, hp16]; decide
  -- 17: SSTORE @ 40
  have hd17 : decode s17.executionEnv.code s17.pc = some (.SSTORE, none) := by
    rw [hc17, hp17]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s18, hst17, hrun⟩ := wethRun_succ_step callFuel N s17 _ _ _ hd17 (by decide) hrun
  have h17 : EVM.step (callFuel + 1) 0 (decode s17.executionEnv.code s17.pc) s17 = .ok s18 := by
    rw [hd17]; exact hst17
  obtain ⟨h18pc, h18ee⟩ :=
    step_SSTORE_pc_ee s17 s18 callFuel 0 none _ _ [] h17stk hst17
  have hc18 : s18.executionEnv.code = bytecode := by rw [h18ee]; exact hc17
  have hp18 : s18.pc = UInt256.ofNat 41 := by rw [h18pc, hp17]; decide
  -- 18: STOP @ 41 — halt, empty return data
  have hd18 : decode s18.executionEnv.code s18.pc = some (.STOP, none) := by
    rw [hc18, hp18]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  have hres := wethRun_halt_step callFuel N s18 _ _ _ hd18 (by decide) hrun
  -- res = (s18, .empty)
  have hres1 : res.1 = s18 := by rw [hres]
  have hres2 : res.2 = ByteArray.empty := by rw [hres]; rfl
  -- === deliver the domain conclusion via the credits-from-call theorem ===
  obtain ⟨hcredit, hother⟩ :=
    weth_deposit_credits_from_call s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18
      callFuel 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 C acc
      hcode hpc0 hstk0 hsel hCo hfind
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  refine ⟨?_, ?_, hres2⟩
  · rw [hres1]; exact hcredit
  · intro b hb; rw [hres1]; exact hother b hb

/-- **Unknown selector, as a single big-step over the gas-free
interpreter.** From a call entry whose ABI selector is neither entry
point's, *running the contract to its halt* (`wethRun … = some (s', o)`)
changes no account: both dispatch comparisons fall through, no function
body is entered, and execution reaches the dispatcher's `REVERT` having
modified nothing. The entire 15-instruction dispatch is hidden in the
single `wethRun` hypothesis. -/
theorem weth_unknown_run
    (s0 : EVM.State) (callFuel N : ℕ) (res : EVM.State × ByteArray)
    (hcode : s0.executionEnv.code = wethBytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (hne_dep : functionSelector s0.executionEnv.calldata ≠ depositSelector)
    (hne_wd : functionSelector s0.executionEnv.calldata ≠ withdrawSelector)
    (hrun : wethRun callFuel N s0 = some res) :
    res.1.accountMap = s0.accountMap := by
  have hcodeB : s0.executionEnv.code = bytecode := hcode
  have hne_depB : selectorOf s0.executionEnv.calldata ≠ depositSelector := hne_dep
  have hne_wdB : selectorOf s0.executionEnv.calldata ≠ withdrawSelector := hne_wd
  set selVal := selectorOf s0.executionEnv.calldata with hselVal
  -- 0: PUSH1 0 @ 0
  have hd0 : decode s0.executionEnv.code s0.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
    rw [hcodeB, hpc0]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s1, hst0, hrun⟩ := wethRun_succ_step callFuel N s0 _ _ _ hd0 (by decide) hrun
  have h0 : EVM.step (callFuel + 1) 0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1 := by
    rw [hd0]; exact hst0
  obtain ⟨h1pc, h1stk, h1ee, h1am⟩ := step_PUSH1_shape_strong s0 s1 callFuel 0 (UInt256.ofNat 0) hst0
  have hc1 : s1.executionEnv.code = bytecode := by rw [h1ee]; exact hcodeB
  have hp1 : s1.pc = UInt256.ofNat 2 := by rw [h1pc, hpc0]; decide
  -- 1: CALLDATALOAD @ 2
  have hd1 : decode s1.executionEnv.code s1.pc = some (.CALLDATALOAD, none) := by
    rw [hc1, hp1]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s2, hst1, hrun⟩ := wethRun_succ_step callFuel N s1 _ _ _ hd1 (by decide) hrun
  have h1 : EVM.step (callFuel + 1) 0 (decode s1.executionEnv.code s1.pc) s1 = .ok s2 := by
    rw [hd1]; exact hst1
  have hc2 : s2.executionEnv.code = bytecode := by
    obtain ⟨_, _, h2ee, _⟩ := step_CALLDATALOAD_value s1 s2 callFuel 0 none (UInt256.ofNat 0) [] (by rw [h1stk, hstk0]) hst1
    rw [h2ee]; exact hc1
  have hp2 : s2.pc = UInt256.ofNat 3 := by
    obtain ⟨h2pc, _, _, _⟩ := step_CALLDATALOAD_value s1 s2 callFuel 0 none (UInt256.ofNat 0) [] (by rw [h1stk, hstk0]) hst1
    rw [h2pc, hp1]; decide
  -- 2: PUSH1 0xe0 @ 3
  have hd2 : decode s2.executionEnv.code s2.pc = some (.Push .PUSH1, some (UInt256.ofNat 0xe0, 1)) := by
    rw [hc2, hp2]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s3, hst2, hrun⟩ := wethRun_succ_step callFuel N s2 _ _ _ hd2 (by decide) hrun
  have h2 : EVM.step (callFuel + 1) 0 (decode s2.executionEnv.code s2.pc) s2 = .ok s3 := by
    rw [hd2]; exact hst2
  obtain ⟨h3pc, _, h3ee, _⟩ := step_PUSH1_shape_strong s2 s3 callFuel 0 (UInt256.ofNat 0xe0) hst2
  have hc3 : s3.executionEnv.code = bytecode := by rw [h3ee]; exact hc2
  have hp3 : s3.pc = UInt256.ofNat 5 := by rw [h3pc, hp2]; decide
  -- 3: SHR @ 5
  have hd3 : decode s3.executionEnv.code s3.pc = some (.SHR, none) := by
    rw [hc3, hp3]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s4, hst3, hrun⟩ := wethRun_succ_step callFuel N s3 _ _ _ hd3 (by decide) hrun
  have h3 : EVM.step (callFuel + 1) 0 (decode s3.executionEnv.code s3.pc) s3 = .ok s4 := by
    rw [hd3]; exact hst3
  -- dispatch reaches the selector on the stack at pc 6
  obtain ⟨hs4stk, hs4pc, hs4ee, hs4am⟩ :=
    weth_dispatcher_computes_selector s0 s1 s2 s3 s4 callFuel 0 0 0 0 hcodeB hpc0 hstk0 h0 h1 h2 h3
  rw [← hselVal] at hs4stk
  have hc4 : s4.executionEnv.code = bytecode := by rw [hs4ee]; exact hcodeB
  -- 4: DUP1 @ 6
  have hd4 : decode s4.executionEnv.code s4.pc = some (.DUP1, none) := by
    rw [hc4, hs4pc]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s5, hst4, hrun⟩ := wethRun_succ_step callFuel N s4 _ _ _ hd4 (by decide) hrun
  have h4 : EVM.step (callFuel + 1) 0 (decode s4.executionEnv.code s4.pc) s4 = .ok s5 := by
    rw [hd4]; exact hst4
  obtain ⟨h5pc, h5stk, h5ee, _⟩ := step_DUP1_shape_strong s4 s5 callFuel 0 none selVal [] hs4stk hst4
  rw [hs4stk] at h5stk
  have hc5 : s5.executionEnv.code = bytecode := by rw [h5ee]; exact hc4
  have hp5 : s5.pc = UInt256.ofNat 7 := by rw [h5pc, hs4pc]; decide
  -- 5: PUSH4 depositSelector @ 7
  have hd5 : decode s5.executionEnv.code s5.pc = some (.Push .PUSH4, some (depositSelector, 4)) := by
    rw [hc5, hp5]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s6, hst5, hrun⟩ := wethRun_succ_step callFuel N s5 _ _ _ hd5 (by decide) hrun
  have h5 : EVM.step (callFuel + 1) 0 (decode s5.executionEnv.code s5.pc) s5 = .ok s6 := by
    rw [hd5]; exact hst5
  obtain ⟨h6pc, h6stk, h6ee, _⟩ :=
    step_PUSH_shape_strong s5 s6 callFuel 0 .PUSH4 (by decide) depositSelector 4 hst5
  rw [h5stk] at h6stk
  have hc6 : s6.executionEnv.code = bytecode := by rw [h6ee]; exact hc5
  have hp6 : s6.pc = UInt256.ofNat 12 := by rw [h6pc, hp5]; decide
  -- 6: EQ @ 12
  have hd6 : decode s6.executionEnv.code s6.pc = some (.EQ, none) := by
    rw [hc6, hp6]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s7, hst6, hrun⟩ := wethRun_succ_step callFuel N s6 _ _ _ hd6 (by decide) hrun
  have h6 : EVM.step (callFuel + 1) 0 (decode s6.executionEnv.code s6.pc) s6 = .ok s7 := by
    rw [hd6]; exact hst6
  obtain ⟨h7pc, h7stk, h7ee, _⟩ :=
    step_EQ_value s6 s7 callFuel 0 none depositSelector selVal [selVal] h6stk hst6
  have hc7 : s7.executionEnv.code = bytecode := by rw [h7ee]; exact hc6
  have hp7 : s7.pc = UInt256.ofNat 13 := by rw [h7pc, hp6]; decide
  -- 7: PUSH2 depositLbl @ 13
  have hd7 : decode s7.executionEnv.code s7.pc = some (.Push .PUSH2, some (depositLbl, 2)) := by
    rw [hc7, hp7]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s8, hst7, hrun⟩ := wethRun_succ_step callFuel N s7 _ _ _ hd7 (by decide) hrun
  have h7 : EVM.step (callFuel + 1) 0 (decode s7.executionEnv.code s7.pc) s7 = .ok s8 := by
    rw [hd7]; exact hst7
  obtain ⟨h8pc, h8stk, h8ee, _⟩ :=
    step_PUSH_shape_strong s7 s8 callFuel 0 .PUSH2 (by decide) depositLbl 2 hst7
  rw [h7stk] at h8stk
  have hc8 : s8.executionEnv.code = bytecode := by rw [h8ee]; exact hc7
  have hp8 : s8.pc = UInt256.ofNat 16 := by rw [h8pc, hp7]; decide
  -- 8: JUMPI @ 16 — not taken (selector ≠ deposit)
  have hd8 : decode s8.executionEnv.code s8.pc = some (.JUMPI, none) := by
    rw [hc8, hp8]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s9, hst8, hrun⟩ := wethRun_succ_step callFuel N s8 _ _ _ hd8 (by decide) hrun
  have h8 : EVM.step (callFuel + 1) 0 (decode s8.executionEnv.code s8.pc) s8 = .ok s9 := by
    rw [hd8]; exact hst8
  obtain ⟨h9pc, h9stk, h9ee, _⟩ :=
    step_JUMPI_shape_strong s8 s9 callFuel 0 none depositLbl
      (UInt256.eq depositSelector selVal) [selVal] h8stk hst8
  have hc9 : s9.executionEnv.code = bytecode := by rw [h9ee]; exact hc8
  have hp9 : s9.pc = UInt256.ofNat 17 := by
    rw [h9pc, eq_ne_eq_zero (Ne.symm hne_depB), if_neg (by decide), hp8]; decide
  -- 9: PUSH4 withdrawSelector @ 17
  have hd9 : decode s9.executionEnv.code s9.pc = some (.Push .PUSH4, some (withdrawSelector, 4)) := by
    rw [hc9, hp9]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s10, hst9, hrun⟩ := wethRun_succ_step callFuel N s9 _ _ _ hd9 (by decide) hrun
  have h9 : EVM.step (callFuel + 1) 0 (decode s9.executionEnv.code s9.pc) s9 = .ok s10 := by
    rw [hd9]; exact hst9
  obtain ⟨h10pc, h10stk, h10ee, _⟩ :=
    step_PUSH_shape_strong s9 s10 callFuel 0 .PUSH4 (by decide) withdrawSelector 4 hst9
  rw [h9stk] at h10stk
  have hc10 : s10.executionEnv.code = bytecode := by rw [h10ee]; exact hc9
  have hp10 : s10.pc = UInt256.ofNat 22 := by rw [h10pc, hp9]; decide
  -- 10: EQ @ 22
  have hd10 : decode s10.executionEnv.code s10.pc = some (.EQ, none) := by
    rw [hc10, hp10]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s11, hst10, hrun⟩ := wethRun_succ_step callFuel N s10 _ _ _ hd10 (by decide) hrun
  have h10 : EVM.step (callFuel + 1) 0 (decode s10.executionEnv.code s10.pc) s10 = .ok s11 := by
    rw [hd10]; exact hst10
  obtain ⟨h11pc, h11stk, h11ee, _⟩ :=
    step_EQ_value s10 s11 callFuel 0 none withdrawSelector selVal [] h10stk hst10
  have hc11 : s11.executionEnv.code = bytecode := by rw [h11ee]; exact hc10
  have hp11 : s11.pc = UInt256.ofNat 23 := by rw [h11pc, hp10]; decide
  -- 11: PUSH2 withdrawLbl @ 23
  have hd11 : decode s11.executionEnv.code s11.pc = some (.Push .PUSH2, some (withdrawLbl, 2)) := by
    rw [hc11, hp11]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s12, hst11, hrun⟩ := wethRun_succ_step callFuel N s11 _ _ _ hd11 (by decide) hrun
  have h11 : EVM.step (callFuel + 1) 0 (decode s11.executionEnv.code s11.pc) s11 = .ok s12 := by
    rw [hd11]; exact hst11
  obtain ⟨h12pc, h12stk, h12ee, _⟩ :=
    step_PUSH_shape_strong s11 s12 callFuel 0 .PUSH2 (by decide) withdrawLbl 2 hst11
  rw [h11stk] at h12stk
  have hc12 : s12.executionEnv.code = bytecode := by rw [h12ee]; exact hc11
  have hp12 : s12.pc = UInt256.ofNat 26 := by rw [h12pc, hp11]; decide
  -- 12: JUMPI @ 26 — not taken (selector ≠ withdraw)
  have hd12 : decode s12.executionEnv.code s12.pc = some (.JUMPI, none) := by
    rw [hc12, hp12]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s13, hst12, hrun⟩ := wethRun_succ_step callFuel N s12 _ _ _ hd12 (by decide) hrun
  have h12 : EVM.step (callFuel + 1) 0 (decode s12.executionEnv.code s12.pc) s12 = .ok s13 := by
    rw [hd12]; exact hst12
  obtain ⟨h13pc, h13stk, h13ee, _⟩ :=
    step_JUMPI_shape_strong s12 s13 callFuel 0 none withdrawLbl
      (UInt256.eq withdrawSelector selVal) [] h12stk hst12
  have hc13 : s13.executionEnv.code = bytecode := by rw [h13ee]; exact hc12
  have hp13 : s13.pc = UInt256.ofNat 27 := by
    rw [h13pc, eq_ne_eq_zero (Ne.symm hne_wdB), if_neg (by decide), hp12]; decide
  -- 13: PUSH1 0 @ 27
  have hd13 : decode s13.executionEnv.code s13.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
    rw [hc13, hp13]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s14, hst13, hrun⟩ := wethRun_succ_step callFuel N s13 _ _ _ hd13 (by decide) hrun
  have h13 : EVM.step (callFuel + 1) 0 (decode s13.executionEnv.code s13.pc) s13 = .ok s14 := by
    rw [hd13]; exact hst13
  obtain ⟨h14pc, _, h14ee, _⟩ := step_PUSH1_shape_strong s13 s14 callFuel 0 (UInt256.ofNat 0) hst13
  have hc14 : s14.executionEnv.code = bytecode := by rw [h14ee]; exact hc13
  have hp14 : s14.pc = UInt256.ofNat 29 := by rw [h14pc, hp13]; decide
  -- 14: PUSH1 0 @ 29
  have hd14 : decode s14.executionEnv.code s14.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
    rw [hc14, hp14]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s15, hst14, hrun⟩ := wethRun_succ_step callFuel N s14 _ _ _ hd14 (by decide) hrun
  have h14 : EVM.step (callFuel + 1) 0 (decode s14.executionEnv.code s14.pc) s14 = .ok s15 := by
    rw [hd14]; exact hst14
  obtain ⟨h15pc, _, h15ee, _⟩ := step_PUSH1_shape_strong s14 s15 callFuel 0 (UInt256.ofNat 0) hst14
  have hc15 : s15.executionEnv.code = bytecode := by rw [h15ee]; exact hc14
  have hp15 : s15.pc = UInt256.ofNat 31 := by rw [h15pc, hp14]; decide
  -- 15: REVERT @ 31 — halt
  have hd15 : decode s15.executionEnv.code s15.pc = some (.REVERT, none) := by
    rw [hc15, hp15]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  have hres := wethRun_halt_step callFuel N s15 _ _ _ hd15 (by decide) hrun
  have hres1 : res.1 = s15 := by rw [hres]
  -- account map unchanged across the whole dispatch
  obtain ⟨_, _, ham⟩ :=
    weth_unknown_selector_no_state_change s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
      callFuel 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 hcodeB hpc0 hstk0 hne_depB hne_wdB
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  rw [hres1]; exact ham

/-- **withdraw through the external CALL, as a single big-step over the
gas-free interpreter.** From a call entry (`pc = 0`, empty stack, running
WETH's bytecode) whose ABI selector is `withdraw`'s, with sufficient
balance (`x ≤ balance`), *running the contract to its halt* — dispatch,
the `SSTORE` decrement, the call-setup, **the outbound `CALL` itself**,
and the success check — leaves the caller's recorded balance decreased by
exactly `x`. The external `CALL` is genuinely stepped through; its effect
on `C`'s storage is the explicit no-reentrancy / codeless-recipient
hypothesis `hcallKeep`. Holds whether the call succeeds (→ `STOP`) or
fails (→ `REVERT`). The whole ~40-instruction chain is hidden in the
single `wethRun` hypothesis. -/
theorem weth_withdraw_run
    (s0 : EVM.State) (callFuel N : ℕ) (res : EVM.State × ByteArray)
    (C : Address) (acc : Account .EVM)
    (hcode : s0.executionEnv.code = wethBytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (hsel : functionSelector s0.executionEnv.calldata = withdrawSelector)
    (hCo : s0.executionEnv.codeOwner = C)
    (hfind : s0.accountMap.find? C = some acc)
    (hle : (withdrawArg s0).toNat
            ≤ (acc.lookupStorage (tokenBalanceSlot s0.executionEnv.source)).toNat)
    (hcallKeep : ∀ (sa sb : EVM.State),
        EVM.step (callFuel + 1) 0 (some (.CALL, none)) sa = .ok sb →
        recordedBalance sb.accountMap C (msgSender s0)
          = recordedBalance sa.accountMap C (msgSender s0))
    (hrun : wethRun callFuel N s0 = some res) :
    recordedBalance res.1.accountMap C (msgSender s0)
        = UInt256.sub (recordedBalance s0.accountMap C (msgSender s0)) (withdrawArg s0) := by
  have hcodeB : s0.executionEnv.code = bytecode := hcode
  have hselB : selectorOf s0.executionEnv.calldata = withdrawSelector := hsel
  have hne_depB : selectorOf s0.executionEnv.calldata ≠ depositSelector := by
    rw [hselB]; exact (Ne.symm selectors_distinct)
  -- ===== DISPATCH (PCs 0–26): extract h0..h12, route to the withdraw body =====
  have hd0 : decode s0.executionEnv.code s0.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
    rw [hcodeB, hpc0]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s1, hst0, hrun⟩ := wethRun_succ_step callFuel N s0 _ _ _ hd0 (by decide) hrun
  have h0 : EVM.step (callFuel + 1) 0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1 := by
    rw [hd0]; exact hst0
  obtain ⟨h1pc, h1stk, h1ee, _⟩ := step_PUSH1_shape_strong s0 s1 callFuel 0 (UInt256.ofNat 0) hst0
  rw [hstk0] at h1stk
  have hc1 : s1.executionEnv.code = bytecode := by rw [h1ee]; exact hcodeB
  have hp1 : s1.pc = UInt256.ofNat 2 := by rw [h1pc, hpc0]; decide
  have hd1 : decode s1.executionEnv.code s1.pc = some (.CALLDATALOAD, none) := by
    rw [hc1, hp1]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s2, hst1, hrun⟩ := wethRun_succ_step callFuel N s1 _ _ _ hd1 (by decide) hrun
  have h1 : EVM.step (callFuel + 1) 0 (decode s1.executionEnv.code s1.pc) s1 = .ok s2 := by
    rw [hd1]; exact hst1
  obtain ⟨h2pc, _, h2ee, _⟩ := step_CALLDATALOAD_value s1 s2 callFuel 0 none (UInt256.ofNat 0) [] h1stk hst1
  have hc2 : s2.executionEnv.code = bytecode := by rw [h2ee]; exact hc1
  have hp2 : s2.pc = UInt256.ofNat 3 := by rw [h2pc, hp1]; decide
  have hd2 : decode s2.executionEnv.code s2.pc = some (.Push .PUSH1, some (UInt256.ofNat 0xe0, 1)) := by
    rw [hc2, hp2]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s3, hst2, hrun⟩ := wethRun_succ_step callFuel N s2 _ _ _ hd2 (by decide) hrun
  have h2 : EVM.step (callFuel + 1) 0 (decode s2.executionEnv.code s2.pc) s2 = .ok s3 := by
    rw [hd2]; exact hst2
  obtain ⟨h3pc, _, h3ee, _⟩ := step_PUSH1_shape_strong s2 s3 callFuel 0 (UInt256.ofNat 0xe0) hst2
  have hc3 : s3.executionEnv.code = bytecode := by rw [h3ee]; exact hc2
  have hp3 : s3.pc = UInt256.ofNat 5 := by rw [h3pc, hp2]; decide
  have hd3 : decode s3.executionEnv.code s3.pc = some (.SHR, none) := by
    rw [hc3, hp3]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s4, hst3, hrun⟩ := wethRun_succ_step callFuel N s3 _ _ _ hd3 (by decide) hrun
  have h3 : EVM.step (callFuel + 1) 0 (decode s3.executionEnv.code s3.pc) s3 = .ok s4 := by
    rw [hd3]; exact hst3
  obtain ⟨hs4stk, hs4pc, hs4ee, _⟩ :=
    weth_dispatcher_computes_selector s0 s1 s2 s3 s4 callFuel 0 0 0 0 hcodeB hpc0 hstk0 h0 h1 h2 h3
  rw [hselB] at hs4stk
  have hc4 : s4.executionEnv.code = bytecode := by rw [hs4ee]; exact hcodeB
  have hd4 : decode s4.executionEnv.code s4.pc = some (.DUP1, none) := by
    rw [hc4, hs4pc]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s5, hst4, hrun⟩ := wethRun_succ_step callFuel N s4 _ _ _ hd4 (by decide) hrun
  have h4 : EVM.step (callFuel + 1) 0 (decode s4.executionEnv.code s4.pc) s4 = .ok s5 := by
    rw [hd4]; exact hst4
  obtain ⟨h5pc, h5stk, h5ee, _⟩ := step_DUP1_shape_strong s4 s5 callFuel 0 none withdrawSelector [] hs4stk hst4
  rw [hs4stk] at h5stk
  have hc5 : s5.executionEnv.code = bytecode := by rw [h5ee]; exact hc4
  have hp5 : s5.pc = UInt256.ofNat 7 := by rw [h5pc, hs4pc]; decide
  have hd5 : decode s5.executionEnv.code s5.pc = some (.Push .PUSH4, some (depositSelector, 4)) := by
    rw [hc5, hp5]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s6, hst5, hrun⟩ := wethRun_succ_step callFuel N s5 _ _ _ hd5 (by decide) hrun
  have h5 : EVM.step (callFuel + 1) 0 (decode s5.executionEnv.code s5.pc) s5 = .ok s6 := by
    rw [hd5]; exact hst5
  obtain ⟨h6pc, h6stk, h6ee, _⟩ :=
    step_PUSH_shape_strong s5 s6 callFuel 0 .PUSH4 (by decide) depositSelector 4 hst5
  rw [h5stk] at h6stk
  have hc6 : s6.executionEnv.code = bytecode := by rw [h6ee]; exact hc5
  have hp6 : s6.pc = UInt256.ofNat 12 := by rw [h6pc, hp5]; decide
  have hd6 : decode s6.executionEnv.code s6.pc = some (.EQ, none) := by
    rw [hc6, hp6]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s7, hst6, hrun⟩ := wethRun_succ_step callFuel N s6 _ _ _ hd6 (by decide) hrun
  have h6 : EVM.step (callFuel + 1) 0 (decode s6.executionEnv.code s6.pc) s6 = .ok s7 := by
    rw [hd6]; exact hst6
  obtain ⟨h7pc, h7stk, h7ee, _⟩ :=
    step_EQ_value s6 s7 callFuel 0 none depositSelector withdrawSelector [withdrawSelector] h6stk hst6
  have hc7 : s7.executionEnv.code = bytecode := by rw [h7ee]; exact hc6
  have hp7 : s7.pc = UInt256.ofNat 13 := by rw [h7pc, hp6]; decide
  have hd7 : decode s7.executionEnv.code s7.pc = some (.Push .PUSH2, some (depositLbl, 2)) := by
    rw [hc7, hp7]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s8, hst7, hrun⟩ := wethRun_succ_step callFuel N s7 _ _ _ hd7 (by decide) hrun
  have h7 : EVM.step (callFuel + 1) 0 (decode s7.executionEnv.code s7.pc) s7 = .ok s8 := by
    rw [hd7]; exact hst7
  obtain ⟨h8pc, h8stk, h8ee, _⟩ :=
    step_PUSH_shape_strong s7 s8 callFuel 0 .PUSH2 (by decide) depositLbl 2 hst7
  rw [h7stk] at h8stk
  have hc8 : s8.executionEnv.code = bytecode := by rw [h8ee]; exact hc7
  have hp8 : s8.pc = UInt256.ofNat 16 := by rw [h8pc, hp7]; decide
  have hd8 : decode s8.executionEnv.code s8.pc = some (.JUMPI, none) := by
    rw [hc8, hp8]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s9, hst8, hrun⟩ := wethRun_succ_step callFuel N s8 _ _ _ hd8 (by decide) hrun
  have h8 : EVM.step (callFuel + 1) 0 (decode s8.executionEnv.code s8.pc) s8 = .ok s9 := by
    rw [hd8]; exact hst8
  obtain ⟨h9pc, h9stk, h9ee, _⟩ :=
    step_JUMPI_shape_strong s8 s9 callFuel 0 none depositLbl
      (UInt256.eq depositSelector withdrawSelector) [withdrawSelector] h8stk hst8
  have hc9 : s9.executionEnv.code = bytecode := by rw [h9ee]; exact hc8
  have hp9 : s9.pc = UInt256.ofNat 17 := by
    rw [h9pc, eq_ne_eq_zero selectors_distinct, if_neg (by decide), hp8]; decide
  have hd9 : decode s9.executionEnv.code s9.pc = some (.Push .PUSH4, some (withdrawSelector, 4)) := by
    rw [hc9, hp9]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s10, hst9, hrun⟩ := wethRun_succ_step callFuel N s9 _ _ _ hd9 (by decide) hrun
  have h9 : EVM.step (callFuel + 1) 0 (decode s9.executionEnv.code s9.pc) s9 = .ok s10 := by
    rw [hd9]; exact hst9
  obtain ⟨h10pc, h10stk, h10ee, _⟩ :=
    step_PUSH_shape_strong s9 s10 callFuel 0 .PUSH4 (by decide) withdrawSelector 4 hst9
  rw [h9stk] at h10stk
  have hc10 : s10.executionEnv.code = bytecode := by rw [h10ee]; exact hc9
  have hp10 : s10.pc = UInt256.ofNat 22 := by rw [h10pc, hp9]; decide
  have hd10 : decode s10.executionEnv.code s10.pc = some (.EQ, none) := by
    rw [hc10, hp10]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s11, hst10, hrun⟩ := wethRun_succ_step callFuel N s10 _ _ _ hd10 (by decide) hrun
  have h10 : EVM.step (callFuel + 1) 0 (decode s10.executionEnv.code s10.pc) s10 = .ok s11 := by
    rw [hd10]; exact hst10
  obtain ⟨h11pc, h11stk, h11ee, _⟩ :=
    step_EQ_value s10 s11 callFuel 0 none withdrawSelector withdrawSelector [] h10stk hst10
  have hc11 : s11.executionEnv.code = bytecode := by rw [h11ee]; exact hc10
  have hp11 : s11.pc = UInt256.ofNat 23 := by rw [h11pc, hp10]; decide
  have hd11 : decode s11.executionEnv.code s11.pc = some (.Push .PUSH2, some (withdrawLbl, 2)) := by
    rw [hc11, hp11]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s12, hst11, hrun⟩ := wethRun_succ_step callFuel N s11 _ _ _ hd11 (by decide) hrun
  have h11 : EVM.step (callFuel + 1) 0 (decode s11.executionEnv.code s11.pc) s11 = .ok s12 := by
    rw [hd11]; exact hst11
  obtain ⟨h12pc, _, h12ee, _⟩ :=
    step_PUSH_shape_strong s11 s12 callFuel 0 .PUSH2 (by decide) withdrawLbl 2 hst11
  have hc12 : s12.executionEnv.code = bytecode := by rw [h12ee]; exact hc11
  have hp12 : s12.pc = UInt256.ofNat 26 := by rw [h12pc, hp11]; decide
  have hd12 : decode s12.executionEnv.code s12.pc = some (.JUMPI, none) := by
    rw [hc12, hp12]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s13, hst12, hrun⟩ := wethRun_succ_step callFuel N s12 _ _ _ hd12 (by decide) hrun
  have h12 : EVM.step (callFuel + 1) 0 (decode s12.executionEnv.code s12.pc) s12 = .ok s13 := by
    rw [hd12]; exact hst12
  obtain ⟨h13pc, h13stk, h13ee, h13am⟩ :=
    weth_routes_withdraw s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 callFuel
      0 0 0 0 0 0 0 0 0 0 0 0 0 hcodeB hpc0 hstk0 hselB
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hc13 : s13.executionEnv.code = bytecode := by rw [h13ee]; exact hcodeB
  have hCo13 : s13.executionEnv.codeOwner = C := by rw [h13ee]; exact hCo
  have hfind13 : s13.accountMap.find? C = some acc := by rw [h13am]; exact hfind
  -- transport sufficient-balance to s13
  have hcdld13 : EvmYul.State.calldataload s13.toState (UInt256.ofNat 4)
               = EvmYul.State.calldataload s0.toState (UInt256.ofNat 4) := by
    unfold EvmYul.State.calldataload
    rw [show s13.toState.executionEnv.calldata = s0.toState.executionEnv.calldata from
        congrArg EvmYul.ExecutionEnv.calldata h13ee]
  have hsrc13 : s13.executionEnv.source = s0.executionEnv.source :=
    congrArg EvmYul.ExecutionEnv.source h13ee
  have hle13 : (EvmYul.State.calldataload s13.toState (UInt256.ofNat 4)).toNat
             ≤ (acc.lookupStorage (UInt256.ofNat s13.executionEnv.source.val)).toNat := by
    rw [hcdld13, hsrc13]; exact hle
  -- ===== WITHDRAW BODY (PCs 42–60): extract h13..h28, reach pc 61 =====
  -- 13: JUMPDEST @ 42
  have hd13d : decode s13.executionEnv.code s13.pc = some (.JUMPDEST, none) := by
    rw [hc13, h13pc]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s14, hst13, hrun⟩ := wethRun_succ_step callFuel N s13 _ _ _ hd13d (by decide) hrun
  have h13' : EVM.step (callFuel + 1) 0 (decode s13.executionEnv.code s13.pc) s13 = .ok s14 := by
    rw [hd13d]; exact hst13
  obtain ⟨h14pc, h14stk, h14ee, _⟩ := step_JUMPDEST_shape_strong s13 s14 callFuel 0 none hst13
  rw [h13stk] at h14stk
  have hc14 : s14.executionEnv.code = bytecode := by rw [h14ee]; exact hc13
  have hp14 : s14.pc = UInt256.ofNat 43 := by rw [h14pc, h13pc]; decide
  -- 14: PUSH1 4 @ 43
  have hd14d : decode s14.executionEnv.code s14.pc = some (.Push .PUSH1, some (UInt256.ofNat 4, 1)) := by
    rw [hc14, hp14]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s15, hst14, hrun⟩ := wethRun_succ_step callFuel N s14 _ _ _ hd14d (by decide) hrun
  have h14' : EVM.step (callFuel + 1) 0 (decode s14.executionEnv.code s14.pc) s14 = .ok s15 := by
    rw [hd14d]; exact hst14
  obtain ⟨h15pc, h15stk, h15ee, _⟩ := step_PUSH1_shape_strong s14 s15 callFuel 0 (UInt256.ofNat 4) hst14
  rw [h14stk] at h15stk
  have hc15 : s15.executionEnv.code = bytecode := by rw [h15ee]; exact hc14
  have hp15 : s15.pc = UInt256.ofNat 45 := by rw [h15pc, hp14]; decide
  -- 15: CALLDATALOAD @ 45
  have hd15d : decode s15.executionEnv.code s15.pc = some (.CALLDATALOAD, none) := by
    rw [hc15, hp15]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s16, hst15, hrun⟩ := wethRun_succ_step callFuel N s15 _ _ _ hd15d (by decide) hrun
  have h15' : EVM.step (callFuel + 1) 0 (decode s15.executionEnv.code s15.pc) s15 = .ok s16 := by
    rw [hd15d]; exact hst15
  obtain ⟨h16pc, h16stk, h16ee, _⟩ :=
    step_CALLDATALOAD_value s15 s16 callFuel 0 none (UInt256.ofNat 4) [] h15stk hst15
  have hc16 : s16.executionEnv.code = bytecode := by rw [h16ee]; exact hc15
  have hp16 : s16.pc = UInt256.ofNat 46 := by rw [h16pc, hp15]; decide
  -- name the withdraw amount `x = calldata[4:36]` (the value now on the stack)
  set xV := EvmYul.State.calldataload s15.toState (UInt256.ofNat 4) with hxV
  -- 16: CALLER @ 46
  have hd16d : decode s16.executionEnv.code s16.pc = some (.CALLER, none) := by
    rw [hc16, hp16]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s17, hst16, hrun⟩ := wethRun_succ_step callFuel N s16 _ _ _ hd16d (by decide) hrun
  have h16'' : EVM.step (callFuel + 1) 0 (decode s16.executionEnv.code s16.pc) s16 = .ok s17 := by
    rw [hd16d]; exact hst16
  obtain ⟨h17pc, h17stk, h17ee, _⟩ := step_CALLER_value s16 s17 callFuel 0 none hst16
  rw [h16stk] at h17stk
  have hc17 : s17.executionEnv.code = bytecode := by rw [h17ee]; exact hc16
  have hp17 : s17.pc = UInt256.ofNat 47 := by rw [h17pc, hp16]; decide
  -- s17.stack = [callerV, xV] where callerV = ofNat s16.source.val
  -- 17: DUP1 @ 47
  have hd17d : decode s17.executionEnv.code s17.pc = some (.DUP1, none) := by
    rw [hc17, hp17]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s18, hst17, hrun⟩ := wethRun_succ_step callFuel N s17 _ _ _ hd17d (by decide) hrun
  have h17' : EVM.step (callFuel + 1) 0 (decode s17.executionEnv.code s17.pc) s17 = .ok s18 := by
    rw [hd17d]; exact hst17
  obtain ⟨h18pc, h18stk, h18ee, _⟩ :=
    step_DUP1_shape_strong s17 s18 callFuel 0 none (UInt256.ofNat s16.executionEnv.source.val) [xV] h17stk hst17
  rw [h17stk] at h18stk
  have hc18 : s18.executionEnv.code = bytecode := by rw [h18ee]; exact hc17
  have hp18 : s18.pc = UInt256.ofNat 48 := by rw [h18pc, hp17]; decide
  -- 18: SLOAD @ 48
  set balV := s18.lookupAccount s18.executionEnv.codeOwner |>.option ⟨0⟩
      (Account.lookupStorage (k := UInt256.ofNat s16.executionEnv.source.val)) with hbalV
  have hd18d : decode s18.executionEnv.code s18.pc = some (.SLOAD, none) := by
    rw [hc18, hp18]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s19, hst18, hrun⟩ := wethRun_succ_step callFuel N s18 _ _ _ hd18d (by decide) hrun
  have h18' : EVM.step (callFuel + 1) 0 (decode s18.executionEnv.code s18.pc) s18 = .ok s19 := by
    rw [hd18d]; exact hst18
  obtain ⟨h19pc, h19stk, h19ee, _⟩ :=
    step_SLOAD_shape_strong s18 s19 callFuel 0 none (UInt256.ofNat s16.executionEnv.source.val)
      [UInt256.ofNat s16.executionEnv.source.val, xV] h18stk hst18
  have hc19 : s19.executionEnv.code = bytecode := by rw [h19ee]; exact hc18
  have hp19 : s19.pc = UInt256.ofNat 49 := by rw [h19pc, hp18]; decide
  -- 19: DUP3 @ 49
  have hd19d : decode s19.executionEnv.code s19.pc = some (.DUP3, none) := by
    rw [hc19, hp19]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s20, hst19, hrun⟩ := wethRun_succ_step callFuel N s19 _ _ _ hd19d (by decide) hrun
  have h19' : EVM.step (callFuel + 1) 0 (decode s19.executionEnv.code s19.pc) s19 = .ok s20 := by
    rw [hd19d]; exact hst19
  obtain ⟨h20pc, h20stk, h20ee, _⟩ :=
    step_DUP3_shape_strong s19 s20 callFuel 0 none balV (UInt256.ofNat s16.executionEnv.source.val) xV [] h19stk hst19
  rw [h19stk] at h20stk
  have hc20 : s20.executionEnv.code = bytecode := by rw [h20ee]; exact hc19
  have hp20 : s20.pc = UInt256.ofNat 50 := by rw [h20pc, hp19]; decide
  -- 20: DUP2 @ 50
  have hd20d : decode s20.executionEnv.code s20.pc = some (.DUP2, none) := by
    rw [hc20, hp20]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s21, hst20, hrun⟩ := wethRun_succ_step callFuel N s20 _ _ _ hd20d (by decide) hrun
  have h20' : EVM.step (callFuel + 1) 0 (decode s20.executionEnv.code s20.pc) s20 = .ok s21 := by
    rw [hd20d]; exact hst20
  obtain ⟨h21pc, h21stk, h21ee, _⟩ :=
    step_DUP2_shape_strong s20 s21 callFuel 0 none xV balV [UInt256.ofNat s16.executionEnv.source.val, xV] h20stk hst20
  rw [h20stk] at h21stk
  have hc21 : s21.executionEnv.code = bytecode := by rw [h21ee]; exact hc20
  have hp21 : s21.pc = UInt256.ofNat 51 := by rw [h21pc, hp20]; decide
  -- 21: LT @ 51
  have hd21d : decode s21.executionEnv.code s21.pc = some (.LT, none) := by
    rw [hc21, hp21]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s22, hst21, hrun⟩ := wethRun_succ_step callFuel N s21 _ _ _ hd21d (by decide) hrun
  have h21' : EVM.step (callFuel + 1) 0 (decode s21.executionEnv.code s21.pc) s21 = .ok s22 := by
    rw [hd21d]; exact hst21
  obtain ⟨h22pc, h22stk, h22ee, _⟩ :=
    step_LT_shape_strong s21 s22 callFuel 0 none balV xV [balV, UInt256.ofNat s16.executionEnv.source.val, xV] h21stk hst21
  have hc22 : s22.executionEnv.code = bytecode := by rw [h22ee]; exact hc21
  have hp22 : s22.pc = UInt256.ofNat 52 := by rw [h22pc, hp21]; decide
  -- 22: PUSH2 revertLbl @ 52
  have hd22d : decode s22.executionEnv.code s22.pc = some (.Push .PUSH2, some (revertLbl, 2)) := by
    rw [hc22, hp22]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s23, hst22, hrun⟩ := wethRun_succ_step callFuel N s22 _ _ _ hd22d (by decide) hrun
  have h22' : EVM.step (callFuel + 1) 0 (decode s22.executionEnv.code s22.pc) s22 = .ok s23 := by
    rw [hd22d]; exact hst22
  obtain ⟨h23pc, h23stk, h23ee, _⟩ :=
    step_PUSH_shape_strong s22 s23 callFuel 0 .PUSH2 (by decide) revertLbl 2 hst22
  rw [h22stk] at h23stk
  have hc23 : s23.executionEnv.code = bytecode := by rw [h23ee]; exact hc22
  have hp23 : s23.pc = UInt256.ofNat 55 := by rw [h23pc, hp22]; decide
  -- gate: LT balV xV = 0
  have hee16_0 : s16.executionEnv = s13.executionEnv := by rw [h16ee, h15ee, h14ee]
  have h18ee0 : s18.executionEnv = s13.executionEnv := by rw [h18ee, h17ee, hee16_0]
  have h18am13 : s18.accountMap = s13.accountMap := by
    obtain ⟨_, _, _, a14⟩ := step_JUMPDEST_shape_strong s13 s14 callFuel 0 none hst13
    obtain ⟨_, _, _, a15⟩ := step_PUSH1_shape_strong s14 s15 callFuel 0 (UInt256.ofNat 4) hst14
    obtain ⟨_, _, _, a16⟩ := step_CALLDATALOAD_value s15 s16 callFuel 0 none (UInt256.ofNat 4) [] h15stk hst15
    obtain ⟨_, _, _, a17⟩ := step_CALLER_value s16 s17 callFuel 0 none hst16
    obtain ⟨_, _, _, a18⟩ := step_DUP1_shape_strong s17 s18 callFuel 0 none (UInt256.ofNat s16.executionEnv.source.val) [xV] h17stk hst17
    rw [a18, a17, a16, a15, a14]
  have hbalEq : balV = acc.lookupStorage (UInt256.ofNat s16.executionEnv.source.val) := by
    rw [hbalV]; simp only [EvmYul.State.lookupAccount]
    rw [h18am13, h13am, h18ee0, h13ee, hCo, hfind]; rfl
  have hsrc16 : s16.executionEnv.source = s0.executionEnv.source := by
    rw [hee16_0, h13ee]
  have hxV0 : xV = EvmYul.State.calldataload s0.toState (UInt256.ofNat 4) := by
    rw [hxV]; unfold EvmYul.State.calldataload
    rw [show s15.toState.executionEnv.calldata = s0.toState.executionEnv.calldata from
        congrArg EvmYul.ExecutionEnv.calldata
          (show s15.executionEnv = s0.executionEnv by rw [h15ee, h14ee, h13ee])]
  have hgate : UInt256.lt balV xV = UInt256.ofNat 0 := by
    apply lt_eq_zero_of_le
    rw [hxV0, hbalEq, hsrc16]; exact hle
  -- 23: JUMPI @ 55 — not taken (sufficient balance), pc → 56
  have hd23d : decode s23.executionEnv.code s23.pc = some (.JUMPI, none) := by
    rw [hc23, hp23]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s24, hst23, hrun⟩ := wethRun_succ_step callFuel N s23 _ _ _ hd23d (by decide) hrun
  have h23' : EVM.step (callFuel + 1) 0 (decode s23.executionEnv.code s23.pc) s23 = .ok s24 := by
    rw [hd23d]; exact hst23
  obtain ⟨h24pc, h24stk, h24ee, _⟩ :=
    step_JUMPI_shape_strong s23 s24 callFuel 0 none revertLbl (UInt256.lt balV xV)
      [balV, UInt256.ofNat s16.executionEnv.source.val, xV] h23stk hst23
  have hc24 : s24.executionEnv.code = bytecode := by rw [h24ee]; exact hc23
  have hp24 : s24.pc = UInt256.ofNat 56 := by
    rw [h24pc, hgate, if_neg (by decide), hp23]; decide
  -- 24: DUP3 @ 56
  have hd24d : decode s24.executionEnv.code s24.pc = some (.DUP3, none) := by
    rw [hc24, hp24]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s25, hst24, hrun⟩ := wethRun_succ_step callFuel N s24 _ _ _ hd24d (by decide) hrun
  have h24' : EVM.step (callFuel + 1) 0 (decode s24.executionEnv.code s24.pc) s24 = .ok s25 := by
    rw [hd24d]; exact hst24
  obtain ⟨h25pc, h25stk, h25ee, _⟩ :=
    step_DUP3_shape_strong s24 s25 callFuel 0 none balV (UInt256.ofNat s16.executionEnv.source.val) xV [] h24stk hst24
  rw [h24stk] at h25stk
  have hc25 : s25.executionEnv.code = bytecode := by rw [h25ee]; exact hc24
  have hp25 : s25.pc = UInt256.ofNat 57 := by rw [h25pc, hp24]; decide
  -- 25: SWAP1 @ 57
  have hd25d : decode s25.executionEnv.code s25.pc = some (.SWAP1, none) := by
    rw [hc25, hp25]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s26, hst25, hrun⟩ := wethRun_succ_step callFuel N s25 _ _ _ hd25d (by decide) hrun
  have h25' : EVM.step (callFuel + 1) 0 (decode s25.executionEnv.code s25.pc) s25 = .ok s26 := by
    rw [hd25d]; exact hst25
  obtain ⟨h26pc, h26stk, h26ee, _⟩ :=
    step_SWAP1_shape_strong s25 s26 callFuel 0 none xV balV [UInt256.ofNat s16.executionEnv.source.val, xV] h25stk hst25
  have hc26 : s26.executionEnv.code = bytecode := by rw [h26ee]; exact hc25
  have hp26 : s26.pc = UInt256.ofNat 58 := by rw [h26pc, hp25]; decide
  -- 26: SUB @ 58
  have hd26d : decode s26.executionEnv.code s26.pc = some (.SUB, none) := by
    rw [hc26, hp26]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s27, hst26, hrun⟩ := wethRun_succ_step callFuel N s26 _ _ _ hd26d (by decide) hrun
  have h26' : EVM.step (callFuel + 1) 0 (decode s26.executionEnv.code s26.pc) s26 = .ok s27 := by
    rw [hd26d]; exact hst26
  obtain ⟨h27pc, h27stk, h27ee, _⟩ :=
    step_SUB_shape_strong s26 s27 callFuel 0 none balV xV [UInt256.ofNat s16.executionEnv.source.val, xV] h26stk hst26
  have hc27 : s27.executionEnv.code = bytecode := by rw [h27ee]; exact hc26
  have hp27 : s27.pc = UInt256.ofNat 59 := by rw [h27pc, hp26]; decide
  -- 27: SWAP1 @ 59
  have hd27d : decode s27.executionEnv.code s27.pc = some (.SWAP1, none) := by
    rw [hc27, hp27]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s28, hst27, hrun⟩ := wethRun_succ_step callFuel N s27 _ _ _ hd27d (by decide) hrun
  have h27' : EVM.step (callFuel + 1) 0 (decode s27.executionEnv.code s27.pc) s27 = .ok s28 := by
    rw [hd27d]; exact hst27
  obtain ⟨h28pc, h28stk, h28ee, _⟩ :=
    step_SWAP1_shape_strong s27 s28 callFuel 0 none (UInt256.sub balV xV) (UInt256.ofNat s16.executionEnv.source.val) [xV] h27stk hst27
  have hc28 : s28.executionEnv.code = bytecode := by rw [h28ee]; exact hc27
  have hp28 : s28.pc = UInt256.ofNat 60 := by rw [h28pc, hp27]; decide
  -- 28: SSTORE @ 60 — reach pc 61, stack [xV]
  have hd28d : decode s28.executionEnv.code s28.pc = some (.SSTORE, none) := by
    rw [hc28, hp28]; native_decide
  obtain _ | N := N
  · simp [wethRun] at hrun
  obtain ⟨s29, hst28, hrun⟩ := wethRun_succ_step callFuel N s28 _ _ _ hd28d (by decide) hrun
  have h28' : EVM.step (callFuel + 1) 0 (decode s28.executionEnv.code s28.pc) s28 = .ok s29 := by
    rw [hd28d]; exact hst28
  obtain ⟨h29pc, h29stk, h29ee⟩ :=
    step_SSTORE_shape s28 s29 callFuel 0 none (UInt256.ofNat s16.executionEnv.source.val) (UInt256.sub balV xV) [xV] h28stk hst28
  have hc29 : s29.executionEnv.code = bytecode := by rw [h29ee]; exact hc28
  have hp29 : s29.pc = UInt256.ofNat 61 := by rw [h29pc, hp28]; decide
  -- recorded-balance delta at s29 (the end-to-end decrement theorem)
  obtain ⟨hrb29, _⟩ :=
    weth_withdraw_decrements_from_call s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18
      s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29
      callFuel 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 C acc
      hcode hpc0 hstk0 hsel hCo hfind hle
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13' h14' h15' h16'' h17' h18' h19' h20' h21'
      h22' h23' h24' h25' h26' h27' h28'
  -- s29.stack = [xV]
  have h29stk' : s29.stack = [xV] := h29stk
  -- ===== run the tail through the CALL to the halt =====
  exact wethRun_withdraw_tail s29 callFuel N res C (msgSender s0) xV
    (UInt256.sub (recordedBalance s0.accountMap C (msgSender s0)) (withdrawArg s0))
    hc29 hp29 h29stk' hrb29 hcallKeep hrun

end EvmSmith.Weth
