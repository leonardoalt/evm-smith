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

open EvmYul EvmYul.EVM EvmYul.Frame

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
    s18.accountMap
      = s0.accountMap.insert C
          (acc.updateStorage (tokenBalanceSlot s0.executionEnv.source)
            (UInt256.add s0.executionEnv.weiValue
              (acc.lookupStorage (tokenBalanceSlot s0.executionEnv.source)))) :=
  weth_deposit_from_entry s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18
    f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 C acc
    hcode hpc0 hstk0 hsel hCo hfind
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

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
    s29.accountMap
      = s0.accountMap.insert C
          (acc.updateStorage (tokenBalanceSlot s0.executionEnv.source)
            (UInt256.sub (acc.lookupStorage (tokenBalanceSlot s0.executionEnv.source))
              (EvmYul.State.calldataload s0.toState (UInt256.ofNat 4)))) :=
  weth_withdraw_from_entry s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18
    s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29
    f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
    c23 c24 c25 c26 c27 c28 C acc hcode hpc0 hstk0 hsel hCo hfind hle
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
    h23 h24 h25 h26 h27 h28

end EvmSmith.Weth
