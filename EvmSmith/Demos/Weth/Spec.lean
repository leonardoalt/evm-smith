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
   *do*, established by executing the bytecode (`functionSelector`,
   `weth_computes_function_selector`, …). More postconditions are added
   here as they are proved.

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

`functionSelector` is the ABI selector a call carries. The step
hypotheses `hN` in the theorems below say "instruction N executed
successfully"; whether a step succeeds depends on gas, which is
orthogonal to *what* the instruction computes. -/

/-- The ABI **function selector** of a call: the high 4 bytes of the
first calldata word, `calldataload(0) >> 224`. -/
def functionSelector (calldata : ByteArray) : UInt256 :=
  selectorOf calldata

/-- **The dispatcher computes the ABI selector.** From the contract's
entry state (empty stack), executing the dispatcher's selector-extraction
instructions (`PUSH1 0; CALLDATALOAD; PUSH1 0xe0; SHR`) leaves exactly
`functionSelector calldata` on the stack — the value the two entry-point
branches are then compared against. -/
theorem weth_computes_function_selector
    (s0 s1 s2 s3 s4 : EVM.State) (f c0 c1 c2 c3 : ℕ)
    (hstk0 : s0.stack = [])
    (h0 : EVM.step (f + 1) c0 (some (.Push .PUSH1, some (UInt256.ofNat 0, 1))) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (some (.CALLDATALOAD, none)) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (some (.Push .PUSH1, some (UInt256.ofNat 0xe0, 1))) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (some (.SHR, none)) s3 = .ok s4) :
    s4.stack = [functionSelector s0.executionEnv.calldata] :=
  weth_dispatcher_computes_selector s0 s1 s2 s3 s4 f c0 c1 c2 c3 hstk0 h0 h1 h2 h3

end EvmSmith.Weth
