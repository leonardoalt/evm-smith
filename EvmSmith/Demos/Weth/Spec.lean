import EvmSmith.Demos.Weth.Behaviour

/-!
# WETH — the formal spec (human-readable)

This file is **the spec**: the single place an auditor or smart contract dev
needs to read to know *what* the WETH contract guarantees. It states the
guarantees in plain Lean `def`s and `theorem`s with English names; all
the proof machinery — the storage-readback lemmas, the bytecode walk,
the gas-free interpreter — lives in `Behaviour.lean` (and below it,
`Dispatch.lean` / `Solvency.lean` / EVMYulLean). Each headline theorem
here is *proved by* one line into that machinery:

    read this file  ──►  weth_is_always_solvent     weth_deposit_run / … _run
                              │                              │
                              ▼                              ▼
                    weth_solvency_invariant        weth_*_run_impl   (Behaviour.lean)
                              │                              │
                              ▼                              ▼
                  the bytecode walk + EVMYulLean semantics

The spec vocabulary (`ethBalance`, `recordedTokenSupply`, `Solvent`, …)
is *definitionally equal* to the predicates the proofs use (`balanceOf`,
`storageSum`, `WethInv`); the `*_iff_*` bridge lemmas, each proved by
`rfl`, witness that equality — so "the spec is what the theorems use" is
checked by Lean, not asserted.

## How to read it

1. **The vocabulary** — `ethBalance`, `tokenBalanceOf`,
   `recordedTokenSupply` (and, from `Behaviour.lean`, `tokenBalanceSlot`,
   `recordedBalance`, `msgSender`, `msgValue`, `withdrawArg`).
2. **The property** — `Solvent`.
3. **Running a transaction** — `ExecContext`, `runTx`, `SolventAfter`.
4. **The assumptions** — `SolvencyAssumptions`.
5. **The solvency guarantee** — `weth_is_always_solvent`.
6. **The behavioural guarantees (big-step)** — what each entry point
   *does*, each stated as a single run of the contract to its halt
   (`wethRun … = some (s', o)`, the real `EVM.step` with gas ignored):
   - `weth_deposit_run` — a deposit call credits `msg.value` to the
     caller and returns empty data;
   - `weth_unknown_run` — an unknown selector changes no account
     (reverts; no fallback/receive);
   - `weth_withdraw_run` — a withdraw call, run *through the external
     `CALL`*, decrements the caller by `x`, under the explicit
     no-reentrancy / codeless-recipient hypothesis `hcallKeep` (covering
     both the success → `STOP` and failure → `REVERT` halts).

   The finer-grained engine lemmas these are built from — dispatch
   routing, the bare-transfer `CALL` arguments, the per-step `*_from_call`
   deltas — live in `Behaviour.lean`.

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
address directly as the slot key. The spec relies only on distinct users
getting distinct slots (`addressSlot_injective`).
-/

namespace EvmSmith.Weth

open EvmYul EvmYul.EVM EvmYul.Frame Batteries EvmSmith.Layer1

/-! ## Solvency vocabulary

Readable wrappers over the EVMYulLean state projections, interpreted in
`ℕ` (unbounded), matching the underlying `balanceOf` / `storageSum`
convention. (`tokenBalanceSlot` and the `UInt256`-valued `recordedBalance`
live in `Behaviour.lean`, since the behavioural postconditions use them.) -/

/-- WETH's actual on-chain ETH balance (in wei), as held by the EVM
account map `σ` at address `weth`. Unknown account ⇒ `0`. -/
def ethBalance (σ : AccountMap .EVM) (weth : Address) : ℕ :=
  balanceOf σ weth

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

/-! ## The solvency guarantee

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
engine that does the instruction-by-instruction bytecode walk. -/
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

/-! ## The behavioural guarantees (big-step)

What each entry point *does*, established by **running the contract to
its halt**: each takes a single `wethRun callFuel N s0 = some (s', o)`
hypothesis — `wethRun` is the real `EVM.step` iterated from the
contract's own bytecode with gas ignored — and concludes the final
state and return data. The entire per-instruction chain (dispatch
routing + the function body, ~15–40 steps) is hidden inside that one
hypothesis. Each is a one-line restatement of the proof in
`Behaviour.lean`. -/

/-- **A deposit call credits the caller.** Run from the call entry
(`pc = 0`, empty stack, WETH's bytecode) with the `deposit` selector,
the caller's recorded balance grows by `msg.value`, every other balance
is unchanged, and the call returns empty data. -/
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
    ∧ res.2 = ByteArray.empty :=
  weth_deposit_run_impl s0 callFuel N res C acc hcode hpc0 hstk0 hsel hCo hfind hrun

/-- **An unknown selector changes nothing.** Run from the call entry with
a selector that is neither entry point's, the contract reverts having
modified no account (no fallback / `receive`). -/
theorem weth_unknown_run
    (s0 : EVM.State) (callFuel N : ℕ) (res : EVM.State × ByteArray)
    (hcode : s0.executionEnv.code = wethBytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (hne_dep : functionSelector s0.executionEnv.calldata ≠ depositSelector)
    (hne_wd : functionSelector s0.executionEnv.calldata ≠ withdrawSelector)
    (hrun : wethRun callFuel N s0 = some res) :
    res.1.accountMap = s0.accountMap :=
  weth_unknown_run_impl s0 callFuel N res hcode hpc0 hstk0 hne_dep hne_wd hrun

/-- **A withdraw call debits the caller — through the external CALL.**
Run from the call entry with the `withdraw` selector and sufficient
balance (`x ≤ balance`), to its halt — including the outbound `CALL`
back to the caller — the caller's recorded balance decreases by exactly
`x = calldata[4:36]`. `hcallKeep` is the explicit no-reentrancy /
codeless-recipient assumption (the external call does not reenter to
alter `C`'s recorded balance); the conclusion holds whether the call
succeeds (→ `STOP`) or fails (→ `REVERT`). -/
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
        = UInt256.sub (recordedBalance s0.accountMap C (msgSender s0)) (withdrawArg s0) :=
  weth_withdraw_run_impl s0 callFuel N res C acc hcode hpc0 hstk0 hsel hCo hfind hle hcallKeep hrun

end EvmSmith.Weth
