import EvmSmith.Demos.Weth.SpecDSL

/-!
# WETH — the spec (high-level statements only)

This file is **the spec a reader opens**: nothing but WETH's guarantees,
each one a short statement they can read like a Solidity pre/post spec.
Everything supporting it is elsewhere:

* the spec vocabulary (`balance[·]`, `sender`, `value`, `amount`,
  `ensures`, `untouched (others)`, `Calls`, `Halts`, `Solvent`, …) is in
  `SpecDSL.lean`;
* the proofs from the bytecode are in `Behaviour.lean` (the gas-free
  interpreter `wethRun` + the `weth_*_run_impl` walks) and `Solvency.lean`.

Each theorem below is discharged by one line into that machinery — so if a
statement here did not *mean* what it appears to, the proof would not
type-check. The prettiness cannot drift from what is proven.

## The contract (86 bytes of runtime code)

| Selector     | Solidity                | Behaviour                                   |
|--------------|-------------------------|---------------------------------------------|
| `0xd0e30db0` | `deposit() payable`     | `balance[msg.sender] += msg.value`          |
| `0x2e1a7d4d` | `withdraw(uint256 x)`   | require `balance[msg.sender] ≥ x`; subtract `x`; then `CALL` `x` wei back to `msg.sender` |

Token balances live at `storage[address]` directly (not Solidity's
hashed `mapping` slot) — see `tokenBalanceSlot` in `SpecDSL.lean`.

## How to read the statements

* `Calls .deposit s` — `s` is the entry of a `deposit()` call (pc 0, empty
  stack, WETH's code, that selector).
* `ensures …` — for every run of the contract to its halt: `balance[a]` is
  the post-state balance, `old balance[a]` the pre-state one, `sender` /
  `value` / `amount` are `msg.sender` / `msg.value` / the `uint256` arg.
* `untouched (others)` — every balance except the caller's is unchanged.
* `NoReentrancy s` — the external call does not reenter to change balances.
-/

namespace EvmSmith.Weth

open EvmYul EvmYul.EVM EvmYul.Frame Batteries EvmSmith.Layer1 EvmSmith.Spec

/-! ## Behavioural guarantees -/

/-- **`deposit()` credits the caller by `msg.value`.** -/
theorem deposit (s : EVM.State) (call : Calls .deposit s) :
    ensures
      balance[sender] = old balance[sender] + value
    ∧ untouched (others)
    ∧ returndata = empty := by
  obtain ⟨hcode, hpc0, hstk0, ⟨acc, hfind⟩, hsel⟩ := call
  intro s' o ⟨callFuel, N, hrun⟩
  have h := weth_deposit_run_impl s callFuel N (s', o) s.executionEnv.codeOwner acc
    hcode hpc0 hstk0 hsel rfl hfind hrun
  exact ⟨h.1.trans (uint256_add_comm _ _), h.2.1, h.2.2⟩

/-- **`withdraw(x)` debits the caller by `x`** — end to end, *through the
external `CALL`* — given sufficient balance and no reentrancy. -/
theorem withdraw (s : EVM.State) (call : Calls .withdraw s)
    (funded : amount ≤ old balance[sender]) (noReentry : NoReentrancy s) :
    ensures
      balance[sender] = old balance[sender] - amount := by
  obtain ⟨hcode, hpc0, hstk0, ⟨acc, hfind⟩, hsel⟩ := call
  intro s' o ⟨callFuel, N, hrun⟩
  have hle : (withdrawArg s).toNat
      ≤ (acc.lookupStorage (tokenBalanceSlot s.executionEnv.source)).toNat := by
    rw [recordedBalance_of_find s.accountMap s.executionEnv.codeOwner
          s.executionEnv.source acc hfind] at funded
    exact funded
  exact weth_withdraw_run_impl s callFuel N (s', o) s.executionEnv.codeOwner acc
    hcode hpc0 hstk0 hsel rfl hfind hle (fun sa sb h => noReentry callFuel sa sb h) hrun

/-- **An unknown selector changes nothing** (reverts; no fallback/receive). -/
theorem fallback (s : EVM.State) (call : Calls .unknown s) :
    ensures
      storage = old storage := by
  obtain ⟨hcode, hpc0, hstk0, _, hne_dep, hne_wd⟩ := call
  intro s' o ⟨callFuel, N, hrun⟩
  exact weth_unknown_run_impl s callFuel N (s', o) hcode hpc0 hstk0 hne_dep hne_wd hrun

/-! ## Solvency guarantee -/

/-- **WETH is always solvent.** If WETH is solvent before a transaction,
then after running *any* Ethereum transaction it is still solvent (or the
transaction reverted, in which case nothing changed). Conditional on the
pre-state being well-formed, WETH not being the sender/miner, the tx being
valid, and the deployment/chain-state bundle `SolvencyAssumptions`. -/
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

end EvmSmith.Weth
