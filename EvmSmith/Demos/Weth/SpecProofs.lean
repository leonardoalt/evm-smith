import EvmSmith.Demos.Weth.Spec
import EvmSmith.Demos.Weth.Behaviour

/-!
# WETH satisfies its spec

The witness that WETH's bytecode obeys every field of `WethSpec` (the
interface in `Spec.lean`). Each guarantee is proved as its own theorem
(`weth_deposit`, `weth_withdraw`, …) — so each gets its own editor
checkmark — and the theorems are then bundled into `weth_spec : WethSpec`.
Every proof is one delegation into the `weth_*_run_impl` engine
(`Behaviour.lean`) / `weth_solvency_invariant` (`Solvency.lean`).
-/

namespace EvmSmith.Weth

open EvmYul EvmYul.EVM EvmYul.Frame Batteries EvmSmith.Layer1 EvmSmith.Spec

/-- `deposit()` credits the caller by `msg.value`; others untouched; empty return. -/
theorem weth_deposit (s : EVM.State) (call : Calls .deposit s) :
    ensures
      balance[sender] = old balance[sender] + value
    ∧ untouched (others)
    ∧ returndata = empty := by
  obtain ⟨hcode, hpc0, hstk0, ⟨acc, hfind⟩, hsel⟩ := call
  intro s' o ⟨callFuel, N, hrun⟩
  have h := weth_deposit_run_impl s callFuel N (s', o) s.executionEnv.codeOwner acc
    hcode hpc0 hstk0 hsel rfl hfind hrun
  exact ⟨h.1.trans (uint256_add_comm _ _), h.2.1, h.2.2⟩

/-- `withdraw(x)` debits the caller by `x` at its own write — no assumption. -/
theorem weth_withdraw_debits (s : EVM.State) (call : Calls .withdraw s)
    (funded : amount ≤ old balance[sender]) :
    before_call:
      balance[sender] = old balance[sender] - amount := by
  obtain ⟨hcode, hpc0, hstk0, ⟨acc, hfind⟩, hsel⟩ := call
  intro s' ⟨callFuel, N, hrun⟩
  have hle : (withdrawArg s).toNat
      ≤ (acc.lookupStorage (tokenBalanceSlot s.executionEnv.source)).toNat := by
    rw [recordedBalance_of_find s.accountMap s.executionEnv.codeOwner
          s.executionEnv.source acc hfind] at funded
    exact funded
  exact weth_withdraw_to_call_impl s callFuel N s' s.executionEnv.codeOwner acc
    hcode hpc0 hstk0 hsel rfl hfind hle hrun

/-- `withdraw(x)` debits the caller by `x` end-to-end, given no reentrancy. -/
theorem weth_withdraw (s : EVM.State) (call : Calls .withdraw s)
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

/-- An unknown selector reverts, changing no account. -/
theorem weth_fallback (s : EVM.State) (call : Calls .unknown s) :
    ensures
      storage = old storage := by
  obtain ⟨hcode, hpc0, hstk0, _, hne_dep, hne_wd⟩ := call
  intro s' o ⟨callFuel, N, hrun⟩
  exact weth_unknown_run_impl s callFuel N (s', o) hcode hpc0 hstk0 hne_dep hne_wd hrun

/-- WETH is solvent after any transaction (or it reverted). -/
theorem weth_solvent (ctx : ExecContext) (σ : AccountMap .EVM)
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

/-- **WETH's bytecode satisfies `WethSpec`.** -/
def weth_spec : WethSpec where
  deposit         := weth_deposit
  withdraw_debits := weth_withdraw_debits
  withdraw        := weth_withdraw
  fallback        := weth_fallback
  solvent         := weth_solvent

end EvmSmith.Weth
