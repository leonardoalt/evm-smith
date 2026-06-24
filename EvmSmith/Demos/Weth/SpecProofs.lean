import EvmSmith.Demos.Weth.Spec
import EvmSmith.Demos.Weth.Behaviour

/-!
# WETH satisfies its spec

The witness that WETH's bytecode obeys every field of `WethSpec` (the
interface in `Spec.lean`). Each field is discharged by one delegation into
the `weth_*_run_impl` engine (`Behaviour.lean`) / `weth_solvency_invariant`
(`Solvency.lean`) — so reading `Spec.lean` is enough to know *what* is
guaranteed, and this file is *why*.
-/

namespace EvmSmith.Weth

open EvmYul EvmYul.EVM EvmYul.Frame Batteries EvmSmith.Layer1 EvmSmith.Spec

/-- **WETH's bytecode satisfies `WethSpec`.** -/
def weth_spec : WethSpec where
  deposit s call := by
    obtain ⟨hcode, hpc0, hstk0, ⟨acc, hfind⟩, hsel⟩ := call
    intro s' o ⟨callFuel, N, hrun⟩
    have h := weth_deposit_run_impl s callFuel N (s', o) s.executionEnv.codeOwner acc
      hcode hpc0 hstk0 hsel rfl hfind hrun
    exact ⟨h.1.trans (uint256_add_comm _ _), h.2.1, h.2.2⟩
  withdraw_debits s call funded := by
    obtain ⟨hcode, hpc0, hstk0, ⟨acc, hfind⟩, hsel⟩ := call
    intro s' ⟨callFuel, N, hrun⟩
    have hle : (withdrawArg s).toNat
        ≤ (acc.lookupStorage (tokenBalanceSlot s.executionEnv.source)).toNat := by
      rw [recordedBalance_of_find s.accountMap s.executionEnv.codeOwner
            s.executionEnv.source acc hfind] at funded
      exact funded
    exact weth_withdraw_to_call_impl s callFuel N s' s.executionEnv.codeOwner acc
      hcode hpc0 hstk0 hsel rfl hfind hle hrun
  withdraw s call funded noReentry := by
    obtain ⟨hcode, hpc0, hstk0, ⟨acc, hfind⟩, hsel⟩ := call
    intro s' o ⟨callFuel, N, hrun⟩
    have hle : (withdrawArg s).toNat
        ≤ (acc.lookupStorage (tokenBalanceSlot s.executionEnv.source)).toNat := by
      rw [recordedBalance_of_find s.accountMap s.executionEnv.codeOwner
            s.executionEnv.source acc hfind] at funded
      exact funded
    exact weth_withdraw_run_impl s callFuel N (s', o) s.executionEnv.codeOwner acc
      hcode hpc0 hstk0 hsel rfl hfind hle (fun sa sb h => noReentry callFuel sa sb h) hrun
  fallback s call := by
    obtain ⟨hcode, hpc0, hstk0, _, hne_dep, hne_wd⟩ := call
    intro s' o ⟨callFuel, N, hrun⟩
    exact weth_unknown_run_impl s callFuel N (s', o) hcode hpc0 hstk0 hne_dep hne_wd hrun
  solvent ctx σ tx S_T weth hWellFormed hSolventBefore hNotSender hNotMiner hTxValid hAssumptions :=
    weth_solvency_invariant ctx.fuel σ ctx.baseFee ctx.block ctx.genesis ctx.history
      tx S_T weth hWellFormed hSolventBefore hNotSender hNotMiner hTxValid hAssumptions

end EvmSmith.Weth
