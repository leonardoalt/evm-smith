import EvmSmith.Demos.Register.Upsilon

/-!
# Register balance-monotonicity — main theorem

The user-facing statement. Delegates to `Layer3.Υ_preserves_RegInv`
and extracts the `bal` conjunct.
-/

namespace EvmSmith.RegisterProofs

open EvmSmith.RegisterInvariant EvmSmith.RegisterProofs.Layer3
     EvmYul EvmYul.EVM EvmSmith EvmSmith.Register Batteries

export EvmSmith.RegisterInvariant
  (balanceOf codeAt totalETH RegInv)

/-- **Register's balance never decreases across a transaction.**

Given:
- the inductive invariant `RegInv σ ∅ C b₀` holds at tx entry
  (`codeAt`, `b₀ ≤ balanceOf σ C`, `C ∉ selfDestructSet`,
  `totalETH σ < 2^256`);
- `C` is neither the tx sender nor the block beneficiary;
- no address created during this tx equals `C`;

then after executing the transaction, `balanceOf σ' C ≥ b₀`. -/
theorem register_balance_mono
    (fuel : ℕ) (σ σ' : AccountMap .EVM)
    (H_f : ℕ) (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress) (b₀ : ℕ)
    (hInv : RegInv σ (default : Substate) C b₀)
    (hCS  : C ≠ S_T)
    (hCH  : C ≠ H.beneficiary)
    (hNewC : ∀ a : AccountAddress, a ≠ C)
    (hRun : ∃ A' r₁ r₂, EVM.Υ fuel σ H_f H H_gen blocks tx S_T
              = .ok (σ', A', r₁, r₂)) :
    b₀ ≤ balanceOf σ' C := by
  have h := Υ_preserves_RegInv fuel σ H_f H H_gen blocks tx S_T C b₀
              hInv hCS hCH hNewC
  obtain ⟨A', r₁, r₂, hEq⟩ := hRun
  rw [hEq] at h
  exact h.bal

end EvmSmith.RegisterProofs
