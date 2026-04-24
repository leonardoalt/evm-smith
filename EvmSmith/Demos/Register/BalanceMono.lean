import EvmYul.Frame
import EvmSmith.Demos.Register.Invariant
import EvmSmith.Demos.Register.BytecodeFrame

/-!
# Register — balance monotonicity, main theorem (B3)

**`register_balance_mono`** — after any single Ethereum transaction,
Register's balance is not less than it was at the start of the
transaction.

Hypotheses (from `BALANCE_MONOTONICITY.md`):

1. `C ≠ S_T` — Register is not the transaction sender. (Otherwise Υ's
   pre-dispatch gas debit `β(S_T) -= gasLimit·p + blobFee` would drain
   `β(C)`.)
2. `C ≠ H.beneficiary` — Register is not the block miner. (Weaker —
   miner credit is non-negative, not non-positive — but kept for
   narrative clarity; without it we'd still have monotonicity.)
3. No CREATE/CREATE2 in this transaction's call tree produces address
   `C`. (Otherwise a nested untrusted contract could deploy foreign
   code at `C` mid-tx, breaking the code invariant. Under Keccak-256
   collision-resistance this holds for any sane transaction.)

Proof: compose `bytecodePreservesBalance` (B2) with `Υ_balanceOf_ge`
(A6). The boundary hypotheses discharge Υ's preconditions; the
bytecode witness discharges the `ΞPreservesAtC C` parameter.
-/

namespace EvmSmith.Register
open EvmYul EvmYul.EVM EvmYul.Frame

/-- Register's balance is non-decreasing across any transaction, under
the boundary hypotheses and real-world well-formedness. -/
theorem register_balance_mono
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress) (b₀ : ℕ)
    (hWF : StateWF σ)
    (hInv : RegInv σ C b₀)
    (hS_T : C ≠ S_T)
    (hBen : C ≠ H.beneficiary) :
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => b₀ ≤ balanceOf σ' C
    | .error _ => True :=
  Υ_balanceOf_ge fuel σ H_f H H_gen blocks tx S_T C b₀
    hWF hInv.bal hS_T hBen (bytecodePreservesBalance C)

end EvmSmith.Register
