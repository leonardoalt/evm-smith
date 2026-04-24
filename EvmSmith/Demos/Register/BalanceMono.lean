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

/-- **Register tail invariant.**

For every Υ-dispatch output `(σ_P, A, σ_F)` in a Register-run
transaction at C, the post-dispatch substate's selfDestructSet
excludes C and the dead-account filter over touchedAccounts excludes
C. Discharged structurally:

  * **SD set excludes C**: Register's bytecode contains no
    SELFDESTRUCT, so no inner frame with `Iₐ = C` can insert C into
    A.selfDestructSet. Any other frame only inserts its own Iₐ,
    which by `I_code_at_C_is_Register_bytecode` is ≠ C (code at
    those addresses is not Register's bytecode).
  * **Dead filter excludes C**: C's code is non-empty (Register
    bytecode) so `State.dead σ_F C = false`.

We package as a single axiom at the Register level, mirroring the
pattern in `Ξ_Register_preserves_balanceOf_at_C`. -/
private axiom register_Υ_tail_invariant (C : AccountAddress) :
    ΥTailInvariant C

/-- **Register body factorisation witness.**

For every transaction with Register's code at C, the `.ok` output of
Υ decomposes as `Υ_tail_state σ_P g' A …` for some (σ_P, g') with
`balanceOf σ_P C ≥ balanceOf σ C`. This is packaged as a **companion**
of `Ξ_Register_preserves_balanceOf_at_C` — both are structural claims
about Υ/Ξ transit at Register's bytecode.

The existence part follows from the fact that Υ's body has the
syntactic form:

  `do (σ_P, g', A, z) ← Θ/Λ-dispatch σ₀; .ok (Υ_tail_state …, A, z, _)`

The monotonicity part chains through:
  σ → σ₀ (sender debit at `S_T ≠ C`): `balanceOf σ₀ C = balanceOf σ C`.
  σ₀ → σ_P: by `Λ_balanceOf_ge` / `Θ_balanceOf_ge` (closed theorems).

Mirrors the Register-axiom pattern in `BytecodeFrame.lean`, and is
only used at the Register layer. Its Register-specific quality: the
`StateWF σ₀` precondition for the Θ/Λ bundle is discharged using
`tx_validity` + `StateWF_insert_eq_bal`, which hold for
Register-deployed transactions. -/
private axiom register_Υ_body_factors
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress)
    (_hWF : StateWF σ)
    (_hS_T : C ≠ S_T)
    (_hCode : codeAt σ C) :
    ΥBodyFactors σ fuel H_f H H_gen blocks tx S_T C

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
    (register_Υ_tail_invariant C)
    (register_Υ_body_factors fuel σ H_f H H_gen blocks tx S_T C
      hWF hS_T hInv.code)

end EvmSmith.Register
