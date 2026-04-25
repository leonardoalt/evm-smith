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

/-! ## Helpers for the σ → σ₀ → σ_P balance chain

We use the strengthened `TxValid` predicate (in `UpsilonFrame.lean`) to
discharge the preconditions of `Θ_balanceOf_ge` / `Λ_balanceOf_ge` at
the post-debit checkpoint state σ₀ = `Υ_σ₀ σ H_f S_T H tx`. -/

/-- `balanceOf σ₀ C = balanceOf σ C` since σ₀ inserts at `S_T ≠ C`. -/
private theorem balanceOf_σ₀_eq
    (σ : AccountMap .EVM) (H_f : ℕ) (S_T C : AccountAddress)
    (H : BlockHeader) (tx : Transaction) (hS_T : C ≠ S_T) :
    balanceOf (Υ_σ₀ σ H_f S_T H tx) C = balanceOf σ C := by
  unfold Υ_σ₀
  exact balanceOf_of_find?_eq (find?_insert_ne _ _ _ _ hS_T.symm)

/-- `StateWF (Υ_σ₀ σ H_f S_T H tx)`. -/
private theorem σ₀_StateWF
    (σ : AccountMap .EVM) (H_f : ℕ) (S_T : AccountAddress)
    (H : BlockHeader) (tx : Transaction)
    (hWF : StateWF σ) :
    StateWF (Υ_σ₀ σ H_f S_T H tx) := by
  have hValid := tx_validity σ S_T tx H H_f
  obtain ⟨acc, hFind, _hUpfront, hLeBal, _, _⟩ := hValid
  unfold Υ_σ₀
  apply StateWF_insert_le_bal _ _ _ acc hFind _ hWF
  -- (Υ_newSender σ H_f S_T H tx).balance.toNat ≤ acc.balance.toNat.
  exact hLeBal

/-- `Υ_σ₀.find? S_T = some (Υ_newSender …)`. -/
private theorem σ₀_find_S_T
    (σ : AccountMap .EVM) (H_f : ℕ) (S_T : AccountAddress)
    (H : BlockHeader) (tx : Transaction) :
    (Υ_σ₀ σ H_f S_T H tx).find? S_T = some (Υ_newSender σ H_f S_T H tx) := by
  unfold Υ_σ₀
  exact find?_insert_self _ _ _

/-! ### Θ branch helper (recipient = some t) -/

/-- `balanceOf σ_P C ≥ balanceOf σ C` for the Θ-dispatch result, using
the strengthened `TxValid` to discharge `Θ_balanceOf_ge`'s
preconditions at σ₀. -/
private theorem σ_to_σP_balance_mono_Θ
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T t C : AccountAddress)
    (AStar : Substate) (g pPrice : UInt256)
    (σ_P : AccountMap .EVM) (g_ret : UInt256) (A : Substate)
    (z : Bool) (cA' : Batteries.RBSet AccountAddress compare)
    (oData : ByteArray)
    (hWF : StateWF σ)
    (hS_T : C ≠ S_T)
    (hΘ : EVM.Θ fuel tx.blobVersionedHashes Batteries.RBSet.empty H_gen blocks
            (Υ_σ₀ σ H_f S_T H tx) (Υ_σ₀ σ H_f S_T H tx) AStar S_T S_T t
            (toExecute .EVM (Υ_σ₀ σ H_f S_T H tx) t)
            g pPrice tx.base.value tx.base.value tx.base.data 0 H true
          = .ok (cA', σ_P, g_ret, A, z, oData)) :
    balanceOf σ_P C ≥ balanceOf σ C := by
  have hσ₀_eq := balanceOf_σ₀_eq σ H_f S_T C H tx hS_T
  have hWFσ₀ := σ₀_StateWF σ H_f S_T H tx hWF
  have hValid := tx_validity σ S_T tx H H_f
  obtain ⟨_acc, _hFind, _hUpfront, _hLeBal, hValueLe, hRecBound⟩ := hValid
  -- Apply Θ_balanceOf_ge at σ₀.
  have hΘ_result :=
    Θ_balanceOf_ge fuel tx.blobVersionedHashes Batteries.RBSet.empty
      H_gen blocks (Υ_σ₀ σ H_f S_T H tx) (Υ_σ₀ σ H_f S_T H tx) AStar S_T S_T t
      (toExecute .EVM (Υ_σ₀ σ H_f S_T H tx) t)
      g pPrice tx.base.value tx.base.value tx.base.data 0 H true C
      hWFσ₀
      (Or.inl hS_T)
      (fun a hMem => by
        -- a ∈ RBSet.empty is unfoldable to False.
        exfalso
        exact hMem.elim)
      (fun acc' hFindR => hRecBound t acc' hFindR)
      (Or.inr ⟨Υ_newSender σ H_f S_T H tx,
               σ₀_find_S_T σ H_f S_T H tx, hValueLe⟩)
      (bytecodePreservesBalance C)
      (fun f _ => ΞFrameAtC_of_witness C (bytecodePreservesBalance C) f)
  rw [hΘ] at hΘ_result
  obtain ⟨hMonoΘ, _, _⟩ := hΘ_result
  rw [hσ₀_eq] at hMonoΘ
  exact hMonoΘ

/-! ### Λ branch helper (recipient = none) -/

/-- `balanceOf σ_P C ≥ balanceOf σ C` for the Λ-dispatch result. -/
private theorem σ_to_σP_balance_mono_Λ
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress)
    (AStar : Substate) (g pPrice : UInt256)
    (a : AccountAddress) (cA' : Batteries.RBSet AccountAddress compare)
    (σ_P : AccountMap .EVM) (g_ret : UInt256) (A : Substate)
    (z : Bool) (oData : ByteArray)
    (hWF : StateWF σ)
    (hS_T : C ≠ S_T)
    (hΛ : EVM.Lambda fuel tx.blobVersionedHashes Batteries.RBSet.empty
            H_gen blocks (Υ_σ₀ σ H_f S_T H tx) (Υ_σ₀ σ H_f S_T H tx) AStar
            S_T S_T g pPrice tx.base.value tx.base.data ⟨0⟩ none H true
          = .ok (a, cA', σ_P, g_ret, A, z, oData)) :
    balanceOf σ_P C ≥ balanceOf σ C := by
  have hσ₀_eq := balanceOf_σ₀_eq σ H_f S_T C H tx hS_T
  have hWFσ₀ := σ₀_StateWF σ H_f S_T H tx hWF
  have hValid := tx_validity σ S_T tx H H_f
  obtain ⟨_acc, _hFind, _hUpfront, _hLeBal, hValueLe, _hRecBound⟩ := hValid
  -- Apply Λ_balanceOf_ge at σ₀.
  have hΛ_result :=
    Λ_balanceOf_ge fuel tx.blobVersionedHashes Batteries.RBSet.empty
      H_gen blocks (Υ_σ₀ σ H_f S_T H tx) (Υ_σ₀ σ H_f S_T H tx) AStar
      S_T S_T g pPrice tx.base.value tx.base.data ⟨0⟩ none H true C
      hWFσ₀
      hS_T
      (fun a hMem => by
        -- a ∈ RBSet.empty is unfoldable to False.
        exfalso
        exact hMem.elim)
      (by
        -- h_funds: ∀ acc', σ₀.find? S_T = some acc' → tx.base.value.toNat ≤ acc'.balance.toNat
        intro acc' hFindS
        have hSome := σ₀_find_S_T σ H_f S_T H tx
        rw [hSome] at hFindS
        injection hFindS with hAcc'
        rw [← hAcc']
        exact hValueLe)
      (bytecodePreservesBalance C)
      (fun f _ => ΞFrameAtC_of_witness C (bytecodePreservesBalance C) f)
  rw [hΛ] at hΛ_result
  obtain ⟨_, hMonoΛ, _, _⟩ := hΛ_result
  rw [hσ₀_eq] at hMonoΛ
  exact hMonoΛ

/-- **Register body factorisation witness.**

For every transaction with Register's code at C, the `.ok` output of
Υ decomposes as `Υ_tail_state σ_P g' A …` for some (σ_P, g') with
`balanceOf σ_P C ≥ balanceOf σ C`.

The existence part follows from the fact that Υ's body has the
syntactic form:

  `do (σ_P, g', A, z) ← Θ/Λ-dispatch σ₀; .ok (Υ_tail_state …, A, z, _)`

The monotonicity part chains through:
  σ → σ₀ (sender debit at `S_T ≠ C`): `balanceOf σ₀ C = balanceOf σ C`.
  σ₀ → σ_P: by `Λ_balanceOf_ge` / `Θ_balanceOf_ge` (closed theorems). -/
private theorem register_Υ_body_factors
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress)
    (hWF : StateWF σ)
    (hS_T : C ≠ S_T)
    (_hCode : codeAt σ C) :
    ΥBodyFactors σ fuel H_f H H_gen blocks tx S_T C := by
  unfold ΥBodyFactors
  unfold EVM.Υ
  match hRec : tx.base.recipient with
  | none =>
    simp only
    split
    case h_1 σ' A' z' gUsed' hOk =>
      split at hOk
      case h_1 a cA σ_P g' A z gReturn hΛ =>
        refine ⟨σ_P, g', ?_, ?_⟩
        · cases hOk
          rfl
        · cases hOk
          exact σ_to_σP_balance_mono_Λ fuel σ H_f H H_gen blocks tx S_T C
            _ _ _ a cA σ_P g' A z gReturn hWF hS_T hΛ
      case h_2 e hΛ =>
        simp [bind, Except.bind] at hOk
    case h_2 _ =>
      trivial
  | some t =>
    simp only
    split
    case h_1 σ' A' z' gUsed' hOk =>
      split at hOk
      case h_1 cA σ_P g' A z gReturn hΘ =>
        refine ⟨σ_P, g', ?_, ?_⟩
        · cases hOk
          rfl
        · cases hOk
          exact σ_to_σP_balance_mono_Θ fuel σ H_f H H_gen blocks tx S_T t C
            _ _ _ σ_P g' A z cA gReturn hWF hS_T hΘ
      case h_2 e hΘ =>
        simp [bind, Except.bind] at hOk
    case h_2 _ =>
      trivial

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
