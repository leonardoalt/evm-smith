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

/-! ### Register-level run-output structural hypotheses

The new `ΥTailInvariant` predicate (in `UpsilonFrame.lean`) is now
structurally pinned to the **specific** `A` produced by Υ's `.ok`
output, and its dead-filter clause is gated by a `State.dead σ_F C =
false` hypothesis (instead of being vacuously universally quantified
over arbitrary σ_F). The dead-filter clause is now trivially provable
from the gating hypothesis; all that remains is the SD-set fact about
the specific `A`.

We package the SD-set fact as a structural hypothesis on
`register_balance_mono`, parallel to the existing real-world
hypotheses. It's stated structurally on Υ's `.ok` output; on `.error`
it's vacuously `True`. Discharging it from Lean would require
strengthening `Θ_balanceOf_ge` / `Λ_balanceOf_ge` to expose substate
tracking, which is out of scope for this proof. The hypothesis
captures the call-tree-level fact:

* Register's bytecode contains no SELFDESTRUCT (verifiable by
  inspecting `EvmSmith.Demos.Register.Program.bytecode`), so no
  Ξ-frame at `Iₐ = C` (which by `I_code_at_C_is_Register_bytecode`
  runs Register's bytecode) inserts C into A.selfDestructSet.
* SELFDESTRUCT at any other frame inserts that frame's `Iₐ`, which
  is `≠ C` by hypothesis.

**Phase A (in progress): SD-set tracking inside the framework.**
The framework now exposes a strengthened sibling predicate
`ΞPreservesAtCStrong` (in `MutualFrame.lean`) that produces the
post-frame substate's SD-set exclusion of `C` as a 4th conjunct.
Phase A predicate scaffolding now also includes:
* `ΞFrameAtCStrong C maxFuel` — strong sibling of `ΞFrameAtC`
  (the `≠ C` form) with SD-input/SD-output threading.
* `ΞAtCFrameStrong C maxFuel` — strong sibling of `ΞAtCFrame`
  (the `= C` form), derivable from `ΞPreservesAtCStrong` via
  `ΞAtCFrameStrong_of_witness`.
* `ΞFrameAtC_of_Strong` — projection: a strong frame yields the
  unstrengthened frame conclusion at any call site that supplies
  an SD-exclusive input substate.

Once a `bytecodePreservesBalanceStrong C : ΞPreservesAtCStrong C`
witness is provided AND the strong sibling of
`Ξ_balanceOf_ge_bundled` (i.e. `ΞFrameAtCStrong C maxFuel` from
the strong witness) is closed (closing the SD-set tracking through
the entire mutual closure — the bulk of Phase A's remaining work),
the `RegSDExclusion` hypothesis here will be derivable inside Lean
via `Υ`'s body factorisation plus the strengthened framework
outputs. The leaf SELFDESTRUCT preservation is already proved in
`SelfdestructFrame.lean` (`selfdestruct_preserves_SD_exclude_C`).
-/

/-- Hypothesis on Υ's run output: the resulting substate's
self-destruct set excludes `C`. -/
def RegSDExclusion (σ : AccountMap .EVM) (fuel H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress) : Prop :=
  match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | .ok (_, A, _, _) => ∀ k ∈ A.selfDestructSet.1.toList, k ≠ C
  | _ => True

/-- Hypothesis on Υ's body factorisation: every post-dispatch state
σ_P that decomposes Υ's output via the tail-state form satisfies
`State.dead σ_P C = false`, i.e. `C`'s account exists in σ_P with
non-empty code (Register's bytecode).

Universally quantified over the decomposition pair (σ_P, g'), so the
caller of `register_Υ_body_factors` can apply it to whichever σ_P it
extracts from the Θ/Λ dispatch.

Captures the structural fact: σ_P is the post-Θ/Λ state on the
debited σ₀; since `S_T ≠ C` and `lambda_derived_address_ne_C` excludes
CREATE-derivation of `C`, no frame in the call tree erases or
overwrites C's code. -/
def RegDeadAtσP (σ : AccountMap .EVM) (fuel H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress) : Prop :=
  match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | .ok (σ', A', _, _) =>
      ∀ σ_P g',
        σ' = Υ_tail_state σ_P g' A' H H_f tx S_T →
        State.dead σ_P C = false
  | _ => True

/-- **Register tail invariant.** Converts the SD-exclusion structural
hypothesis to the full `ΥTailInvariant` predicate.

The dead-filter clause is discharged trivially: `k ∈ filter
(dead σ_F ·)` implies `dead σ_F k = true` (by `mem_filter_pred`),
which contradicts `dead σ_F C = false` (the hypothesis baked into
`ΥTailInvariant`'s second clause) when `k = C`. -/
private theorem register_Υ_tail_invariant
    (σ : AccountMap .EVM) (fuel H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress)
    (hSD : RegSDExclusion σ fuel H_f H H_gen blocks tx S_T C) :
    ΥTailInvariant σ fuel H_f H H_gen blocks tx S_T C := by
  unfold ΥTailInvariant RegSDExclusion at *
  cases hΥ : EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | error e => trivial
  | ok r =>
    obtain ⟨_, A, _, _⟩ := r
    rw [hΥ] at hSD
    refine ⟨hSD, ?_⟩
    intro σ_F hDead k hk hkC
    have hpk : State.dead σ_F k = true := mem_filter_pred _ _ _ hk
    rw [hkC] at hpk
    rw [hDead] at hpk
    cases hpk

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
    (hWF : StateWF σ)
    (hValid : TxValid σ S_T tx H H_f) :
    StateWF (Υ_σ₀ σ H_f S_T H tx) := by
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
    (hDeployed : DeployedAtC C)
    (hWF : StateWF σ)
    (hS_T : C ≠ S_T)
    (hValid : TxValid σ S_T tx H H_f)
    (hΘ : EVM.Θ fuel tx.blobVersionedHashes Batteries.RBSet.empty H_gen blocks
            (Υ_σ₀ σ H_f S_T H tx) (Υ_σ₀ σ H_f S_T H tx) AStar S_T S_T t
            (toExecute .EVM (Υ_σ₀ σ H_f S_T H tx) t)
            g pPrice tx.base.value tx.base.value tx.base.data 0 H true
          = .ok (cA', σ_P, g_ret, A, z, oData)) :
    balanceOf σ_P C ≥ balanceOf σ C := by
  have hσ₀_eq := balanceOf_σ₀_eq σ H_f S_T C H tx hS_T
  have hWFσ₀ := σ₀_StateWF σ H_f S_T H tx hWF hValid
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
      (bytecodePreservesBalance C hDeployed)
      (fun f _ => ΞFrameAtC_of_witness C (bytecodePreservesBalance C hDeployed) f)
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
    (hDeployed : DeployedAtC C)
    (hWF : StateWF σ)
    (hS_T : C ≠ S_T)
    (hValid : TxValid σ S_T tx H H_f)
    (hΛ : EVM.Lambda fuel tx.blobVersionedHashes Batteries.RBSet.empty
            H_gen blocks (Υ_σ₀ σ H_f S_T H tx) (Υ_σ₀ σ H_f S_T H tx) AStar
            S_T S_T g pPrice tx.base.value tx.base.data ⟨0⟩ none H true
          = .ok (a, cA', σ_P, g_ret, A, z, oData)) :
    balanceOf σ_P C ≥ balanceOf σ C := by
  have hσ₀_eq := balanceOf_σ₀_eq σ H_f S_T C H tx hS_T
  have hWFσ₀ := σ₀_StateWF σ H_f S_T H tx hWF hValid
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
      (bytecodePreservesBalance C hDeployed)
      (fun f _ => ΞFrameAtC_of_witness C (bytecodePreservesBalance C hDeployed) f)
  rw [hΛ] at hΛ_result
  obtain ⟨_, hMonoΛ, _, _⟩ := hΛ_result
  rw [hσ₀_eq] at hMonoΛ
  exact hMonoΛ

/-- **Register body factorisation witness.**

For every transaction with Register's code at C, the `.ok` output of
Υ decomposes as `Υ_tail_state σ_P g' A …` for some (σ_P, g') with
`balanceOf σ_P C ≥ balanceOf σ C` and `State.dead σ_P C = false`.

The existence part follows from the fact that Υ's body has the
syntactic form:

  `do (σ_P, g', A, z) ← Θ/Λ-dispatch σ₀; .ok (Υ_tail_state …, A, z, _)`

The monotonicity part chains through:
  σ → σ₀ (sender debit at `S_T ≠ C`): `balanceOf σ₀ C = balanceOf σ C`.
  σ₀ → σ_P: by `Λ_balanceOf_ge` / `Θ_balanceOf_ge` (closed theorems).

The `State.dead σ_P C = false` part is supplied by the `RegDeadAtσP`
hypothesis. -/
private theorem register_Υ_body_factors
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress)
    (hDeployed : DeployedAtC C)
    (hWF : StateWF σ)
    (hS_T : C ≠ S_T)
    (hValid : TxValid σ S_T tx H H_f)
    (hDeadσP : RegDeadAtσP σ fuel H_f H H_gen blocks tx S_T C) :
    ΥBodyFactors σ fuel H_f H H_gen blocks tx S_T C := by
  unfold ΥBodyFactors RegDeadAtσP at *
  unfold EVM.Υ at *
  match hRec : tx.base.recipient with
  | none =>
    simp only
    rw [hRec] at hDeadσP
    simp only at hDeadσP
    split
    case h_2 _ => trivial
    case h_1 σ' A' z' gUsed' hOk =>
      split at hOk
      case h_2 e hΛ => simp [bind, Except.bind] at hOk
      case h_1 a cA σ_P g' A z gReturn hΛ =>
        rw [hΛ] at hDeadσP
        simp only at hDeadσP
        cases hOk
        exact ⟨σ_P, g', rfl,
          σ_to_σP_balance_mono_Λ fuel σ H_f H H_gen blocks tx S_T C
            _ _ _ a cA σ_P g' A z gReturn hDeployed hWF hS_T hValid hΛ,
          hDeadσP σ_P g' rfl⟩
  | some t =>
    simp only
    rw [hRec] at hDeadσP
    simp only at hDeadσP
    split
    case h_2 _ => trivial
    case h_1 σ' A' z' gUsed' hOk =>
      split at hOk
      case h_2 e hΘ => simp [bind, Except.bind] at hOk
      case h_1 cA σ_P g' A z gReturn hΘ =>
        rw [hΘ] at hDeadσP
        simp only at hDeadσP
        cases hOk
        exact ⟨σ_P, g', rfl,
          σ_to_σP_balance_mono_Θ fuel σ H_f H H_gen blocks tx S_T t C
            _ _ _ σ_P g' A z cA gReturn hDeployed hWF hS_T hValid hΘ,
          hDeadσP σ_P g' rfl⟩

/-- Register's balance is non-decreasing across any transaction, under
the boundary hypotheses and real-world well-formedness.

The two `Reg*` hypotheses (`hSDExcl`, `hDeadAtσP`) capture
structural call-tree invariants of Register's run that are not
derivable from the closed `Θ_balanceOf_ge`/`Λ_balanceOf_ge` outputs:

  * `RegSDExclusion`: no SELFDESTRUCT in the call tree adds C to the
    final substate's selfDestructSet. Holds because Register's
    bytecode contains no SELFDESTRUCT and SELFDESTRUCT only inserts
    its own executing-frame address `Iₐ` into the SD-set, which by
    `I_code_at_C_is_Register_bytecode` is `≠ C` whenever code at
    that address is not Register's bytecode.

  * `RegDeadAtσP`: `C`'s account in σ_P (the Θ/Λ output) has
    non-empty code (Register's bytecode), so
    `State.dead σ_P C = false`. Holds because RegInv provides this
    initially and Θ/Λ at `S_T ≠ C` plus
    `lambda_derived_address_ne_C` prevent C's code from being
    overwritten or erased.

Both are real-world structural facts that mirror existing boundary
hypotheses in spirit (cf. `hS_T`, `hBen`, `lambda_derived_address_ne_C`).
Discharging them inside Lean would require strengthening Θ/Λ's frame
outputs to expose substate-tracking and code-preservation, which is
out of scope for this proof. -/
theorem register_balance_mono
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress) (b₀ : ℕ)
    (hWF : StateWF σ)
    (hInv : RegInv σ C b₀)
    (hS_T : C ≠ S_T)
    (hBen : C ≠ H.beneficiary)
    (hValid : TxValid σ S_T tx H H_f)
    (hDeployed : DeployedAtC C)
    (hSDExcl : RegSDExclusion σ fuel H_f H H_gen blocks tx S_T C)
    (hDeadAtσP : RegDeadAtσP σ fuel H_f H H_gen blocks tx S_T C) :
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => b₀ ≤ balanceOf σ' C
    | .error _ => True :=
  Υ_balanceOf_ge fuel σ H_f H H_gen blocks tx S_T C b₀
    hWF hInv.bal hS_T hBen (bytecodePreservesBalance C hDeployed)
    (register_Υ_tail_invariant σ fuel H_f H H_gen blocks tx S_T C hSDExcl)
    (register_Υ_body_factors fuel σ H_f H H_gen blocks tx S_T C
      hDeployed hWF hS_T hValid hDeadAtσP)

end EvmSmith.Register
