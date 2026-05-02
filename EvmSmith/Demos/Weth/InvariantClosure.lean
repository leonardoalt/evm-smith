import EvmYul.Frame.MutualFrame
import EvmYul.Frame.UpsilonFrame
import EvmYul.Frame.StorageSum
import EvmYul.Frame.Projection

/-!
# Relational solvency invariant — closure chain (consumer-side)

This file hosts the relational-invariant
`StorageSumLeBalance σ C := storageSum σ C ≤ balanceOf σ C` and the
full closure chain that preserves it across Υ. The whole stack is
*consumer-specific* — only WETH-style relational-solvency proofs use
it — so it lives outside the generic frame framework.

Contents:

* The `StorageSumLeBalance` predicate definition.
* §H predicates (`ΞPreservesInvariantAtC`, `ΞInvariantAtCFrame`,
  `ΞInvariantFrameAtC`) and the §H.2 closure
  (`Θ_invariant_preserved_bdd`, `Λ_invariant_preserved_bdd`,
  `Ξ_invariant_preserved_bundled_bdd`, `call_invariant_preserved`,
  `ΞPreservesInvariantAtC_of_Reachable_general*`).
* The transaction-level entry point `Υ_invariant_preserved` plus its
  Υ-tail wrappers (`Υ_tail_invariant_preserves`,
  `Υ_output_invariant_preserves`).

The generic Υ-tail storage-sum helpers (`storageSum_tail_generic`,
`Υ_tail_storageSum_eq`) live framework-side in
`EvmYul/Frame/UpsilonFrame.lean` (parallel to the balance-side
`balanceOf_tail_generic` / `Υ_tail_balanceOf_ge`); the consumer-side
chain here invokes them directly.

Namespace: `EvmYul.Frame` (kept for diff minimality; consumer-side
namespace rename is a possible follow-up).
-/

namespace EvmYul
namespace Frame

open Batteries EvmYul.EVM

/-- The relational solvency invariant at address `C`: the sum of all
`UInt256` values stored at `σ[C].storage` is at most `σ[C].balance`
(interpreted in `ℕ`). -/
def StorageSumLeBalance (σ : AccountMap .EVM) (C : AccountAddress) : Prop :=
  storageSum σ C ≤ balanceOf σ C

/-! ## §H — Invariant-tracking parallel mutual closure (predicates)

This section defines the predicate scaffolding for the parallel mutual
closure that tracks the **(β ≥ S)** solvency invariant, where

  `S := storageSum σ C`     (sum of all UInt256 values in `σ[C].storage`)
  `β := balanceOf σ C`      (`σ[C].balance` cast to `ℕ`).

The closure mirrors the existing balance-monotonicity chain
(`Θ_balanceOf_ge_bdd` / `Λ_balanceOf_ge_bdd` / `Ξ_balanceOf_ge_bundled_bdd`)
but its conclusion is invariant *preservation* `S(σ') ≤ β(σ')` rather
than balance *monotonicity* `β(σ') ≥ β(σ)`. The two chains coexist:
the existing one applies to consumers whose at-C frames preserve
balance monotonically; this chain applies to consumers whose at-C
block decreases β by exactly the amount S also decreases by (a
checks-effects-interactions withdraw block, for instance), so only
the relative invariant `S ≤ β` survives.

### Scope of §H.1 (this commit-set)

* **Predicates** — `ΞPreservesInvariantAtC`, `ΞInvariantAtCFrame`,
  `ΞInvariantFrameAtC` — analogues of `ΞPreservesAtC`, `ΞAtCFrame`,
  `ΞFrameAtC` whose success-branch conjunct is `StorageSumLeBalance σ' C`
  (`storageSum σ' C ≤ balanceOf σ' C`) instead of `β` monotonicity.
* **Structural lemmas** — fuel-monotonicity of the bounded predicates
  and the unbounded-to-bounded conversion `ΞInvariantAtCFrame_of_witness`.
* **Equality-driven lift** — `ΞPreservesInvariantAtC` is preserved by
  `find?`-equal post-states (analogue of `StorageSumLeBalance_of_find?_eq`'s
  closure under projection equality).

### Out of scope here (§H.2 / Phase A.2-style closure)

The mutual closure's closure proofs — `Θ_invariant_preserved_bdd`,
`Λ_invariant_preserved_bdd`, `Ξ_invariant_preserved_bundled_bdd`,
`call_invariant_preserved`, `ΞPreservesInvariantAtC_of_Reachable_general`
— are NOT included here. Those constitute §H.2 and require the joint
mutual induction over `Θ`/`Λ`/`Ξ`/`X` at the invariant level, with the
at-C `CALL` arm dispatching through a new `call_invariant_preserved`
helper (since `call_balanceOf_ge`'s `h_s : C ≠ src ∨ v = 0` cannot be
discharged at the at-C CALL of a CEI-pattern withdraw block where
both `src = C` and `v ≠ 0`). The predicates landed here let
downstream §H.2 work proceed without re-litigating the type
signatures. -/

-- `StorageSumLeBalance` is defined in `EvmYul.Frame.MutualFrame` (kept
-- there because `UpsilonFrame.lean`'s framework-level
-- `Υ_invariant_preserved` chain references it).

/-- The relational-invariant sibling of `ΞPreservesAtC C`: when Ξ runs
at `I.codeOwner = C` (i.e. *executing C's own code*), the **invariant**
`storageSum σ C ≤ balanceOf σ C` is preserved (rather than `balanceOf C`
monotone, which fails when the at-C block performs an SSTORE-decrement
followed by an outbound CALL with that decremented value as `value`).

Universal-fuel form. The fuel-bounded sibling `ΞInvariantAtCFrame` below
mirrors `ΞAtCFrame`'s relationship to `ΞPreservesAtC`. -/
def ΞPreservesInvariantAtC (C : AccountAddress) : Prop :=
  ∀ (fuel : ℕ) (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM),
    StateWF σ →
    I.codeOwner = C →
    (∀ a ∈ createdAccounts, a ≠ C) →
    StorageSumLeBalance σ C →
    match EVM.Ξ fuel createdAccounts genesisBlockHeader blocks σ σ₀ g A I with
    | .ok (.success (cA', σ', _, _) _) =>
        StorageSumLeBalance σ' C ∧ StateWF σ' ∧ (∀ a ∈ cA', a ≠ C)
    | _ => True

/-- Fuel-bounded sibling of `ΞPreservesInvariantAtC`: at every fuel
`≤ maxFuel`, the at-`C` Ξ run preserves the invariant + StateWF +
cA-exclusion at `C`. Mirror of `ΞAtCFrame` for the invariant chain.

Used by the at-`C` proof chain to support strong-fuel induction. When
proving `Ξ_invariant_preserved_bundled_bdd` at fuel `n+1`, the inner Ξ
runs at fuels `≤ n` are all covered by `ΞInvariantAtCFrame C n` from
the strong IH. -/
def ΞInvariantAtCFrame (C : AccountAddress) (maxFuel : ℕ) : Prop :=
  ∀ (fuel : ℕ), fuel ≤ maxFuel →
    ∀ (createdAccounts : RBSet AccountAddress compare)
      (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
      (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
      (I : ExecutionEnv .EVM),
      StateWF σ →
      I.codeOwner = C →
      (∀ a ∈ createdAccounts, a ≠ C) →
      StorageSumLeBalance σ C →
      match EVM.Ξ fuel createdAccounts genesisBlockHeader blocks σ σ₀ g A I with
      | .ok (.success (cA', σ', _, _) _) =>
          StorageSumLeBalance σ' C ∧ StateWF σ' ∧ (∀ a ∈ cA', a ≠ C)
      | _ => True

/-- The complement of `ΞInvariantAtCFrame`: at `C ≠ I.codeOwner`, the
non-at-C Ξ run preserves the invariant at every fuel `≤ maxFuel`.

The closure proof of this (in §H.2) routes through the existing
balance-monotonicity frame for `β` (β monotone at non-C frames, but
nested at-C sub-frames may also touch S — handled via mutual recursion
with the `ΞInvariantAtCFrame` witness). -/
def ΞInvariantFrameAtC (C : AccountAddress) (maxFuel : ℕ) : Prop :=
  ∀ (fuel : ℕ), fuel ≤ maxFuel →
    ∀ (createdAccounts : RBSet AccountAddress compare)
      (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
      (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
      (I : ExecutionEnv .EVM),
      StateWF σ →
      C ≠ I.codeOwner →
      (∀ a ∈ createdAccounts, a ≠ C) →
      StorageSumLeBalance σ C →
      match EVM.Ξ fuel createdAccounts genesisBlockHeader blocks σ σ₀ g A I with
      | .ok (.success (cA', σ', _, _) _) =>
          StorageSumLeBalance σ' C ∧ StateWF σ' ∧ (∀ a ∈ cA', a ≠ C)
      | _ => True

/-! ### Structural lemmas for the §H predicates -/

/-- An unbounded `ΞPreservesInvariantAtC C` witness yields
`ΞInvariantAtCFrame C maxFuel` at any `maxFuel`. Mirror of
`ΞAtCFrame_of_witness`. -/
theorem ΞInvariantAtCFrame_of_witness (C : AccountAddress)
    (hWitness : ΞPreservesInvariantAtC C) (maxFuel : ℕ) :
    ΞInvariantAtCFrame C maxFuel := by
  intro fuel _hf cA gbh bs σ σ₀ g A I hWF hCO hNC hInv
  exact hWitness fuel cA gbh bs σ σ₀ g A I hWF hCO hNC hInv

/-- Monotonicity of `ΞInvariantAtCFrame` in the fuel bound. -/
theorem ΞInvariantAtCFrame_mono (C : AccountAddress) (a b : ℕ) (hab : b ≤ a)
    (hA : ΞInvariantAtCFrame C a) : ΞInvariantAtCFrame C b := by
  intro f hf
  exact hA f (Nat.le_trans hf hab)

/-- Monotonicity of `ΞInvariantFrameAtC` in the fuel bound. -/
theorem ΞInvariantFrameAtC_mono (C : AccountAddress) (a b : ℕ) (hab : b ≤ a)
    (hA : ΞInvariantFrameAtC C a) : ΞInvariantFrameAtC C b := by
  intro f hf
  exact hA f (Nat.le_trans hf hab)

/-- `StorageSumLeBalance` is preserved by `find?`-equality at `C`. Direct
projection-equality lemma: if two states agree on `find? C`, they have
the same `storageSum C` and the same `balanceOf C`, so the invariant
projects identically. -/
theorem StorageSumLeBalance_of_find?_eq
    {σ σ' : AccountMap .EVM} {C : AccountAddress}
    (h : σ'.find? C = σ.find? C)
    (hInv : StorageSumLeBalance σ C) :
    StorageSumLeBalance σ' C := by
  unfold StorageSumLeBalance at *
  rw [storageSum_of_find?_eq h, balanceOf_of_find?_eq h]
  exact hInv

/-- Projection: an `ΞInvariantAtCFrame C maxFuel` witness restricted to
a single fuel level `f ≤ maxFuel` collapses to the same shape as the
unbounded `ΞPreservesInvariantAtC` predicate at that fuel. Symmetric
with `ΞAtCFrame_of_witness`'s reverse direction; useful when consumers
have a per-fuel witness and need the unbounded form. -/
theorem ΞInvariantAtCFrame_apply (C : AccountAddress) (maxFuel : ℕ)
    (h : ΞInvariantAtCFrame C maxFuel)
    (fuel : ℕ) (hf : fuel ≤ maxFuel)
    (cA : RBSet AccountAddress compare) (gbh : BlockHeader)
    (bs : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (g : UInt256)
    (A : Substate) (I : ExecutionEnv .EVM)
    (hWF : StateWF σ) (hCO : I.codeOwner = C)
    (hNC : ∀ a ∈ cA, a ≠ C) (hInv : StorageSumLeBalance σ C) :
    match EVM.Ξ fuel cA gbh bs σ σ₀ g A I with
    | .ok (.success (cA', σ', _, _) _) =>
        StorageSumLeBalance σ' C ∧ StateWF σ' ∧ (∀ a ∈ cA', a ≠ C)
    | _ => True :=
  h fuel hf cA gbh bs σ σ₀ g A I hWF hCO hNC hInv

/-- Projection counterpart for `ΞInvariantFrameAtC`. -/
theorem ΞInvariantFrameAtC_apply (C : AccountAddress) (maxFuel : ℕ)
    (h : ΞInvariantFrameAtC C maxFuel)
    (fuel : ℕ) (hf : fuel ≤ maxFuel)
    (cA : RBSet AccountAddress compare) (gbh : BlockHeader)
    (bs : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (g : UInt256)
    (A : Substate) (I : ExecutionEnv .EVM)
    (hWF : StateWF σ) (hCO : C ≠ I.codeOwner)
    (hNC : ∀ a ∈ cA, a ≠ C) (hInv : StorageSumLeBalance σ C) :
    match EVM.Ξ fuel cA gbh bs σ σ₀ g A I with
    | .ok (.success (cA', σ', _, _) _) =>
        StorageSumLeBalance σ' C ∧ StateWF σ' ∧ (∀ a ∈ cA', a ≠ C)
    | _ => True :=
  h fuel hf cA gbh bs σ σ₀ g A I hWF hCO hNC hInv

/-! ### §H — Per-step `StorageSumLeBalance` preservation at non-`C` codeOwner

This is the leaf for the storage-side of §H's tracking. At any non-SD
handled step where the executing frame's `codeOwner ≠ C`, both
`storageSum σ C` and `balanceOf σ C` are preserved, so `StorageSumLeBalance σ C`
is preserved verbatim.

* `storageSum`-side: from `EvmYul.step_modifies_storage_only_at_codeOwner`
  (the `a ≠ codeOwner` storage-projection-equality lemma) plus
  `storageSum_of_storage_proj_eq`.
* `balanceOf`-side: from `EvmYul.step_preserves_balanceOf` (any
  handled non-SD step is a frame at every account address).

Used in §H.2's `Ξ_invariant_preserved_bundled_bdd` for the per-step
non-CALL/non-CREATE/non-SELFDESTRUCT case at codeOwner ≠ C. -/

/-- `storageSum σ C` is preserved by any handled non-SELFDESTRUCT step
when the executing frame's `codeOwner ≠ C`. -/
theorem EvmYul.step_preserves_storageSum_at_non_codeOwner
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State) (C : AccountAddress)
    (h_handled : handledByEvmYulStep op)
    (h_ne_sd : op ≠ .SELFDESTRUCT)
    (h : EvmYul.step op arg s = .ok s')
    (h_ne : C ≠ s.executionEnv.codeOwner) :
    storageSum s'.accountMap C = storageSum s.accountMap C := by
  -- Storage projection at C is unchanged by the step.
  -- `step_modifies_storage_only_at_codeOwner` takes `a ≠ codeOwner`;
  -- our `h_ne : C ≠ codeOwner` is the symmetric form.
  have h_ne' : C ≠ s.executionEnv.codeOwner := h_ne
  have hProj :
      ((s'.accountMap.find? C).map (·.storage))
        = ((s.accountMap.find? C).map (·.storage)) :=
    EvmYul.step_modifies_storage_only_at_codeOwner op arg s s' C
      h_handled h_ne_sd h h_ne'
  exact storageSum_of_storage_proj_eq hProj

/-- `StorageSumLeBalance σ C` is preserved by any handled non-SELFDESTRUCT step
when the executing frame's `codeOwner ≠ C`. The leaf for §H's
non-`C` tracking through `Θ`/`Λ`/`Ξ`. -/
theorem EvmYul_step_preserves_StorageSumLeBalance_at_non_C
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State) (C : AccountAddress)
    (h_handled : handledByEvmYulStep op)
    (h_ne_sd : op ≠ .SELFDESTRUCT)
    (h : EvmYul.step op arg s = .ok s')
    (h_ne : C ≠ s.executionEnv.codeOwner)
    (hInv : StorageSumLeBalance s.accountMap C) :
    StorageSumLeBalance s'.accountMap C := by
  unfold StorageSumLeBalance at *
  -- storageSum unchanged at C.
  have hStg : storageSum s'.accountMap C = storageSum s.accountMap C :=
    EvmYul.step_preserves_storageSum_at_non_codeOwner op arg s s' C
      h_handled h_ne_sd h h_ne
  -- balanceOf unchanged at C (any handled non-SD step is a frame at
  -- every address).
  have hBal : balanceOf s'.accountMap C = balanceOf s.accountMap C :=
    EvmYul.step_preserves_balanceOf op arg s s' C h_handled h_ne_sd h
  rw [hStg, hBal]
  exact hInv

/-- `StorageSumLeBalance σ C` is preserved by any handled step that strictly
preserves `accountMap` (i.e. neither SSTORE / TSTORE / SELFDESTRUCT
nor a CALL/CREATE-family op). At the at-C codeOwner, this is the
non-SSTORE / non-CALL part of §H.2's at-C step bundle: every "boring"
opcode (arithmetic, stack manipulation, environment query, jump,
log, …) preserves the invariant trivially because the whole
`accountMap` is preserved. -/
theorem EvmYul_step_preserves_StorageSumLeBalance_of_strict
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State) (C : AccountAddress)
    (hStrict : strictlyPreservesAccountMap op)
    (h : EvmYul.step op arg s = .ok s')
    (hInv : StorageSumLeBalance s.accountMap C) :
    StorageSumLeBalance s'.accountMap C := by
  -- accountMap is literally unchanged.
  have hAM : s'.accountMap = s.accountMap :=
    EvmYul.step_accountMap_eq_of_strict op arg s s' hStrict h
  -- The invariant projects through accountMap-equality verbatim.
  unfold StorageSumLeBalance at *
  rw [hAM]
  exact hInv

/-! ## §H.2 — Storage-side helpers for Θ's value-transfer prefix

The invariant `StorageSumLeBalance σ C := storageSum σ C ≤ balanceOf σ C` only
depends on the *balance* and *storage* projections of `σ` at `C`. Θ's
value-transfer prefix (credit `r` then debit `s`) only modifies
`balance` (storage is preserved through both `.insert` operations).
These helpers bridge the storage-side projection equality so the
invariant tracking through Θ's prefix only needs to handle balance
changes. -/

/-- Θ's `σ'₁` credit step preserves `storageSum C` for every `C`.

Both `.insert` branches preserve storage at every key:
* `none → some v`: insert at `r` with default storage. At `C ≠ r`,
  `storageSum` is preserved by `find?_insert_ne`. At `C = r`, the
  default storage's foldl-sum is `0`, and the σ-side has `find? r =
  none` ⇒ `storageSum σ r = 0` (definitional). So both equal `0`.
* `none → σ` (v = 0): trivial.
* `some acc → some {acc with balance := acc.balance + v}`: storage in
  the inserted account equals `acc.storage`, which is the storage at
  `r` in `σ`, so storage projection is preserved at every key. -/
theorem theta_σ'₁_storageSum_eq
    (σ : AccountMap .EVM) (r C : AccountAddress) (v : UInt256) :
    let σ'₁ :=
      match σ.find? r with
        | none =>
          if v != ⟨0⟩ then
            σ.insert r { (default : Account .EVM) with balance := v }
          else σ
        | some acc => σ.insert r { acc with balance := acc.balance + v }
    storageSum σ'₁ C = storageSum σ C := by
  simp only
  split
  · case _ hLook =>
    split
    · -- v ≠ 0, insert default-record with balance v
      by_cases hrC : r = C
      · -- r = C: the inserted account has default storage; storageSum σ C = 0 from hLook.
        subst hrC
        unfold storageSum
        rw [find?_insert_self, hLook]
        -- LHS: foldl over default storage = 0; RHS: 0.
        rfl
      · apply storageSum_unchanged_at_other_account
        exact hrC
    · -- v = 0, σ unchanged
      rfl
  · case _ acc hLook =>
    by_cases hrC : r = C
    · -- r = C: inserted account has acc.storage; storageSum projects identically.
      subst hrC
      unfold storageSum
      rw [find?_insert_self, hLook]
    · apply storageSum_unchanged_at_other_account
      exact hrC

/-- Θ's `σ₁` debit step preserves `storageSum C` for every `C`.

Same shape as `theta_σ'₁_storageSum_eq` but for the `s`-side debit:
`.insert s { acc with balance := acc.balance - v }`. The storage
projection is unchanged because `acc.storage` is reused. -/
theorem theta_σ₁_storageSum_eq
    (σ'₁ : AccountMap .EVM) (s C : AccountAddress) (v : UInt256) :
    let σ₁ :=
      match σ'₁.find? s with
        | none => σ'₁
        | some acc => σ'₁.insert s { acc with balance := acc.balance - v }
    storageSum σ₁ C = storageSum σ'₁ C := by
  simp only
  split
  · rfl
  · case _ acc hLook =>
    by_cases hsC : s = C
    · subst hsC
      unfold storageSum
      rw [find?_insert_self, hLook]
    · apply storageSum_unchanged_at_other_account
      exact hsC

/-- The credit prefix `σ → σ'₁` preserves `StorageSumLeBalance σ C` always (slack
weakly increases: at `r = C` balance grows; at `r ≠ C` balance is
unchanged).

Combined with `theta_σ'₁_storageSum_eq` (storage unchanged at `C`), and
`theta_σ'₁_ge` (balance monotone at `C`), the invariant carries
through verbatim. -/
theorem theta_σ'₁_invariant_preserved
    (σ : AccountMap .EVM) (r C : AccountAddress) (v : UInt256)
    (hWF : StateWF σ)
    (hValBound : ∀ acc, σ.find? r = some acc →
        acc.balance.toNat + v.toNat < UInt256.size)
    (hInv : StorageSumLeBalance σ C) :
    let σ'₁ :=
      match σ.find? r with
        | none =>
          if v != ⟨0⟩ then
            σ.insert r { (default : Account .EVM) with balance := v }
          else σ
        | some acc => σ.insert r { acc with balance := acc.balance + v }
    StorageSumLeBalance σ'₁ C := by
  unfold StorageSumLeBalance at *
  -- storageSum unchanged + balance monotone ⇒ invariant preserved.
  have hStg := theta_σ'₁_storageSum_eq σ r C v
  have hBal := theta_σ'₁_ge σ r C v hWF hValBound
  simp only at hStg hBal ⊢
  rw [hStg]
  exact Nat.le_trans hInv hBal

/-- **Θ-pre-credit slack at recipient = C.**

Given `σ` satisfying `StorageSumLeBalance σ C` and `r = C`, the post-credit
state `σ'₁` (after Θ adds `v` to `C`'s balance) satisfies the
strengthened slack `v.toNat + storageSum σ'₁ C ≤ balanceOf σ'₁ C`.

This is the precise hypothesis consumed by
`theta_σ₁_invariant_preserved_at_C` for the s = C, v ≠ 0 debit, and
also the bytecode-level "Θ-pre-credit" fact backing a deposit-style
SSTORE that writes `oldVal + msg.value` into the same slot, so the net
storageSum delta is `+v`.

Proof: `storageSum σ'₁ C = storageSum σ C` (storage unchanged at `C`
through credit) plus `balanceOf σ'₁ C = balanceOf σ C + v.toNat`
(from no-wrap balance arithmetic at `r = C`). Combined with
`storageSum σ C ≤ balanceOf σ C` (the input invariant), we get
`v.toNat + storageSum σ'₁ C = v.toNat + storageSum σ C ≤ v.toNat +
balanceOf σ C = balanceOf σ'₁ C`. -/
theorem theta_σ'₁_pre_credit_slack_at_C
    (σ : AccountMap .EVM) (C : AccountAddress) (v : UInt256)
    (hValBound : ∀ acc, σ.find? C = some acc →
        acc.balance.toNat + v.toNat < UInt256.size)
    (hInv : StorageSumLeBalance σ C) :
    let σ'₁ :=
      match σ.find? C with
        | none =>
          if v != ⟨0⟩ then
            σ.insert C { (default : Account .EVM) with balance := v }
          else σ
        | some acc => σ.insert C { acc with balance := acc.balance + v }
    v.toNat + storageSum σ'₁ C ≤ balanceOf σ'₁ C := by
  -- Storage unchanged at C through the credit (theta_σ'₁_storageSum_eq with r := C).
  have hStg := theta_σ'₁_storageSum_eq σ C C v
  unfold StorageSumLeBalance at hInv
  simp only at hStg
  -- Compute balanceOf σ'₁ C precisely by case split.
  cases hLook : σ.find? C with
  | none =>
    -- σ.find? C = none, so balanceOf σ C = 0 and storageSum σ C = 0 from hInv.
    have hBal0 : balanceOf σ C = 0 := by
      unfold balanceOf; rw [hLook]; rfl
    have hStg0 : storageSum σ C = 0 := by
      rw [hBal0] at hInv; omega
    -- Both v = 0 and v ≠ 0 sub-cases give 0 + 0 ≤ 0 or v.toNat ≤ v.toNat.
    -- Reduce the goal by computing σ'₁ via simp.
    show v.toNat +
        storageSum (
          if v != ⟨0⟩ then
            σ.insert C { (default : Account .EVM) with balance := v }
          else σ) C ≤
        balanceOf (
          if v != ⟨0⟩ then
            σ.insert C { (default : Account .EVM) with balance := v }
          else σ) C
    by_cases hv_eq_0 : v = (⟨0⟩ : UInt256)
    · -- v = 0 branch: σ'₁ = σ.
      have hbne : (v != (⟨0⟩ : UInt256)) = false := by rw [hv_eq_0]; rfl
      rw [show (if (v != ⟨0⟩) = true then
            σ.insert C { (default : Account .EVM) with balance := v} else σ) = σ from by
        rw [hbne]; rfl]
      have hvNat : v.toNat = 0 := by rw [hv_eq_0]; rfl
      rw [hvNat, Nat.zero_add]
      exact hInv
    · -- v ≠ 0 branch: σ'₁ = σ.insert C { default with balance := v }.
      have hbne : (v != (⟨0⟩ : UInt256)) = true := by
        by_contra hc
        have hbF : (v != (⟨0⟩ : UInt256)) = false := by
          cases hh : (v != (⟨0⟩ : UInt256)) with
          | true => exact absurd hh hc
          | false => rfl
        have h_eq : v = (⟨0⟩ : UInt256) := by
          have h_beq : (v == (⟨0⟩ : UInt256)) = true := by
            cases hh : (v == (⟨0⟩ : UInt256)) with
            | true => rfl
            | false =>
              have : (v != (⟨0⟩ : UInt256)) = true := by
                show (!(v == (⟨0⟩ : UInt256))) = true
                rw [hh]; rfl
              rw [this] at hbF; cases hbF
          cases v with
          | mk vv =>
            cases vv with
            | mk m lt =>
              have h_m0 : m = 0 := by
                cases m with
                | zero => rfl
                | succ k =>
                  exfalso
                  have : (Nat.beq (k + 1) 0) = true := h_beq
                  exact Bool.noConfusion this
              subst h_m0; rfl
        exact hv_eq_0 h_eq
      rw [show (if (v != ⟨0⟩) = true then
            σ.insert C { (default : Account .EVM) with balance := v} else σ)
          = σ.insert C { (default : Account .EVM) with balance := v} from by
        rw [hbne]; rfl]
      -- Compute storageSum and balanceOf at C in the inserted map.
      have hStg' : storageSum
            (σ.insert C { (default : Account .EVM) with balance := v }) C = 0 := by
        have hcomb := hStg
        rw [hLook] at hcomb
        simp only at hcomb
        rw [hbne] at hcomb
        simp only [if_true] at hcomb
        rw [hcomb]; exact hStg0
      have hBal' : balanceOf
            (σ.insert C { (default : Account .EVM) with balance := v }) C
            = v.toNat := by
        unfold balanceOf
        rw [find?_insert_self]
        rfl
      rw [hStg', hBal']
      omega
  | some acc =>
    -- σ.find? C = some acc, σ'₁ = σ.insert C { acc with balance := acc.balance + v }.
    simp only []
    have hWrap : acc.balance.toNat + v.toNat < UInt256.size := hValBound acc hLook
    -- storageSum σ'₁ C = storageSum σ C from hStg.
    have hStg' : storageSum (σ.insert C { acc with balance := acc.balance + v }) C
        = storageSum σ C := by
      have := hStg
      rw [hLook] at this
      simp only at this
      exact this
    -- balanceOf σ'₁ C = (acc.balance + v).toNat = acc.balance.toNat + v.toNat.
    have hBal' : balanceOf (σ.insert C { acc with balance := acc.balance + v }) C
        = acc.balance.toNat + v.toNat := by
      unfold balanceOf
      rw [find?_insert_self]
      simp only [Option.elim]
      exact UInt256_add_toNat_of_no_wrap _ _ hWrap
    -- balanceOf σ C = acc.balance.toNat.
    have hBalσ : balanceOf σ C = acc.balance.toNat := by
      unfold balanceOf; rw [hLook]; rfl
    rw [hStg', hBal']
    rw [hBalσ] at hInv
    omega

/-- The debit prefix `σ'₁ → σ₁` preserves `StorageSumLeBalance σ'₁ C` when
either `s ≠ C` (balance unchanged) or `v = 0` (balance unchanged).

For the s = C, v ≠ 0 case, see `theta_σ₁_invariant_preserved_at_C`
which takes the slack hypothesis as input. -/
theorem theta_σ₁_invariant_preserved_general
    (σ'₁ : AccountMap .EVM) (s C : AccountAddress) (v : UInt256)
    (h_s : C ≠ s ∨ v = ⟨0⟩)
    (hInv : StorageSumLeBalance σ'₁ C) :
    let σ₁ :=
      match σ'₁.find? s with
        | none => σ'₁
        | some acc => σ'₁.insert s { acc with balance := acc.balance - v }
    StorageSumLeBalance σ₁ C := by
  unfold StorageSumLeBalance at *
  -- storageSum unchanged + balance unchanged at C ⇒ invariant preserved.
  have hStg := theta_σ₁_storageSum_eq σ'₁ s C v
  have hBal := theta_σ₁_preserves σ'₁ s C v h_s
  simp only at hStg hBal ⊢
  exact hStg ▸ hBal ▸ hInv

/-- The debit prefix `σ'₁ → σ₁` at `s = C` (and `v ≠ 0`): the
balance shrinks by `v` at `C`, but the invariant holds *if* the slack
hypothesis covers `v`. The slack hypothesis takes the form
`v.toNat + storageSum σ'₁ C ≤ balanceOf σ'₁ C` which is the precise
form of "the credit/debit doesn't violate the invariant". -/
theorem theta_σ₁_invariant_preserved_at_C
    (σ'₁ : AccountMap .EVM) (C : AccountAddress) (v : UInt256)
    (h_funds : ∀ acc, σ'₁.find? C = some acc → v.toNat ≤ acc.balance.toNat)
    (h_slack : v.toNat + storageSum σ'₁ C ≤ balanceOf σ'₁ C) :
    let σ₁ :=
      match σ'₁.find? C with
        | none => σ'₁
        | some acc => σ'₁.insert C { acc with balance := acc.balance - v }
    StorageSumLeBalance σ₁ C := by
  unfold StorageSumLeBalance
  simp only
  -- storageSum unchanged at C through the s=C insert.
  have hStg := theta_σ₁_storageSum_eq σ'₁ C C v
  simp only at hStg
  rw [hStg]
  -- balanceOf σ₁ C: split on σ'₁.find? C.
  cases hLook : σ'₁.find? C with
  | none =>
    -- σ₁ = σ'₁, balanceOf σ'₁ C = 0 (since find? = none), storageSum σ'₁ C
    -- ≤ 0 from h_slack so storageSum = 0; goal is 0 ≤ 0.
    have hBal0 : balanceOf σ'₁ C = 0 := by
      unfold balanceOf; rw [hLook]; rfl
    rw [hBal0] at h_slack ⊢
    have hS0 : storageSum σ'₁ C = 0 := by omega
    rw [hS0]
  | some acc =>
    -- σ₁ = σ'₁.insert C { acc with balance := acc.balance - v }.
    -- balanceOf σ₁ C = (acc.balance - v).toNat.
    have hBal_v : v.toNat ≤ acc.balance.toNat := h_funds acc hLook
    have hBalσ'₁ : balanceOf σ'₁ C = acc.balance.toNat := by
      unfold balanceOf; rw [hLook]; rfl
    show balanceOf
        (σ'₁.insert C { acc with balance := acc.balance - v }) C
        ≥ storageSum σ'₁ C
    unfold balanceOf
    rw [find?_insert_self]
    show (acc.balance - v).toNat ≥ storageSum σ'₁ C
    -- show acc.balance - v |>.toNat ≥ storageSum σ'₁ C.
    rw [UInt256_sub_toNat_of_le _ _ hBal_v]
    -- v.toNat + storageSum ≤ balanceOf σ'₁ C = acc.balance.toNat
    rw [hBalσ'₁] at h_slack
    omega

/-- Θ's σ'-clamp step for the invariant: if the interpreter-dispatch
result `σ''` either preserves StorageSumLeBalance (when non-empty by BEq) or is
∅, then `σ' = if σ'' == ∅ then σ else σ''` preserves StorageSumLeBalance too. -/
theorem theta_σ'_clamp_invariant
    (σ σ'' : AccountMap .EVM) (C : AccountAddress)
    (hInvσ : StorageSumLeBalance σ C)
    (hInv : (σ'' == ∅) = false → StorageSumLeBalance σ'' C) :
    StorageSumLeBalance (if σ'' == ∅ then σ else σ'') C := by
  cases h : (σ'' == ∅) with
  | true => simp only [if_true]; exact hInvσ
  | false => simp only [Bool.false_eq_true, if_false]; exact hInv h

/-- Strengthened clamp using the case analysis `σ'' = σ₁ ∨ σ'' = ∅`,
mirroring `theta_σ'_clamp_ge_of_σ₁_or_empty`. -/
theorem theta_σ'_clamp_invariant_of_σ₁_or_empty
    (σ σ₁ σ'' : AccountMap .EVM) (C : AccountAddress)
    (hInvσ : StorageSumLeBalance σ C)
    (hInvσ₁ : StorageSumLeBalance σ₁ C)
    (hσ''_cases : σ'' = σ₁ ∨ σ'' = ∅) :
    StorageSumLeBalance (if σ'' == ∅ then σ else σ'') C := by
  apply theta_σ'_clamp_invariant _ _ _ hInvσ
  intro hNotEmpty
  rcases hσ''_cases with heq | heq
  · rw [heq]; exact hInvσ₁
  · exfalso
    rw [heq] at hNotEmpty
    have hTrue : ((∅ : AccountMap .EVM) == ∅) = true := rfl
    rw [hTrue] at hNotEmpty
    exact Bool.noConfusion hNotEmpty

/-! ## §H.2 — `Θ_invariant_preserved_bdd`

The relational-invariant sibling of `Θ_balanceOf_ge_bdd`. Tracks `StorageSumLeBalance
σ C` (rather than `≥ b₀`) through `EVM.Θ`. Same closure structure
(value-transfer prefix → precompile/code dispatch → σ'-clamp), but
with two key changes:

* The hypothesis on the s-side debit. For the balance closure, the
  debit only mattered when s = C (where it would shrink the balance
  in a way that broke `≥ b₀`). For the invariant closure, the same
  s = C case is the *only* one that needs special handling: we need a
  slack hypothesis `v.toNat + storageSum σ C ≤ balanceOf σ C` to
  cover the debit. The hypothesis `h_slack` provides this disjunction
  (s ≠ C ∨ v = 0 ∨ slack covers v).
* The two mutual-induction frames are now the invariant variants:
  `ΞInvariantAtCFrame` for r = C and `ΞInvariantFrameAtC` for r ≠ C.

The proof structure mirrors `Θ_balanceOf_ge_bdd`'s precompile/code
dispatch but uses the invariant-tracking helpers `theta_σ'₁_invariant_preserved`,
`theta_σ₁_invariant_preserved_general`,
`theta_σ₁_invariant_preserved_at_C`, and
`theta_σ'_clamp_invariant_of_σ₁_or_empty`. -/

/-- Θ's body — precompile arm, invariant version. The conclusion is
`StorageSumLeBalance σ' C` instead of `balanceOf σ' C ≥ balanceOf σ C`. -/
private theorem Θ_body_precompile_invariant
    (σ σ₁ : AccountMap .EVM) (A : Substate) (I : ExecutionEnv .EVM)
    (C : AccountAddress) (fuel' : Nat)
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ₀ : AccountMap .EVM) (s o r : AccountAddress) (pc : AccountAddress)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat)
    (H : BlockHeader) (w : Bool)
    (hInvσ : StorageSumLeBalance σ C)
    (hInvσ₁ : StorageSumLeBalance σ₁ C)
    (hWF : StateWF σ)
    (h_WFσ₁ : StateWF σ₁)
    (hΘeq : EVM.Θ (fuel' + 1) blobVersionedHashes createdAccounts
                genesisBlockHeader blocks σ σ₀ A s o r
                (ToExecute.Precompiled pc) g p v v' d e H w
          = (do
              let y ← EVM.applyPrecompile pc σ₁ g A I
              match y with
              | (cA'', z, σ'', g', A'', out) =>
                let σ' := if (σ'' == ∅) then σ else σ''
                let A' := if (σ'' == ∅) then A else A''
                pure (cA'', σ', g', A', z, out))) :
    match EVM.Θ (fuel' + 1) blobVersionedHashes createdAccounts
                  genesisBlockHeader blocks σ σ₀ A s o r
                  (ToExecute.Precompiled pc) g p v v' d e H w with
    | .ok (cA'_out, σ', _, _, _, _) =>
        StorageSumLeBalance σ' C ∧ StateWF σ' ∧ (∀ a ∈ cA'_out, a ≠ C)
    | .error _ => True := by
  rw [hΘeq]
  obtain ⟨tup, hTup, hCases, hcA_empty⟩ := applyPrecompile_bundled pc σ₁ g A I
  rw [hTup]
  refine ⟨?_, ?_, ?_⟩
  · -- StorageSumLeBalance.
    exact theta_σ'_clamp_invariant_of_σ₁_or_empty σ σ₁ tup.2.2.1 C
      hInvσ hInvσ₁ hCases
  · -- StateWF σ'.
    show StateWF (if (tup.2.2.1 == ∅) = true then σ else tup.2.2.1)
    rcases hCases with heq | heq
    · split_ifs
      · exact hWF
      · rw [heq]; exact h_WFσ₁
    · rw [heq]
      have h : ((∅ : AccountMap .EVM) == ∅) = true := rfl
      rw [h]; simp only [if_true]; exact hWF
  · show ∀ a' ∈ tup.1, a' ≠ C
    rw [hcA_empty]
    intro a' ha'
    exact absurd ha' (fun h => by cases h)

/-- Θ's body — code arm, invariant version. -/
private theorem Θ_body_code_invariant
    (σ σ₁ : AccountMap .EVM) (A : Substate) (I : ExecutionEnv .EVM)
    (C : AccountAddress) (fuel' : Nat)
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ₀ : AccountMap .EVM) (s o r : AccountAddress) (c_code : ByteArray)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat)
    (H : BlockHeader) (w : Bool)
    (hInvσ : StorageSumLeBalance σ C)
    (hInvσ₁ : StorageSumLeBalance σ₁ C)
    (hWF : StateWF σ)
    (h_WFσ₁ : StateWF σ₁)
    (h_newC : ∀ a ∈ createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C fuel')
    (hFrame : ΞInvariantFrameAtC C fuel')
    (hI_codeOwner : I.codeOwner = r)
    (hΘeq : EVM.Θ (fuel' + 1) blobVersionedHashes createdAccounts
                genesisBlockHeader blocks σ σ₀ A s o r
                (ToExecute.Code c_code) g p v v' d e H w
          = (do
              let y ←
                match EVM.Ξ fuel' createdAccounts genesisBlockHeader blocks
                        σ₁ σ₀ g A I with
                | .error e =>
                  if e == .OutOfFuel then throw .OutOfFuel
                  else pure (createdAccounts, false, σ, ⟨0⟩, A, .empty)
                | .ok (.revert g' o) =>
                  pure (createdAccounts, false, σ, g', A, o)
                | .ok (.success (a, b, c', d) o) =>
                  pure (a, true, b, c', d, o)
              match y with
              | (cA'', z, σ'', g', A'', out) =>
                let σ' := if (σ'' == ∅) then σ else σ''
                let A' := if (σ'' == ∅) then A else A''
                pure (cA'', σ', g', A', z, out))) :
    match EVM.Θ (fuel' + 1) blobVersionedHashes createdAccounts
                  genesisBlockHeader blocks σ σ₀ A s o r
                  (ToExecute.Code c_code) g p v v' d e H w with
    | .ok (cA'_out, σ', _, _, _, _) =>
        StorageSumLeBalance σ' C ∧ StateWF σ' ∧ (∀ a ∈ cA'_out, a ≠ C)
    | .error _ => True := by
  rw [hΘeq]
  cases hΞ : EVM.Ξ fuel' createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I
  case error err =>
    split
    case h_1 =>
      rename_i cA'' σ'' g' A'' z out heq
      by_cases hErr : err = EVM.ExecutionException.OutOfFuel
      · subst hErr
        simp only [bind, Except.bind, pure, Except.pure] at heq
        exact Except.noConfusion heq
      · have hBEq : (err == EVM.ExecutionException.OutOfFuel) = false := by
          cases err
          all_goals first
            | (exfalso; exact hErr rfl)
            | rfl
        simp only [bind, Except.bind, pure, Except.pure, hBEq,
                   Bool.false_eq_true, if_false] at heq
        injection heq with h1
        injection h1 with h1a h1b
        injection h1b with h1ba h1bb
        subst h1a
        subst h1ba
        refine ⟨?_, ?_, h_newC⟩
        · -- σ'' = σ → σ' = σ. Invariant preserved.
          show StorageSumLeBalance (if (σ == ∅) = true then σ else σ) C
          split_ifs <;> exact hInvσ
        · split_ifs <;> exact hWF
    case h_2 => trivial
  case ok res =>
    cases res
    case revert g' o_out =>
      split
      case h_1 =>
        rename_i cA'' σ'' g' A'' z out heq
        simp only [bind, Except.bind, pure, Except.pure] at heq
        injection heq with h1
        injection h1 with h1a h1b
        injection h1b with h1ba h1bb
        subst h1a
        subst h1ba
        refine ⟨?_, ?_, h_newC⟩
        · show StorageSumLeBalance (if (σ == ∅) = true then σ else σ) C
          split_ifs <;> exact hInvσ
        · split_ifs <;> exact hWF
      case h_2 => trivial
    case success details out =>
      obtain ⟨cA', σ_Ξ, g', A_Ξ⟩ := details
      split
      case h_1 =>
        rename_i cA'' σ'' g' A'' z out' heq
        simp only [bind, Except.bind, pure, Except.pure] at heq
        injection heq with h1
        injection h1 with h1a h1b
        injection h1b with h1ba h1bb
        subst h1a
        subst h1ba
        -- σ'' = σ_Ξ, cA'' = cA'.
        by_cases hrC : r = C
        · -- r = C: invoke ΞInvariantAtCFrame.
          have hIowner : I.codeOwner = C := by rw [hI_codeOwner]; exact hrC
          have hW := hAtCFrame fuel' (Nat.le_refl _) createdAccounts genesisBlockHeader blocks
              σ₁ σ₀ g A I h_WFσ₁ hIowner h_newC hInvσ₁
          rw [hΞ] at hW
          obtain ⟨hW_inv, hW_WF, hW_newC⟩ := hW
          refine ⟨?_, ?_, ?_⟩
          · apply theta_σ'_clamp_invariant
            · exact hInvσ
            · intro _; exact hW_inv
          · show StateWF (if (σ_Ξ == ∅) = true then σ else σ_Ξ)
            split_ifs
            · exact hWF
            · exact hW_WF
          · exact hW_newC
        · -- r ≠ C: invoke ΞInvariantFrameAtC.
          have hIowner_ne : C ≠ I.codeOwner := by
            rw [hI_codeOwner]; intro h; exact hrC h.symm
          have hW := hFrame fuel' (Nat.le_refl _)
              createdAccounts genesisBlockHeader blocks
              σ₁ σ₀ g A I h_WFσ₁ hIowner_ne h_newC hInvσ₁
          rw [hΞ] at hW
          obtain ⟨hW_inv, hW_WF, hW_newC⟩ := hW
          refine ⟨?_, ?_, ?_⟩
          · apply theta_σ'_clamp_invariant
            · exact hInvσ
            · intro _; exact hW_inv
          · show StateWF (if (σ_Ξ == ∅) = true then σ else σ_Ξ)
            split_ifs
            · exact hWF
            · exact hW_WF
          · exact hW_newC
      case h_2 => trivial

/-- §H.2's Θ frame for `StorageSumLeBalance`. Mirror of `Θ_balanceOf_ge_bdd`
but tracking the invariant. -/
private theorem Θ_invariant_preserved_bdd
    (fuel : Nat) (blobVersionedHashes : List ByteArray)
    (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute .EVM)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat)
    (H : BlockHeader) (w : Bool) (C : AccountAddress)
    (hWF : StateWF σ)
    (h_newC : ∀ a ∈ createdAccounts, a ≠ C)
    (hValBound : ∀ acc, σ.find? r = some acc →
        acc.balance.toNat + v.toNat < UInt256.size)
    (h_funds_strict :
        v = ⟨0⟩ ∨ ∃ acc, σ.find? s = some acc ∧ v.toNat ≤ acc.balance.toNat)
    (h_slack :
        C ≠ s ∨ v = ⟨0⟩ ∨
        v.toNat + storageSum σ C ≤ balanceOf σ C)
    (hInv : StorageSumLeBalance σ C)
    (hAtCFrame : ΞInvariantAtCFrame C fuel)
    (hFrame : ΞInvariantFrameAtC C fuel) :
    match EVM.Θ fuel blobVersionedHashes createdAccounts
                  genesisBlockHeader blocks σ σ₀ A s o r c g p v v' d e H w with
    | .ok (cA'_out, σ', _, _, _, _) =>
        StorageSumLeBalance σ' C ∧ StateWF σ' ∧ (∀ a ∈ cA'_out, a ≠ C)
    | .error _ => True := by
  match fuel with
  | 0 =>
    rw [show EVM.Θ 0 blobVersionedHashes createdAccounts genesisBlockHeader
                  blocks σ σ₀ A s o r c g p v v' d e H w = .error .OutOfFuel from rfl]
    trivial
  | fuel' + 1 =>
    -- Establish StorageSumLeBalance σ'₁ C via the credit-prefix helper.
    have h_σ'₁_inv := theta_σ'₁_invariant_preserved σ r C v hWF hValBound hInv
    set σ'₁ : AccountMap .EVM :=
      match σ.find? r with
        | none =>
          if v != ⟨0⟩ then
            σ.insert r
              { nonce := (default : Account .EVM).nonce
                balance := v
                storage := (default : Account .EVM).storage
                code := (default : Account .EVM).code
                tstorage := (default : Account .EVM).tstorage }
          else σ
        | some acc =>
          σ.insert r
            { nonce := acc.nonce
              balance := acc.balance + v
              storage := acc.storage
              code := acc.code
              tstorage := acc.tstorage }
      with hσ'₁_def
    set σ₁ : AccountMap .EVM :=
      match σ'₁.find? s with
        | none => σ'₁
        | some acc =>
          σ'₁.insert s
            { nonce := acc.nonce
              balance := acc.balance - v
              storage := acc.storage
              code := acc.code
              tstorage := acc.tstorage }
      with hσ₁_def
    -- Establish StorageSumLeBalance σ₁ C via the debit-prefix helper.
    have h_σ₁_inv : StorageSumLeBalance σ₁ C := by
      -- Decompose h_slack into the three cases.
      rcases h_slack with hCs | hv | hSlack
      · -- C ≠ s: use the general (s ≠ C disjunct) helper.
        exact theta_σ₁_invariant_preserved_general σ'₁ s C v (Or.inl hCs) h_σ'₁_inv
      · -- v = 0: use the general (v = 0 disjunct) helper.
        exact theta_σ₁_invariant_preserved_general σ'₁ s C v (Or.inr hv) h_σ'₁_inv
      · -- s = C, v ≠ 0, slack covers v: use the at-C helper.
        -- Need s = C — unfold from the (negated) form. Actually
        -- h_slack is over original σ; we need to lift to σ'₁.
        -- Use the trichotomy to pick C ≠ s for use in the general,
        -- otherwise s = C.
        by_cases hCs : C = s
        · -- s = C in h_slack. Need to show:
          -- h_funds : ∀ acc, σ'₁.find? C = some acc → v.toNat ≤ acc.balance.toNat.
          subst hCs
          -- Lift slack from σ to σ'₁ via balance monotonicity + storage equality.
          have hStg : storageSum σ'₁ C = storageSum σ C := theta_σ'₁_storageSum_eq σ r C v
          have hBal : balanceOf σ'₁ C ≥ balanceOf σ C := theta_σ'₁_ge σ r C v hWF hValBound
          have h_slack_σ'₁ : v.toNat + storageSum σ'₁ C ≤ balanceOf σ'₁ C := by
            rw [hStg]; omega
          have h_funds : ∀ acc, σ'₁.find? C = some acc → v.toNat ≤ acc.balance.toNat := by
            intro acc hLook
            have hBal_eq : balanceOf σ'₁ C = acc.balance.toNat := by
              unfold balanceOf; rw [hLook]; rfl
            have hVle : v.toNat ≤ balanceOf σ'₁ C := by omega
            rw [hBal_eq] at hVle
            exact hVle
          exact theta_σ₁_invariant_preserved_at_C σ'₁ C v h_funds h_slack_σ'₁
        · -- C ≠ s.
          push_neg at hCs
          exact theta_σ₁_invariant_preserved_general σ'₁ s C v (Or.inl hCs) h_σ'₁_inv
    -- StateWF σ₁.
    have h_WFσ₁ : StateWF σ₁ :=
      stateWF_theta_σ₁ σ hWF s r v hValBound h_funds_strict
    -- Execution env I.
    set I : ExecutionEnv .EVM :=
      { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d,
        code :=
          match c with
            | ToExecute.Precompiled _ => default
            | ToExecute.Code code => code,
        gasPrice := p.toNat, header := H, depth := e, perm := w,
        blobVersionedHashes := blobVersionedHashes }
      with hI_def
    cases c with
    | Precompiled pc =>
      have hΘeq :
          EVM.Θ (fuel' + 1) blobVersionedHashes createdAccounts
                genesisBlockHeader blocks σ σ₀ A s o r
                (ToExecute.Precompiled pc) g p v v' d e H w
            = (do
                let y ← EVM.applyPrecompile pc σ₁ g A I
                match y with
                | (cA'', z, σ'', g', A'', out) =>
                  let σ' := if (σ'' == ∅) then σ else σ''
                  let A' := if (σ'' == ∅) then A else A''
                  pure (cA'', σ', g', A', z, out)) := by
        show _ = _
        rfl
      exact Θ_body_precompile_invariant σ σ₁ A I C fuel' blobVersionedHashes
        createdAccounts genesisBlockHeader blocks σ₀ s o r pc g p v v' d e H w
        hInv h_σ₁_inv hWF h_WFσ₁ hΘeq
    | Code c_code =>
      have hΘeq :
          EVM.Θ (fuel' + 1) blobVersionedHashes createdAccounts
                genesisBlockHeader blocks σ σ₀ A s o r
                (ToExecute.Code c_code) g p v v' d e H w
            = (do
                let y ←
                  match EVM.Ξ fuel' createdAccounts genesisBlockHeader blocks
                          σ₁ σ₀ g A I with
                  | .error e =>
                    if e == .OutOfFuel then throw .OutOfFuel
                    else pure (createdAccounts, false, σ, ⟨0⟩, A, .empty)
                  | .ok (.revert g' o) =>
                    pure (createdAccounts, false, σ, g', A, o)
                  | .ok (.success (a, b, c', d) o) =>
                    pure (a, true, b, c', d, o)
                match y with
                | (cA'', z, σ'', g', A'', out) =>
                  let σ' := if (σ'' == ∅) then σ else σ''
                  let A' := if (σ'' == ∅) then A else A''
                  pure (cA'', σ', g', A', z, out)) := by
        show _ = _
        rfl
      have hI_co : I.codeOwner = r := by rw [hI_def]
      have hAtCFrame' : ΞInvariantAtCFrame C fuel' :=
        ΞInvariantAtCFrame_mono C (fuel' + 1) fuel' (Nat.le_succ _) hAtCFrame
      have hFrame' : ΞInvariantFrameAtC C fuel' :=
        ΞInvariantFrameAtC_mono C (fuel' + 1) fuel' (Nat.le_succ _) hFrame
      exact Θ_body_code_invariant σ σ₁ A I C fuel' blobVersionedHashes
        createdAccounts genesisBlockHeader blocks σ₀ s o r c_code g p v v' d e H w
        hInv h_σ₁_inv hWF h_WFσ₁ h_newC hAtCFrame' hFrame' hI_co hΘeq

/-! ## §H.2 — `call_invariant_preserved`

The relational-invariant sibling of `call_balanceOf_ge`. Tracks `StorageSumLeBalance σ
C` through `EVM.call`'s gate-passing dispatch to `Θ`. The at-C CALL
helper used by §H.2's at-C step bundle (the at-C CALL arm of a CEI-pattern
withdraw block).

Hypotheses (analogous to `call_balanceOf_ge`, plus `hInv` and the
slack disjunction):
* `hWF`, `hNC`: T1, T5.
* `hAtCFrame`/`hFrame`: dual mutual IHs at smaller fuel for r = C / r ≠ C.
* `h_vb`/`h_fs`: no-wrap/funds at recipient/source.
* `hInv`: input invariant.
* `h_slack`: the at-C debit case requires
  `v.toNat + storageSum σ C ≤ balanceOf σ C` (the SSTORE-decrement
  step that precedes the outbound CALL). -/
theorem call_invariant_preserved
    (C : AccountAddress) (fuel : ℕ) (gasCost : ℕ)
    (gas src rcp t v v' inOff inSize outOff outSize : UInt256)
    (permission : Bool) (evmState state' : EVM.State) (x : UInt256)
    (hWF : StateWF evmState.accountMap)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C fuel)
    (hFrame : ΞInvariantFrameAtC C fuel)
    (h_vb : ∀ acc,
        (evmState.accountMap).find? (AccountAddress.ofUInt256 rcp) = some acc →
        acc.balance.toNat + v.toNat < UInt256.size)
    (h_fs : v = ⟨0⟩ ∨ ∃ acc,
              (evmState.accountMap).find? (AccountAddress.ofUInt256 src) = some acc ∧
              v.toNat ≤ acc.balance.toNat)
    (h_slack :
        C ≠ AccountAddress.ofUInt256 src ∨ v = ⟨0⟩ ∨
        v.toNat + storageSum evmState.accountMap C ≤ balanceOf evmState.accountMap C)
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hCall :
      EVM.call fuel gasCost evmState.executionEnv.blobVersionedHashes
        gas src rcp t v v' inOff inSize outOff outSize permission evmState
      = .ok (x, state')) :
    StorageSumLeBalance state'.accountMap C ∧
    StateWF state'.accountMap ∧
    state'.executionEnv.codeOwner = evmState.executionEnv.codeOwner ∧
    (∀ a ∈ state'.createdAccounts, a ≠ C) := by
  unfold EVM.call at hCall
  simp only [bind, Except.bind, pure, Except.pure] at hCall
  cases fuel with
  | zero =>
    simp only at hCall
    exact absurd hCall (by simp)
  | succ f =>
    simp only at hCall
    split at hCall
    · -- Gate passed. Θ was invoked at fuel f.
      rename_i hGate
      split at hCall
      · exact absurd hCall (by simp)
      · rename_i hΘ_prod hΘ
        obtain ⟨cA, σ', g', A', z, o⟩ := hΘ_prod
        injection hCall with hEq
        have hAtCFrame_f : ΞInvariantAtCFrame C f :=
          ΞInvariantAtCFrame_mono C (f + 1) f (Nat.le_succ _) hAtCFrame
        have hFrame_f : ΞInvariantFrameAtC C f :=
          ΞInvariantFrameAtC_mono C (f + 1) f (Nat.le_succ _) hFrame
        have hΘFrame :=
          Θ_invariant_preserved_bdd f
            evmState.executionEnv.blobVersionedHashes
            evmState.createdAccounts
            evmState.genesisBlockHeader
            evmState.blocks
            evmState.accountMap
            evmState.σ₀
            ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
            (AccountAddress.ofUInt256 src)
            evmState.executionEnv.sender
            (AccountAddress.ofUInt256 rcp)
            (toExecute .EVM evmState.accountMap (AccountAddress.ofUInt256 t))
            (.ofNat <| Ccallgas (AccountAddress.ofUInt256 t)
                                (AccountAddress.ofUInt256 rcp) v gas
                                evmState.accountMap evmState.toMachineState
                                evmState.substate)
            (.ofNat evmState.executionEnv.gasPrice)
            v v' (evmState.memory.readWithPadding inOff.toNat inSize.toNat)
            (evmState.executionEnv.depth + 1)
            evmState.executionEnv.header permission
            C hWF hNC h_vb h_fs h_slack hInv hAtCFrame_f hFrame_f
        rw [hΘ] at hΘFrame
        obtain ⟨hInv', hWF', hCA'⟩ := hΘFrame
        have hState_eq := (Prod.mk.injEq _ _ _ _).mp hEq
        obtain ⟨_hx, hState⟩ := hState_eq
        rw [← hState]
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact hInv'
        · exact hWF'
        · rfl
        · exact hCA'
    · -- Gate failed. accountMap unchanged.
      injection hCall with hEq
      have hState_eq := (Prod.mk.injEq _ _ _ _).mp hEq
      obtain ⟨_hx, hState⟩ := hState_eq
      rw [← hState]
      refine ⟨hInv, hWF, rfl, hNC⟩

/-! ## §H.2 — `Λ_invariant_preserved_bdd`

Mirror of `Λ_balanceOf_ge_bdd` for `StorageSumLeBalance`. Easier than Θ because
Λ's inner Ξ runs at `I.codeOwner = a ≠ C` (by `lambda_derived_address_ne_C`):
no joint mutual recursion needed; only `ΞInvariantFrameAtC` IH suffices.

The value-transfer prefix in Λ is `s → a`: insert at `s` with debit,
insert at `a` with credit. Since `a ≠ C` (Keccak axiom T5) and `s ≠ C`
(hypothesis), both inserts frame at `C` for both balance and storage.
So `StorageSumLeBalance σStarMap C = StorageSumLeBalance σ C` directly. -/
private theorem Λ_invariant_preserved_bdd
    (fuel : Nat) (blobVersionedHashes : List ByteArray)
    (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o : AccountAddress) (g p v : UInt256) (i : ByteArray) (e : UInt256)
    (ζ : Option ByteArray) (H : BlockHeader) (w : Bool)
    (C : AccountAddress)
    (hWF : StateWF σ)
    (h_s : C ≠ s)
    (h_newC : ∀ a ∈ createdAccounts, a ≠ C)
    (h_funds : ∀ acc, σ.find? s = some acc → v.toNat ≤ acc.balance.toNat)
    (hInv : StorageSumLeBalance σ C)
    (hFrame : ΞInvariantFrameAtC C fuel) :
    match EVM.Lambda fuel blobVersionedHashes createdAccounts
                  genesisBlockHeader blocks σ σ₀ A s o g p v i e ζ H w with
    | .ok (a, cA', σ', _, _, _, _) =>
        a ≠ C ∧ StorageSumLeBalance σ' C ∧ StateWF σ' ∧ (∀ a' ∈ cA', a' ≠ C)
    | .error _ => True := by
  set_option maxHeartbeats 2400000 in
  match fuel with
  | 0 =>
    rw [show EVM.Lambda 0 blobVersionedHashes createdAccounts genesisBlockHeader
                  blocks σ σ₀ A s o g p v i e ζ H w = .error .OutOfFuel from rfl]
    trivial
  | f + 1 =>
    have ha_ne_C : ∀ (n' : UInt256) lₐ, EVM.Lambda.L_A s n' ζ i = some lₐ →
        (Fin.ofNat AccountAddress.size
           (fromByteArrayBigEndian ((ffi.KEC lₐ).extract 12 32))
          : AccountAddress) ≠ C := by
      intro n' lₐ hLA
      have h := lambda_derived_address_ne_C s n' ζ i C
      have hGet : ((EVM.Lambda.L_A s n' ζ i).getD default) = lₐ := by
        rw [hLA]; rfl
      rw [← hGet]; exact h
    have ha_ne_s : ∀ (n' : UInt256) lₐ, EVM.Lambda.L_A s n' ζ i = some lₐ →
        (Fin.ofNat AccountAddress.size
           (fromByteArrayBigEndian ((ffi.KEC lₐ).extract 12 32))
          : AccountAddress) ≠ s := by
      intro n' lₐ hLA
      have h := lambda_derived_address_ne_C s n' ζ i s
      have hGet : ((EVM.Lambda.L_A s n' ζ i).getD default) = lₐ := by
        rw [hLA]; rfl
      rw [← hGet]; exact h
    unfold EVM.Lambda
    cases hLA : EVM.Lambda.L_A s
        ((σ.find? s |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩) ζ i with
    | none =>
      simp only [hLA]
      trivial
    | some lₐ =>
      simp only [hLA]
      set a : AccountAddress :=
        Fin.ofNat AccountAddress.size
          (fromByteArrayBigEndian ((ffi.KEC lₐ).extract 12 32))
      have ha_ne_C' : a ≠ C := ha_ne_C _ lₐ hLA
      have ha_ne_s' : a ≠ s := ha_ne_s _ lₐ hLA
      set existentAccount : Account .EVM := σ.findD a default
      set iPair :
        ByteArray × Batteries.RBSet AccountAddress compare :=
        if (decide (existentAccount.nonce ≠ ⟨0⟩)
            || decide (existentAccount.code.size ≠ 0)
            || existentAccount.storage != default) = true
        then ((⟨#[0xfe]⟩ : ByteArray), createdAccounts)
        else (i, createdAccounts.insert a) with hiPair_def
      have h_newC_iPair : ∀ a' ∈ iPair.2, a' ≠ C := by
        by_cases hIf :
            (decide (existentAccount.nonce ≠ ⟨0⟩)
              || decide (existentAccount.code.size ≠ 0)
              || existentAccount.storage != default) = true
        · have : iPair.2 = createdAccounts := by
            show (if
              (decide (existentAccount.nonce ≠ ⟨0⟩)
                || decide (existentAccount.code.size ≠ 0)
                || existentAccount.storage != default) = true
              then ((⟨#[0xfe]⟩ : ByteArray), createdAccounts)
              else (i, createdAccounts.insert a)).2 = createdAccounts
            rw [if_pos hIf]
          rw [this]
          exact h_newC
        · have : iPair.2 = createdAccounts.insert a := by
            show (if
              (decide (existentAccount.nonce ≠ ⟨0⟩)
                || decide (existentAccount.code.size ≠ 0)
                || existentAccount.storage != default) = true
              then ((⟨#[0xfe]⟩ : ByteArray), createdAccounts)
              else (i, createdAccounts.insert a)).2 = createdAccounts.insert a
            rw [if_neg hIf]
          rw [this]
          intro a' ha'_mem
          rw [Batteries.RBSet.mem_insert] at ha'_mem
          rcases ha'_mem with h_orig | h_eq
          · exact h_newC a' h_orig
          · have : a = a' := Std.LawfulEqCmp.compare_eq_iff_eq.mp h_eq
            rw [← this]; exact ha_ne_C'
      -- σStar's StorageSumLeBalance at C: balance unchanged (both inserts at ≠C),
      -- storage unchanged (both inserts at ≠C). So invariant carries.
      have hσStar_inv :
          ∀ (σ' : AccountMap .EVM),
            (σ' = (match σ.find? s with
                   | none => σ
                   | some ac =>
                     (σ.insert s
                       { nonce := ac.nonce, balance := ac.balance - v
                         storage := ac.storage, code := ac.code
                         tstorage := ac.tstorage })
                      |>.insert a
                       { nonce := existentAccount.nonce + ⟨1⟩
                         balance := v + existentAccount.balance
                         storage := existentAccount.storage
                         code := existentAccount.code
                         tstorage := existentAccount.tstorage })) →
            StorageSumLeBalance σ' C := by
        intro σ' hσ'
        rw [hσ']
        cases hFs : σ.find? s with
        | none =>
          -- match σ.find? s reduces to σ; goal is StorageSumLeBalance σ C.
          exact hInv
        | some ac =>
          have hsC : s ≠ C := fun h => h_s h.symm
          unfold StorageSumLeBalance
          rw [storageSum_unchanged_at_other_account _ _ _ _ ha_ne_C']
          rw [storageSum_unchanged_at_other_account _ _ _ _ hsC]
          rw [balanceOf_of_find?_eq (find?_insert_ne _ a C _ ha_ne_C')]
          rw [balanceOf_of_find?_eq (find?_insert_ne _ s C _ hsC)]
          exact hInv
      have hWFσStar :
          StateWF (match σ.find? s with
                   | none => σ
                   | some ac =>
                     (σ.insert s
                       { nonce := ac.nonce, balance := ac.balance - v
                         storage := ac.storage, code := ac.code
                         tstorage := ac.tstorage })
                      |>.insert a
                       { nonce := existentAccount.nonce + ⟨1⟩
                         balance := v + existentAccount.balance
                         storage := existentAccount.storage
                         code := existentAccount.code
                         tstorage := existentAccount.tstorage }) := by
        cases hFs : σ.find? s with
        | none => exact hWF
        | some ac =>
          have h_bound := h_funds ac hFs
          have := stateWF_lambda_σStar_some σ hWF s a ac v ha_ne_s' hFs h_bound
          exact this
      set σStarMap : AccountMap .EVM :=
        (match σ.find? s with
         | none => σ
         | some ac =>
           (σ.insert s
             { nonce := ac.nonce, balance := ac.balance - v
               storage := ac.storage, code := ac.code
               tstorage := ac.tstorage })
            |>.insert a
             { nonce := existentAccount.nonce + ⟨1⟩
               balance := v + existentAccount.balance
               storage := existentAccount.storage
               code := existentAccount.code
               tstorage := existentAccount.tstorage })
        with hσStarMap_def
      have hσStar_invMap : StorageSumLeBalance σStarMap C := hσStar_inv σStarMap hσStarMap_def
      have hWFσStarMap : StateWF σStarMap := by rw [hσStarMap_def]; exact hWFσStar
      set exEnv : ExecutionEnv .EVM :=
        { codeOwner := a, sender := o, source := s, weiValue := v
          calldata := default, code := iPair.1, gasPrice := p.toNat
          header := H, depth := e.toNat, perm := w
          blobVersionedHashes := blobVersionedHashes } with hexEnv_def
      split
      case h_2 => trivial
      case h_1 heq =>
        simp only [bind, Except.bind, pure, Except.pure] at heq
        split at heq
        · exact absurd heq (by simp)
        · rename_i lin hvok
          have hv_eq : lin = lₐ := by
            injection hvok with h1
            exact h1.symm
          rw [hv_eq] at heq
          clear hvok hv_eq lin
          split at heq
          · split at heq
            · exact absurd heq (by simp)
            · injection heq with h1
              injection h1 with h1a h1b
              injection h1b with h1ba h1bb
              injection h1bb with h1bba h1bbb
              subst h1a
              subst h1ba
              subst h1bba
              refine ⟨ha_ne_C', hInv, hWF, ?_⟩
              exact h_newC_iPair
          · injection heq with h1
            injection h1 with h1a h1b
            injection h1b with h1ba h1bb
            injection h1bb with h1bba h1bbb
            subst h1a
            subst h1ba
            subst h1bba
            refine ⟨ha_ne_C', hInv, hWF, ?_⟩
            exact h_newC_iPair
          · -- Ξ-success branch.
            rename_i cA_out σ_Ξ gSS AStarStar returnedData hΞeq
            injection heq with h1
            injection h1 with h1a h1b
            injection h1b with h1ba h1bb
            injection h1bb with h1bba h1bbb
            subst h1a
            subst h1ba
            subst h1bba
            have hΞeq_folded :
                EVM.Ξ f iPair.2 genesisBlockHeader blocks σStarMap σ₀ g
                      (A.addAccessedAccount a) exEnv
                    = .ok (.success (cA_out, σ_Ξ, gSS, AStarStar) returnedData) := hΞeq
            -- exEnv.codeOwner = a, and a ≠ C.
            have hCO_ne : C ≠ exEnv.codeOwner := by
              rw [hexEnv_def]; exact ha_ne_C'.symm
            have hFrame_f : ΞInvariantFrameAtC C f :=
              ΞInvariantFrameAtC_mono C (f + 1) f (Nat.le_succ _) hFrame
            have hΞInv_raw := hFrame_f f (Nat.le_refl _) iPair.2
              genesisBlockHeader blocks
              σStarMap σ₀ g (A.addAccessedAccount a) exEnv
              hWFσStarMap hCO_ne h_newC_iPair hσStar_invMap
            rw [hΞeq_folded] at hΞInv_raw
            obtain ⟨hΞInv_inv, hWFσ_Ξ, h_newC_out⟩ := hΞInv_raw
            refine ⟨ha_ne_C', ?_, ?_, h_newC_out⟩
            · -- σ_final = if F then σ else σ_Ξ.insert a {... with code := returnedData}.
              split_ifs with hF
              · exact hInv
              · -- StorageSumLeBalance (σ_Ξ.insert a {... with code := returnedData}) C.
                -- a ≠ C, so the insert frames at C for both balance & storage.
                unfold StorageSumLeBalance
                rw [storageSum_unchanged_at_other_account _ _ _ _ ha_ne_C']
                rw [balanceOf_of_find?_eq (find?_insert_ne _ a C _ ha_ne_C')]
                exact hΞInv_inv
            · split_ifs with hF
              · exact hWF
              · exact StateWF_insert_findD_code σ_Ξ a returnedData hWFσ_Ξ

/-! ## §H.2 — Per-arm system-call invariant helpers

Mirrors of `step_CALL_arm` / `step_CREATE_arm` / `step_CALLCODE_arm` /
`step_DELEGATECALL_arm` / `step_STATICCALL_arm` / `step_CREATE2_arm`,
but tracking `StorageSumLeBalance` instead of just `balanceOf σ C ≥ balanceOf σ
C`. Each arm dispatches to `call_invariant_preserved` or `Λ`
invariant analogue; the body otherwise follows the balance-side
template verbatim. -/

/-- DELEGATECALL invariant arm: `StorageSumLeBalance` is preserved through the
DELEGATECALL step at non-`C` codeOwner. DELEGATECALL passes value
`⟨0⟩` to `call`, so the slack hypothesis is trivially satisfied via
`Or.inr (Or.inl rfl)`. -/
private theorem step_DELEGATECALL_arm_invariant
    (C : AccountAddress) (f : ℕ) (cost₂ : ℕ) (arg : Option (UInt256 × Nat))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCO : C ≠ evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C (f + 1))
    (hFrame : ΞInvariantFrameAtC C (f + 1))
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hStep : EVM.step (f + 1) cost₂ (some (.DELEGATECALL, arg)) evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C ≠ sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  simp only [EVM.step, Operation.DELEGATECALL, bind, Except.bind, pure, Except.pure] at hStep
  set eS1 : EVM.State := { evmState with execLength := evmState.execLength + 1 } with heS1_def
  split at hStep
  · exact absurd hStep (by simp)
  · rename_i p hpop6
    obtain ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩ := p
    split at hStep
    · exact absurd hStep (by simp)
    · rename_i p_call hCallRes
      obtain ⟨x, state'⟩ := p_call
      injection hStep with hEq
      rw [← hEq]
      have hWFes1 : StateWF eS1.accountMap := hWF
      have hCOes1 : C ≠ eS1.executionEnv.codeOwner := hCO
      have hNCes1 : ∀ a ∈ eS1.createdAccounts, a ≠ C := hNC
      have hInves1 : StorageSumLeBalance eS1.accountMap C := hInv
      have h_vb_call :
          ∀ acc, (eS1.accountMap).find?
              (AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner)) = some acc →
            acc.balance.toNat + (⟨0⟩ : UInt256).toNat < UInt256.size := by
        intro acc _
        show acc.balance.toNat + 0 < UInt256.size
        rw [Nat.add_zero]
        exact acc.balance.val.isLt
      have h_fs_call :
          (⟨0⟩ : UInt256) = ⟨0⟩ ∨ ∃ acc, (eS1.accountMap).find?
                        (AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.source)) = some acc ∧
                  (⟨0⟩ : UInt256).toNat ≤ acc.balance.toNat := Or.inl rfl
      have h_slack_call :
          C ≠ AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.source) ∨
              (⟨0⟩ : UInt256) = ⟨0⟩ ∨
              (⟨0⟩ : UInt256).toNat + storageSum eS1.accountMap C
                ≤ balanceOf eS1.accountMap C := Or.inr (Or.inl rfl)
      have hAtCFrame_f : ΞInvariantAtCFrame C f :=
        ΞInvariantAtCFrame_mono C (f + 1) f (Nat.le_succ _) hAtCFrame
      have hFrame_f : ΞInvariantFrameAtC C f :=
        ΞInvariantFrameAtC_mono C (f + 1) f (Nat.le_succ _) hFrame
      have hBundle :=
        call_invariant_preserved C f cost₂ μ₀ (.ofNat eS1.executionEnv.source)
          (.ofNat eS1.executionEnv.codeOwner) μ₁ ⟨0⟩ eS1.executionEnv.weiValue
          μ₃ μ₄ μ₅ μ₆ eS1.executionEnv.perm eS1 state' x
          hWFes1 hNCes1 hAtCFrame_f hFrame_f h_vb_call h_fs_call h_slack_call hInves1 hCallRes
      obtain ⟨hInvres, hWFres, hCOres, hNCres⟩ := hBundle
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [accountMap_replaceStackAndIncrPC]; exact hInvres
      · simp only [accountMap_replaceStackAndIncrPC]; exact hWFres
      · simp only [executionEnv_replaceStackAndIncrPC]; rw [hCOres]; exact hCO
      · simp only [createdAccounts_replaceStackAndIncrPC]; exact hNCres

/-- CALL invariant arm: `StorageSumLeBalance` is preserved through the CALL step
at non-`C` codeOwner. The slack hypothesis is satisfied by
`Or.inl hCO` since `src = codeOwner ≠ C`. Body mirrors
`step_CALL_arm` exactly. -/
private theorem step_CALL_arm_invariant
    (C : AccountAddress) (f : ℕ) (cost₂ : ℕ) (arg : Option (UInt256 × Nat))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCO : C ≠ evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C (f + 1))
    (hFrame : ΞInvariantFrameAtC C (f + 1))
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hStep : EVM.step (f + 1) cost₂ (some (.CALL, arg)) evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C ≠ sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  -- Unfold the CALL arm body, mirroring `step_CALL_arm`.
  simp only [EVM.step, Operation.CALL, bind, Except.bind, pure, Except.pure] at hStep
  set eS1 : EVM.State := { evmState with execLength := evmState.execLength + 1 } with heS1_def
  split at hStep
  · exact absurd hStep (by simp)
  · rename_i p hpop7
    obtain ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩ := p
    split at hStep
    · exact absurd hStep (by simp)
    · rename_i p_call hCallRes
      obtain ⟨x, state'⟩ := p_call
      injection hStep with hEq
      rw [← hEq]
      have hWFes1 : StateWF eS1.accountMap := hWF
      have hCOes1 : C ≠ eS1.executionEnv.codeOwner := hCO
      have hNCes1 : ∀ a ∈ eS1.createdAccounts, a ≠ C := hNC
      have hInves1 : StorageSumLeBalance eS1.accountMap C := hInv
      -- Round-trip: AccountAddress.ofUInt256 (.ofNat codeOwner) = codeOwner.
      have hRoundtrip :
          AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner)
            = eS1.executionEnv.codeOwner := by
        show Fin.ofNat _ (((Fin.ofNat UInt256.size
                eS1.executionEnv.codeOwner.val).val) % AccountAddress.size)
             = eS1.executionEnv.codeOwner
        have hAddrLtUSize : AccountAddress.size ≤ UInt256.size := by
          show AccountAddress.size ≤ UInt256.size
          decide
        have hCoLtAddr : eS1.executionEnv.codeOwner.val < AccountAddress.size :=
          eS1.executionEnv.codeOwner.isLt
        have hCoLtU : eS1.executionEnv.codeOwner.val < UInt256.size :=
          Nat.lt_of_lt_of_le hCoLtAddr hAddrLtUSize
        have h1 : (Fin.ofNat UInt256.size eS1.executionEnv.codeOwner.val).val
                  = eS1.executionEnv.codeOwner.val := by
          show eS1.executionEnv.codeOwner.val % UInt256.size
                = eS1.executionEnv.codeOwner.val
          exact Nat.mod_eq_of_lt hCoLtU
        rw [h1]
        show Fin.ofNat _ (eS1.executionEnv.codeOwner.val % AccountAddress.size)
             = eS1.executionEnv.codeOwner
        rw [Nat.mod_eq_of_lt hCoLtAddr]
        show Fin.ofNat _ eS1.executionEnv.codeOwner.val = eS1.executionEnv.codeOwner
        apply Fin.ext
        show eS1.executionEnv.codeOwner.val % AccountAddress.size
             = eS1.executionEnv.codeOwner.val
        exact Nat.mod_eq_of_lt hCoLtAddr
      -- Slack via Or.inl (C ≠ src).
      have h_slack_call :
          C ≠ AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner) ∨
              μ₂ = ⟨0⟩ ∨
              μ₂.toNat + storageSum eS1.accountMap C ≤ balanceOf eS1.accountMap C := by
        left; rw [hRoundtrip]; exact hCOes1
      set Iₐ : AccountAddress := eS1.executionEnv.codeOwner
      by_cases hGate :
          μ₂ ≤ (eS1.accountMap.find? Iₐ |>.option (⟨0⟩ : UInt256) (·.balance))
            ∧ eS1.executionEnv.depth < 1024
      · have hμle := hGate.1
        have h_fs_call :
            μ₂ = ⟨0⟩ ∨ ∃ acc,
              (eS1.accountMap).find? (AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner))
                = some acc ∧ μ₂.toNat ≤ acc.balance.toNat := by
          cases hFo : eS1.accountMap.find? Iₐ with
          | none =>
            rw [hFo] at hμle
            have hNle : μ₂.toNat ≤ (⟨0⟩ : UInt256).toNat := by
              show μ₂.val.val ≤ (⟨0⟩ : UInt256).val.val
              exact hμle
            have hμ0N : μ₂.toNat = 0 := Nat.le_zero.mp hNle
            left
            show μ₂ = ⟨⟨0, by decide⟩⟩
            cases μ₂ with
            | mk v =>
              cases v with
              | mk x hx =>
                simp only [UInt256.toNat] at hμ0N
                subst hμ0N
                rfl
          | some acc_Ia =>
            right
            have hFo' :
                eS1.accountMap.find? (AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner))
                  = some acc_Ia := by
              rw [hRoundtrip]; exact hFo
            refine ⟨acc_Ia, hFo', ?_⟩
            rw [hFo] at hμle
            show μ₂.val.val ≤ acc_Ia.balance.val.val
            exact hμle
        have h_vb_call :
            ∀ acc, (eS1.accountMap).find? (AccountAddress.ofUInt256 μ₁) = some acc →
              acc.balance.toNat + μ₂.toNat < UInt256.size := by
          intro acc h_find_r
          by_cases hrs : AccountAddress.ofUInt256 μ₁ = Iₐ
          · have h_find_Ia : eS1.accountMap.find? Iₐ = some acc := by
              rw [← hrs]; exact h_find_r
            have hμle' : μ₂.toNat ≤ acc.balance.toNat := by
              rw [h_find_Ia] at hμle
              show μ₂.val.val ≤ acc.balance.val.val
              exact hμle
            have hBalLe : acc.balance.toNat ≤ totalETH eS1.accountMap :=
              balance_toNat_le_totalETH eS1.accountMap Iₐ acc h_find_Ia
            have hDbl : 2 * totalETH eS1.accountMap < UInt256.size :=
              hWFes1.boundedTotalDouble
            calc acc.balance.toNat + μ₂.toNat
                ≤ acc.balance.toNat + acc.balance.toNat := by omega
              _ = 2 * acc.balance.toNat := by ring
              _ ≤ 2 * totalETH eS1.accountMap := by omega
              _ < UInt256.size := hDbl
          · cases hFo : eS1.accountMap.find? Iₐ with
            | none =>
              rw [hFo] at hμle
              have : μ₂.toNat ≤ (⟨0⟩ : UInt256).toNat := by
                show μ₂.val.val ≤ (⟨0⟩ : UInt256).val.val
                exact hμle
              have hμ0 : μ₂.toNat = 0 := Nat.le_zero.mp this
              rw [hμ0, Nat.add_zero]
              exact no_wrap_one eS1.accountMap hWFes1 (AccountAddress.ofUInt256 μ₁) acc h_find_r
            | some σ_s =>
              rw [hFo] at hμle
              have hμle' : μ₂.toNat ≤ σ_s.balance.toNat := by
                show μ₂.val.val ≤ σ_s.balance.val.val
                exact hμle
              have hPair :=
                no_wrap_pair eS1.accountMap hWFes1 (AccountAddress.ofUInt256 μ₁) Iₐ
                  acc σ_s h_find_r hFo hrs
              omega
        have hAtCFrame_f : ΞInvariantAtCFrame C f :=
          ΞInvariantAtCFrame_mono C (f + 1) f (Nat.le_succ _) hAtCFrame
        have hFrame_f : ΞInvariantFrameAtC C f :=
          ΞInvariantFrameAtC_mono C (f + 1) f (Nat.le_succ _) hFrame
        have hBundle :=
          call_invariant_preserved C f cost₂ μ₀ (.ofNat eS1.executionEnv.codeOwner)
            μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ eS1.executionEnv.perm eS1 state' x
            hWFes1 hNCes1 hAtCFrame_f hFrame_f h_vb_call h_fs_call h_slack_call hInves1 hCallRes
        obtain ⟨hInvres, hWFres, hCOres, hNCres⟩ := hBundle
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [accountMap_replaceStackAndIncrPC]; exact hInvres
        · simp only [accountMap_replaceStackAndIncrPC]; exact hWFres
        · simp only [executionEnv_replaceStackAndIncrPC]; rw [hCOres]; exact hCO
        · simp only [createdAccounts_replaceStackAndIncrPC]; exact hNCres
      · -- Gate failed: call returns with accountMap = eS1.accountMap.
        unfold EVM.call at hCallRes
        simp only [bind, Except.bind, pure, Except.pure] at hCallRes
        cases hf : f with
        | zero =>
          rw [hf] at hCallRes
          exact absurd hCallRes (by simp)
        | succ f' =>
          rw [hf] at hCallRes
          simp only at hCallRes
          rw [if_neg hGate] at hCallRes
          simp only [Except.ok.injEq, Prod.mk.injEq] at hCallRes
          obtain ⟨_hxEq, hStateEq⟩ := hCallRes
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [accountMap_replaceStackAndIncrPC, ← hStateEq]
            exact hInves1
          · simp only [accountMap_replaceStackAndIncrPC, ← hStateEq]
            exact hWFes1
          · simp only [executionEnv_replaceStackAndIncrPC, ← hStateEq]
            exact hCOes1
          · simp only [createdAccounts_replaceStackAndIncrPC, ← hStateEq]
            exact hNCes1

/-- STATICCALL invariant arm: same structure as DELEGATECALL but with
`v = 0`, `permission = false`, and `src = codeOwner`. -/
private theorem step_STATICCALL_arm_invariant
    (C : AccountAddress) (f : ℕ) (cost₂ : ℕ) (arg : Option (UInt256 × Nat))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCO : C ≠ evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C (f + 1))
    (hFrame : ΞInvariantFrameAtC C (f + 1))
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hStep : EVM.step (f + 1) cost₂ (some (.STATICCALL, arg)) evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C ≠ sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  simp only [EVM.step, Operation.STATICCALL, bind, Except.bind, pure, Except.pure] at hStep
  set eS1 : EVM.State := { evmState with execLength := evmState.execLength + 1 } with heS1_def
  split at hStep
  · exact absurd hStep (by simp)
  · rename_i p hpop6
    obtain ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩ := p
    split at hStep
    · exact absurd hStep (by simp)
    · rename_i p_call hCallRes
      obtain ⟨x, state'⟩ := p_call
      injection hStep with hEq
      rw [← hEq]
      have hWFes1 : StateWF eS1.accountMap := hWF
      have hCOes1 : C ≠ eS1.executionEnv.codeOwner := hCO
      have hNCes1 : ∀ a ∈ eS1.createdAccounts, a ≠ C := hNC
      have hInves1 : StorageSumLeBalance eS1.accountMap C := hInv
      have h_vb_call :
          ∀ acc, (eS1.accountMap).find? (AccountAddress.ofUInt256 μ₁) = some acc →
            acc.balance.toNat + (⟨0⟩ : UInt256).toNat < UInt256.size := by
        intro acc _
        show acc.balance.toNat + 0 < UInt256.size
        rw [Nat.add_zero]
        exact acc.balance.val.isLt
      have h_fs_call :
          (⟨0⟩ : UInt256) = ⟨0⟩ ∨ ∃ acc, (eS1.accountMap).find?
                        (AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner)) = some acc ∧
                  (⟨0⟩ : UInt256).toNat ≤ acc.balance.toNat := Or.inl rfl
      have h_slack_call :
          C ≠ AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner) ∨
              (⟨0⟩ : UInt256) = ⟨0⟩ ∨
              (⟨0⟩ : UInt256).toNat + storageSum eS1.accountMap C
                ≤ balanceOf eS1.accountMap C := Or.inr (Or.inl rfl)
      have hAtCFrame_f : ΞInvariantAtCFrame C f :=
        ΞInvariantAtCFrame_mono C (f + 1) f (Nat.le_succ _) hAtCFrame
      have hFrame_f : ΞInvariantFrameAtC C f :=
        ΞInvariantFrameAtC_mono C (f + 1) f (Nat.le_succ _) hFrame
      have hBundle :=
        call_invariant_preserved C f cost₂ μ₀ (.ofNat eS1.executionEnv.codeOwner)
          μ₁ μ₁ ⟨0⟩ ⟨0⟩ μ₃ μ₄ μ₅ μ₆ false eS1 state' x
          hWFes1 hNCes1 hAtCFrame_f hFrame_f h_vb_call h_fs_call h_slack_call hInves1 hCallRes
      obtain ⟨hInvres, hWFres, hCOres, hNCres⟩ := hBundle
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [accountMap_replaceStackAndIncrPC]; exact hInvres
      · simp only [accountMap_replaceStackAndIncrPC]; exact hWFres
      · simp only [executionEnv_replaceStackAndIncrPC]; rw [hCOres]; exact hCO
      · simp only [createdAccounts_replaceStackAndIncrPC]; exact hNCres

/-- CALLCODE invariant arm: same body shape as CALL, but `src = rcp =
codeOwner` (self-call). The slack discharge is `Or.inl hCO` after
`hRoundtrip`. -/
private theorem step_CALLCODE_arm_invariant
    (C : AccountAddress) (f : ℕ) (cost₂ : ℕ) (arg : Option (UInt256 × Nat))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCO : C ≠ evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C (f + 1))
    (hFrame : ΞInvariantFrameAtC C (f + 1))
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hStep : EVM.step (f + 1) cost₂ (some (.CALLCODE, arg)) evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C ≠ sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  simp only [EVM.step, Operation.CALLCODE, bind, Except.bind, pure, Except.pure] at hStep
  set eS1 : EVM.State := { evmState with execLength := evmState.execLength + 1 } with heS1_def
  split at hStep
  · exact absurd hStep (by simp)
  · rename_i p hpop7
    obtain ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩ := p
    split at hStep
    · exact absurd hStep (by simp)
    · rename_i p_call hCallRes
      obtain ⟨x, state'⟩ := p_call
      injection hStep with hEq
      rw [← hEq]
      have hWFes1 : StateWF eS1.accountMap := hWF
      have hCOes1 : C ≠ eS1.executionEnv.codeOwner := hCO
      have hNCes1 : ∀ a ∈ eS1.createdAccounts, a ≠ C := hNC
      have hInves1 : StorageSumLeBalance eS1.accountMap C := hInv
      have hRoundtrip :
          AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner)
            = eS1.executionEnv.codeOwner := by
        show Fin.ofNat _ (((Fin.ofNat UInt256.size
                eS1.executionEnv.codeOwner.val).val) % AccountAddress.size)
             = eS1.executionEnv.codeOwner
        have hAddrLtUSize : AccountAddress.size ≤ UInt256.size := by
          show AccountAddress.size ≤ UInt256.size
          decide
        have hCoLtAddr : eS1.executionEnv.codeOwner.val < AccountAddress.size :=
          eS1.executionEnv.codeOwner.isLt
        have hCoLtU : eS1.executionEnv.codeOwner.val < UInt256.size :=
          Nat.lt_of_lt_of_le hCoLtAddr hAddrLtUSize
        have h1 : (Fin.ofNat UInt256.size eS1.executionEnv.codeOwner.val).val
                  = eS1.executionEnv.codeOwner.val := by
          show eS1.executionEnv.codeOwner.val % UInt256.size
                = eS1.executionEnv.codeOwner.val
          exact Nat.mod_eq_of_lt hCoLtU
        rw [h1]
        show Fin.ofNat _ (eS1.executionEnv.codeOwner.val % AccountAddress.size)
             = eS1.executionEnv.codeOwner
        rw [Nat.mod_eq_of_lt hCoLtAddr]
        show Fin.ofNat _ eS1.executionEnv.codeOwner.val = eS1.executionEnv.codeOwner
        apply Fin.ext
        show eS1.executionEnv.codeOwner.val % AccountAddress.size
             = eS1.executionEnv.codeOwner.val
        exact Nat.mod_eq_of_lt hCoLtAddr
      have h_slack_call :
          C ≠ AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner) ∨
              μ₂ = ⟨0⟩ ∨
              μ₂.toNat + storageSum eS1.accountMap C ≤ balanceOf eS1.accountMap C := by
        left; rw [hRoundtrip]; exact hCOes1
      set Iₐ : AccountAddress := eS1.executionEnv.codeOwner
      by_cases hGate :
          μ₂ ≤ (eS1.accountMap.find? Iₐ |>.option (⟨0⟩ : UInt256) (·.balance))
            ∧ eS1.executionEnv.depth < 1024
      · have hμle := hGate.1
        have h_fs_call :
            μ₂ = ⟨0⟩ ∨ ∃ acc,
              (eS1.accountMap).find? (AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner))
                = some acc ∧ μ₂.toNat ≤ acc.balance.toNat := by
          cases hFo : eS1.accountMap.find? Iₐ with
          | none =>
            rw [hFo] at hμle
            have hNle : μ₂.toNat ≤ (⟨0⟩ : UInt256).toNat := by
              show μ₂.val.val ≤ (⟨0⟩ : UInt256).val.val
              exact hμle
            have hμ0N : μ₂.toNat = 0 := Nat.le_zero.mp hNle
            left
            show μ₂ = ⟨⟨0, by decide⟩⟩
            cases μ₂ with
            | mk v =>
              cases v with
              | mk x hx =>
                simp only [UInt256.toNat] at hμ0N
                subst hμ0N
                rfl
          | some acc_Ia =>
            right
            have hFo' :
                eS1.accountMap.find? (AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner))
                  = some acc_Ia := by
              rw [hRoundtrip]; exact hFo
            refine ⟨acc_Ia, hFo', ?_⟩
            rw [hFo] at hμle
            show μ₂.val.val ≤ acc_Ia.balance.val.val
            exact hμle
        have h_vb_call :
            ∀ acc, (eS1.accountMap).find? (AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner))
                = some acc →
              acc.balance.toNat + μ₂.toNat < UInt256.size := by
          intro acc h_find_r
          rw [hRoundtrip] at h_find_r
          have hμle' : μ₂.toNat ≤ acc.balance.toNat := by
            rw [h_find_r] at hμle
            show μ₂.val.val ≤ acc.balance.val.val
            exact hμle
          have hBalLe : acc.balance.toNat ≤ totalETH eS1.accountMap :=
            balance_toNat_le_totalETH eS1.accountMap Iₐ acc h_find_r
          have hDbl : 2 * totalETH eS1.accountMap < UInt256.size :=
            hWFes1.boundedTotalDouble
          calc acc.balance.toNat + μ₂.toNat
              ≤ acc.balance.toNat + acc.balance.toNat := by omega
            _ = 2 * acc.balance.toNat := by ring
            _ ≤ 2 * totalETH eS1.accountMap := by omega
            _ < UInt256.size := hDbl
        have hAtCFrame_f : ΞInvariantAtCFrame C f :=
          ΞInvariantAtCFrame_mono C (f + 1) f (Nat.le_succ _) hAtCFrame
        have hFrame_f : ΞInvariantFrameAtC C f :=
          ΞInvariantFrameAtC_mono C (f + 1) f (Nat.le_succ _) hFrame
        have hBundle :=
          call_invariant_preserved C f cost₂ μ₀ (.ofNat eS1.executionEnv.codeOwner)
            (.ofNat eS1.executionEnv.codeOwner) μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
            eS1.executionEnv.perm eS1 state' x
            hWFes1 hNCes1 hAtCFrame_f hFrame_f h_vb_call h_fs_call h_slack_call hInves1 hCallRes
        obtain ⟨hInvres, hWFres, hCOres, hNCres⟩ := hBundle
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [accountMap_replaceStackAndIncrPC]; exact hInvres
        · simp only [accountMap_replaceStackAndIncrPC]; exact hWFres
        · simp only [executionEnv_replaceStackAndIncrPC]; rw [hCOres]; exact hCO
        · simp only [createdAccounts_replaceStackAndIncrPC]; exact hNCres
      · -- Gate failed: state unchanged.
        unfold EVM.call at hCallRes
        simp only [bind, Except.bind, pure, Except.pure] at hCallRes
        cases hf : f with
        | zero =>
          rw [hf] at hCallRes
          exact absurd hCallRes (by simp)
        | succ f' =>
          rw [hf] at hCallRes
          simp only at hCallRes
          rw [if_neg hGate] at hCallRes
          simp only [Except.ok.injEq, Prod.mk.injEq] at hCallRes
          obtain ⟨_hxEq, hStateEq⟩ := hCallRes
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [accountMap_replaceStackAndIncrPC, ← hStateEq]
            exact hInves1
          · simp only [accountMap_replaceStackAndIncrPC, ← hStateEq]
            exact hWFes1
          · simp only [executionEnv_replaceStackAndIncrPC, ← hStateEq]
            exact hCOes1
          · simp only [createdAccounts_replaceStackAndIncrPC, ← hStateEq]
            exact hNCes1

/-- CREATE invariant arm: `StorageSumLeBalance` is preserved through the CREATE
step at non-`C` codeOwner. Mirrors `step_CREATE_arm` exactly, with the
Λ dispatch routed through `Λ_invariant_preserved_bdd`. The `σStar`
nonce-bump preserves `StorageSumLeBalance σ C` because `Iₐ ≠ C`. -/
private theorem step_CREATE_arm_invariant
    (C : AccountAddress) (f : ℕ) (cost₂ : ℕ) (arg : Option (UInt256 × Nat))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCO : C ≠ evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (_hAtCFrame : ΞInvariantAtCFrame C (f + 1))
    (hFrame : ΞInvariantFrameAtC C (f + 1))
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hStep : EVM.step (f + 1) cost₂ (some (.CREATE, arg)) evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C ≠ sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  simp only [EVM.step, Operation.CREATE, bind, Except.bind, pure, Except.pure] at hStep
  set eS1 : EVM.State := { evmState with execLength := evmState.execLength + 1 } with heS1_def
  set eS2 : EVM.State :=
    { eS1 with gasAvailable := eS1.gasAvailable - UInt256.ofNat cost₂ } with heS2_def
  rcases hpop3 : eS2.stack.pop3 with _ | ⟨stack, μ₀, μ₁, μ₂⟩
  · rw [hpop3] at hStep
    exact absurd hStep (by simp)
  · rw [hpop3] at hStep
    set i : ByteArray := eS2.memory.readWithPadding μ₁.toNat μ₂.toNat with hi_def
    set Iₐ : AccountAddress := eS2.executionEnv.codeOwner with hIₐ_def
    set Iₒ : AccountAddress := eS2.executionEnv.sender with hIₒ_def
    set Iₑ : ℕ := eS2.executionEnv.depth with hIₑ_def
    set σ : AccountMap .EVM := eS2.accountMap with hσ_def
    set σ_Iₐ : Account .EVM := σ.find? Iₐ |>.getD default with hσIₐ_def
    set σStar : AccountMap .EVM :=
      σ.insert Iₐ { σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩ } with hσStar_def
    have hAM2 : eS2.accountMap = evmState.accountMap := by simp [heS2_def, heS1_def]
    have hEE2 : eS2.executionEnv = evmState.executionEnv := by simp [heS2_def, heS1_def]
    have hCA2 : eS2.createdAccounts = evmState.createdAccounts := by simp [heS2_def, heS1_def]
    have hWF2 : StateWF eS2.accountMap := by rw [hAM2]; exact hWF
    have hCO2 : C ≠ eS2.executionEnv.codeOwner := by rw [hEE2]; exact hCO
    have hNC2 : ∀ a ∈ eS2.createdAccounts, a ≠ C := by rw [hCA2]; exact hNC
    have hInv2 : StorageSumLeBalance eS2.accountMap C := by rw [hAM2]; exact hInv
    by_cases hNonceOv : σ_Iₐ.nonce.toNat ≥ 2^64-1
    · simp only [hNonceOv, if_true] at hStep
      split at hStep
      · exact absurd hStep (by simp)
      · injection hStep with hEq
        rw [← hEq]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [accountMap_replaceStackAndIncrPC]; exact hInv
        · simp only [accountMap_replaceStackAndIncrPC]; exact hWF
        · simp only [executionEnv_replaceStackAndIncrPC]; exact hCO
        · simp only [createdAccounts_replaceStackAndIncrPC]; exact hNC
    · simp only [hNonceOv, if_false] at hStep
      by_cases hPreCheck :
          μ₀ ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 ∧ i.size ≤ 49152
      · rw [if_pos hPreCheck] at hStep
        split at hStep
        · rename_i a cA σ' g' A' z o hΛ
          split at hStep
          · exact absurd hStep (by simp)
          · injection hStep with hEq
            rw [← hEq]
            simp only [accountMap_replaceStackAndIncrPC,
                       executionEnv_replaceStackAndIncrPC,
                       createdAccounts_replaceStackAndIncrPC]
            have hIₐC : Iₐ ≠ C := fun h => hCO2 h.symm
            have hσStarBalC : balanceOf σStar C = balanceOf σ C := by
              show balanceOf (σ.insert Iₐ _) C = balanceOf σ C
              apply balanceOf_of_find?_eq
              exact find?_insert_ne _ _ _ _ hIₐC
            have hσStarStgC : storageSum σStar C = storageSum σ C := by
              show storageSum (σ.insert Iₐ _) C = storageSum σ C
              apply storageSum_unchanged_at_other_account
              exact hIₐC
            have hInvσStar : StorageSumLeBalance σStar C := by
              unfold StorageSumLeBalance
              rw [hσStarStgC, hσStarBalC]
              exact hInv2
            have hWFσStar : StateWF σStar := by
              show StateWF (σ.insert Iₐ _)
              by_cases hFindIₐ : ∃ acc, σ.find? Iₐ = some acc
              · obtain ⟨acc, hFind⟩ := hFindIₐ
                have hσIₐ_eq : σ_Iₐ = acc := by
                  show (σ.find? Iₐ).getD default = acc
                  rw [hFind]; rfl
                refine StateWF_insert_eq_bal σ Iₐ _ acc hFind ?_ hWF2
                show (σ_Iₐ.balance : UInt256) = acc.balance
                rw [hσIₐ_eq]
              · push_neg at hFindIₐ
                have hFindNone : σ.find? Iₐ = none := by
                  match hF : σ.find? Iₐ with
                  | none => rfl
                  | some acc => exact absurd hF (hFindIₐ acc)
                have hσIₐ_def_eq : σ_Iₐ = default := by
                  show (σ.find? Iₐ).getD default = default
                  rw [hFindNone]; rfl
                refine ⟨?_⟩
                have hEq2 := totalETH_insert_of_not_mem σ Iₐ
                  { σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩ } hFindNone
                have h0 : ({ σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩ } : Account .EVM).balance.toNat = 0 := by
                  rw [hσIₐ_def_eq]; rfl
                rw [h0, Nat.add_zero] at hEq2
                rw [hEq2]; exact hWF2.boundedTotal
            have h_funds_at_σStar :
                ∀ acc, σStar.find? Iₐ = some acc → μ₀.toNat ≤ acc.balance.toNat := by
              intro acc hFind
              have hFindEq : σStar.find? Iₐ =
                  some { σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩ } := find?_insert_self _ _ _
              rw [hFindEq] at hFind
              injection hFind with hAcc
              subst hAcc
              have hμ := hPreCheck.1
              have hU : (σ.find? Iₐ |>.option (⟨0⟩ : UInt256) (·.balance)) = σ_Iₐ.balance := by
                show (σ.find? Iₐ |>.option (⟨0⟩ : UInt256) (·.balance))
                       = ((σ.find? Iₐ).getD default).balance
                cases hF : σ.find? Iₐ with
                | none => rfl
                | some acc2 => rfl
              rw [hU] at hμ
              exact hμ
            have hFrame_f : ΞInvariantFrameAtC C f :=
              ΞInvariantFrameAtC_mono C (f + 1) f (Nat.le_succ _) hFrame
            have hΛFrame :=
              Λ_invariant_preserved_bdd f
                eS2.executionEnv.blobVersionedHashes
                eS2.createdAccounts
                eS2.genesisBlockHeader
                eS2.blocks
                σStar
                eS2.σ₀
                eS2.toState.substate
                Iₐ
                Iₒ
                (.ofNat <| L eS2.gasAvailable.toNat)
                (.ofNat eS2.executionEnv.gasPrice)
                μ₀ i
                (.ofNat <| Iₑ + 1)
                none
                eS2.executionEnv.header
                eS2.executionEnv.perm
                C hWFσStar hCO2
                (by rw [hCA2]; exact hNC)
                h_funds_at_σStar hInvσStar hFrame_f
            rw [hΛ] at hΛFrame
            obtain ⟨_ha_ne_C, hInvσ', hWFσ', hNCcA⟩ := hΛFrame
            refine ⟨?_, hWFσ', ?_, ?_⟩
            · show StorageSumLeBalance σ' C
              exact hInvσ'
            · show C ≠ ({eS2 with accountMap := σ', substate := A', createdAccounts := cA }).executionEnv.codeOwner
              rw [hEE2] at hCO2
              exact hCO
            · exact hNCcA
        · rename_i hΛ
          split at hStep
          · exact absurd hStep (by simp)
          · injection hStep with hEq
            rw [← hEq]
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [accountMap_replaceStackAndIncrPC]; exact hInv
            · simp only [accountMap_replaceStackAndIncrPC]; exact hWF
            · simp only [executionEnv_replaceStackAndIncrPC]; exact hCO
            · simp only [createdAccounts_replaceStackAndIncrPC]; exact hNC
      · rw [if_neg hPreCheck] at hStep
        split at hStep
        · exact absurd hStep (by simp)
        · injection hStep with hEq
          rw [← hEq]
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [accountMap_replaceStackAndIncrPC]; exact hInv
          · simp only [accountMap_replaceStackAndIncrPC]; exact hWF
          · simp only [executionEnv_replaceStackAndIncrPC]; exact hCO
          · simp only [createdAccounts_replaceStackAndIncrPC]; exact hNC

/-- CREATE2 invariant arm: structurally identical to CREATE with pop4
+ ζ := some (toByteArray μ₃). -/
private theorem step_CREATE2_arm_invariant
    (C : AccountAddress) (f : ℕ) (cost₂ : ℕ) (arg : Option (UInt256 × Nat))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCO : C ≠ evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (_hAtCFrame : ΞInvariantAtCFrame C (f + 1))
    (hFrame : ΞInvariantFrameAtC C (f + 1))
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hStep : EVM.step (f + 1) cost₂ (some (.CREATE2, arg)) evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C ≠ sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  simp only [EVM.step, Operation.CREATE2, bind, Except.bind, pure, Except.pure] at hStep
  set eS1 : EVM.State := { evmState with execLength := evmState.execLength + 1 } with heS1_def
  set eS2 : EVM.State :=
    { eS1 with gasAvailable := eS1.gasAvailable - UInt256.ofNat cost₂ } with heS2_def
  rcases hpop4 : eS2.stack.pop4 with _ | ⟨stack, μ₀, μ₁, μ₂, μ₃⟩
  · rw [hpop4] at hStep
    exact absurd hStep (by simp)
  · rw [hpop4] at hStep
    set i : ByteArray := eS2.memory.readWithPadding μ₁.toNat μ₂.toNat with hi_def
    set Iₐ : AccountAddress := eS2.executionEnv.codeOwner with hIₐ_def
    set Iₑ : ℕ := eS2.executionEnv.depth with hIₑ_def
    set σ : AccountMap .EVM := eS2.accountMap with hσ_def
    set σ_Iₐ : Account .EVM := σ.find? Iₐ |>.getD default with hσIₐ_def
    have hAM2 : eS2.accountMap = evmState.accountMap := by simp [heS2_def, heS1_def]
    have hEE2 : eS2.executionEnv = evmState.executionEnv := by simp [heS2_def, heS1_def]
    have hCA2 : eS2.createdAccounts = evmState.createdAccounts := by simp [heS2_def, heS1_def]
    have hWF2 : StateWF eS2.accountMap := by rw [hAM2]; exact hWF
    have hCO2 : C ≠ eS2.executionEnv.codeOwner := by rw [hEE2]; exact hCO
    have hNC2 : ∀ a ∈ eS2.createdAccounts, a ≠ C := by rw [hCA2]; exact hNC
    have hInv2 : StorageSumLeBalance eS2.accountMap C := by rw [hAM2]; exact hInv
    by_cases hNonceOv : σ_Iₐ.nonce.toNat ≥ 2^64-1
    · simp only [hNonceOv, if_true] at hStep
      split at hStep
      · exact absurd hStep (by simp)
      · injection hStep with hEq
        rw [← hEq]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [accountMap_replaceStackAndIncrPC]; exact hInv
        · simp only [accountMap_replaceStackAndIncrPC]; exact hWF
        · simp only [executionEnv_replaceStackAndIncrPC]; exact hCO
        · simp only [createdAccounts_replaceStackAndIncrPC]; exact hNC
    · simp only [hNonceOv, if_false] at hStep
      set σStar : AccountMap .EVM :=
        σ.insert Iₐ { σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩ } with hσStar_def
      by_cases hPreCheck :
          μ₀ ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 ∧ i.size ≤ 49152
      · rw [if_pos hPreCheck] at hStep
        split at hStep
        · rename_i a cA σ' g' A' z o hΛ
          split at hStep
          · exact absurd hStep (by simp)
          · injection hStep with hEq
            rw [← hEq]
            simp only [accountMap_replaceStackAndIncrPC,
                       executionEnv_replaceStackAndIncrPC,
                       createdAccounts_replaceStackAndIncrPC]
            have hIₐC : Iₐ ≠ C := fun h => hCO2 h.symm
            have hσStarBalC : balanceOf σStar C = balanceOf σ C := by
              show balanceOf (σ.insert Iₐ _) C = balanceOf σ C
              apply balanceOf_of_find?_eq
              exact find?_insert_ne _ _ _ _ hIₐC
            have hσStarStgC : storageSum σStar C = storageSum σ C := by
              show storageSum (σ.insert Iₐ _) C = storageSum σ C
              apply storageSum_unchanged_at_other_account
              exact hIₐC
            have hInvσStar : StorageSumLeBalance σStar C := by
              unfold StorageSumLeBalance
              rw [hσStarStgC, hσStarBalC]
              exact hInv2
            have hWFσStar : StateWF σStar := by
              show StateWF (σ.insert Iₐ _)
              by_cases hFindIₐ : ∃ acc, σ.find? Iₐ = some acc
              · obtain ⟨acc, hFind⟩ := hFindIₐ
                have hσIₐ_eq : σ_Iₐ = acc := by
                  show (σ.find? Iₐ).getD default = acc
                  rw [hFind]; rfl
                refine StateWF_insert_eq_bal σ Iₐ _ acc hFind ?_ hWF2
                show (σ_Iₐ.balance : UInt256) = acc.balance
                rw [hσIₐ_eq]
              · push_neg at hFindIₐ
                have hFindNone : σ.find? Iₐ = none := by
                  match hF : σ.find? Iₐ with
                  | none => rfl
                  | some acc => exact absurd hF (hFindIₐ acc)
                have hσIₐ_def_eq : σ_Iₐ = default := by
                  show (σ.find? Iₐ).getD default = default
                  rw [hFindNone]; rfl
                refine ⟨?_⟩
                have hEq2 := totalETH_insert_of_not_mem σ Iₐ
                  { σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩ } hFindNone
                have h0 : ({ σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩ } : Account .EVM).balance.toNat = 0 := by
                  rw [hσIₐ_def_eq]; rfl
                rw [h0, Nat.add_zero] at hEq2
                rw [hEq2]; exact hWF2.boundedTotal
            have h_funds_at_σStar :
                ∀ acc, σStar.find? Iₐ = some acc → μ₀.toNat ≤ acc.balance.toNat := by
              intro acc hFind
              have hFindEq : σStar.find? Iₐ =
                  some { σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩ } := find?_insert_self _ _ _
              rw [hFindEq] at hFind
              injection hFind with hAcc
              subst hAcc
              have hμ := hPreCheck.1
              have hU : (σ.find? Iₐ |>.option (⟨0⟩ : UInt256) (·.balance)) = σ_Iₐ.balance := by
                show (σ.find? Iₐ |>.option (⟨0⟩ : UInt256) (·.balance))
                       = ((σ.find? Iₐ).getD default).balance
                cases hF : σ.find? Iₐ with
                | none => rfl
                | some acc2 => rfl
              rw [hU] at hμ
              exact hμ
            have hFrame_f : ΞInvariantFrameAtC C f :=
              ΞInvariantFrameAtC_mono C (f + 1) f (Nat.le_succ _) hFrame
            have hΛFrame :=
              Λ_invariant_preserved_bdd f
                eS2.executionEnv.blobVersionedHashes
                eS2.createdAccounts
                eS2.genesisBlockHeader
                eS2.blocks
                σStar
                eS2.σ₀
                eS2.toState.substate
                Iₐ
                eS2.executionEnv.sender
                (.ofNat <| L eS2.gasAvailable.toNat)
                (.ofNat eS2.executionEnv.gasPrice)
                μ₀ i
                (.ofNat <| Iₑ + 1)
                (some (EvmYul.UInt256.toByteArray μ₃))
                eS2.executionEnv.header
                eS2.executionEnv.perm
                C hWFσStar hCO2
                (by rw [hCA2]; exact hNC)
                h_funds_at_σStar hInvσStar hFrame_f
            rw [hΛ] at hΛFrame
            obtain ⟨_ha_ne_C, hInvσ', hWFσ', hNCcA⟩ := hΛFrame
            refine ⟨?_, hWFσ', ?_, ?_⟩
            · exact hInvσ'
            · show C ≠ ({eS2 with accountMap := σ', substate := A', createdAccounts := cA }).executionEnv.codeOwner
              rw [hEE2] at hCO2
              exact hCO
            · exact hNCcA
        · rename_i hΛ
          split at hStep
          · exact absurd hStep (by simp)
          · injection hStep with hEq
            rw [← hEq]
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [accountMap_replaceStackAndIncrPC]; exact hInv
            · simp only [accountMap_replaceStackAndIncrPC]; exact hWF
            · simp only [executionEnv_replaceStackAndIncrPC]; exact hCO
            · simp only [createdAccounts_replaceStackAndIncrPC]; exact hNC
      · rw [if_neg hPreCheck] at hStep
        split at hStep
        · exact absurd hStep (by simp)
        · injection hStep with hEq
          rw [← hEq]
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [accountMap_replaceStackAndIncrPC]; exact hInv
          · simp only [accountMap_replaceStackAndIncrPC]; exact hWF
          · simp only [executionEnv_replaceStackAndIncrPC]; exact hCO
          · simp only [createdAccounts_replaceStackAndIncrPC]; exact hNC

/-- **Aggregator over the 6 system arms (invariant side).** Mirror of
`step_bundled_system_arm` for `StorageSumLeBalance`. Dispatches to the per-arm
invariant helpers based on `op`'s system-call/create classification. -/
private theorem step_bundled_system_arm_invariant
    (C : AccountAddress) (f : ℕ) (cost₂ : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCO : C ≠ evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C (f + 1))
    (hFrame : ΞInvariantFrameAtC C (f + 1))
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hSys : opIsSystemCallOrCreate op)
    (hStep : EVM.step (f + 1) cost₂ (some (op, arg)) evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C ≠ sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  rcases hSys with h1 | h2 | h3 | h4 | h5 | h6
  · subst h1; exact step_CREATE_arm_invariant     C f cost₂ arg evmState sstepState hWF hCO hNC hAtCFrame hFrame hInv hStep
  · subst h2; exact step_CREATE2_arm_invariant    C f cost₂ arg evmState sstepState hWF hCO hNC hAtCFrame hFrame hInv hStep
  · subst h3; exact step_CALL_arm_invariant       C f cost₂ arg evmState sstepState hWF hCO hNC hAtCFrame hFrame hInv hStep
  · subst h4; exact step_CALLCODE_arm_invariant   C f cost₂ arg evmState sstepState hWF hCO hNC hAtCFrame hFrame hInv hStep
  · subst h5; exact step_DELEGATECALL_arm_invariant C f cost₂ arg evmState sstepState hWF hCO hNC hAtCFrame hFrame hInv hStep
  · subst h6; exact step_STATICCALL_arm_invariant C f cost₂ arg evmState sstepState hWF hCO hNC hAtCFrame hFrame hInv hStep

/-- **Handled-case invariant helper.** Mirror of
`step_bundled_handled_case` for the invariant-side: when `op` is a
handled non-CALL/non-CREATE op, `StorageSumLeBalance` is preserved at non-C
codeOwner. SELFDESTRUCT is special: balance grows or is unchanged
at C (`selfdestruct_balanceOf_ne_Iₐ_ge`), and storage is unchanged
(`selfdestruct_storageSum_at_ne_Iₐ_eq`), so the invariant is
preserved. Other handled non-SD ops preserve the invariant directly via
`EvmYul_step_preserves_StorageSumLeBalance_at_non_C`. -/
private theorem step_bundled_handled_case_invariant
    (C : AccountAddress) (_f : ℕ) (cost₂ : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCO : C ≠ evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hHandled : handledByEvmYulStep op)
    (hStep : EvmYul.step op arg
              {evmState with
                execLength := evmState.execLength + 1,
                gasAvailable := evmState.gasAvailable - UInt256.ofNat cost₂}
              = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C ≠ sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  set s_pre : EVM.State :=
    {evmState with
      execLength := evmState.execLength + 1,
      gasAvailable := evmState.gasAvailable - UInt256.ofNat cost₂}
    with hs_pre_def
  have hAM : s_pre.accountMap = evmState.accountMap := rfl
  have hCOEq : s_pre.executionEnv = evmState.executionEnv := rfl
  have hCAEq : s_pre.createdAccounts = evmState.createdAccounts := rfl
  have hWF_pre : StateWF s_pre.accountMap := by rw [hAM]; exact hWF
  have hCO_pre : C ≠ s_pre.executionEnv.codeOwner := by rw [hCOEq]; exact hCO
  have hNC_pre : ∀ a ∈ s_pre.createdAccounts, a ≠ C := by rw [hCAEq]; exact hNC
  have hInv_pre : StorageSumLeBalance s_pre.accountMap C := by rw [hAM]; exact hInv
  by_cases hSD : op = .SELFDESTRUCT
  · subst hSD
    have hStep_none : EvmYul.step (.SELFDESTRUCT : Operation .EVM) .none s_pre = .ok sstepState := by
      have : EvmYul.step (.SELFDESTRUCT : Operation .EVM) arg s_pre
          = EvmYul.step (.SELFDESTRUCT : Operation .EVM) .none s_pre := by
        unfold EvmYul.step; rfl
      rw [← this]; exact hStep
    have hBalGE :=
      selfdestruct_balanceOf_ne_Iₐ_ge s_pre sstepState C hWF_pre hStep_none hCO_pre
    have hStgEq :=
      selfdestruct_storageSum_at_ne_Iₐ_eq s_pre sstepState C hStep_none hCO_pre
    have hWFresult := selfdestruct_preserves_StateWF s_pre sstepState hWF_pre hStep_none
    have hEnv := selfdestruct_preserves_executionEnv s_pre sstepState hStep_none
    have hCA := selfdestruct_preserves_createdAccounts s_pre sstepState hStep_none
    refine ⟨?_, hWFresult, ?_, ?_⟩
    · -- StorageSumLeBalance sstepState.accountMap C: storageSum unchanged, balance ≥.
      unfold StorageSumLeBalance at hInv_pre ⊢
      rw [hStgEq]
      exact Nat.le_trans hInv_pre hBalGE
    · rw [hEnv, hCOEq]; exact hCO
    · rw [hCA, hCAEq]; exact hNC
  · have hInvResult := EvmYul_step_preserves_StorageSumLeBalance_at_non_C op arg s_pre sstepState C
        hHandled hSD hStep hCO_pre hInv_pre
    have hWFresult := EvmYul_step_preserves_StateWF op arg s_pre sstepState hHandled hSD hStep hWF_pre
    have hEnvCA := EvmYul.step_preserves_eEnv_cA op arg s_pre sstepState hHandled hStep
    refine ⟨hInvResult, hWFresult, ?_, ?_⟩
    · rw [hEnvCA.1, hCOEq]; exact hCO
    · rw [hEnvCA.2, hCAEq]; exact hNC

/-- **Aggregator: step-level bundled invariant at non-`C` codeOwner.**
Mirror of `step_bundled_invariant_at_C` for `StorageSumLeBalance`. Routes
through `step_bundled_system_arm_invariant` for system-call/create
ops, and `step_bundled_handled_case_invariant` for the handled
non-CALL/non-CREATE fallthrough. -/
private theorem step_bundled_invariant_at_C_invariant_general
    (C : AccountAddress) (f' : ℕ) (cost₂ : ℕ)
    (instr : Option (Operation .EVM × Option (UInt256 × Nat)))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCO : C ≠ evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C f')
    (hFrame : ΞInvariantFrameAtC C f')
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hStep : EVM.step f' cost₂ instr evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C ≠ sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  match f' with
  | 0 =>
    simp only [EVM.step] at hStep
    exact absurd hStep (by simp)
  | f + 1 =>
    have hResolved : ∃ (op : Operation .EVM) (arg : Option (UInt256 × Nat)),
        EVM.step (f + 1) cost₂ (some (op, arg)) evmState = .ok sstepState := by
      match instr with
      | .some (op, arg) => exact ⟨op, arg, hStep⟩
      | .none =>
        unfold EVM.step at hStep
        simp only [bind, Except.bind, pure, Except.pure] at hStep
        cases hFetch : fetchInstr evmState.executionEnv evmState.pc with
        | error e => rw [hFetch] at hStep; exact absurd hStep (by simp)
        | ok pair =>
          obtain ⟨op, arg⟩ := pair
          rw [hFetch] at hStep
          simp only at hStep
          refine ⟨op, arg, ?_⟩
          show EVM.step (f + 1) cost₂ (some (op, arg)) evmState = .ok sstepState
          unfold EVM.step
          simp only [bind, Except.bind, pure, Except.pure]
          exact hStep
    obtain ⟨op, arg, hStep⟩ := hResolved
    rcases op_classification op with hSysCall | hHandled
    · exact step_bundled_system_arm_invariant C f cost₂ op arg evmState sstepState
        hWF hCO hNC hAtCFrame hFrame hInv hSysCall hStep
    · have hStep' :
          EvmYul.step op arg
            { evmState with
              execLength := evmState.execLength + 1,
              gasAvailable := evmState.gasAvailable - UInt256.ofNat cost₂ }
          = .ok sstepState := by
        unfold EVM.step at hStep
        simp only [bind, Except.bind, pure, Except.pure] at hStep
        obtain ⟨hne1, hne2, hne3, hne4, hne5, hne6⟩ := hHandled
        cases op with
        | StopArith _ => exact hStep
        | CompBit _ => exact hStep
        | Keccak _ => exact hStep
        | Env _ => exact hStep
        | Block _ => exact hStep
        | StackMemFlow _ => exact hStep
        | Push _ => exact hStep
        | Dup _ => exact hStep
        | Exchange _ => exact hStep
        | Log _ => exact hStep
        | System o =>
          cases o with
          | CREATE => exact absurd rfl hne1
          | CALL => exact absurd rfl hne3
          | CALLCODE => exact absurd rfl hne4
          | RETURN => exact hStep
          | DELEGATECALL => exact absurd rfl hne5
          | CREATE2 => exact absurd rfl hne2
          | STATICCALL => exact absurd rfl hne6
          | REVERT => exact hStep
          | INVALID => exact hStep
          | SELFDESTRUCT => exact hStep
      exact step_bundled_handled_case_invariant C f cost₂ op arg evmState sstepState
        hWF hCO hNC hInv hHandled hStep'

/-- **X-induction invariant for `StorageSumLeBalance`.** Mirror of `X_inv`. -/
private def X_inv_invariant (C : AccountAddress) (f : ℕ) (validJumps : Array UInt256)
    (evmState : EVM.State) : Prop :=
  StateWF evmState.accountMap →
  C ≠ evmState.executionEnv.codeOwner →
  (∀ a ∈ evmState.createdAccounts, a ≠ C) →
  ΞInvariantAtCFrame C f →
  ΞInvariantFrameAtC C f →
  StorageSumLeBalance evmState.accountMap C →
  match EVM.X f validJumps evmState with
  | .ok (.success s' _) =>
      StorageSumLeBalance s'.accountMap C ∧
      StateWF s'.accountMap ∧
      (∀ a ∈ s'.createdAccounts, a ≠ C)
  | _ => True

/-- Per-step invariant projections. -/
private theorem step_invariant_preserved_at_non_C
    (C : AccountAddress) (f' : ℕ) (cost₂ : ℕ)
    (instr : Option (Operation .EVM × Option (UInt256 × Nat)))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCO : C ≠ evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C f')
    (hFrame : ΞInvariantFrameAtC C f')
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hStep : EVM.step f' cost₂ instr evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C :=
  (step_bundled_invariant_at_C_invariant_general C f' cost₂ instr evmState sstepState
    hWF hCO hNC hAtCFrame hFrame hInv hStep).1

private theorem step_invariant_StateWF
    (C : AccountAddress) (f' : ℕ) (cost₂ : ℕ)
    (instr : Option (Operation .EVM × Option (UInt256 × Nat)))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCO : C ≠ evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C f')
    (hFrame : ΞInvariantFrameAtC C f')
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hStep : EVM.step f' cost₂ instr evmState = .ok sstepState) :
    StateWF sstepState.accountMap :=
  (step_bundled_invariant_at_C_invariant_general C f' cost₂ instr evmState sstepState
    hWF hCO hNC hAtCFrame hFrame hInv hStep).2.1

private theorem step_invariant_codeOwner
    (C : AccountAddress) (f' : ℕ) (cost₂ : ℕ)
    (instr : Option (Operation .EVM × Option (UInt256 × Nat)))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCO : C ≠ evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C f')
    (hFrame : ΞInvariantFrameAtC C f')
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hStep : EVM.step f' cost₂ instr evmState = .ok sstepState) :
    C ≠ sstepState.executionEnv.codeOwner :=
  (step_bundled_invariant_at_C_invariant_general C f' cost₂ instr evmState sstepState
    hWF hCO hNC hAtCFrame hFrame hInv hStep).2.2.1

private theorem step_invariant_createdAccounts
    (C : AccountAddress) (f' : ℕ) (cost₂ : ℕ)
    (instr : Option (Operation .EVM × Option (UInt256 × Nat)))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCO : C ≠ evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C f')
    (hFrame : ΞInvariantFrameAtC C f')
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hStep : EVM.step f' cost₂ instr evmState = .ok sstepState) :
    ∀ a ∈ sstepState.createdAccounts, a ≠ C :=
  (step_bundled_invariant_at_C_invariant_general C f' cost₂ instr evmState sstepState
    hWF hCO hNC hAtCFrame hFrame hInv hStep).2.2.2

/-- **Content-carrying `.succ` closure of `X_inv_invariant_holds`.**
Mirror of `X_inv_succ_content`. -/
private theorem X_inv_invariant_succ_content
    (C : AccountAddress) (f' : ℕ) (validJumps : Array UInt256)
    (evmState finalState : EVM.State) (_out : ByteArray)
    (_hWF : StateWF evmState.accountMap)
    (_hCO : C ≠ evmState.executionEnv.codeOwner)
    (_hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (_hAtCFrame : ΞInvariantAtCFrame C f')
    (hFrame : ΞInvariantFrameAtC C f')
    (_hInv : StorageSumLeBalance evmState.accountMap C)
    (_IH : ∀ evmState', X_inv_invariant C f' validJumps evmState')
    (hXres : EVM.X (f' + 1) validJumps evmState
              = .ok (.success finalState _out)) :
    StorageSumLeBalance finalState.accountMap C ∧
    StateWF finalState.accountMap ∧
    (∀ a ∈ finalState.createdAccounts, a ≠ C) := by
  simp only [EVM.X] at hXres
  split at hXres
  case h_1 _ _ =>
    exact absurd hXres (by simp)
  case h_2 _ evmStateZ cost₂ hZ =>
    have hZ_struct :
        evmStateZ.accountMap = evmState.accountMap ∧
        evmStateZ.executionEnv = evmState.executionEnv ∧
        evmStateZ.createdAccounts = evmState.createdAccounts := by
      simp only [bind, Except.bind, pure, Except.pure] at hZ
      by_cases hc1 : evmState.gasAvailable.toNat < memoryExpansionCost evmState ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1
      · rw [if_pos hc1] at hZ; exact Except.noConfusion hZ
      rw [if_neg hc1] at hZ
      set evmState' : EVM.State :=
        { evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1) } with hevmState'
      have h_accMap : evmState'.accountMap = evmState.accountMap := by rw [hevmState']
      have h_eEnv   : evmState'.executionEnv = evmState.executionEnv := by rw [hevmState']
      have h_cA     : evmState'.createdAccounts = evmState.createdAccounts := by rw [hevmState']
      by_cases hc2 : evmState'.gasAvailable.toNat < C' evmState' ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1
      · rw [if_pos hc2] at hZ; exact Except.noConfusion hZ
      rw [if_neg hc2] at hZ
      by_cases hc3 : δ ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1 = none
      · rw [if_pos hc3] at hZ; exact Except.noConfusion hZ
      rw [if_neg hc3] at hZ
      by_cases hc4 : evmState'.stack.length < (δ ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1).getD 0
      · rw [if_pos hc4] at hZ; exact Except.noConfusion hZ
      rw [if_neg hc4] at hZ
      (split_ifs at hZ;
        first
        | exact Except.noConfusion hZ
        | (injection hZ with h_inj
           injection h_inj with h_inj1 _
           subst h_inj1
           exact ⟨h_accMap, h_eEnv, h_cA⟩))
    obtain ⟨hZ_accMap, hZ_eEnv, hZ_cA⟩ := hZ_struct
    have hWFZ : StateWF evmStateZ.accountMap := by rw [hZ_accMap]; exact _hWF
    have hCOZ : C ≠ evmStateZ.executionEnv.codeOwner := by
      rw [hZ_eEnv]; exact _hCO
    have hNCZ : ∀ a ∈ evmStateZ.createdAccounts, a ≠ C := by
      rw [hZ_cA]; exact _hNC
    have hInvZ : StorageSumLeBalance evmStateZ.accountMap C := by rw [hZ_accMap]; exact _hInv
    simp only [bind, Except.bind] at hXres
    split at hXres
    case h_1 _ _ =>
      exact absurd hXres (by simp)
    case h_2 _ sstepState hStep =>
      split at hXres
      case h_1 _ hH_none =>
        have hInvSstep : StorageSumLeBalance sstepState.accountMap C :=
          step_invariant_preserved_at_non_C C f' cost₂ _ evmStateZ sstepState
            hWFZ hCOZ hNCZ _hAtCFrame hFrame hInvZ hStep
        have hWFsstep : StateWF sstepState.accountMap :=
          step_invariant_StateWF C f' cost₂ _ evmStateZ sstepState
            hWFZ hCOZ hNCZ _hAtCFrame hFrame hInvZ hStep
        have hCOsstep : C ≠ sstepState.executionEnv.codeOwner :=
          step_invariant_codeOwner C f' cost₂ _ evmStateZ sstepState
            hWFZ hCOZ hNCZ _hAtCFrame hFrame hInvZ hStep
        have hNCsstep : ∀ a ∈ sstepState.createdAccounts, a ≠ C :=
          step_invariant_createdAccounts C f' cost₂ _ evmStateZ sstepState
            hWFZ hCOZ hNCZ _hAtCFrame hFrame hInvZ hStep
        have hIH := _IH sstepState hWFsstep hCOsstep hNCsstep _hAtCFrame hFrame hInvSstep
        rw [hXres] at hIH
        exact hIH
      case h_2 _ o hH_some =>
        split at hXres
        case isTrue _ =>
          exact absurd hXres (by simp)
        case isFalse _ =>
          injection hXres with hXres_inj
          injection hXres_inj with hfin _
          subst hfin
          have hInvSstep : StorageSumLeBalance sstepState.accountMap C :=
            step_invariant_preserved_at_non_C C f' cost₂ _ evmStateZ sstepState
              hWFZ hCOZ hNCZ _hAtCFrame hFrame hInvZ hStep
          have hWFsstep : StateWF sstepState.accountMap :=
            step_invariant_StateWF C f' cost₂ _ evmStateZ sstepState
              hWFZ hCOZ hNCZ _hAtCFrame hFrame hInvZ hStep
          have hNCsstep : ∀ a ∈ sstepState.createdAccounts, a ≠ C :=
            step_invariant_createdAccounts C f' cost₂ _ evmStateZ sstepState
              hWFZ hCOZ hNCZ _hAtCFrame hFrame hInvZ hStep
          exact ⟨hInvSstep, hWFsstep, hNCsstep⟩

/-- **The inner X-fuel induction for the invariant chain.** Mirror of
`X_inv_holds`. -/
private theorem X_inv_invariant_holds
    (C : AccountAddress) (f : ℕ) (validJumps : Array UInt256)
    (evmState : EVM.State)
    (hAtCFrameAll : ∀ f', f' ≤ f → ΞInvariantAtCFrame C f')
    (hFrame : ∀ f', f' ≤ f → ΞInvariantFrameAtC C f') :
    X_inv_invariant C f validJumps evmState := by
  induction f generalizing evmState with
  | zero =>
    intro _ _ _ _ _ _
    rw [show EVM.X 0 validJumps evmState = .error .OutOfFuel from rfl]
    trivial
  | succ f' IH =>
    intro hWF hCO hNC _hAtCFrameAtSucc _hFrameAtSucc hInv
    show match EVM.X (f' + 1) validJumps evmState with
      | .ok (.success s' _) =>
          StorageSumLeBalance s'.accountMap C ∧
          StateWF s'.accountMap ∧
          (∀ a ∈ s'.createdAccounts, a ≠ C)
      | _ => True
    generalize hXres : EVM.X (f' + 1) validJumps evmState = xRes
    cases xRes with
    | error _ => trivial
    | ok er =>
      cases er with
      | revert _ _ => trivial
      | success finalState out =>
        have hFrame_f' : ΞInvariantFrameAtC C f' := hFrame f' (Nat.le_succ f')
        have hAtCFrame_f' : ΞInvariantAtCFrame C f' := hAtCFrameAll f' (Nat.le_succ f')
        have hFrame' : ∀ f'_1, f'_1 ≤ f' → ΞInvariantFrameAtC C f'_1 :=
          fun f1 h1 => hFrame f1 (Nat.le_trans h1 (Nat.le_succ f'))
        have hAtCFrame' : ∀ f'_1, f'_1 ≤ f' → ΞInvariantAtCFrame C f'_1 :=
          fun f1 h1 => hAtCFrameAll f1 (Nat.le_trans h1 (Nat.le_succ f'))
        have IH' : ∀ evmState', X_inv_invariant C f' validJumps evmState' :=
          fun es => IH es hAtCFrame' hFrame'
        exact X_inv_invariant_succ_content C f' validJumps evmState finalState out
          hWF hCO hNC hAtCFrame_f' hFrame_f' hInv IH' hXres

/-- **Bounded variant of `Ξ_invariant_preserved_bundled`.** Mirror of
`Ξ_balanceOf_ge_bundled_bdd` for the invariant chain. Takes per-fuel
`ΞInvariantAtCFrame C f` witnesses (one per fuel level less than `n`)
and builds the corresponding `ΞInvariantFrameAtC` projection. -/
theorem Ξ_invariant_preserved_bundled_bdd (C : AccountAddress)
    (n : ℕ)
    (hAtCBdd : ∀ f', f' < n → ΞInvariantAtCFrame C f') :
    ∀ (cA' : RBSet AccountAddress compare) (gbh' : BlockHeader)
      (bs' : ProcessedBlocks) (σ' σ₀' : AccountMap .EVM) (g' : UInt256)
      (A' : Substate) (I' : ExecutionEnv .EVM),
      StateWF σ' →
      C ≠ I'.codeOwner →
      (∀ a ∈ cA', a ≠ C) →
      StorageSumLeBalance σ' C →
      match EVM.Ξ n cA' gbh' bs' σ' σ₀' g' A' I' with
      | .ok (.success (cA_out, σ''final, _, _) _) =>
          StorageSumLeBalance σ''final C ∧ StateWF σ''final ∧
            (∀ a ∈ cA_out, a ≠ C)
      | _ => True := by
  intro cA' gbh' bs' σ' σ₀' g' A' I' hWF' hco' hnc' hInv'
  match n with
  | 0 =>
    rw [show EVM.Ξ 0 cA' gbh' bs' σ' σ₀' g' A' I' = .error .OutOfFuel from rfl]
    trivial
  | f + 1 =>
    have Ξ_frame_at : ∀ m, m ≤ f → ΞInvariantFrameAtC C m := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m IHm =>
        intro hm
        intro f'' hf'' cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hco'' hnc'' hInv''
        match f'' with
        | 0 =>
          rw [show EVM.Ξ 0 cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I''
                = .error .OutOfFuel from rfl]
          trivial
        | k + 1 =>
          have hkLeF : k + 1 ≤ f := Nat.le_trans hf'' hm
          have hAtCSubst : ∀ k', k' ≤ k → ΞInvariantAtCFrame C k' := by
            intro k' hk'
            have hk'LtSucc : k' < f + 1 := by omega
            exact hAtCBdd k' hk'LtSucc
          have hFrameSubst : ∀ k', k' ≤ k → ΞInvariantFrameAtC C k' := by
            intro k' hk'
            have hkLtM : k < m := by
              have : k + 1 ≤ m := hf''
              omega
            have hk'LtM : k' < m := Nat.lt_of_le_of_lt hk' hkLtM
            have hk'LeF : k' ≤ f := by omega
            exact IHm k' hk'LtM hk'LeF
          have hΞ_eq :
              EVM.Ξ (k + 1) cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I''
                = (do
                    let defState : EVM.State := default
                    let freshEvmState : EVM.State :=
                      { defState with
                          accountMap := σ''
                          σ₀ := σ₀''
                          executionEnv := I''
                          substate := A''
                          createdAccounts := cA''
                          gasAvailable := g''
                          blocks := bs''
                          genesisBlockHeader := gbh'' }
                    let result ← EVM.X k (D_J I''.code ⟨0⟩) freshEvmState
                    match result with
                    | .success evmState' o =>
                      let finalGas := evmState'.gasAvailable
                      .ok (ExecutionResult.success
                        (evmState'.createdAccounts, evmState'.accountMap,
                         finalGas, evmState'.substate) o)
                    | .revert g' o => .ok (ExecutionResult.revert g' o)) := rfl
          rw [hΞ_eq]
          simp only [bind, Except.bind]
          generalize hXres : EVM.X k (D_J I''.code ⟨0⟩) _ = xRes
          have hXinv : X_inv_invariant C k (D_J I''.code ⟨0⟩)
            { (default : EVM.State) with
                accountMap := σ''
                σ₀ := σ₀''
                executionEnv := I''
                substate := A''
                createdAccounts := cA''
                gasAvailable := g''
                blocks := bs''
                genesisBlockHeader := gbh'' } :=
            X_inv_invariant_holds C k (D_J I''.code ⟨0⟩) _ hAtCSubst hFrameSubst
          unfold X_inv_invariant at hXinv
          have := hXinv hWF'' hco'' hnc''
                  (hAtCSubst k (Nat.le_refl _)) (hFrameSubst k (Nat.le_refl _)) hInv''
          rw [hXres] at this
          cases xRes with
          | error _ => trivial
          | ok er =>
            cases er with
            | success evmState' out => exact this
            | revert _ _ => trivial
    have hAtCAll : ∀ f', f' ≤ f → ΞInvariantAtCFrame C f' := by
      intro f' hf'
      exact hAtCBdd f' (Nat.lt_succ_of_le hf')
    have hΞ_eq :
        EVM.Ξ (f + 1) cA' gbh' bs' σ' σ₀' g' A' I'
          = (do
              let defState : EVM.State := default
              let freshEvmState : EVM.State :=
                { defState with
                    accountMap := σ'
                    σ₀ := σ₀'
                    executionEnv := I'
                    substate := A'
                    createdAccounts := cA'
                    gasAvailable := g'
                    blocks := bs'
                    genesisBlockHeader := gbh' }
              let result ← EVM.X f (D_J I'.code ⟨0⟩) freshEvmState
              match result with
              | .success evmState' o =>
                let finalGas := evmState'.gasAvailable
                .ok (ExecutionResult.success
                  (evmState'.createdAccounts, evmState'.accountMap,
                   finalGas, evmState'.substate) o)
              | .revert g' o => .ok (ExecutionResult.revert g' o)) := rfl
    rw [hΞ_eq]
    simp only [bind, Except.bind]
    generalize hXres : EVM.X f (D_J I'.code ⟨0⟩) _ = xRes
    have hXinv : X_inv_invariant C f (D_J I'.code ⟨0⟩)
      { (default : EVM.State) with
          accountMap := σ'
          σ₀ := σ₀'
          executionEnv := I'
          substate := A'
          createdAccounts := cA'
          gasAvailable := g'
          blocks := bs'
          genesisBlockHeader := gbh' } :=
      X_inv_invariant_holds C f (D_J I'.code ⟨0⟩) _ hAtCAll Ξ_frame_at
    unfold X_inv_invariant at hXinv
    have hWFF : StateWF σ' := hWF'
    have hCOF : C ≠ I'.codeOwner := hco'
    have hNCF : ∀ a ∈ cA', a ≠ C := hnc'
    have hInvF : StorageSumLeBalance σ' C := hInv'
    have := hXinv hWFF hCOF hNCF (hAtCAll f (Nat.le_refl _)) (Ξ_frame_at f (Nat.le_refl _)) hInvF
    rw [hXres] at this
    cases xRes with
    | error _ => trivial
    | ok er =>
      cases er with
      | success evmState' out =>
        exact this
      | revert _ _ => trivial

/-- An unbounded `ΞPreservesInvariantAtC C` witness yields
`ΞInvariantFrameAtC C maxFuel` at any `maxFuel`. Routes via
`Ξ_invariant_preserved_bundled_bdd` — the at-C IHs at every `f' < fuel`
are derived from the witness via `ΞInvariantAtCFrame_of_witness`. -/
theorem ΞInvariantFrameAtC_of_witness (C : AccountAddress)
    (hWitness : ΞPreservesInvariantAtC C) (maxFuel : ℕ) :
    ΞInvariantFrameAtC C maxFuel := by
  intro fuel _hf cA gbh bs σ σ₀ g A I hWF hCO_ne hNC hInv
  have hAtCSub : ∀ k, k < fuel → ΞInvariantAtCFrame C k :=
    fun k _ => ΞInvariantAtCFrame_of_witness C hWitness k
  exact Ξ_invariant_preserved_bundled_bdd C fuel hAtCSub
    cA gbh bs σ σ₀ g A I hWF hCO_ne hNC hInv

/-! ## §H.2 — At-`C` invariant step bundle (consumer-facing)

Mirror of `step_bundled_invariant_at_C_general` (§G.1) for the
`StorageSumLeBalance` chain. Same op-whitelist parameterization, but the
conclusion tracks `StorageSumLeBalance` preservation rather than `balanceOf`
monotonicity, and the closure dispatcher recognizes one extra arm:
the at-`C` SSTORE arm, whose post-state invariant must be supplied as
a per-step hypothesis (the consumer discharges this at concrete
bytecode states via decrement-pattern reasoning).

The aggregator routes:
* Strict (handled, ¬SD, ¬SSTORE, ¬TSTORE) — `accountMap` is preserved
  literally → invariant projects through verbatim.
* `.CALL` with `stack[2] = ⟨0⟩` — outbound zero-value call;
  routed through `call_invariant_preserved` with slack hypothesis
  `Or.inr (Or.inl rfl)` (i.e., `v = 0`).
* `.StackMemFlow .SSTORE` — at-`C` storage write. Output invariant
  flows from a per-step hypothesis `h_sstore_post`.

At-`C` SELFDESTRUCT, TSTORE, and other system ops (CREATE/CREATE2/
CALLCODE/DELEGATECALL/STATICCALL) are excluded from `OpAllowedSet` by
the consumer (the per-PC bytecode walk). -/

/-- **Strict-handled invariant helper at-`C`.** Mirror of
`step_handled_helper_at_C_general` (balance side) for the invariant
chain. For ops that strictly preserve `accountMap` (handled,
non-SELFDESTRUCT, non-SSTORE, non-TSTORE), the entire `accountMap` is
preserved literally, so `StorageSumLeBalance` projects identically. -/
private theorem step_handled_strict_helper_at_C_invariant
    (op : Operation .EVM) (C : AccountAddress) (f : ℕ) (cost₂ : ℕ)
    (arg : Option (UInt256 × Nat))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCC : C = evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hStrict : strictlyPreservesAccountMap op)
    (hStep : EVM.step (f + 1) cost₂ (some (op, arg)) evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C = sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  set s_pre : EVM.State :=
    { evmState with
        execLength := evmState.execLength + 1,
        gasAvailable := evmState.gasAvailable - UInt256.ofNat cost₂ }
    with hs_pre_def
  have hAM : s_pre.accountMap = evmState.accountMap := rfl
  have hCOEq : s_pre.executionEnv = evmState.executionEnv := rfl
  have hCAEq : s_pre.createdAccounts = evmState.createdAccounts := rfl
  have hWF_pre : StateWF s_pre.accountMap := by rw [hAM]; exact hWF
  have hHandled : handledByEvmYulStep op := hStrict.1
  have hSDne : op ≠ .SELFDESTRUCT := hStrict.2.1
  -- Reduce EVM.step to EvmYul.step.
  have hStep' : EvmYul.step op arg s_pre = .ok sstepState := by
    unfold EVM.step at hStep
    simp only [bind, Except.bind, pure, Except.pure] at hStep
    obtain ⟨hne1, hne2, hne3, hne4, hne5, hne6⟩ := hHandled
    cases op with
    | StopArith _ => exact hStep
    | CompBit _ => exact hStep
    | Keccak _ => exact hStep
    | Env _ => exact hStep
    | Block _ => exact hStep
    | StackMemFlow _ => exact hStep
    | Push _ => exact hStep
    | Dup _ => exact hStep
    | Exchange _ => exact hStep
    | Log _ => exact hStep
    | System o =>
      cases o with
      | CREATE => exact absurd rfl hne1
      | CALL => exact absurd rfl hne3
      | CALLCODE => exact absurd rfl hne4
      | RETURN => exact hStep
      | DELEGATECALL => exact absurd rfl hne5
      | CREATE2 => exact absurd rfl hne2
      | STATICCALL => exact absurd rfl hne6
      | REVERT => exact hStep
      | INVALID => exact hStep
      | SELFDESTRUCT => exact hStep
  -- accountMap literally preserved.
  have hAMeq : sstepState.accountMap = s_pre.accountMap :=
    EvmYul.step_accountMap_eq_of_strict op arg s_pre sstepState hStrict hStep'
  -- StorageSumLeBalance projects through accountMap-equality.
  have hInvres : StorageSumLeBalance sstepState.accountMap C := by
    unfold StorageSumLeBalance at hInv ⊢
    rw [hAMeq, hAM]; exact hInv
  -- StateWF preserved.
  have hWFres : StateWF sstepState.accountMap :=
    EvmYul_step_preserves_StateWF op arg s_pre sstepState hHandled hSDne hStep' hWF_pre
  -- Execution env / created accounts preserved.
  have hEnvCA :=
    EvmYul.step_preserves_eEnv_cA op arg s_pre sstepState hHandled hStep'
  refine ⟨hInvres, hWFres, ?_, ?_⟩
  · rw [hEnvCA.1, hCOEq]; exact hCC
  · intro a haIn
    rw [hEnvCA.2, hCAEq] at haIn
    exact hNC a haIn

/-- **At-`C` CALL invariant arm with `stack[2] = 0` (outbound v=0).**
Mirror of `step_CALL_arm_at_C_v0` for the invariant chain. The slack
disjunction is satisfied via `Or.inr (Or.inl hμ2)` (i.e., `v = 0`).
The recipient may be any address (including `C` itself, which is
re-entrancy); since `v = 0`, the inner Ξ frame is the
`ΞInvariantAtCFrame` (when `r = C`) or `ΞInvariantFrameAtC` (when
`r ≠ C`) — both already supplied. -/
private theorem step_CALL_arm_at_C_v0_invariant
    (C : AccountAddress) (f : ℕ) (cost₂ : ℕ) (arg : Option (UInt256 × Nat))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCC : C = evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C (f + 1))
    (hFrame : ΞInvariantFrameAtC C (f + 1))
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (h_v0 : evmState.stack[2]? = some ⟨0⟩)
    (hStep : EVM.step (f + 1) cost₂ (some (.CALL, arg)) evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C = sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  -- Unfold the CALL arm body, mirroring step_CALL_arm_at_C_v0.
  simp only [EVM.step, Operation.CALL, bind, Except.bind, pure, Except.pure] at hStep
  set eS1 : EVM.State := { evmState with execLength := evmState.execLength + 1 } with heS1_def
  split at hStep
  · exact absurd hStep (by simp)
  · rename_i p hpop7
    obtain ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩ := p
    have hStackEq : eS1.stack = evmState.stack := rfl
    have hpop7' : eS1.stack.pop7 = some (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) := by
      cases hP : eS1.stack.pop7 with
      | none =>
        rw [hP] at hpop7
        have hcontra :
            (Except.error EVM.ExecutionException.StackUnderflow :
                Except EVM.ExecutionException _)
              = .ok (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) := hpop7
        cases hcontra
      | some q =>
        rw [hP] at hpop7
        have : (Except.ok q : Except EVM.ExecutionException _) =
               .ok (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) := hpop7
        injection this with h
        rw [h]
    have hμ2 : μ₂ = (⟨0⟩ : UInt256) := by
      cases hS : eS1.stack with
      | nil => rw [hS] at hpop7'; simp [Stack.pop7] at hpop7'
      | cons a₀ rest =>
        cases rest with
        | nil => rw [hS] at hpop7'; simp [Stack.pop7] at hpop7'
        | cons a₁ rest =>
          cases rest with
          | nil => rw [hS] at hpop7'; simp [Stack.pop7] at hpop7'
          | cons a₂ rest =>
            cases rest with
            | nil => rw [hS] at hpop7'; simp [Stack.pop7] at hpop7'
            | cons a₃ rest =>
              cases rest with
              | nil => rw [hS] at hpop7'; simp [Stack.pop7] at hpop7'
              | cons a₄ rest =>
                cases rest with
                | nil => rw [hS] at hpop7'; simp [Stack.pop7] at hpop7'
                | cons a₅ rest =>
                  cases rest with
                  | nil => rw [hS] at hpop7'; simp [Stack.pop7] at hpop7'
                  | cons a₆ tl =>
                    rw [hS] at hpop7'
                    simp only [Stack.pop7] at hpop7'
                    injection hpop7' with hpop7''
                    have hμ2_eq : a₂ = μ₂ := by
                      have := hpop7''
                      simp only [Prod.mk.injEq] at this
                      exact this.2.2.2.1
                    rw [hStackEq] at hS
                    rw [hS] at h_v0
                    simp at h_v0
                    rw [← hμ2_eq]; exact h_v0
    split at hStep
    · exact absurd hStep (by simp)
    · rename_i p_call hCallRes
      obtain ⟨x, state'⟩ := p_call
      injection hStep with hEq
      rw [← hEq]
      have hWFes1 : StateWF eS1.accountMap := hWF
      have hCCes1 : C = eS1.executionEnv.codeOwner := hCC
      have hNCes1 : ∀ a ∈ eS1.createdAccounts, a ≠ C := hNC
      have hInves1 : StorageSumLeBalance eS1.accountMap C := hInv
      -- Discharge h_vb, h_fs, h_slack via μ₂ = 0.
      have h_vb_call :
          ∀ acc, (eS1.accountMap).find? (AccountAddress.ofUInt256 μ₁) = some acc →
            acc.balance.toNat + μ₂.toNat < UInt256.size := by
        intro acc _
        rw [hμ2]
        show acc.balance.toNat + 0 < UInt256.size
        rw [Nat.add_zero]
        exact acc.balance.val.isLt
      have h_fs_call :
          μ₂ = ⟨0⟩ ∨ ∃ acc,
              (eS1.accountMap).find? (AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner))
                = some acc ∧ μ₂.toNat ≤ acc.balance.toNat := Or.inl hμ2
      have h_slack_call :
          C ≠ AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner) ∨
              μ₂ = ⟨0⟩ ∨
              μ₂.toNat + storageSum eS1.accountMap C ≤ balanceOf eS1.accountMap C :=
        Or.inr (Or.inl hμ2)
      have hAtCFrame_f : ΞInvariantAtCFrame C f :=
        ΞInvariantAtCFrame_mono C (f + 1) f (Nat.le_succ _) hAtCFrame
      have hFrame_f : ΞInvariantFrameAtC C f :=
        ΞInvariantFrameAtC_mono C (f + 1) f (Nat.le_succ _) hFrame
      have hBundle :=
        call_invariant_preserved C f cost₂ μ₀ (.ofNat eS1.executionEnv.codeOwner)
          μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ eS1.executionEnv.perm eS1 state' x
          hWFes1 hNCes1 hAtCFrame_f hFrame_f h_vb_call h_fs_call h_slack_call hInves1 hCallRes
      obtain ⟨hInvres, hWFres, hCOres, hNCres⟩ := hBundle
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [accountMap_replaceStackAndIncrPC]; exact hInvres
      · simp only [accountMap_replaceStackAndIncrPC]; exact hWFres
      · simp only [executionEnv_replaceStackAndIncrPC]; rw [hCOres]; exact hCCes1
      · simp only [createdAccounts_replaceStackAndIncrPC]; exact hNCres

/-- **At-`C` CALL invariant arm with slack disjunction (outbound non-zero).**

Slack-based sibling of `step_CALL_arm_at_C_v0_invariant`. The consumer
supplies a per-state callback `h_call_pre` that — given the seven popped
CALL parameters `(μ₀ = gas, μ₁ = recipient, μ₂ = value, μ₃ = inOff,
μ₄ = inSize, μ₅ = outOff, μ₆ = outSize)` and the residual stack tail —
produces the three preconditions of `call_invariant_preserved`:

* `h_vb_call` — recipient no-wrap.
* `h_fs_call` — sender funds disjunction.
* `h_slack_call` — at-`C` slack disjunction (`C ≠ source ∨ v = 0 ∨
  v + storageSum ≤ balanceOf`).

Compared to the v=0 helper, this lets the consumer carry the at-`C`
non-zero CALL by exposing the SSTORE-decrement fact preceding the
outbound CALL (which establishes the slack inequality). The IHs
`hAtCFrame`/`hFrame` at fuel `f + 1` are mono'd down to `f` and threaded
into `call_invariant_preserved` here — so the consumer never sees the
IHs. -/
theorem step_CALL_arm_at_C_slack_invariant
    (C : AccountAddress) (f : ℕ) (cost₂ : ℕ) (arg : Option (UInt256 × Nat))
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCC : C = evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C (f + 1))
    (hFrame : ΞInvariantFrameAtC C (f + 1))
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (h_call_pre :
      ∀ (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256) (tl : Stack UInt256),
        evmState.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: tl →
        (∀ acc,
            evmState.accountMap.find? (AccountAddress.ofUInt256 μ₁) = some acc →
            acc.balance.toNat + μ₂.toNat < UInt256.size) ∧
        (μ₂ = ⟨0⟩ ∨ ∃ acc,
            evmState.accountMap.find?
                (AccountAddress.ofUInt256
                  (.ofNat evmState.executionEnv.codeOwner)) = some acc ∧
            μ₂.toNat ≤ acc.balance.toNat) ∧
        (C ≠ AccountAddress.ofUInt256
                (.ofNat evmState.executionEnv.codeOwner) ∨
         μ₂ = ⟨0⟩ ∨
         μ₂.toNat + storageSum evmState.accountMap C
           ≤ balanceOf evmState.accountMap C))
    (hStep : EVM.step (f + 1) cost₂ (some (.CALL, arg)) evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C = sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  -- Unfold the CALL arm body, mirroring step_CALL_arm_at_C_v0_invariant.
  simp only [EVM.step, Operation.CALL, bind, Except.bind, pure, Except.pure] at hStep
  set eS1 : EVM.State := { evmState with execLength := evmState.execLength + 1 } with heS1_def
  split at hStep
  · exact absurd hStep (by simp)
  · rename_i p hpop7
    obtain ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩ := p
    have hStackEq : eS1.stack = evmState.stack := rfl
    have hpop7' : eS1.stack.pop7 = some (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) := by
      cases hP : eS1.stack.pop7 with
      | none =>
        rw [hP] at hpop7
        have hcontra :
            (Except.error EVM.ExecutionException.StackUnderflow :
                Except EVM.ExecutionException _)
              = .ok (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) := hpop7
        cases hcontra
      | some q =>
        rw [hP] at hpop7
        have : (Except.ok q : Except EVM.ExecutionException _) =
               .ok (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) := hpop7
        injection this with h
        rw [h]
    -- Recover the 7-element prefix of evmState.stack from `pop7'`.
    have hStkShape :
        evmState.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: stack := by
      cases hS : eS1.stack with
      | nil => rw [hS] at hpop7'; simp [Stack.pop7] at hpop7'
      | cons a₀ rest =>
        cases rest with
        | nil => rw [hS] at hpop7'; simp [Stack.pop7] at hpop7'
        | cons a₁ rest =>
          cases rest with
          | nil => rw [hS] at hpop7'; simp [Stack.pop7] at hpop7'
          | cons a₂ rest =>
            cases rest with
            | nil => rw [hS] at hpop7'; simp [Stack.pop7] at hpop7'
            | cons a₃ rest =>
              cases rest with
              | nil => rw [hS] at hpop7'; simp [Stack.pop7] at hpop7'
              | cons a₄ rest =>
                cases rest with
                | nil => rw [hS] at hpop7'; simp [Stack.pop7] at hpop7'
                | cons a₅ rest =>
                  cases rest with
                  | nil => rw [hS] at hpop7'; simp [Stack.pop7] at hpop7'
                  | cons a₆ tl =>
                    rw [hS] at hpop7'
                    simp only [Stack.pop7] at hpop7'
                    injection hpop7' with hpop7''
                    -- hpop7'' : (tl, a₀, a₁, a₂, a₃, a₄, a₅, a₆) =
                    --            (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆)
                    simp only [Prod.mk.injEq] at hpop7''
                    obtain ⟨htl, h0, h1, h2, h3, h4, h5, h6_eq⟩ := hpop7''
                    -- evmState.stack = eS1.stack = a₀ :: ... :: a₆ :: tl;
                    -- with aᵢ=μᵢ and tl=stack, this is μ₀ :: ... :: stack.
                    rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6_eq, ← htl,
                        ← hS, hStackEq]
    -- Apply consumer's per-state callback, getting h_vb / h_fs / h_slack.
    have ⟨h_vb_e, h_fs_e, h_slack_e⟩ :=
      h_call_pre μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ stack hStkShape
    split at hStep
    · exact absurd hStep (by simp)
    · rename_i p_call hCallRes
      obtain ⟨x, state'⟩ := p_call
      injection hStep with hEq
      rw [← hEq]
      have hWFes1 : StateWF eS1.accountMap := hWF
      have hCCes1 : C = eS1.executionEnv.codeOwner := hCC
      have hNCes1 : ∀ a ∈ eS1.createdAccounts, a ≠ C := hNC
      have hInves1 : StorageSumLeBalance eS1.accountMap C := hInv
      -- Re-state the consumer's preconditions on `eS1` (definitionally
      -- equal to `evmState` on the `.accountMap`/`.executionEnv` fields).
      have hAM_eS1 : eS1.accountMap = evmState.accountMap := rfl
      have hEE_eS1 : eS1.executionEnv = evmState.executionEnv := rfl
      have h_vb_call :
          ∀ acc, (eS1.accountMap).find? (AccountAddress.ofUInt256 μ₁) = some acc →
            acc.balance.toNat + μ₂.toNat < UInt256.size := by
        rw [hAM_eS1]; exact h_vb_e
      have h_fs_call :
          μ₂ = ⟨0⟩ ∨ ∃ acc,
              (eS1.accountMap).find?
                  (AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner))
                = some acc ∧ μ₂.toNat ≤ acc.balance.toNat := by
        rw [hAM_eS1, hEE_eS1]; exact h_fs_e
      have h_slack_call :
          C ≠ AccountAddress.ofUInt256 (.ofNat eS1.executionEnv.codeOwner) ∨
              μ₂ = ⟨0⟩ ∨
              μ₂.toNat + storageSum eS1.accountMap C ≤ balanceOf eS1.accountMap C := by
        rw [hAM_eS1, hEE_eS1]; exact h_slack_e
      have hAtCFrame_f : ΞInvariantAtCFrame C f :=
        ΞInvariantAtCFrame_mono C (f + 1) f (Nat.le_succ _) hAtCFrame
      have hFrame_f : ΞInvariantFrameAtC C f :=
        ΞInvariantFrameAtC_mono C (f + 1) f (Nat.le_succ _) hFrame
      have hBundle :=
        call_invariant_preserved C f cost₂ μ₀ (.ofNat eS1.executionEnv.codeOwner)
          μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ eS1.executionEnv.perm eS1 state' x
          hWFes1 hNCes1 hAtCFrame_f hFrame_f h_vb_call h_fs_call h_slack_call hInves1 hCallRes
      obtain ⟨hInvres, hWFres, hCOres, hNCres⟩ := hBundle
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [accountMap_replaceStackAndIncrPC]; exact hInvres
      · simp only [accountMap_replaceStackAndIncrPC]; exact hWFres
      · simp only [executionEnv_replaceStackAndIncrPC]; rw [hCOres]; exact hCCes1
      · simp only [createdAccounts_replaceStackAndIncrPC]; exact hNCres

/-- **At-`C` invariant step bundle.** Op-whitelist generalization
mirroring `step_bundled_invariant_at_C_general` (§G.1) for the
`StorageSumLeBalance` chain.

Allowed op-classes (per `hDischarge`):
* Strict-handled (handled, ¬SD, ¬SSTORE, ¬TSTORE) — preserves
  invariant via `accountMap` equality.
* `.CALL` — outbound v=0 routing via `step_CALL_arm_at_C_v0_invariant`.
* `.StackMemFlow .SSTORE` — at-`C` SSTORE; per-step output invariant
  supplied via `h_sstore_post`.

The consumer (the per-PC bytecode walk) supplies `h_sstore_post`
per-state by decrement-pattern reasoning (withdraw: val=0 ⇒ slot
zeroed ⇒ invariant trivially) or by msg.value-credit slack (deposit:
SSTORE follows a Θ-prefix that credited C with msg.value, so the
storage-sum increment is matched by the balance increment). -/
private theorem step_bundled_invariant_at_C_invariant_at_C
    (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress) (f : ℕ) (cost₂ : ℕ) (arg : Option (UInt256 × Nat))
    (op : Operation .EVM)
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCC : C = evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C (f + 1))
    (hFrame : ΞInvariantFrameAtC C (f + 1))
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hAllowed : OpAllowedSet op)
    (hDischarge : ∀ op', OpAllowedSet op' →
        strictlyPreservesAccountMap op' ∨ op' = .CALL ∨
        op' = .StackMemFlow .SSTORE)
    (h_v0 : op = .CALL → evmState.stack[2]? = some ⟨0⟩)
    (h_sstore_post : op = .StackMemFlow .SSTORE →
        StorageSumLeBalance sstepState.accountMap C)
    (hStep : EVM.step (f + 1) cost₂ (some (op, arg)) evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C = sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  rcases hDischarge op hAllowed with hStrict | hCall | hSStore
  · -- Strict-handled op.
    exact step_handled_strict_helper_at_C_invariant op C f cost₂ arg evmState sstepState
      hWF hCC hNC hInv hStrict hStep
  · -- CALL with v=0.
    subst hCall
    exact step_CALL_arm_at_C_v0_invariant C f cost₂ arg evmState sstepState
      hWF hCC hNC hAtCFrame hFrame hInv (h_v0 rfl) hStep
  · -- SSTORE: invariant flows via the per-step hypothesis. We still
    -- need to derive StateWF, codeOwner, and createdAccounts preservation
    -- from the underlying EvmYul.step.
    subst hSStore
    have hInvres : StorageSumLeBalance sstepState.accountMap C := h_sstore_post rfl
    -- Reduce EVM.step to EvmYul.step (SSTORE is handled, ¬SD).
    have hHandled : handledByEvmYulStep (.StackMemFlow .SSTORE : Operation .EVM) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
    have hSDne : (.StackMemFlow .SSTORE : Operation .EVM) ≠ .SELFDESTRUCT := by decide
    set s_pre : EVM.State :=
      { evmState with
          execLength := evmState.execLength + 1,
          gasAvailable := evmState.gasAvailable - UInt256.ofNat cost₂ }
      with hs_pre_def
    have hAM : s_pre.accountMap = evmState.accountMap := rfl
    have hCOEq : s_pre.executionEnv = evmState.executionEnv := rfl
    have hCAEq : s_pre.createdAccounts = evmState.createdAccounts := rfl
    have hWF_pre : StateWF s_pre.accountMap := by rw [hAM]; exact hWF
    have hStep' : EvmYul.step (.StackMemFlow .SSTORE : Operation .EVM) arg s_pre
                = .ok sstepState := by
      unfold EVM.step at hStep
      simp only [bind, Except.bind, pure, Except.pure] at hStep
      exact hStep
    have hWFres : StateWF sstepState.accountMap :=
      EvmYul_step_preserves_StateWF (.StackMemFlow .SSTORE) arg s_pre sstepState
        hHandled hSDne hStep' hWF_pre
    have hEnvCA :=
      EvmYul.step_preserves_eEnv_cA (.StackMemFlow .SSTORE) arg s_pre sstepState
        hHandled hStep'
    refine ⟨hInvres, hWFres, ?_, ?_⟩
    · rw [hEnvCA.1, hCOEq]; exact hCC
    · intro a haIn
      rw [hEnvCA.2, hCAEq] at haIn
      exact hNC a haIn

/-- **At-`C` invariant X-induction predicate.** Mirror of
`X_inv_at_C_general` for the `StorageSumLeBalance` chain.

In addition to the structural reachability/closure hypotheses (Z, step,
decode-some, op ∈ allowed-set), we take a per-step output-invariant
hypothesis for the SSTORE arm: for every reachable state where the
fetched instruction is `.SSTORE` and the step succeeds, the post-step
`StorageSumLeBalance` holds. The consumer (the per-PC bytecode walk) discharges this
via decrement-pattern reasoning at concrete bytecode states (e.g. a
withdraw-style SSTORE that zeroes the slot, or a deposit-style SSTORE
that increments by `msg.value` where the slack came from the Θ-prefix
value transfer). -/
private def X_inv_at_C_invariant (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress) (f : ℕ) (validJumps : Array UInt256)
    (Reachable : EVM.State → Prop)
    (evmState : EVM.State) : Prop :=
  StateWF evmState.accountMap →
  C = evmState.executionEnv.codeOwner →
  (∀ a ∈ evmState.createdAccounts, a ≠ C) →
  ΞInvariantAtCFrame C f →
  ΞInvariantFrameAtC C f →
  StorageSumLeBalance evmState.accountMap C →
  Reachable evmState →
  -- Z preserves Reachable.
  (∀ s : EVM.State, ∀ g : UInt256, Reachable s →
      Reachable { s with gasAvailable := g }) →
  -- step preserves Reachable.
  (∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ op arg, Reachable s →
      fetchInstr s.executionEnv s.pc = .ok (op, arg) →
      EVM.step (f' + 1) cost (some (op, arg)) s = .ok s' →
      Reachable s') →
  -- Reachable ⇒ decode-some.
  (∀ s : EVM.State, Reachable s →
      ∃ pair, decode s.executionEnv.code s.pc = some pair) →
  -- Reachable + decode ⇒ op ∈ OpAllowedSet.
  (∀ s : EVM.State, ∀ op : Operation .EVM, ∀ arg,
    Reachable s →
    fetchInstr s.executionEnv s.pc = .ok (op, arg) →
    OpAllowedSet op) →
  -- OpAllowedSet ⇒ strict ∨ op=.CALL ∨ op=.SSTORE.
  (∀ op', OpAllowedSet op' →
    strictlyPreservesAccountMap op' ∨ op' = .CALL ∨
    op' = .StackMemFlow .SSTORE) →
  -- Reachable + op=.CALL ⇒ stack[2]? = some 0.
  (∀ s : EVM.State, ∀ arg,
    Reachable s →
    fetchInstr s.executionEnv s.pc = .ok (.CALL, arg) →
    s.stack[2]? = some ⟨0⟩) →
  -- Per-step SSTORE output invariant: at every reachable state with
  -- `op = SSTORE`, the post-step `StorageSumLeBalance` is preserved.
  (∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ arg,
    Reachable s →
    StateWF s.accountMap →
    C = s.executionEnv.codeOwner →
    StorageSumLeBalance s.accountMap C →
    fetchInstr s.executionEnv s.pc = .ok (.StackMemFlow .SSTORE, arg) →
    EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s' →
    StorageSumLeBalance s'.accountMap C) →
  match EVM.X f validJumps evmState with
  | .ok (.success s' _) =>
      StorageSumLeBalance s'.accountMap C ∧
      StateWF s'.accountMap ∧
      (∀ a ∈ s'.createdAccounts, a ≠ C)
  | _ => True

/-- **Fuel induction for `X_inv_at_C_invariant`.** Mirror of
`X_inv_at_C_general_holds`. -/
private theorem X_inv_at_C_invariant_holds
    (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress) (f : ℕ) (validJumps : Array UInt256)
    (Reachable : EVM.State → Prop)
    (evmState : EVM.State)
    (hAtCFrameAll : ∀ f', f' ≤ f → ΞInvariantAtCFrame C f')
    (hFrame : ∀ f', f' ≤ f → ΞInvariantFrameAtC C f') :
    X_inv_at_C_invariant OpAllowedSet C f validJumps Reachable evmState := by
  induction f generalizing evmState with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [show EVM.X 0 validJumps evmState = .error .OutOfFuel from rfl]
    trivial
  | succ f' IH =>
    intro hWF hCC hNC _hAtCFrameAtSucc _hFrameAtSucc hInv
            hReach hReach_Z hReach_step hReach_decodeSome
            hOpAllowedReach hDischarge h_v0_Reach h_sstore_Reach
    show match EVM.X (f' + 1) validJumps evmState with
      | .ok (.success s' _) =>
          StorageSumLeBalance s'.accountMap C ∧
          StateWF s'.accountMap ∧
          (∀ a ∈ s'.createdAccounts, a ≠ C)
      | _ => True
    generalize hXres : EVM.X (f' + 1) validJumps evmState = xRes
    cases xRes with
    | error _ => trivial
    | ok er =>
      cases er with
      | revert _ _ => trivial
      | success finalState out =>
        simp only [EVM.X] at hXres
        split at hXres
        case h_1 _ _ => exact absurd hXres (by simp)
        case h_2 _ evmStateZ cost₂ hZ =>
          have hZ_full :
              evmStateZ = { evmState with gasAvailable := evmStateZ.gasAvailable } := by
            simp only [bind, Except.bind, pure, Except.pure] at hZ
            by_cases hc1 : evmState.gasAvailable.toNat < memoryExpansionCost evmState ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1
            · rw [if_pos hc1] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc1] at hZ
            set evmState' : EVM.State :=
              { evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1) } with hevmState'
            by_cases hc2 : evmState'.gasAvailable.toNat < C' evmState' ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1
            · rw [if_pos hc2] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc2] at hZ
            by_cases hc3 : δ ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1 = none
            · rw [if_pos hc3] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc3] at hZ
            by_cases hc4 : evmState'.stack.length < (δ ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1).getD 0
            · rw [if_pos hc4] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc4] at hZ
            (split_ifs at hZ;
              first
              | exact Except.noConfusion hZ
              | (injection hZ with h_inj
                 injection h_inj with h_inj1 _
                 subst h_inj1
                 rfl))
          have hZ_accMap : evmStateZ.accountMap = evmState.accountMap := by rw [hZ_full]
          have hZ_eEnv : evmStateZ.executionEnv = evmState.executionEnv := by rw [hZ_full]
          have hZ_cA : evmStateZ.createdAccounts = evmState.createdAccounts := by rw [hZ_full]
          have hZ_pc : evmStateZ.pc = evmState.pc := by rw [hZ_full]
          have hWFZ : StateWF evmStateZ.accountMap := by rw [hZ_accMap]; exact hWF
          have hCCZ : C = evmStateZ.executionEnv.codeOwner := by
            rw [hZ_eEnv]; exact hCC
          have hNCZ : ∀ a ∈ evmStateZ.createdAccounts, a ≠ C := by
            rw [hZ_cA]; exact hNC
          have hInvZ : StorageSumLeBalance evmStateZ.accountMap C := by rw [hZ_accMap]; exact hInv
          have hReachZ : Reachable evmStateZ := by
            rw [hZ_full]
            exact hReach_Z evmState evmStateZ.gasAvailable hReach
          simp only [bind, Except.bind] at hXres
          split at hXres
          case h_1 _ _ => exact absurd hXres (by simp)
          case h_2 _ sstepState hStep =>
            match f' with
            | 0 =>
              simp only [EVM.step] at hStep
              exact absurd hStep (by simp)
            | f'' + 1 =>
              set decRes : Operation .EVM × Option (UInt256 × Nat) :=
                (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none) with hDecRes
              obtain ⟨op, arg⟩ := decRes
              have hFrameAtSuccF' : ΞInvariantFrameAtC C (f'' + 1) :=
                ΞInvariantFrameAtC_mono C ((f'' + 1) + 1) (f'' + 1) (Nat.le_succ _) _hFrameAtSucc
              have hAtCFrameAtSuccF' : ΞInvariantAtCFrame C (f'' + 1) :=
                ΞInvariantAtCFrame_mono C ((f'' + 1) + 1) (f'' + 1) (Nat.le_succ _) _hAtCFrameAtSucc
              -- Discharge OpAllowedSet op via reachability + decode-some.
              have hAllowed : OpAllowedSet op := by
                cases hDec : decode evmStateZ.executionEnv.code evmStateZ.pc with
                | none =>
                  obtain ⟨_, hSome⟩ := hReach_decodeSome evmStateZ hReachZ
                  rw [hDec] at hSome
                  exact absurd hSome (by simp)
                | some pair =>
                  have hDec' : decode evmState.executionEnv.code evmState.pc = some pair := by
                    rw [← hZ_eEnv, ← hZ_pc]; exact hDec
                  have hPair : ((op, arg) : Operation .EVM × Option (UInt256 × Nat)) = pair := by
                    have : (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                         = pair := by rw [hDec']; rfl
                    rw [show ((op, arg) : Operation .EVM × Option (UInt256 × Nat))
                          = (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                        from hDecRes]
                    exact this
                  have hFetch : fetchInstr evmStateZ.executionEnv evmStateZ.pc = .ok pair := by
                    unfold fetchInstr
                    rw [hDec]; rfl
                  obtain ⟨op', arg'⟩ := pair
                  have hOpEq : op = op' := (Prod.mk.inj hPair).1
                  have hArgEq : arg = arg' := (Prod.mk.inj hPair).2
                  have hFetch' : fetchInstr evmStateZ.executionEnv evmStateZ.pc = .ok (op, arg) := by
                    rw [hFetch, hOpEq, hArgEq]
                  exact hOpAllowedReach evmStateZ op arg hReachZ hFetch'
              -- Discharge h_v0.
              have h_v0 : op = .CALL → evmStateZ.stack[2]? = some ⟨0⟩ := by
                intro hOpCall
                cases hDec : decode evmStateZ.executionEnv.code evmStateZ.pc with
                | none =>
                  obtain ⟨_, hSome⟩ := hReach_decodeSome evmStateZ hReachZ
                  rw [hDec] at hSome
                  exact absurd hSome (by simp)
                | some pair =>
                  have hDec' : decode evmState.executionEnv.code evmState.pc = some pair := by
                    rw [← hZ_eEnv, ← hZ_pc]; exact hDec
                  have hPair : ((op, arg) : Operation .EVM × Option (UInt256 × Nat)) = pair := by
                    have : (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                         = pair := by rw [hDec']; rfl
                    rw [show ((op, arg) : Operation .EVM × Option (UInt256 × Nat))
                          = (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                        from hDecRes]
                    exact this
                  obtain ⟨op', arg'⟩ := pair
                  have hOpEq : op = op' := (Prod.mk.inj hPair).1
                  have hArgEq : arg = arg' := (Prod.mk.inj hPair).2
                  have hFetch : fetchInstr evmStateZ.executionEnv evmStateZ.pc
                              = .ok (.CALL, arg') := by
                    unfold fetchInstr
                    rw [hDec]
                    rw [hOpEq] at hOpCall
                    rw [hOpCall]
                    rfl
                  exact h_v0_Reach evmStateZ arg' hReachZ hFetch
              -- Discharge h_sstore_post via reachability and h_sstore_Reach.
              have hFetchOK : fetchInstr evmStateZ.executionEnv evmStateZ.pc = .ok (op, arg) := by
                cases hDec : decode evmStateZ.executionEnv.code evmStateZ.pc with
                | none =>
                  obtain ⟨_, hSome⟩ := hReach_decodeSome evmStateZ hReachZ
                  rw [hDec] at hSome
                  exact absurd hSome (by simp)
                | some pair =>
                  have hDec' : decode evmState.executionEnv.code evmState.pc = some pair := by
                    rw [← hZ_eEnv, ← hZ_pc]; exact hDec
                  have hPair : ((op, arg) : Operation .EVM × Option (UInt256 × Nat)) = pair := by
                    have : (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                         = pair := by rw [hDec']; rfl
                    rw [show ((op, arg) : Operation .EVM × Option (UInt256 × Nat))
                          = (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                        from hDecRes]
                    exact this
                  obtain ⟨op', arg'⟩ := pair
                  have hOpEq : op = op' := (Prod.mk.inj hPair).1
                  have hArgEq : arg = arg' := (Prod.mk.inj hPair).2
                  unfold fetchInstr; rw [hDec, hOpEq, hArgEq]; rfl
              have hStep' : EVM.step (f'' + 1) cost₂ (some (op, arg)) evmStateZ
                          = .ok sstepState := hStep
              have h_sstore_post : op = .StackMemFlow .SSTORE →
                  StorageSumLeBalance sstepState.accountMap C := by
                intro hOpSStore
                rw [hOpSStore] at hFetchOK hStep'
                exact h_sstore_Reach evmStateZ sstepState f'' cost₂ arg
                  hReachZ hWFZ hCCZ hInvZ hFetchOK hStep'
              have hBundle :=
                step_bundled_invariant_at_C_invariant_at_C OpAllowedSet C f'' cost₂ arg op
                  evmStateZ sstepState
                  hWFZ hCCZ hNCZ hAtCFrameAtSuccF' hFrameAtSuccF' hInvZ
                  hAllowed hDischarge h_v0 h_sstore_post hStep'
              obtain ⟨hInvSstep, hWFsstep, hCCsstep, hNCsstep⟩ := hBundle
              have hReachStep : Reachable sstepState :=
                hReach_step evmStateZ sstepState f'' cost₂ op arg hReachZ hFetchOK hStep'
              split at hXres
              case h_1 _ hH_none =>
                have hFrame' : ∀ f'_1, f'_1 ≤ (f'' + 1) → ΞInvariantFrameAtC C f'_1 :=
                  fun f1 h1 =>
                    ΞInvariantFrameAtC_mono C ((f'' + 1) + 1) f1
                      (Nat.le_trans h1 (Nat.le_succ _)) _hFrameAtSucc
                have hAtCFrame' : ∀ f'_1, f'_1 ≤ (f'' + 1) → ΞInvariantAtCFrame C f'_1 :=
                  fun f1 h1 =>
                    ΞInvariantAtCFrame_mono C ((f'' + 1) + 1) f1
                      (Nat.le_trans h1 (Nat.le_succ _)) _hAtCFrameAtSucc
                have IH' : ∀ evmState',
                    X_inv_at_C_invariant OpAllowedSet C (f'' + 1) validJumps Reachable evmState' :=
                  fun es => IH es hAtCFrame' hFrame'
                have hIH := IH' sstepState hWFsstep hCCsstep hNCsstep hAtCFrameAtSuccF'
                                hFrameAtSuccF' hInvSstep hReachStep hReach_Z hReach_step
                                hReach_decodeSome hOpAllowedReach hDischarge h_v0_Reach
                                h_sstore_Reach
                rw [hXres] at hIH
                exact hIH
              case h_2 _ o hH_some =>
                split at hXres
                case isTrue _ => exact absurd hXres (by simp)
                case isFalse _ =>
                  injection hXres with hXres_inj
                  injection hXres_inj with hfin _
                  subst hfin
                  exact ⟨hInvSstep, hWFsstep, hNCsstep⟩

/-- **Consumer-facing entry point for `ΞPreservesInvariantAtC` (§H.2).**

Mirror of §G.1's `ΞPreservesAtC_of_Reachable_general` for the
`StorageSumLeBalance` chain. Per-bytecode entry point: a consumer
supplies a `Reachable` predicate witnessing that the bytecode trace at
`C` stays inside an op-whitelist (strict-handled / `.CALL` /
`.StackMemFlow .SSTORE`), only emits CALL with `stack[2] = 0`, and
preserves `StorageSumLeBalance` per-step at SSTORE.

The proof structure mirrors `ΞPreservesAtC_of_Reachable_general`:
strong fuel induction, with the IH supplying `ΞInvariantAtCFrame C f`
at all `f ≤ n` directly and `ΞInvariantFrameAtC C f'` via the
bounded-witness conversion through `Ξ_invariant_preserved_bundled_bdd`.
The at-`C` X-induction step uses `X_inv_at_C_invariant_holds`. -/
theorem ΞPreservesInvariantAtC_of_Reachable_general
    (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress)
    (Reachable : EVM.State → Prop)
    (hReach_Z : ∀ s : EVM.State, ∀ g : UInt256, Reachable s →
        Reachable { s with gasAvailable := g })
    (hReach_step : ∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ op arg, Reachable s →
        fetchInstr s.executionEnv s.pc = .ok (op, arg) →
        EVM.step (f' + 1) cost (some (op, arg)) s = .ok s' →
        Reachable s')
    (hReach_decodeSome : ∀ s : EVM.State, Reachable s →
        ∃ pair, decode s.executionEnv.code s.pc = some pair)
    (hReach_op : ∀ s : EVM.State, ∀ op : Operation .EVM, ∀ arg, Reachable s →
        fetchInstr s.executionEnv s.pc = .ok (op, arg) →
        OpAllowedSet op)
    (hDischarge : ∀ op', OpAllowedSet op' →
        strictlyPreservesAccountMap op' ∨ op' = .CALL ∨
        op' = .StackMemFlow .SSTORE)
    (hReach_v0 : ∀ s : EVM.State, ∀ arg, Reachable s →
        fetchInstr s.executionEnv s.pc = .ok (.CALL, arg) →
        s.stack[2]? = some ⟨0⟩)
    (hReach_sstore : ∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ arg,
        Reachable s →
        StateWF s.accountMap →
        C = s.executionEnv.codeOwner →
        StorageSumLeBalance s.accountMap C →
        fetchInstr s.executionEnv s.pc = .ok (.StackMemFlow .SSTORE, arg) →
        EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s' →
        StorageSumLeBalance s'.accountMap C)
    (hReachInit : ∀ (cA : RBSet AccountAddress compare)
                    (gbh : BlockHeader) (bs : ProcessedBlocks)
                    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
                    (I : ExecutionEnv .EVM),
        I.codeOwner = C →
        Reachable
          { (default : EVM.State) with
              accountMap := σ
              σ₀ := σ₀
              executionEnv := I
              substate := A
              createdAccounts := cA
              gasAvailable := g
              blocks := bs
              genesisBlockHeader := gbh }) :
    ΞPreservesInvariantAtC C := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro cA gbh bs σ σ₀ g A I hWF hCO hNC hInv
    match n with
    | 0 =>
      rw [show EVM.Ξ 0 cA gbh bs σ σ₀ g A I = .error .OutOfFuel from rfl]
      trivial
    | f + 1 =>
      -- Strong IH gives `ΞInvariantAtCFrame C f'` at all f' ≤ f.
      have hAtCBdd : ∀ f', f' ≤ f → ΞInvariantAtCFrame C f' := by
        intro f' hf'
        intro f'' hf'' cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO'' hNC'' hInv''
        have hlt : f'' < f + 1 := Nat.lt_succ_of_le (Nat.le_trans hf'' hf')
        exact IH f'' hlt cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO'' hNC'' hInv''
      -- Derive `ΞInvariantFrameAtC C f'` for f' ≤ f.
      have Ξ_frame_at : ∀ f', f' ≤ f → ΞInvariantFrameAtC C f' := by
        intro f' hf'
        intro f'' hf'' cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO_ne'' hNC'' hInv''
        have hf''_le_f : f'' ≤ f := Nat.le_trans hf'' hf'
        have hAtCSub : ∀ k, k < f'' → ΞInvariantAtCFrame C k := by
          intro k hk
          have : k ≤ f := by omega
          exact hAtCBdd k this
        exact Ξ_invariant_preserved_bundled_bdd C f'' hAtCSub
          cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO_ne'' hNC'' hInv''
      have hΞ_eq :
          EVM.Ξ (f + 1) cA gbh bs σ σ₀ g A I
            = (do
                let defState : EVM.State := default
                let freshEvmState : EVM.State :=
                  { defState with
                      accountMap := σ
                      σ₀ := σ₀
                      executionEnv := I
                      substate := A
                      createdAccounts := cA
                      gasAvailable := g
                      blocks := bs
                      genesisBlockHeader := gbh }
                let result ← EVM.X f (D_J I.code ⟨0⟩) freshEvmState
                match result with
                | .success evmState' o =>
                  let finalGas := evmState'.gasAvailable
                  .ok (ExecutionResult.success
                    (evmState'.createdAccounts, evmState'.accountMap,
                     finalGas, evmState'.substate) o)
                | .revert g' o => .ok (ExecutionResult.revert g' o)) := rfl
      rw [hΞ_eq]
      simp only [bind, Except.bind]
      generalize hXres : EVM.X f (D_J I.code ⟨0⟩) _ = xRes
      set freshState : EVM.State :=
        { (default : EVM.State) with
            accountMap := σ
            σ₀ := σ₀
            executionEnv := I
            substate := A
            createdAccounts := cA
            gasAvailable := g
            blocks := bs
            genesisBlockHeader := gbh } with hFresh_def
      have hWFFresh : StateWF freshState.accountMap := hWF
      have hCCFresh : C = freshState.executionEnv.codeOwner := hCO.symm
      have hNCFresh : ∀ a ∈ freshState.createdAccounts, a ≠ C := hNC
      have hInvFresh : StorageSumLeBalance freshState.accountMap C := hInv
      have hReachFresh : Reachable freshState :=
        hReachInit cA gbh bs σ σ₀ g A I hCO
      have hAtCBddF : ΞInvariantAtCFrame C f := hAtCBdd f (Nat.le_refl _)
      have Ξ_frame_atF : ΞInvariantFrameAtC C f := Ξ_frame_at f (Nat.le_refl _)
      have hXinv : X_inv_at_C_invariant OpAllowedSet C f (D_J I.code ⟨0⟩) Reachable freshState :=
        X_inv_at_C_invariant_holds OpAllowedSet C f (D_J I.code ⟨0⟩) Reachable freshState
          hAtCBdd Ξ_frame_at
      unfold X_inv_at_C_invariant at hXinv
      have hRes := hXinv hWFFresh hCCFresh hNCFresh hAtCBddF Ξ_frame_atF hInvFresh
        hReachFresh hReach_Z hReach_step hReach_decodeSome hReach_op hDischarge
        hReach_v0 hReach_sstore
      rw [hXres] at hRes
      cases xRes with
      | error _ => trivial
      | ok er =>
        cases er with
        | success evmState' out =>
          exact hRes
        | revert _ _ => trivial

/-! ## §H.2 — CALL-dispatch consumer entry

The `ΞPreservesInvariantAtC_of_Reachable_general` consumer entry above
hard-codes the at-`C` CALL arm to require `stack[2]? = some 0`. A
CEI-pattern withdraw block calls with a non-zero value `x` (the user's
withdrawal amount) but with the slot pre-decremented before the CALL,
so v=0 is not universally available.

The dispatch variant below takes a **per-state CALL dispatcher** in
place of `hReach_v0`. At each reachable state where the fetched
instruction is `.CALL` and a step has produced a successor state, the
consumer chooses one of two routes:

* `Or.inl`: `stack[2]? = some 0` — re-uses the existing v=0 routing.
* `Or.inr`: a complete post-CALL bundle — the consumer derives this
  themselves (typically via `call_invariant_preserved` with concrete
  slack at that PC).

This is the entry consumed by the per-PC bytecode walk for an at-`C`
CALL where the slack `v.toNat + storageSum σ C ≤ balanceOf σ C` holds
via the preceding SSTORE decrement (or alternatively where the
recipient `≠ C` so the at-C debit case never fires). -/

private theorem step_bundled_invariant_at_C_invariant_at_C_dispatch
    (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress) (f : ℕ) (cost₂ : ℕ) (arg : Option (UInt256 × Nat))
    (op : Operation .EVM)
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCC : C = evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C (f + 1))
    (hFrame : ΞInvariantFrameAtC C (f + 1))
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hAllowed : OpAllowedSet op)
    (hDischarge : ∀ op', OpAllowedSet op' →
        strictlyPreservesAccountMap op' ∨ op' = .CALL ∨
        op' = .StackMemFlow .SSTORE)
    (h_call_dispatch : op = .CALL →
        evmState.stack[2]? = some ⟨0⟩ ∨
        (StorageSumLeBalance sstepState.accountMap C ∧
         StateWF sstepState.accountMap ∧
         C = sstepState.executionEnv.codeOwner ∧
         (∀ a ∈ sstepState.createdAccounts, a ≠ C)))
    (h_sstore_post : op = .StackMemFlow .SSTORE →
        StorageSumLeBalance sstepState.accountMap C)
    (hStep : EVM.step (f + 1) cost₂ (some (op, arg)) evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C = sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  rcases hDischarge op hAllowed with hStrict | hCall | hSStore
  · -- Strict-handled op.
    exact step_handled_strict_helper_at_C_invariant op C f cost₂ arg evmState sstepState
      hWF hCC hNC hInv hStrict hStep
  · -- CALL: dispatcher chooses between v=0 path and direct bundle.
    subst hCall
    rcases h_call_dispatch rfl with h_v0 | h_bundle
    · exact step_CALL_arm_at_C_v0_invariant C f cost₂ arg evmState sstepState
        hWF hCC hNC hAtCFrame hFrame hInv h_v0 hStep
    · exact h_bundle
  · -- SSTORE: same as the non-dispatch variant.
    subst hSStore
    have hInvres : StorageSumLeBalance sstepState.accountMap C := h_sstore_post rfl
    have hHandled : handledByEvmYulStep (.StackMemFlow .SSTORE : Operation .EVM) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
    have hSDne : (.StackMemFlow .SSTORE : Operation .EVM) ≠ .SELFDESTRUCT := by decide
    set s_pre : EVM.State :=
      { evmState with
          execLength := evmState.execLength + 1,
          gasAvailable := evmState.gasAvailable - UInt256.ofNat cost₂ }
      with hs_pre_def
    have hAM : s_pre.accountMap = evmState.accountMap := rfl
    have hCOEq : s_pre.executionEnv = evmState.executionEnv := rfl
    have hCAEq : s_pre.createdAccounts = evmState.createdAccounts := rfl
    have hWF_pre : StateWF s_pre.accountMap := by rw [hAM]; exact hWF
    have hStep' : EvmYul.step (.StackMemFlow .SSTORE : Operation .EVM) arg s_pre
                = .ok sstepState := by
      unfold EVM.step at hStep
      simp only [bind, Except.bind, pure, Except.pure] at hStep
      exact hStep
    have hWFres : StateWF sstepState.accountMap :=
      EvmYul_step_preserves_StateWF (.StackMemFlow .SSTORE) arg s_pre sstepState
        hHandled hSDne hStep' hWF_pre
    have hEnvCA :=
      EvmYul.step_preserves_eEnv_cA (.StackMemFlow .SSTORE) arg s_pre sstepState
        hHandled hStep'
    refine ⟨hInvres, hWFres, ?_, ?_⟩
    · rw [hEnvCA.1, hCOEq]; exact hCC
    · intro a haIn
      rw [hEnvCA.2, hCAEq] at haIn
      exact hNC a haIn

/-- **Slack-based variant of `step_bundled_invariant_at_C_invariant_at_C_dispatch`.**

Same as the v=0/bundle dispatch, but the CALL arm takes a per-state
*slack-precondition* callback `h_call_pre_slack` — which (given the
seven popped CALL parameters and the residual stack tail) supplies the
three preconditions of `call_invariant_preserved` (no-wrap, sender
funds, slack). The IHs `hAtCFrame`/`hFrame` are threaded through
`step_CALL_arm_at_C_slack_invariant`, so the consumer never sees them.

This admits non-zero CALL `v` via the slack inequality
`v + storageSum ≤ balanceOf` — the SSTORE-decrement fact preceding
the outbound CALL in a CEI-pattern withdraw block. -/
private theorem step_bundled_invariant_at_C_invariant_at_C_slack_dispatch
    (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress) (f : ℕ) (cost₂ : ℕ) (arg : Option (UInt256 × Nat))
    (op : Operation .EVM)
    (evmState sstepState : EVM.State)
    (hWF : StateWF evmState.accountMap)
    (hCC : C = evmState.executionEnv.codeOwner)
    (hNC : ∀ a ∈ evmState.createdAccounts, a ≠ C)
    (hAtCFrame : ΞInvariantAtCFrame C (f + 1))
    (hFrame : ΞInvariantFrameAtC C (f + 1))
    (hInv : StorageSumLeBalance evmState.accountMap C)
    (hAllowed : OpAllowedSet op)
    (hDischarge : ∀ op', OpAllowedSet op' →
        strictlyPreservesAccountMap op' ∨ op' = .CALL ∨
        op' = .StackMemFlow .SSTORE)
    (h_call_pre_slack : op = .CALL →
        ∀ (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256) (tl : Stack UInt256),
          evmState.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: tl →
          (∀ acc,
              evmState.accountMap.find? (AccountAddress.ofUInt256 μ₁) = some acc →
              acc.balance.toNat + μ₂.toNat < UInt256.size) ∧
          (μ₂ = ⟨0⟩ ∨ ∃ acc,
              evmState.accountMap.find?
                  (AccountAddress.ofUInt256
                    (.ofNat evmState.executionEnv.codeOwner)) = some acc ∧
              μ₂.toNat ≤ acc.balance.toNat) ∧
          (C ≠ AccountAddress.ofUInt256
                  (.ofNat evmState.executionEnv.codeOwner) ∨
           μ₂ = ⟨0⟩ ∨
           μ₂.toNat + storageSum evmState.accountMap C
             ≤ balanceOf evmState.accountMap C))
    (h_sstore_post : op = .StackMemFlow .SSTORE →
        StorageSumLeBalance sstepState.accountMap C)
    (hStep : EVM.step (f + 1) cost₂ (some (op, arg)) evmState = .ok sstepState) :
    StorageSumLeBalance sstepState.accountMap C ∧
    StateWF sstepState.accountMap ∧
    (C = sstepState.executionEnv.codeOwner) ∧
    (∀ a ∈ sstepState.createdAccounts, a ≠ C) := by
  rcases hDischarge op hAllowed with hStrict | hCall | hSStore
  · -- Strict-handled op.
    exact step_handled_strict_helper_at_C_invariant op C f cost₂ arg evmState sstepState
      hWF hCC hNC hInv hStrict hStep
  · -- CALL: route through the slack helper.
    subst hCall
    exact step_CALL_arm_at_C_slack_invariant C f cost₂ arg evmState sstepState
      hWF hCC hNC hAtCFrame hFrame hInv (h_call_pre_slack rfl) hStep
  · -- SSTORE: same as the non-dispatch variant.
    subst hSStore
    have hInvres : StorageSumLeBalance sstepState.accountMap C := h_sstore_post rfl
    have hHandled : handledByEvmYulStep (.StackMemFlow .SSTORE : Operation .EVM) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
    have hSDne : (.StackMemFlow .SSTORE : Operation .EVM) ≠ .SELFDESTRUCT := by decide
    set s_pre : EVM.State :=
      { evmState with
          execLength := evmState.execLength + 1,
          gasAvailable := evmState.gasAvailable - UInt256.ofNat cost₂ }
      with hs_pre_def
    have hAM : s_pre.accountMap = evmState.accountMap := rfl
    have hCOEq : s_pre.executionEnv = evmState.executionEnv := rfl
    have hCAEq : s_pre.createdAccounts = evmState.createdAccounts := rfl
    have hWF_pre : StateWF s_pre.accountMap := by rw [hAM]; exact hWF
    have hStep' : EvmYul.step (.StackMemFlow .SSTORE : Operation .EVM) arg s_pre
                = .ok sstepState := by
      unfold EVM.step at hStep
      simp only [bind, Except.bind, pure, Except.pure] at hStep
      exact hStep
    have hWFres : StateWF sstepState.accountMap :=
      EvmYul_step_preserves_StateWF (.StackMemFlow .SSTORE) arg s_pre sstepState
        hHandled hSDne hStep' hWF_pre
    have hEnvCA :=
      EvmYul.step_preserves_eEnv_cA (.StackMemFlow .SSTORE) arg s_pre sstepState
        hHandled hStep'
    refine ⟨hInvres, hWFres, ?_, ?_⟩
    · rw [hEnvCA.1, hCOEq]; exact hCC
    · intro a haIn
      rw [hEnvCA.2, hCAEq] at haIn
      exact hNC a haIn

/-- **Dispatch X-induction predicate.** Mirror of `X_inv_at_C_invariant`
with the `h_v0` hypothesis replaced by a per-state CALL dispatcher. The
step-closure obligation is restricted to non-halt ops (op ∉ {RETURN,
REVERT, STOP, SELFDESTRUCT}), since halt ops cause X to exit the X loop
without recursing — so the post-halt state's reachability is never
needed downstream. -/
private def X_inv_at_C_invariant_dispatch (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress) (f : ℕ) (validJumps : Array UInt256)
    (Reachable : EVM.State → Prop)
    (evmState : EVM.State) : Prop :=
  StateWF evmState.accountMap →
  C = evmState.executionEnv.codeOwner →
  (∀ a ∈ evmState.createdAccounts, a ≠ C) →
  ΞInvariantAtCFrame C f →
  ΞInvariantFrameAtC C f →
  StorageSumLeBalance evmState.accountMap C →
  Reachable evmState →
  (∀ s : EVM.State, ∀ g : UInt256, Reachable s →
      Reachable { s with gasAvailable := g }) →
  (∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ op arg, Reachable s →
      fetchInstr s.executionEnv s.pc = .ok (op, arg) →
      EVM.step (f' + 1) cost (some (op, arg)) s = .ok s' →
      op ≠ .RETURN → op ≠ .REVERT → op ≠ .STOP → op ≠ .SELFDESTRUCT →
      Reachable s') →
  (∀ s : EVM.State, Reachable s →
      ∃ pair, decode s.executionEnv.code s.pc = some pair) →
  (∀ s : EVM.State, ∀ op : Operation .EVM, ∀ arg,
    Reachable s →
    fetchInstr s.executionEnv s.pc = .ok (op, arg) →
    OpAllowedSet op) →
  (∀ op', OpAllowedSet op' →
    strictlyPreservesAccountMap op' ∨ op' = .CALL ∨
    op' = .StackMemFlow .SSTORE) →
  -- Per-state CALL dispatcher: at each reachable CALL site with a
  -- successful step, choose between v=0 routing and direct bundle.
  (∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ arg,
    Reachable s →
    StateWF s.accountMap →
    C = s.executionEnv.codeOwner →
    (∀ a ∈ s.createdAccounts, a ≠ C) →
    StorageSumLeBalance s.accountMap C →
    fetchInstr s.executionEnv s.pc = .ok (.CALL, arg) →
    EVM.step (f' + 1) cost (some (.CALL, arg)) s = .ok s' →
    s.stack[2]? = some ⟨0⟩ ∨
    (StorageSumLeBalance s'.accountMap C ∧ StateWF s'.accountMap ∧
     C = s'.executionEnv.codeOwner ∧
     (∀ a ∈ s'.createdAccounts, a ≠ C))) →
  (∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ arg,
    Reachable s →
    StateWF s.accountMap →
    C = s.executionEnv.codeOwner →
    StorageSumLeBalance s.accountMap C →
    fetchInstr s.executionEnv s.pc = .ok (.StackMemFlow .SSTORE, arg) →
    EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s' →
    StorageSumLeBalance s'.accountMap C) →
  match EVM.X f validJumps evmState with
  | .ok (.success s' _) =>
      StorageSumLeBalance s'.accountMap C ∧
      StateWF s'.accountMap ∧
      (∀ a ∈ s'.createdAccounts, a ≠ C)
  | _ => True

/-- **Fuel induction for `X_inv_at_C_invariant_dispatch`.** Mirror of
`X_inv_at_C_invariant_holds` with the dispatcher in place of
`h_v0_Reach`. -/
private theorem X_inv_at_C_invariant_holds_dispatch
    (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress) (f : ℕ) (validJumps : Array UInt256)
    (Reachable : EVM.State → Prop)
    (evmState : EVM.State)
    (hAtCFrameAll : ∀ f', f' ≤ f → ΞInvariantAtCFrame C f')
    (hFrame : ∀ f', f' ≤ f → ΞInvariantFrameAtC C f') :
    X_inv_at_C_invariant_dispatch OpAllowedSet C f validJumps Reachable evmState := by
  induction f generalizing evmState with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [show EVM.X 0 validJumps evmState = .error .OutOfFuel from rfl]
    trivial
  | succ f' IH =>
    intro hWF hCC hNC _hAtCFrameAtSucc _hFrameAtSucc hInv
            hReach hReach_Z hReach_step hReach_decodeSome
            hOpAllowedReach hDischarge h_call_Reach h_sstore_Reach
    show match EVM.X (f' + 1) validJumps evmState with
      | .ok (.success s' _) =>
          StorageSumLeBalance s'.accountMap C ∧
          StateWF s'.accountMap ∧
          (∀ a ∈ s'.createdAccounts, a ≠ C)
      | _ => True
    generalize hXres : EVM.X (f' + 1) validJumps evmState = xRes
    cases xRes with
    | error _ => trivial
    | ok er =>
      cases er with
      | revert _ _ => trivial
      | success finalState out =>
        simp only [EVM.X] at hXres
        split at hXres
        case h_1 _ _ => exact absurd hXres (by simp)
        case h_2 _ evmStateZ cost₂ hZ =>
          have hZ_full :
              evmStateZ = { evmState with gasAvailable := evmStateZ.gasAvailable } := by
            simp only [bind, Except.bind, pure, Except.pure] at hZ
            by_cases hc1 : evmState.gasAvailable.toNat < memoryExpansionCost evmState ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1
            · rw [if_pos hc1] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc1] at hZ
            set evmState' : EVM.State :=
              { evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1) } with hevmState'
            by_cases hc2 : evmState'.gasAvailable.toNat < C' evmState' ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1
            · rw [if_pos hc2] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc2] at hZ
            by_cases hc3 : δ ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1 = none
            · rw [if_pos hc3] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc3] at hZ
            by_cases hc4 : evmState'.stack.length < (δ ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1).getD 0
            · rw [if_pos hc4] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc4] at hZ
            (split_ifs at hZ;
              first
              | exact Except.noConfusion hZ
              | (injection hZ with h_inj
                 injection h_inj with h_inj1 _
                 subst h_inj1
                 rfl))
          have hZ_accMap : evmStateZ.accountMap = evmState.accountMap := by rw [hZ_full]
          have hZ_eEnv : evmStateZ.executionEnv = evmState.executionEnv := by rw [hZ_full]
          have hZ_cA : evmStateZ.createdAccounts = evmState.createdAccounts := by rw [hZ_full]
          have hZ_pc : evmStateZ.pc = evmState.pc := by rw [hZ_full]
          have hWFZ : StateWF evmStateZ.accountMap := by rw [hZ_accMap]; exact hWF
          have hCCZ : C = evmStateZ.executionEnv.codeOwner := by
            rw [hZ_eEnv]; exact hCC
          have hNCZ : ∀ a ∈ evmStateZ.createdAccounts, a ≠ C := by
            rw [hZ_cA]; exact hNC
          have hInvZ : StorageSumLeBalance evmStateZ.accountMap C := by rw [hZ_accMap]; exact hInv
          have hReachZ : Reachable evmStateZ := by
            rw [hZ_full]
            exact hReach_Z evmState evmStateZ.gasAvailable hReach
          simp only [bind, Except.bind] at hXres
          split at hXres
          case h_1 _ _ => exact absurd hXres (by simp)
          case h_2 _ sstepState hStep =>
            match f' with
            | 0 =>
              simp only [EVM.step] at hStep
              exact absurd hStep (by simp)
            | f'' + 1 =>
              set decRes : Operation .EVM × Option (UInt256 × Nat) :=
                (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none) with hDecRes
              obtain ⟨op, arg⟩ := decRes
              have hFrameAtSuccF' : ΞInvariantFrameAtC C (f'' + 1) :=
                ΞInvariantFrameAtC_mono C ((f'' + 1) + 1) (f'' + 1) (Nat.le_succ _) _hFrameAtSucc
              have hAtCFrameAtSuccF' : ΞInvariantAtCFrame C (f'' + 1) :=
                ΞInvariantAtCFrame_mono C ((f'' + 1) + 1) (f'' + 1) (Nat.le_succ _) _hAtCFrameAtSucc
              have hAllowed : OpAllowedSet op := by
                cases hDec : decode evmStateZ.executionEnv.code evmStateZ.pc with
                | none =>
                  obtain ⟨_, hSome⟩ := hReach_decodeSome evmStateZ hReachZ
                  rw [hDec] at hSome
                  exact absurd hSome (by simp)
                | some pair =>
                  have hDec' : decode evmState.executionEnv.code evmState.pc = some pair := by
                    rw [← hZ_eEnv, ← hZ_pc]; exact hDec
                  have hPair : ((op, arg) : Operation .EVM × Option (UInt256 × Nat)) = pair := by
                    have : (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                         = pair := by rw [hDec']; rfl
                    rw [show ((op, arg) : Operation .EVM × Option (UInt256 × Nat))
                          = (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                        from hDecRes]
                    exact this
                  have hFetch : fetchInstr evmStateZ.executionEnv evmStateZ.pc = .ok pair := by
                    unfold fetchInstr
                    rw [hDec]; rfl
                  obtain ⟨op', arg'⟩ := pair
                  have hOpEq : op = op' := (Prod.mk.inj hPair).1
                  have hArgEq : arg = arg' := (Prod.mk.inj hPair).2
                  have hFetch' : fetchInstr evmStateZ.executionEnv evmStateZ.pc = .ok (op, arg) := by
                    rw [hFetch, hOpEq, hArgEq]
                  exact hOpAllowedReach evmStateZ op arg hReachZ hFetch'
              have hFetchOK : fetchInstr evmStateZ.executionEnv evmStateZ.pc = .ok (op, arg) := by
                cases hDec : decode evmStateZ.executionEnv.code evmStateZ.pc with
                | none =>
                  obtain ⟨_, hSome⟩ := hReach_decodeSome evmStateZ hReachZ
                  rw [hDec] at hSome
                  exact absurd hSome (by simp)
                | some pair =>
                  have hDec' : decode evmState.executionEnv.code evmState.pc = some pair := by
                    rw [← hZ_eEnv, ← hZ_pc]; exact hDec
                  have hPair : ((op, arg) : Operation .EVM × Option (UInt256 × Nat)) = pair := by
                    have : (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                         = pair := by rw [hDec']; rfl
                    rw [show ((op, arg) : Operation .EVM × Option (UInt256 × Nat))
                          = (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                        from hDecRes]
                    exact this
                  obtain ⟨op', arg'⟩ := pair
                  have hOpEq : op = op' := (Prod.mk.inj hPair).1
                  have hArgEq : arg = arg' := (Prod.mk.inj hPair).2
                  unfold fetchInstr; rw [hDec, hOpEq, hArgEq]; rfl
              have hStep' : EVM.step (f'' + 1) cost₂ (some (op, arg)) evmStateZ
                          = .ok sstepState := hStep
              -- Discharge h_call_dispatch via the per-state dispatcher.
              have h_call_dispatch_op :
                  op = .CALL →
                    evmStateZ.stack[2]? = some ⟨0⟩ ∨
                    (StorageSumLeBalance sstepState.accountMap C ∧
                     StateWF sstepState.accountMap ∧
                     C = sstepState.executionEnv.codeOwner ∧
                     (∀ a ∈ sstepState.createdAccounts, a ≠ C)) := by
                intro hOpCall
                rw [hOpCall] at hFetchOK hStep'
                exact h_call_Reach evmStateZ sstepState f'' cost₂ arg
                  hReachZ hWFZ hCCZ hNCZ hInvZ hFetchOK hStep'
              have h_sstore_post : op = .StackMemFlow .SSTORE →
                  StorageSumLeBalance sstepState.accountMap C := by
                intro hOpSStore
                rw [hOpSStore] at hFetchOK hStep'
                exact h_sstore_Reach evmStateZ sstepState f'' cost₂ arg
                  hReachZ hWFZ hCCZ hInvZ hFetchOK hStep'
              have hBundle :=
                step_bundled_invariant_at_C_invariant_at_C_dispatch OpAllowedSet C f'' cost₂ arg op
                  evmStateZ sstepState
                  hWFZ hCCZ hNCZ hAtCFrameAtSuccF' hFrameAtSuccF' hInvZ
                  hAllowed hDischarge h_call_dispatch_op h_sstore_post hStep'
              obtain ⟨hInvSstep, hWFsstep, hCCsstep, hNCsstep⟩ := hBundle
              split at hXres
              case h_1 _ hH_none =>
                -- H = none ⇒ op ∉ {RETURN, REVERT, STOP, SELFDESTRUCT}.
                have hOpRet : op ≠ .RETURN := by
                  intro hEq; rw [hEq] at hH_none; simp at hH_none
                have hOpRev : op ≠ .REVERT := by
                  intro hEq; rw [hEq] at hH_none; simp at hH_none
                have hOpStop : op ≠ .STOP := by
                  intro hEq; rw [hEq] at hH_none; simp at hH_none
                have hOpSD : op ≠ .SELFDESTRUCT := by
                  intro hEq; rw [hEq] at hH_none; simp at hH_none
                have hReachStep : Reachable sstepState :=
                  hReach_step evmStateZ sstepState f'' cost₂ op arg hReachZ hFetchOK hStep'
                    hOpRet hOpRev hOpStop hOpSD
                have hFrame' : ∀ f'_1, f'_1 ≤ (f'' + 1) → ΞInvariantFrameAtC C f'_1 :=
                  fun f1 h1 =>
                    ΞInvariantFrameAtC_mono C ((f'' + 1) + 1) f1
                      (Nat.le_trans h1 (Nat.le_succ _)) _hFrameAtSucc
                have hAtCFrame' : ∀ f'_1, f'_1 ≤ (f'' + 1) → ΞInvariantAtCFrame C f'_1 :=
                  fun f1 h1 =>
                    ΞInvariantAtCFrame_mono C ((f'' + 1) + 1) f1
                      (Nat.le_trans h1 (Nat.le_succ _)) _hAtCFrameAtSucc
                have IH' : ∀ evmState',
                    X_inv_at_C_invariant_dispatch OpAllowedSet C (f'' + 1) validJumps Reachable evmState' :=
                  fun es => IH es hAtCFrame' hFrame'
                have hIH := IH' sstepState hWFsstep hCCsstep hNCsstep hAtCFrameAtSuccF'
                                hFrameAtSuccF' hInvSstep hReachStep hReach_Z hReach_step
                                hReach_decodeSome hOpAllowedReach hDischarge h_call_Reach
                                h_sstore_Reach
                rw [hXres] at hIH
                exact hIH
              case h_2 _ o hH_some =>
                split at hXres
                case isTrue _ => exact absurd hXres (by simp)
                case isFalse _ =>
                  injection hXres with hXres_inj
                  injection hXres_inj with hfin _
                  subst hfin
                  exact ⟨hInvSstep, hWFsstep, hNCsstep⟩

/-- **Consumer-facing CALL-dispatch entry point for
`ΞPreservesInvariantAtC` (§H.2).**

Sibling of `ΞPreservesInvariantAtC_of_Reachable_general` taking a
per-state CALL dispatcher in place of `hReach_v0`. The dispatcher
returns either `s.stack[2]? = some 0` (route through the existing v=0
path) or a complete post-CALL bundle (typically derived via
`call_invariant_preserved`).

This is the entry consumed by the per-PC bytecode walk for an at-`C`
CALL where the slack `v.toNat + storageSum σ C ≤ balanceOf σ C` holds
via the preceding SSTORE decrement. -/
theorem ΞPreservesInvariantAtC_of_Reachable_general_call_dispatch
    (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress)
    (Reachable : EVM.State → Prop)
    (hReach_Z : ∀ s : EVM.State, ∀ g : UInt256, Reachable s →
        Reachable { s with gasAvailable := g })
    (hReach_step : ∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ op arg, Reachable s →
        fetchInstr s.executionEnv s.pc = .ok (op, arg) →
        EVM.step (f' + 1) cost (some (op, arg)) s = .ok s' →
        op ≠ .RETURN → op ≠ .REVERT → op ≠ .STOP → op ≠ .SELFDESTRUCT →
        Reachable s')
    (hReach_decodeSome : ∀ s : EVM.State, Reachable s →
        ∃ pair, decode s.executionEnv.code s.pc = some pair)
    (hReach_op : ∀ s : EVM.State, ∀ op : Operation .EVM, ∀ arg, Reachable s →
        fetchInstr s.executionEnv s.pc = .ok (op, arg) →
        OpAllowedSet op)
    (hDischarge : ∀ op', OpAllowedSet op' →
        strictlyPreservesAccountMap op' ∨ op' = .CALL ∨
        op' = .StackMemFlow .SSTORE)
    (hReach_call : ∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ arg,
        Reachable s →
        StateWF s.accountMap →
        C = s.executionEnv.codeOwner →
        (∀ a ∈ s.createdAccounts, a ≠ C) →
        StorageSumLeBalance s.accountMap C →
        fetchInstr s.executionEnv s.pc = .ok (.CALL, arg) →
        EVM.step (f' + 1) cost (some (.CALL, arg)) s = .ok s' →
        s.stack[2]? = some ⟨0⟩ ∨
        (StorageSumLeBalance s'.accountMap C ∧ StateWF s'.accountMap ∧
         C = s'.executionEnv.codeOwner ∧
         (∀ a ∈ s'.createdAccounts, a ≠ C)))
    (hReach_sstore : ∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ arg,
        Reachable s →
        StateWF s.accountMap →
        C = s.executionEnv.codeOwner →
        StorageSumLeBalance s.accountMap C →
        fetchInstr s.executionEnv s.pc = .ok (.StackMemFlow .SSTORE, arg) →
        EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s' →
        StorageSumLeBalance s'.accountMap C)
    (hReachInit : ∀ (cA : RBSet AccountAddress compare)
                    (gbh : BlockHeader) (bs : ProcessedBlocks)
                    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
                    (I : ExecutionEnv .EVM),
        I.codeOwner = C →
        Reachable
          { (default : EVM.State) with
              accountMap := σ
              σ₀ := σ₀
              executionEnv := I
              substate := A
              createdAccounts := cA
              gasAvailable := g
              blocks := bs
              genesisBlockHeader := gbh }) :
    ΞPreservesInvariantAtC C := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro cA gbh bs σ σ₀ g A I hWF hCO hNC hInv
    match n with
    | 0 =>
      rw [show EVM.Ξ 0 cA gbh bs σ σ₀ g A I = .error .OutOfFuel from rfl]
      trivial
    | f + 1 =>
      have hAtCBdd : ∀ f', f' ≤ f → ΞInvariantAtCFrame C f' := by
        intro f' hf'
        intro f'' hf'' cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO'' hNC'' hInv''
        have hlt : f'' < f + 1 := Nat.lt_succ_of_le (Nat.le_trans hf'' hf')
        exact IH f'' hlt cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO'' hNC'' hInv''
      have Ξ_frame_at : ∀ f', f' ≤ f → ΞInvariantFrameAtC C f' := by
        intro f' hf'
        intro f'' hf'' cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO_ne'' hNC'' hInv''
        have hf''_le_f : f'' ≤ f := Nat.le_trans hf'' hf'
        have hAtCSub : ∀ k, k < f'' → ΞInvariantAtCFrame C k := by
          intro k hk
          have : k ≤ f := by omega
          exact hAtCBdd k this
        exact Ξ_invariant_preserved_bundled_bdd C f'' hAtCSub
          cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO_ne'' hNC'' hInv''
      have hΞ_eq :
          EVM.Ξ (f + 1) cA gbh bs σ σ₀ g A I
            = (do
                let defState : EVM.State := default
                let freshEvmState : EVM.State :=
                  { defState with
                      accountMap := σ
                      σ₀ := σ₀
                      executionEnv := I
                      substate := A
                      createdAccounts := cA
                      gasAvailable := g
                      blocks := bs
                      genesisBlockHeader := gbh }
                let result ← EVM.X f (D_J I.code ⟨0⟩) freshEvmState
                match result with
                | .success evmState' o =>
                  let finalGas := evmState'.gasAvailable
                  .ok (ExecutionResult.success
                    (evmState'.createdAccounts, evmState'.accountMap,
                     finalGas, evmState'.substate) o)
                | .revert g' o => .ok (ExecutionResult.revert g' o)) := rfl
      rw [hΞ_eq]
      simp only [bind, Except.bind]
      generalize hXres : EVM.X f (D_J I.code ⟨0⟩) _ = xRes
      set freshState : EVM.State :=
        { (default : EVM.State) with
            accountMap := σ
            σ₀ := σ₀
            executionEnv := I
            substate := A
            createdAccounts := cA
            gasAvailable := g
            blocks := bs
            genesisBlockHeader := gbh } with hFresh_def
      have hWFFresh : StateWF freshState.accountMap := hWF
      have hCCFresh : C = freshState.executionEnv.codeOwner := hCO.symm
      have hNCFresh : ∀ a ∈ freshState.createdAccounts, a ≠ C := hNC
      have hInvFresh : StorageSumLeBalance freshState.accountMap C := hInv
      have hReachFresh : Reachable freshState :=
        hReachInit cA gbh bs σ σ₀ g A I hCO
      have hAtCBddF : ΞInvariantAtCFrame C f := hAtCBdd f (Nat.le_refl _)
      have Ξ_frame_atF : ΞInvariantFrameAtC C f := Ξ_frame_at f (Nat.le_refl _)
      have hXinv :
          X_inv_at_C_invariant_dispatch OpAllowedSet C f (D_J I.code ⟨0⟩) Reachable freshState :=
        X_inv_at_C_invariant_holds_dispatch OpAllowedSet C f (D_J I.code ⟨0⟩)
          Reachable freshState hAtCBdd Ξ_frame_at
      unfold X_inv_at_C_invariant_dispatch at hXinv
      have hRes := hXinv hWFFresh hCCFresh hNCFresh hAtCBddF Ξ_frame_atF hInvFresh
        hReachFresh hReach_Z hReach_step hReach_decodeSome hReach_op hDischarge
        hReach_call hReach_sstore
      rw [hXres] at hRes
      cases xRes with
      | error _ => trivial
      | ok er =>
        cases er with
        | success evmState' out =>
          exact hRes
        | revert _ _ => trivial

/-! ## §H.2 — Slack-based dispatch chain

Parallel chain to `_dispatch` that takes a per-state CALL slack callback
in place of the v=0/bundle dispatcher. The callback supplies the three
preconditions of `call_invariant_preserved` (no-wrap, sender funds,
slack disjunction); the IHs are threaded internally. -/

/-- **Slack-based X-induction predicate.** Mirror of
`X_inv_at_C_invariant_dispatch` with the v=0/bundle CALL dispatcher
replaced by a slack-precondition callback. -/
private def X_inv_at_C_invariant_slack_dispatch (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress) (f : ℕ) (validJumps : Array UInt256)
    (Reachable : EVM.State → Prop)
    (evmState : EVM.State) : Prop :=
  StateWF evmState.accountMap →
  C = evmState.executionEnv.codeOwner →
  (∀ a ∈ evmState.createdAccounts, a ≠ C) →
  ΞInvariantAtCFrame C f →
  ΞInvariantFrameAtC C f →
  StorageSumLeBalance evmState.accountMap C →
  Reachable evmState →
  (∀ s : EVM.State, ∀ g : UInt256, Reachable s →
      Reachable { s with gasAvailable := g }) →
  (∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ op arg, Reachable s →
      fetchInstr s.executionEnv s.pc = .ok (op, arg) →
      EVM.step (f' + 1) cost (some (op, arg)) s = .ok s' →
      op ≠ .RETURN → op ≠ .REVERT → op ≠ .STOP → op ≠ .SELFDESTRUCT →
      Reachable s') →
  (∀ s : EVM.State, Reachable s →
      ∃ pair, decode s.executionEnv.code s.pc = some pair) →
  (∀ s : EVM.State, ∀ op : Operation .EVM, ∀ arg,
    Reachable s →
    fetchInstr s.executionEnv s.pc = .ok (op, arg) →
    OpAllowedSet op) →
  (∀ op', OpAllowedSet op' →
    strictlyPreservesAccountMap op' ∨ op' = .CALL ∨
    op' = .StackMemFlow .SSTORE) →
  -- Per-state CALL slack callback. The consumer supplies the three
  -- preconditions of call_invariant_preserved, given the popped CALL
  -- parameters and the residual stack tail.
  (∀ s : EVM.State, ∀ arg,
    Reachable s →
    StateWF s.accountMap →
    C = s.executionEnv.codeOwner →
    (∀ a ∈ s.createdAccounts, a ≠ C) →
    StorageSumLeBalance s.accountMap C →
    fetchInstr s.executionEnv s.pc = .ok (.CALL, arg) →
    ∀ (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256) (tl : Stack UInt256),
      s.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: tl →
      (∀ acc,
          s.accountMap.find? (AccountAddress.ofUInt256 μ₁) = some acc →
          acc.balance.toNat + μ₂.toNat < UInt256.size) ∧
      (μ₂ = ⟨0⟩ ∨ ∃ acc,
          s.accountMap.find?
              (AccountAddress.ofUInt256
                (.ofNat s.executionEnv.codeOwner)) = some acc ∧
          μ₂.toNat ≤ acc.balance.toNat) ∧
      (C ≠ AccountAddress.ofUInt256
              (.ofNat s.executionEnv.codeOwner) ∨
       μ₂ = ⟨0⟩ ∨
       μ₂.toNat + storageSum s.accountMap C
         ≤ balanceOf s.accountMap C)) →
  (∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ arg,
    Reachable s →
    StateWF s.accountMap →
    C = s.executionEnv.codeOwner →
    StorageSumLeBalance s.accountMap C →
    fetchInstr s.executionEnv s.pc = .ok (.StackMemFlow .SSTORE, arg) →
    EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s' →
    StorageSumLeBalance s'.accountMap C) →
  match EVM.X f validJumps evmState with
  | .ok (.success s' _) =>
      StorageSumLeBalance s'.accountMap C ∧
      StateWF s'.accountMap ∧
      (∀ a ∈ s'.createdAccounts, a ≠ C)
  | _ => True

/-- **Fuel induction for `X_inv_at_C_invariant_slack_dispatch`.** Same
proof structure as `X_inv_at_C_invariant_holds_dispatch`, but the per-step
CALL arm calls `step_bundled_invariant_at_C_invariant_at_C_slack_dispatch`
in place of the `_dispatch` variant. -/
private theorem X_inv_at_C_invariant_holds_slack_dispatch
    (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress) (f : ℕ) (validJumps : Array UInt256)
    (Reachable : EVM.State → Prop)
    (evmState : EVM.State)
    (hAtCFrameAll : ∀ f', f' ≤ f → ΞInvariantAtCFrame C f')
    (hFrame : ∀ f', f' ≤ f → ΞInvariantFrameAtC C f') :
    X_inv_at_C_invariant_slack_dispatch OpAllowedSet C f validJumps Reachable evmState := by
  induction f generalizing evmState with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [show EVM.X 0 validJumps evmState = .error .OutOfFuel from rfl]
    trivial
  | succ f' IH =>
    intro hWF hCC hNC _hAtCFrameAtSucc _hFrameAtSucc hInv
            hReach hReach_Z hReach_step hReach_decodeSome
            hOpAllowedReach hDischarge h_call_slack_Reach h_sstore_Reach
    show match EVM.X (f' + 1) validJumps evmState with
      | .ok (.success s' _) =>
          StorageSumLeBalance s'.accountMap C ∧
          StateWF s'.accountMap ∧
          (∀ a ∈ s'.createdAccounts, a ≠ C)
      | _ => True
    generalize hXres : EVM.X (f' + 1) validJumps evmState = xRes
    cases xRes with
    | error _ => trivial
    | ok er =>
      cases er with
      | revert _ _ => trivial
      | success finalState out =>
        simp only [EVM.X] at hXres
        split at hXres
        case h_1 _ _ => exact absurd hXres (by simp)
        case h_2 _ evmStateZ cost₂ hZ =>
          have hZ_full :
              evmStateZ = { evmState with gasAvailable := evmStateZ.gasAvailable } := by
            simp only [bind, Except.bind, pure, Except.pure] at hZ
            by_cases hc1 : evmState.gasAvailable.toNat < memoryExpansionCost evmState ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1
            · rw [if_pos hc1] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc1] at hZ
            set evmState' : EVM.State :=
              { evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1) } with hevmState'
            by_cases hc2 : evmState'.gasAvailable.toNat < C' evmState' ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1
            · rw [if_pos hc2] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc2] at hZ
            by_cases hc3 : δ ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1 = none
            · rw [if_pos hc3] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc3] at hZ
            by_cases hc4 : evmState'.stack.length < (δ ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1).getD 0
            · rw [if_pos hc4] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc4] at hZ
            (split_ifs at hZ;
              first
              | exact Except.noConfusion hZ
              | (injection hZ with h_inj
                 injection h_inj with h_inj1 _
                 subst h_inj1
                 rfl))
          have hZ_accMap : evmStateZ.accountMap = evmState.accountMap := by rw [hZ_full]
          have hZ_eEnv : evmStateZ.executionEnv = evmState.executionEnv := by rw [hZ_full]
          have hZ_cA : evmStateZ.createdAccounts = evmState.createdAccounts := by rw [hZ_full]
          have hZ_pc : evmStateZ.pc = evmState.pc := by rw [hZ_full]
          have hWFZ : StateWF evmStateZ.accountMap := by rw [hZ_accMap]; exact hWF
          have hCCZ : C = evmStateZ.executionEnv.codeOwner := by
            rw [hZ_eEnv]; exact hCC
          have hNCZ : ∀ a ∈ evmStateZ.createdAccounts, a ≠ C := by
            rw [hZ_cA]; exact hNC
          have hInvZ : StorageSumLeBalance evmStateZ.accountMap C := by rw [hZ_accMap]; exact hInv
          have hReachZ : Reachable evmStateZ := by
            rw [hZ_full]
            exact hReach_Z evmState evmStateZ.gasAvailable hReach
          simp only [bind, Except.bind] at hXres
          split at hXres
          case h_1 _ _ => exact absurd hXres (by simp)
          case h_2 _ sstepState hStep =>
            match f' with
            | 0 =>
              simp only [EVM.step] at hStep
              exact absurd hStep (by simp)
            | f'' + 1 =>
              set decRes : Operation .EVM × Option (UInt256 × Nat) :=
                (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none) with hDecRes
              obtain ⟨op, arg⟩ := decRes
              have hFrameAtSuccF' : ΞInvariantFrameAtC C (f'' + 1) :=
                ΞInvariantFrameAtC_mono C ((f'' + 1) + 1) (f'' + 1) (Nat.le_succ _) _hFrameAtSucc
              have hAtCFrameAtSuccF' : ΞInvariantAtCFrame C (f'' + 1) :=
                ΞInvariantAtCFrame_mono C ((f'' + 1) + 1) (f'' + 1) (Nat.le_succ _) _hAtCFrameAtSucc
              have hAllowed : OpAllowedSet op := by
                cases hDec : decode evmStateZ.executionEnv.code evmStateZ.pc with
                | none =>
                  obtain ⟨_, hSome⟩ := hReach_decodeSome evmStateZ hReachZ
                  rw [hDec] at hSome
                  exact absurd hSome (by simp)
                | some pair =>
                  have hDec' : decode evmState.executionEnv.code evmState.pc = some pair := by
                    rw [← hZ_eEnv, ← hZ_pc]; exact hDec
                  have hPair : ((op, arg) : Operation .EVM × Option (UInt256 × Nat)) = pair := by
                    have : (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                         = pair := by rw [hDec']; rfl
                    rw [show ((op, arg) : Operation .EVM × Option (UInt256 × Nat))
                          = (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                        from hDecRes]
                    exact this
                  have hFetch : fetchInstr evmStateZ.executionEnv evmStateZ.pc = .ok pair := by
                    unfold fetchInstr
                    rw [hDec]; rfl
                  obtain ⟨op', arg'⟩ := pair
                  have hOpEq : op = op' := (Prod.mk.inj hPair).1
                  have hArgEq : arg = arg' := (Prod.mk.inj hPair).2
                  have hFetch' : fetchInstr evmStateZ.executionEnv evmStateZ.pc = .ok (op, arg) := by
                    rw [hFetch, hOpEq, hArgEq]
                  exact hOpAllowedReach evmStateZ op arg hReachZ hFetch'
              have hFetchOK : fetchInstr evmStateZ.executionEnv evmStateZ.pc = .ok (op, arg) := by
                cases hDec : decode evmStateZ.executionEnv.code evmStateZ.pc with
                | none =>
                  obtain ⟨_, hSome⟩ := hReach_decodeSome evmStateZ hReachZ
                  rw [hDec] at hSome
                  exact absurd hSome (by simp)
                | some pair =>
                  have hDec' : decode evmState.executionEnv.code evmState.pc = some pair := by
                    rw [← hZ_eEnv, ← hZ_pc]; exact hDec
                  have hPair : ((op, arg) : Operation .EVM × Option (UInt256 × Nat)) = pair := by
                    have : (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                         = pair := by rw [hDec']; rfl
                    rw [show ((op, arg) : Operation .EVM × Option (UInt256 × Nat))
                          = (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                        from hDecRes]
                    exact this
                  obtain ⟨op', arg'⟩ := pair
                  have hOpEq : op = op' := (Prod.mk.inj hPair).1
                  have hArgEq : arg = arg' := (Prod.mk.inj hPair).2
                  unfold fetchInstr; rw [hDec, hOpEq, hArgEq]; rfl
              have hStep' : EVM.step (f'' + 1) cost₂ (some (op, arg)) evmStateZ
                          = .ok sstepState := hStep
              -- Discharge h_call_pre_slack via the per-state slack callback.
              have h_call_pre_slack_op :
                  op = .CALL →
                    ∀ (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256) (tl : Stack UInt256),
                      evmStateZ.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: tl →
                      (∀ acc,
                          evmStateZ.accountMap.find? (AccountAddress.ofUInt256 μ₁) = some acc →
                          acc.balance.toNat + μ₂.toNat < UInt256.size) ∧
                      (μ₂ = ⟨0⟩ ∨ ∃ acc,
                          evmStateZ.accountMap.find?
                              (AccountAddress.ofUInt256
                                (.ofNat evmStateZ.executionEnv.codeOwner)) = some acc ∧
                          μ₂.toNat ≤ acc.balance.toNat) ∧
                      (C ≠ AccountAddress.ofUInt256
                              (.ofNat evmStateZ.executionEnv.codeOwner) ∨
                       μ₂ = ⟨0⟩ ∨
                       μ₂.toNat + storageSum evmStateZ.accountMap C
                         ≤ balanceOf evmStateZ.accountMap C) := by
                intro hOpCall μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
                rw [hOpCall] at hFetchOK
                exact h_call_slack_Reach evmStateZ arg hReachZ hWFZ hCCZ hNCZ hInvZ hFetchOK
                  μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
              have h_sstore_post : op = .StackMemFlow .SSTORE →
                  StorageSumLeBalance sstepState.accountMap C := by
                intro hOpSStore
                rw [hOpSStore] at hFetchOK hStep'
                exact h_sstore_Reach evmStateZ sstepState f'' cost₂ arg
                  hReachZ hWFZ hCCZ hInvZ hFetchOK hStep'
              have hBundle :=
                step_bundled_invariant_at_C_invariant_at_C_slack_dispatch OpAllowedSet C f'' cost₂ arg op
                  evmStateZ sstepState
                  hWFZ hCCZ hNCZ hAtCFrameAtSuccF' hFrameAtSuccF' hInvZ
                  hAllowed hDischarge h_call_pre_slack_op h_sstore_post hStep'
              obtain ⟨hInvSstep, hWFsstep, hCCsstep, hNCsstep⟩ := hBundle
              split at hXres
              case h_1 _ hH_none =>
                -- H = none ⇒ op ∉ {RETURN, REVERT, STOP, SELFDESTRUCT}.
                have hOpRet : op ≠ .RETURN := by
                  intro hEq; rw [hEq] at hH_none; simp at hH_none
                have hOpRev : op ≠ .REVERT := by
                  intro hEq; rw [hEq] at hH_none; simp at hH_none
                have hOpStop : op ≠ .STOP := by
                  intro hEq; rw [hEq] at hH_none; simp at hH_none
                have hOpSD : op ≠ .SELFDESTRUCT := by
                  intro hEq; rw [hEq] at hH_none; simp at hH_none
                have hReachStep : Reachable sstepState :=
                  hReach_step evmStateZ sstepState f'' cost₂ op arg hReachZ hFetchOK hStep'
                    hOpRet hOpRev hOpStop hOpSD
                have hFrame' : ∀ f'_1, f'_1 ≤ (f'' + 1) → ΞInvariantFrameAtC C f'_1 :=
                  fun f1 h1 =>
                    ΞInvariantFrameAtC_mono C ((f'' + 1) + 1) f1
                      (Nat.le_trans h1 (Nat.le_succ _)) _hFrameAtSucc
                have hAtCFrame' : ∀ f'_1, f'_1 ≤ (f'' + 1) → ΞInvariantAtCFrame C f'_1 :=
                  fun f1 h1 =>
                    ΞInvariantAtCFrame_mono C ((f'' + 1) + 1) f1
                      (Nat.le_trans h1 (Nat.le_succ _)) _hAtCFrameAtSucc
                have IH' : ∀ evmState',
                    X_inv_at_C_invariant_slack_dispatch OpAllowedSet C (f'' + 1) validJumps Reachable evmState' :=
                  fun es => IH es hAtCFrame' hFrame'
                have hIH := IH' sstepState hWFsstep hCCsstep hNCsstep hAtCFrameAtSuccF'
                                hFrameAtSuccF' hInvSstep hReachStep hReach_Z hReach_step
                                hReach_decodeSome hOpAllowedReach hDischarge h_call_slack_Reach
                                h_sstore_Reach
                rw [hXres] at hIH
                exact hIH
              case h_2 _ o hH_some =>
                split at hXres
                case isTrue _ => exact absurd hXres (by simp)
                case isFalse _ =>
                  injection hXres with hXres_inj
                  injection hXres_inj with hfin _
                  subst hfin
                  exact ⟨hInvSstep, hWFsstep, hNCsstep⟩

/-- **Slack-based consumer-facing CALL-dispatch entry point for
`ΞPreservesInvariantAtC`.**

Sibling of `ΞPreservesInvariantAtC_of_Reachable_general_call_dispatch`
taking a per-state CALL slack-precondition callback in place of the
v=0/bundle dispatcher. The callback supplies the three preconditions of
`call_invariant_preserved` (no-wrap, sender funds, slack disjunction);
the IHs are threaded internally.

This is the entry point for the at-C non-zero CALL discharger pattern:
the consumer derives the slack `v + storageSum ≤ balanceOf` per-state
from the SSTORE-decrement fact preceding the outbound CALL in a
CEI-pattern withdraw block. -/
theorem ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch
    (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress)
    (Reachable : EVM.State → Prop)
    (hReach_Z : ∀ s : EVM.State, ∀ g : UInt256, Reachable s →
        Reachable { s with gasAvailable := g })
    (hReach_step : ∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ op arg, Reachable s →
        fetchInstr s.executionEnv s.pc = .ok (op, arg) →
        EVM.step (f' + 1) cost (some (op, arg)) s = .ok s' →
        op ≠ .RETURN → op ≠ .REVERT → op ≠ .STOP → op ≠ .SELFDESTRUCT →
        Reachable s')
    (hReach_decodeSome : ∀ s : EVM.State, Reachable s →
        ∃ pair, decode s.executionEnv.code s.pc = some pair)
    (hReach_op : ∀ s : EVM.State, ∀ op : Operation .EVM, ∀ arg, Reachable s →
        fetchInstr s.executionEnv s.pc = .ok (op, arg) →
        OpAllowedSet op)
    (hDischarge : ∀ op', OpAllowedSet op' →
        strictlyPreservesAccountMap op' ∨ op' = .CALL ∨
        op' = .StackMemFlow .SSTORE)
    (hReach_call_slack : ∀ s : EVM.State, ∀ arg,
        Reachable s →
        StateWF s.accountMap →
        C = s.executionEnv.codeOwner →
        (∀ a ∈ s.createdAccounts, a ≠ C) →
        StorageSumLeBalance s.accountMap C →
        fetchInstr s.executionEnv s.pc = .ok (.CALL, arg) →
        ∀ (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256) (tl : Stack UInt256),
          s.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: tl →
          (∀ acc,
              s.accountMap.find? (AccountAddress.ofUInt256 μ₁) = some acc →
              acc.balance.toNat + μ₂.toNat < UInt256.size) ∧
          (μ₂ = ⟨0⟩ ∨ ∃ acc,
              s.accountMap.find?
                  (AccountAddress.ofUInt256
                    (.ofNat s.executionEnv.codeOwner)) = some acc ∧
              μ₂.toNat ≤ acc.balance.toNat) ∧
          (C ≠ AccountAddress.ofUInt256
                  (.ofNat s.executionEnv.codeOwner) ∨
           μ₂ = ⟨0⟩ ∨
           μ₂.toNat + storageSum s.accountMap C
             ≤ balanceOf s.accountMap C))
    (hReach_sstore : ∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ arg,
        Reachable s →
        StateWF s.accountMap →
        C = s.executionEnv.codeOwner →
        StorageSumLeBalance s.accountMap C →
        fetchInstr s.executionEnv s.pc = .ok (.StackMemFlow .SSTORE, arg) →
        EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s' →
        StorageSumLeBalance s'.accountMap C)
    (hReachInit : ∀ (cA : RBSet AccountAddress compare)
                    (gbh : BlockHeader) (bs : ProcessedBlocks)
                    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
                    (I : ExecutionEnv .EVM),
        I.codeOwner = C →
        Reachable
          { (default : EVM.State) with
              accountMap := σ
              σ₀ := σ₀
              executionEnv := I
              substate := A
              createdAccounts := cA
              gasAvailable := g
              blocks := bs
              genesisBlockHeader := gbh }) :
    ΞPreservesInvariantAtC C := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro cA gbh bs σ σ₀ g A I hWF hCO hNC hInv
    match n with
    | 0 =>
      rw [show EVM.Ξ 0 cA gbh bs σ σ₀ g A I = .error .OutOfFuel from rfl]
      trivial
    | f + 1 =>
      have hAtCBdd : ∀ f', f' ≤ f → ΞInvariantAtCFrame C f' := by
        intro f' hf'
        intro f'' hf'' cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO'' hNC'' hInv''
        have hlt : f'' < f + 1 := Nat.lt_succ_of_le (Nat.le_trans hf'' hf')
        exact IH f'' hlt cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO'' hNC'' hInv''
      have Ξ_frame_at : ∀ f', f' ≤ f → ΞInvariantFrameAtC C f' := by
        intro f' hf'
        intro f'' hf'' cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO_ne'' hNC'' hInv''
        have hf''_le_f : f'' ≤ f := Nat.le_trans hf'' hf'
        have hAtCSub : ∀ k, k < f'' → ΞInvariantAtCFrame C k := by
          intro k hk
          have : k ≤ f := by omega
          exact hAtCBdd k this
        exact Ξ_invariant_preserved_bundled_bdd C f'' hAtCSub
          cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO_ne'' hNC'' hInv''
      have hΞ_eq :
          EVM.Ξ (f + 1) cA gbh bs σ σ₀ g A I
            = (do
                let defState : EVM.State := default
                let freshEvmState : EVM.State :=
                  { defState with
                      accountMap := σ
                      σ₀ := σ₀
                      executionEnv := I
                      substate := A
                      createdAccounts := cA
                      gasAvailable := g
                      blocks := bs
                      genesisBlockHeader := gbh }
                let result ← EVM.X f (D_J I.code ⟨0⟩) freshEvmState
                match result with
                | .success evmState' o =>
                  let finalGas := evmState'.gasAvailable
                  .ok (ExecutionResult.success
                    (evmState'.createdAccounts, evmState'.accountMap,
                     finalGas, evmState'.substate) o)
                | .revert g' o => .ok (ExecutionResult.revert g' o)) := rfl
      rw [hΞ_eq]
      simp only [bind, Except.bind]
      generalize hXres : EVM.X f (D_J I.code ⟨0⟩) _ = xRes
      set freshState : EVM.State :=
        { (default : EVM.State) with
            accountMap := σ
            σ₀ := σ₀
            executionEnv := I
            substate := A
            createdAccounts := cA
            gasAvailable := g
            blocks := bs
            genesisBlockHeader := gbh } with hFresh_def
      have hWFFresh : StateWF freshState.accountMap := hWF
      have hCCFresh : C = freshState.executionEnv.codeOwner := hCO.symm
      have hNCFresh : ∀ a ∈ freshState.createdAccounts, a ≠ C := hNC
      have hInvFresh : StorageSumLeBalance freshState.accountMap C := hInv
      have hReachFresh : Reachable freshState :=
        hReachInit cA gbh bs σ σ₀ g A I hCO
      have hAtCBddF : ΞInvariantAtCFrame C f := hAtCBdd f (Nat.le_refl _)
      have Ξ_frame_atF : ΞInvariantFrameAtC C f := Ξ_frame_at f (Nat.le_refl _)
      have hXinv :
          X_inv_at_C_invariant_slack_dispatch OpAllowedSet C f (D_J I.code ⟨0⟩) Reachable freshState :=
        X_inv_at_C_invariant_holds_slack_dispatch OpAllowedSet C f (D_J I.code ⟨0⟩)
          Reachable freshState hAtCBdd Ξ_frame_at
      unfold X_inv_at_C_invariant_slack_dispatch at hXinv
      have hRes := hXinv hWFFresh hCCFresh hNCFresh hAtCBddF Ξ_frame_atF hInvFresh
        hReachFresh hReach_Z hReach_step hReach_decodeSome hReach_op hDischarge
        hReach_call_slack hReach_sstore
      rw [hXres] at hRes
      cases xRes with
      | error _ => trivial
      | ok er =>
        cases er with
        | success evmState' out =>
          exact hRes
        | revert _ _ => trivial

/-! ### Invariant-aware variant of the slack-dispatch X-loop

The variant below mirrors `X_inv_at_C_invariant_slack_dispatch` /
`ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch`,
but exposes `StorageSumLeBalance s'.accountMap C` to the `hReach_step` callback
as an additional hypothesis. This is what the framework already
established internally (via `step_bundled_invariant_at_C_invariant_at_C_slack_dispatch`)
before invoking `hReach_step`, so passing it through breaks the
chicken-and-egg dependency that otherwise forces the consumer to
provide a per-step CALL invariant preservation predicate.

Consumers whose `Reachable` predicate has a closure that includes
`StorageSumLeBalance s'` can therefore be threaded through CALL steps
without needing a separate per-step CALL invariant frame assumption. -/

/-- Same as `X_inv_at_C_invariant_slack_dispatch`, but `hReach_step`
takes an additional `StorageSumLeBalance s'.accountMap C` hypothesis. -/
private def X_inv_at_C_invariant_slack_dispatch_inv_aware (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress) (f : ℕ) (validJumps : Array UInt256)
    (Reachable : EVM.State → Prop)
    (evmState : EVM.State) : Prop :=
  StateWF evmState.accountMap →
  C = evmState.executionEnv.codeOwner →
  (∀ a ∈ evmState.createdAccounts, a ≠ C) →
  ΞInvariantAtCFrame C f →
  ΞInvariantFrameAtC C f →
  StorageSumLeBalance evmState.accountMap C →
  Reachable evmState →
  (∀ s : EVM.State, ∀ g : UInt256, Reachable s →
      Reachable { s with gasAvailable := g }) →
  (∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ op arg, Reachable s →
      fetchInstr s.executionEnv s.pc = .ok (op, arg) →
      EVM.step (f' + 1) cost (some (op, arg)) s = .ok s' →
      op ≠ .RETURN → op ≠ .REVERT → op ≠ .STOP → op ≠ .SELFDESTRUCT →
      StorageSumLeBalance s'.accountMap C →
      Reachable s') →
  (∀ s : EVM.State, Reachable s →
      ∃ pair, decode s.executionEnv.code s.pc = some pair) →
  (∀ s : EVM.State, ∀ op : Operation .EVM, ∀ arg,
    Reachable s →
    fetchInstr s.executionEnv s.pc = .ok (op, arg) →
    OpAllowedSet op) →
  (∀ op', OpAllowedSet op' →
    strictlyPreservesAccountMap op' ∨ op' = .CALL ∨
    op' = .StackMemFlow .SSTORE) →
  (∀ s : EVM.State, ∀ arg,
    Reachable s →
    StateWF s.accountMap →
    C = s.executionEnv.codeOwner →
    (∀ a ∈ s.createdAccounts, a ≠ C) →
    StorageSumLeBalance s.accountMap C →
    fetchInstr s.executionEnv s.pc = .ok (.CALL, arg) →
    ∀ (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256) (tl : Stack UInt256),
      s.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: tl →
      (∀ acc,
          s.accountMap.find? (AccountAddress.ofUInt256 μ₁) = some acc →
          acc.balance.toNat + μ₂.toNat < UInt256.size) ∧
      (μ₂ = ⟨0⟩ ∨ ∃ acc,
          s.accountMap.find?
              (AccountAddress.ofUInt256
                (.ofNat s.executionEnv.codeOwner)) = some acc ∧
          μ₂.toNat ≤ acc.balance.toNat) ∧
      (C ≠ AccountAddress.ofUInt256
              (.ofNat s.executionEnv.codeOwner) ∨
       μ₂ = ⟨0⟩ ∨
       μ₂.toNat + storageSum s.accountMap C
         ≤ balanceOf s.accountMap C)) →
  (∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ arg,
    Reachable s →
    StateWF s.accountMap →
    C = s.executionEnv.codeOwner →
    StorageSumLeBalance s.accountMap C →
    fetchInstr s.executionEnv s.pc = .ok (.StackMemFlow .SSTORE, arg) →
    EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s' →
    StorageSumLeBalance s'.accountMap C) →
  match EVM.X f validJumps evmState with
  | .ok (.success s' _) =>
      StorageSumLeBalance s'.accountMap C ∧
      StateWF s'.accountMap ∧
      (∀ a ∈ s'.createdAccounts, a ≠ C)
  | _ => True

/-- Fuel induction for the invariant-aware variant. Identical to
`X_inv_at_C_invariant_holds_slack_dispatch` modulo the new
`StorageSumLeBalance s'` hypothesis on `hReach_step`. -/
private theorem X_inv_at_C_invariant_holds_slack_dispatch_inv_aware
    (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress) (f : ℕ) (validJumps : Array UInt256)
    (Reachable : EVM.State → Prop)
    (evmState : EVM.State)
    (hAtCFrameAll : ∀ f', f' ≤ f → ΞInvariantAtCFrame C f')
    (hFrame : ∀ f', f' ≤ f → ΞInvariantFrameAtC C f') :
    X_inv_at_C_invariant_slack_dispatch_inv_aware OpAllowedSet C f validJumps Reachable evmState := by
  induction f generalizing evmState with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [show EVM.X 0 validJumps evmState = .error .OutOfFuel from rfl]
    trivial
  | succ f' IH =>
    intro hWF hCC hNC _hAtCFrameAtSucc _hFrameAtSucc hInv
            hReach hReach_Z hReach_step hReach_decodeSome
            hOpAllowedReach hDischarge h_call_slack_Reach h_sstore_Reach
    show match EVM.X (f' + 1) validJumps evmState with
      | .ok (.success s' _) =>
          StorageSumLeBalance s'.accountMap C ∧
          StateWF s'.accountMap ∧
          (∀ a ∈ s'.createdAccounts, a ≠ C)
      | _ => True
    generalize hXres : EVM.X (f' + 1) validJumps evmState = xRes
    cases xRes with
    | error _ => trivial
    | ok er =>
      cases er with
      | revert _ _ => trivial
      | success finalState out =>
        simp only [EVM.X] at hXres
        split at hXres
        case h_1 _ _ => exact absurd hXres (by simp)
        case h_2 _ evmStateZ cost₂ hZ =>
          have hZ_full :
              evmStateZ = { evmState with gasAvailable := evmStateZ.gasAvailable } := by
            simp only [bind, Except.bind, pure, Except.pure] at hZ
            by_cases hc1 : evmState.gasAvailable.toNat < memoryExpansionCost evmState ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1
            · rw [if_pos hc1] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc1] at hZ
            set evmState' : EVM.State :=
              { evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1) } with hevmState'
            by_cases hc2 : evmState'.gasAvailable.toNat < C' evmState' ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1
            · rw [if_pos hc2] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc2] at hZ
            by_cases hc3 : δ ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1 = none
            · rw [if_pos hc3] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc3] at hZ
            by_cases hc4 : evmState'.stack.length < (δ ((decode evmState.executionEnv.code evmState.pc).getD (Operation.STOP, none)).1).getD 0
            · rw [if_pos hc4] at hZ; exact Except.noConfusion hZ
            rw [if_neg hc4] at hZ
            (split_ifs at hZ;
              first
              | exact Except.noConfusion hZ
              | (injection hZ with h_inj
                 injection h_inj with h_inj1 _
                 subst h_inj1
                 rfl))
          have hZ_accMap : evmStateZ.accountMap = evmState.accountMap := by rw [hZ_full]
          have hZ_eEnv : evmStateZ.executionEnv = evmState.executionEnv := by rw [hZ_full]
          have hZ_cA : evmStateZ.createdAccounts = evmState.createdAccounts := by rw [hZ_full]
          have hZ_pc : evmStateZ.pc = evmState.pc := by rw [hZ_full]
          have hWFZ : StateWF evmStateZ.accountMap := by rw [hZ_accMap]; exact hWF
          have hCCZ : C = evmStateZ.executionEnv.codeOwner := by
            rw [hZ_eEnv]; exact hCC
          have hNCZ : ∀ a ∈ evmStateZ.createdAccounts, a ≠ C := by
            rw [hZ_cA]; exact hNC
          have hInvZ : StorageSumLeBalance evmStateZ.accountMap C := by rw [hZ_accMap]; exact hInv
          have hReachZ : Reachable evmStateZ := by
            rw [hZ_full]
            exact hReach_Z evmState evmStateZ.gasAvailable hReach
          simp only [bind, Except.bind] at hXres
          split at hXres
          case h_1 _ _ => exact absurd hXres (by simp)
          case h_2 _ sstepState hStep =>
            match f' with
            | 0 =>
              simp only [EVM.step] at hStep
              exact absurd hStep (by simp)
            | f'' + 1 =>
              set decRes : Operation .EVM × Option (UInt256 × Nat) :=
                (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none) with hDecRes
              obtain ⟨op, arg⟩ := decRes
              have hFrameAtSuccF' : ΞInvariantFrameAtC C (f'' + 1) :=
                ΞInvariantFrameAtC_mono C ((f'' + 1) + 1) (f'' + 1) (Nat.le_succ _) _hFrameAtSucc
              have hAtCFrameAtSuccF' : ΞInvariantAtCFrame C (f'' + 1) :=
                ΞInvariantAtCFrame_mono C ((f'' + 1) + 1) (f'' + 1) (Nat.le_succ _) _hAtCFrameAtSucc
              have hAllowed : OpAllowedSet op := by
                cases hDec : decode evmStateZ.executionEnv.code evmStateZ.pc with
                | none =>
                  obtain ⟨_, hSome⟩ := hReach_decodeSome evmStateZ hReachZ
                  rw [hDec] at hSome
                  exact absurd hSome (by simp)
                | some pair =>
                  have hDec' : decode evmState.executionEnv.code evmState.pc = some pair := by
                    rw [← hZ_eEnv, ← hZ_pc]; exact hDec
                  have hPair : ((op, arg) : Operation .EVM × Option (UInt256 × Nat)) = pair := by
                    have : (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                         = pair := by rw [hDec']; rfl
                    rw [show ((op, arg) : Operation .EVM × Option (UInt256 × Nat))
                          = (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                        from hDecRes]
                    exact this
                  have hFetch : fetchInstr evmStateZ.executionEnv evmStateZ.pc = .ok pair := by
                    unfold fetchInstr
                    rw [hDec]; rfl
                  obtain ⟨op', arg'⟩ := pair
                  have hOpEq : op = op' := (Prod.mk.inj hPair).1
                  have hArgEq : arg = arg' := (Prod.mk.inj hPair).2
                  have hFetch' : fetchInstr evmStateZ.executionEnv evmStateZ.pc = .ok (op, arg) := by
                    rw [hFetch, hOpEq, hArgEq]
                  exact hOpAllowedReach evmStateZ op arg hReachZ hFetch'
              have hFetchOK : fetchInstr evmStateZ.executionEnv evmStateZ.pc = .ok (op, arg) := by
                cases hDec : decode evmStateZ.executionEnv.code evmStateZ.pc with
                | none =>
                  obtain ⟨_, hSome⟩ := hReach_decodeSome evmStateZ hReachZ
                  rw [hDec] at hSome
                  exact absurd hSome (by simp)
                | some pair =>
                  have hDec' : decode evmState.executionEnv.code evmState.pc = some pair := by
                    rw [← hZ_eEnv, ← hZ_pc]; exact hDec
                  have hPair : ((op, arg) : Operation .EVM × Option (UInt256 × Nat)) = pair := by
                    have : (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                         = pair := by rw [hDec']; rfl
                    rw [show ((op, arg) : Operation .EVM × Option (UInt256 × Nat))
                          = (decode evmState.executionEnv.code evmState.pc).getD (.STOP, .none)
                        from hDecRes]
                    exact this
                  obtain ⟨op', arg'⟩ := pair
                  have hOpEq : op = op' := (Prod.mk.inj hPair).1
                  have hArgEq : arg = arg' := (Prod.mk.inj hPair).2
                  unfold fetchInstr; rw [hDec, hOpEq, hArgEq]; rfl
              have hStep' : EVM.step (f'' + 1) cost₂ (some (op, arg)) evmStateZ
                          = .ok sstepState := hStep
              have h_call_pre_slack_op :
                  op = .CALL →
                    ∀ (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256) (tl : Stack UInt256),
                      evmStateZ.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: tl →
                      (∀ acc,
                          evmStateZ.accountMap.find? (AccountAddress.ofUInt256 μ₁) = some acc →
                          acc.balance.toNat + μ₂.toNat < UInt256.size) ∧
                      (μ₂ = ⟨0⟩ ∨ ∃ acc,
                          evmStateZ.accountMap.find?
                              (AccountAddress.ofUInt256
                                (.ofNat evmStateZ.executionEnv.codeOwner)) = some acc ∧
                          μ₂.toNat ≤ acc.balance.toNat) ∧
                      (C ≠ AccountAddress.ofUInt256
                              (.ofNat evmStateZ.executionEnv.codeOwner) ∨
                       μ₂ = ⟨0⟩ ∨
                       μ₂.toNat + storageSum evmStateZ.accountMap C
                         ≤ balanceOf evmStateZ.accountMap C) := by
                intro hOpCall μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
                rw [hOpCall] at hFetchOK
                exact h_call_slack_Reach evmStateZ arg hReachZ hWFZ hCCZ hNCZ hInvZ hFetchOK
                  μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
              have h_sstore_post : op = .StackMemFlow .SSTORE →
                  StorageSumLeBalance sstepState.accountMap C := by
                intro hOpSStore
                rw [hOpSStore] at hFetchOK hStep'
                exact h_sstore_Reach evmStateZ sstepState f'' cost₂ arg
                  hReachZ hWFZ hCCZ hInvZ hFetchOK hStep'
              have hBundle :=
                step_bundled_invariant_at_C_invariant_at_C_slack_dispatch OpAllowedSet C f'' cost₂ arg op
                  evmStateZ sstepState
                  hWFZ hCCZ hNCZ hAtCFrameAtSuccF' hFrameAtSuccF' hInvZ
                  hAllowed hDischarge h_call_pre_slack_op h_sstore_post hStep'
              obtain ⟨hInvSstep, hWFsstep, hCCsstep, hNCsstep⟩ := hBundle
              split at hXres
              case h_1 _ hH_none =>
                have hOpRet : op ≠ .RETURN := by
                  intro hEq; rw [hEq] at hH_none; simp at hH_none
                have hOpRev : op ≠ .REVERT := by
                  intro hEq; rw [hEq] at hH_none; simp at hH_none
                have hOpStop : op ≠ .STOP := by
                  intro hEq; rw [hEq] at hH_none; simp at hH_none
                have hOpSD : op ≠ .SELFDESTRUCT := by
                  intro hEq; rw [hEq] at hH_none; simp at hH_none
                -- Pass `hInvSstep` (already established by the framework's CALL/SSTORE
                -- helpers) into `hReach_step` as the invariant-aware extra hypothesis.
                have hReachStep : Reachable sstepState :=
                  hReach_step evmStateZ sstepState f'' cost₂ op arg hReachZ hFetchOK hStep'
                    hOpRet hOpRev hOpStop hOpSD hInvSstep
                have hFrame' : ∀ f'_1, f'_1 ≤ (f'' + 1) → ΞInvariantFrameAtC C f'_1 :=
                  fun f1 h1 =>
                    ΞInvariantFrameAtC_mono C ((f'' + 1) + 1) f1
                      (Nat.le_trans h1 (Nat.le_succ _)) _hFrameAtSucc
                have hAtCFrame' : ∀ f'_1, f'_1 ≤ (f'' + 1) → ΞInvariantAtCFrame C f'_1 :=
                  fun f1 h1 =>
                    ΞInvariantAtCFrame_mono C ((f'' + 1) + 1) f1
                      (Nat.le_trans h1 (Nat.le_succ _)) _hAtCFrameAtSucc
                have IH' : ∀ evmState',
                    X_inv_at_C_invariant_slack_dispatch_inv_aware OpAllowedSet C (f'' + 1) validJumps Reachable evmState' :=
                  fun es => IH es hAtCFrame' hFrame'
                have hIH := IH' sstepState hWFsstep hCCsstep hNCsstep hAtCFrameAtSuccF'
                                hFrameAtSuccF' hInvSstep hReachStep hReach_Z hReach_step
                                hReach_decodeSome hOpAllowedReach hDischarge h_call_slack_Reach
                                h_sstore_Reach
                rw [hXres] at hIH
                exact hIH
              case h_2 _ o hH_some =>
                split at hXres
                case isTrue _ => exact absurd hXres (by simp)
                case isFalse _ =>
                  injection hXres with hXres_inj
                  injection hXres_inj with hfin _
                  subst hfin
                  exact ⟨hInvSstep, hWFsstep, hNCsstep⟩

/-- **Invariant-aware variant of
`ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch`.**

The `hReach_step` callback receives `StorageSumLeBalance s'.accountMap C` as an
additional hypothesis at every non-halt step. The framework's CALL/SSTORE
arms have already established this fact internally before invoking
`hReach_step`, so passing it through eliminates the consumer-side
chicken-and-egg dependency on a per-step CALL invariant predicate.

Consumers whose `Reachable` predicate has a closure that includes
`StorageSumLeBalance s'` can therefore thread through CALL steps via
the framework's slack callback alone, without needing a separate
per-step CALL invariant frame assumption. -/
theorem ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch_inv_aware
    (OpAllowedSet : Operation .EVM → Prop)
    (C : AccountAddress)
    (Reachable : EVM.State → Prop)
    (hReach_Z : ∀ s : EVM.State, ∀ g : UInt256, Reachable s →
        Reachable { s with gasAvailable := g })
    (hReach_step : ∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ op arg, Reachable s →
        fetchInstr s.executionEnv s.pc = .ok (op, arg) →
        EVM.step (f' + 1) cost (some (op, arg)) s = .ok s' →
        op ≠ .RETURN → op ≠ .REVERT → op ≠ .STOP → op ≠ .SELFDESTRUCT →
        StorageSumLeBalance s'.accountMap C →
        Reachable s')
    (hReach_decodeSome : ∀ s : EVM.State, Reachable s →
        ∃ pair, decode s.executionEnv.code s.pc = some pair)
    (hReach_op : ∀ s : EVM.State, ∀ op : Operation .EVM, ∀ arg, Reachable s →
        fetchInstr s.executionEnv s.pc = .ok (op, arg) →
        OpAllowedSet op)
    (hDischarge : ∀ op', OpAllowedSet op' →
        strictlyPreservesAccountMap op' ∨ op' = .CALL ∨
        op' = .StackMemFlow .SSTORE)
    (hReach_call_slack : ∀ s : EVM.State, ∀ arg,
        Reachable s →
        StateWF s.accountMap →
        C = s.executionEnv.codeOwner →
        (∀ a ∈ s.createdAccounts, a ≠ C) →
        StorageSumLeBalance s.accountMap C →
        fetchInstr s.executionEnv s.pc = .ok (.CALL, arg) →
        ∀ (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256) (tl : Stack UInt256),
          s.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: tl →
          (∀ acc,
              s.accountMap.find? (AccountAddress.ofUInt256 μ₁) = some acc →
              acc.balance.toNat + μ₂.toNat < UInt256.size) ∧
          (μ₂ = ⟨0⟩ ∨ ∃ acc,
              s.accountMap.find?
                  (AccountAddress.ofUInt256
                    (.ofNat s.executionEnv.codeOwner)) = some acc ∧
              μ₂.toNat ≤ acc.balance.toNat) ∧
          (C ≠ AccountAddress.ofUInt256
                  (.ofNat s.executionEnv.codeOwner) ∨
           μ₂ = ⟨0⟩ ∨
           μ₂.toNat + storageSum s.accountMap C
             ≤ balanceOf s.accountMap C))
    (hReach_sstore : ∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ arg,
        Reachable s →
        StateWF s.accountMap →
        C = s.executionEnv.codeOwner →
        StorageSumLeBalance s.accountMap C →
        fetchInstr s.executionEnv s.pc = .ok (.StackMemFlow .SSTORE, arg) →
        EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s' →
        StorageSumLeBalance s'.accountMap C)
    (hReachInit : ∀ (cA : RBSet AccountAddress compare)
                    (gbh : BlockHeader) (bs : ProcessedBlocks)
                    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
                    (I : ExecutionEnv .EVM),
        I.codeOwner = C →
        StorageSumLeBalance σ C →
        Reachable
          { (default : EVM.State) with
              accountMap := σ
              σ₀ := σ₀
              executionEnv := I
              substate := A
              createdAccounts := cA
              gasAvailable := g
              blocks := bs
              genesisBlockHeader := gbh }) :
    ΞPreservesInvariantAtC C := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro cA gbh bs σ σ₀ g A I hWF hCO hNC hInv
    match n with
    | 0 =>
      rw [show EVM.Ξ 0 cA gbh bs σ σ₀ g A I = .error .OutOfFuel from rfl]
      trivial
    | f + 1 =>
      have hAtCBdd : ∀ f', f' ≤ f → ΞInvariantAtCFrame C f' := by
        intro f' hf'
        intro f'' hf'' cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO'' hNC'' hInv''
        have hlt : f'' < f + 1 := Nat.lt_succ_of_le (Nat.le_trans hf'' hf')
        exact IH f'' hlt cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO'' hNC'' hInv''
      have Ξ_frame_at : ∀ f', f' ≤ f → ΞInvariantFrameAtC C f' := by
        intro f' hf'
        intro f'' hf'' cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO_ne'' hNC'' hInv''
        have hf''_le_f : f'' ≤ f := Nat.le_trans hf'' hf'
        have hAtCSub : ∀ k, k < f'' → ΞInvariantAtCFrame C k := by
          intro k hk
          have : k ≤ f := by omega
          exact hAtCBdd k this
        exact Ξ_invariant_preserved_bundled_bdd C f'' hAtCSub
          cA'' gbh'' bs'' σ'' σ₀'' g'' A'' I'' hWF'' hCO_ne'' hNC'' hInv''
      have hΞ_eq :
          EVM.Ξ (f + 1) cA gbh bs σ σ₀ g A I
            = (do
                let defState : EVM.State := default
                let freshEvmState : EVM.State :=
                  { defState with
                      accountMap := σ
                      σ₀ := σ₀
                      executionEnv := I
                      substate := A
                      createdAccounts := cA
                      gasAvailable := g
                      blocks := bs
                      genesisBlockHeader := gbh }
                let result ← EVM.X f (D_J I.code ⟨0⟩) freshEvmState
                match result with
                | .success evmState' o =>
                  let finalGas := evmState'.gasAvailable
                  .ok (ExecutionResult.success
                    (evmState'.createdAccounts, evmState'.accountMap,
                     finalGas, evmState'.substate) o)
                | .revert g' o => .ok (ExecutionResult.revert g' o)) := rfl
      rw [hΞ_eq]
      simp only [bind, Except.bind]
      generalize hXres : EVM.X f (D_J I.code ⟨0⟩) _ = xRes
      set freshState : EVM.State :=
        { (default : EVM.State) with
            accountMap := σ
            σ₀ := σ₀
            executionEnv := I
            substate := A
            createdAccounts := cA
            gasAvailable := g
            blocks := bs
            genesisBlockHeader := gbh } with hFresh_def
      have hWFFresh : StateWF freshState.accountMap := hWF
      have hCCFresh : C = freshState.executionEnv.codeOwner := hCO.symm
      have hNCFresh : ∀ a ∈ freshState.createdAccounts, a ≠ C := hNC
      have hInvFresh : StorageSumLeBalance freshState.accountMap C := hInv
      have hReachFresh : Reachable freshState :=
        hReachInit cA gbh bs σ σ₀ g A I hCO hInv
      have hAtCBddF : ΞInvariantAtCFrame C f := hAtCBdd f (Nat.le_refl _)
      have Ξ_frame_atF : ΞInvariantFrameAtC C f := Ξ_frame_at f (Nat.le_refl _)
      have hXinv :
          X_inv_at_C_invariant_slack_dispatch_inv_aware OpAllowedSet C f (D_J I.code ⟨0⟩) Reachable freshState :=
        X_inv_at_C_invariant_holds_slack_dispatch_inv_aware OpAllowedSet C f (D_J I.code ⟨0⟩)
          Reachable freshState hAtCBdd Ξ_frame_at
      unfold X_inv_at_C_invariant_slack_dispatch_inv_aware at hXinv
      have hRes := hXinv hWFFresh hCCFresh hNCFresh hAtCBddF Ξ_frame_atF hInvFresh
        hReachFresh hReach_Z hReach_step hReach_decodeSome hReach_op hDischarge
        hReach_call_slack hReach_sstore
      rw [hXres] at hRes
      cases xRes with
      | error _ => trivial
      | ok er =>
        cases er with
        | success evmState' out =>
          exact hRes
        | revert _ _ => trivial


/-! ## §1.3 — Υ's invariant-preservation entry point

Mirror of `Υ_balanceOf_ge`'s chain, with conclusion changed from
balance monotonicity to `StorageSumLeBalance` preservation. The structure is:

  * `ΥBodyFactorsInvariant` — invariant-flavoured body factorisation
    (σ' decomposes through the tail; σ_P satisfies `StorageSumLeBalance σ_P C`
    and `dead σ_P C = false`). Discharged per-contract via the at-C
    invariant frames.
  * `Υ_tail_invariant_preserves` — combines `Υ_tail_balanceOf_ge`
    (β unchanged at C across the tail) with `Υ_tail_storageSum_eq`
    (S unchanged at C across the tail) ⇒ `StorageSumLeBalance σ_P C →
    StorageSumLeBalance σ_tail C`.
  * `Υ_invariant_preserved` — top-level consumer entry point. -/

/-- Hypothesis form of Υ's body factorisation, **invariant flavour**.

Whenever Υ returns `.ok (σ', A, z, _)`, σ' decomposes as
`Υ_tail_state σ_P g' A …` for some `(σ_P, g')` produced by the Θ/Λ
dispatch, with `StorageSumLeBalance σ_P C` (rather than balance monotonicity)
and `C` not dead in σ_P. Discharged per-contract by the caller via
the at-C invariant frame chain (`Θ_invariant_preserved` /
`Λ_invariant_preserved` / §H.2's `Ξ_invariant_preserved_bundled_bdd`). -/
def ΥBodyFactorsInvariant (σ : AccountMap .EVM) (fuel H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress) : Prop :=
  match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | .ok (σ', A', _, _) =>
      ∃ σ_P g',
        σ' = Υ_tail_state σ_P g' A' H H_f tx S_T ∧
        StorageSumLeBalance σ_P C ∧
        State.dead σ_P C = false
  | .error _ => True

/-- Combined tail step: under the structural exclusions for the SD/dead
sweeps and the `dead σ_P C = false` hypothesis, the pure tail of Υ
preserves `StorageSumLeBalance` at `C`.

Direct consequence of `Υ_tail_balanceOf_ge` (β unchanged at C across
the tail; the conclusion `balanceOf tail C ≥ balanceOf σ_P C`
upgrades to equality because the tail also doesn't add at C, but for
the invariant we only need `≥`) combined with `Υ_tail_storageSum_eq`
(S unchanged at C across the tail). -/
private theorem Υ_tail_invariant_preserves
    (σ_P : AccountMap .EVM) (g' : UInt256) (A : Substate)
    (H : BlockHeader) (H_f : ℕ) (tx : Transaction)
    (S_T C : AccountAddress)
    (hS_T : C ≠ S_T)
    (hBen : C ≠ H.beneficiary)
    (hSD : ∀ k ∈ A.selfDestructSet.1.toList, k ≠ C)
    (hDeadGated :
       ∀ σ_F : AccountMap .EVM, State.dead σ_F C = false →
         ∀ k ∈ A.touchedAccounts.filter (State.dead σ_F ·), k ≠ C)
    (hDead_σP : State.dead σ_P C = false)
    (hInv_σP : StorageSumLeBalance σ_P C) :
    StorageSumLeBalance (Υ_tail_state σ_P g' A H H_f tx S_T) C := by
  unfold StorageSumLeBalance at hInv_σP ⊢
  have hβ : balanceOf (Υ_tail_state σ_P g' A H H_f tx S_T) C = balanceOf σ_P C :=
    Υ_tail_balanceOf_ge σ_P g' A H H_f tx S_T C hS_T hBen hSD hDeadGated hDead_σP
  have hS : storageSum (Υ_tail_state σ_P g' A H H_f tx S_T) C = storageSum σ_P C :=
    Υ_tail_storageSum_eq σ_P g' A H H_f tx S_T C hS_T hBen hSD hDeadGated hDead_σP
  rw [hβ, hS]
  exact hInv_σP

/-- Υ's invariant-preservation frame, proved from the invariant body
factorisation and tail-invariant hypotheses.

Mirror of `Υ_output_balance_ge` for the (β ≥ S) chain.

Note: this theorem does not require a `ΞPreservesInvariantAtC C`
witness. The body-factor hypothesis (`hFactor`) already carries
`StorageSumLeBalance σ_P C` (post-Θ/Λ-dispatch), and the tail step preserves it
verbatim under the SD-exclusion / dead-set hypotheses, so the at-`C`
Ξ-level witness is structurally redundant at this level. The
consumer-side `ΞPreservesInvariantAtC` witness still feeds into the
Θ/Λ-side propagation chain that establishes `hFactor`'s
`StorageSumLeBalance σ_P C`, but it is not threaded through Υ. -/
theorem Υ_output_invariant_preserves
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress)
    (_hWF : StateWF σ)
    (hS_T : C ≠ S_T)
    (hBen : C ≠ H.beneficiary)
    (hTail : ΥTailInvariant σ fuel H_f H H_gen blocks tx S_T C)
    (hFactor : ΥBodyFactorsInvariant σ fuel H_f H H_gen blocks tx S_T C) :
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => StorageSumLeBalance σ' C
    | .error _ => True := by
  unfold ΥBodyFactorsInvariant at hFactor
  unfold ΥTailInvariant at hTail
  cases hΥ : EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | error e => trivial
  | ok r =>
    obtain ⟨σ', A, z, gUsed⟩ := r
    rw [hΥ] at hFactor
    rw [hΥ] at hTail
    obtain ⟨σ_P, g', hEq, hInv_σP, hDead_σP⟩ := hFactor
    obtain ⟨hSD, hDeadGated⟩ := hTail
    show StorageSumLeBalance σ' C
    rw [hEq]
    exact Υ_tail_invariant_preserves σ_P g' A H H_f tx S_T C hS_T hBen
      hSD hDeadGated hDead_σP hInv_σP

/-- Υ's transaction-level invariant-preservation theorem. Given a
pre-state σ satisfying `StorageSumLeBalance σ C` and the structural hypotheses,
the post-state σ' produced by Υ also satisfies `StorageSumLeBalance σ' C`.

Mirror of `Υ_balanceOf_ge` for the (β ≥ S) chain. The proof composes
`Υ_output_invariant_preserves` (which produces `StorageSumLeBalance σ' C`
directly from σ_P's invariant) — no additional projection is needed
because the body factor's `StorageSumLeBalance σ_P C` is the invariant we want
to lift.

Note: the previously-required `hWitness : ΞPreservesInvariantAtC C`
parameter has been **dropped**. It was structurally unused in the
chain (the proof of `Υ_output_invariant_preserves` does not consume
it), and threading it through forced consumers to provide a universal-σ
σ-presence assumption (`account_at_initial`) that was unprovable in
full generality. Dropping the witness lets consumers close their
proofs without that assumption. -/
theorem Υ_invariant_preserved
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress)
    (hWF : StateWF σ)
    (_hInv : StorageSumLeBalance σ C)
    (hS_T : C ≠ S_T)
    (hBen : C ≠ H.beneficiary)
    (hTail : ΥTailInvariant σ fuel H_f H H_gen blocks tx S_T C)
    (hFactor : ΥBodyFactorsInvariant σ fuel H_f H H_gen blocks tx S_T C) :
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => StorageSumLeBalance σ' C
    | .error _ => True :=
  Υ_output_invariant_preserves fuel σ H_f H H_gen blocks tx S_T C
    hWF hS_T hBen hTail hFactor

end Frame
end EvmYul
