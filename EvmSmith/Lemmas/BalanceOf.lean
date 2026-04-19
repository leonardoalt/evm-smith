import EvmSmith.Lemmas.RBMapSum
import EvmYul.State.AccountOps
import EvmYul.Maps.AccountMap

/-!
# Layer 1 — balance / code frame lemmas for `AccountMap`

Generic helpers around
`balanceOf σ C := (σ.find? C).elim 0 (·.balance.toNat)`
and `totalETH σ := σ.foldl (λ acc _ v ↦ acc + v.balance.toNat) 0`.

Reuses the `RBMap` insert/erase infrastructure from
`EvmSmith/Lemmas/RBMapSum.lean` (Weth Layer 1), specialized to
`AccountMap .EVM`.

The two building blocks below are small: `find?_insert_ne` and the
bridged `find?_erase_ne`. Everything else is derived.
-/

namespace EvmSmith.Layer1Balance

open EvmYul Batteries

/-- `ℕ`-valued balance lookup. Returns 0 for unknown accounts. -/
def balanceOf (σ : AccountMap .EVM) (C : AccountAddress) : ℕ :=
  (σ.find? C).elim 0 (·.balance.toNat)

/-- Total ETH across all accounts, computed in ℕ. -/
def totalETH (σ : AccountMap .EVM) : ℕ :=
  σ.foldl (fun acc _a v => acc + v.balance.toNat) 0

/-! ## `find?` frame lemmas -/

/-- Inserting at `k ≠ C` leaves `σ.find? C` unchanged. -/
theorem find?_insert_ne
    (σ : AccountMap .EVM) (k C : AccountAddress) (a : Account .EVM)
    (hne : k ≠ C) :
    (σ.insert k a).find? C = σ.find? C := by
  have hcmp : compare C k ≠ .eq := by
    intro h; apply hne
    exact (Std.LawfulEqCmp.compare_eq_iff_eq.mp h).symm
  exact RBMap.find?_insert_of_ne σ hcmp

/-- AccountMap-level erase permutation. Bridged from Layer 1's
    `erase_toList_filter` via the `Ordering.byKey Prod.fst compare` cut. -/
private theorem am_erase_toList_filter
    (σ : AccountMap .EVM) (k : AccountAddress) :
    (σ.erase k).toList
      = σ.toList.filter (fun p => decide (compare k p.1 ≠ .eq)) := by
  have ho : σ.1.Ordered (Ordering.byKey Prod.fst compare) := σ.2.out.1
  exact EvmSmith.Layer1.erase_toList_filter
    (cmp := Ordering.byKey Prod.fst compare)
    (cut := fun p => compare k p.1) σ.1 ho

/-- Erasing at `k ≠ C` leaves `σ.find? C` unchanged. -/
theorem find?_erase_ne
    (σ : AccountMap .EVM) (k C : AccountAddress) (hne : k ≠ C) :
    (σ.erase k).find? C = σ.find? C := by
  unfold RBMap.find?
  congr 1
  ext y
  rw [RBMap.findEntry?_some, RBMap.findEntry?_some]
  have hfilter : y ∈ (σ.erase k).toList ↔
      y ∈ σ.toList ∧ compare k y.1 ≠ .eq := by
    rw [am_erase_toList_filter]
    simp [List.mem_filter]
  constructor
  · rintro ⟨hMem, hEq⟩
    rw [hfilter] at hMem
    exact ⟨hMem.1, hEq⟩
  · rintro ⟨hMem, hEq⟩
    refine ⟨?_, hEq⟩
    rw [hfilter]
    refine ⟨hMem, ?_⟩
    have hCy : C = y.1 := Std.LawfulEqCmp.compare_eq_iff_eq.mp hEq
    intro hky
    apply hne
    have hky' : k = y.1 := Std.LawfulEqCmp.compare_eq_iff_eq.mp hky
    rw [hky', hCy]

/-- Fold-erase frame: erasing a set of addresses, none of which is `C`,
    preserves `σ.find? C`. -/
theorem find?_erase_fold_ne
    (σ : AccountMap .EVM) (addrs : List AccountAddress)
    (C : AccountAddress) (hCNotIn : ∀ a ∈ addrs, a ≠ C) :
    (addrs.foldl RBMap.erase σ).find? C = σ.find? C := by
  induction addrs generalizing σ with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldl_cons]
    rw [ih (σ.erase a) (by intro x hx; exact hCNotIn x (List.mem_cons_of_mem _ hx))]
    exact find?_erase_ne σ a C (hCNotIn a (by simp))

/-- `increaseBalance` at `A ≠ C` leaves `σ.find? C` unchanged. -/
theorem find?_increaseBalance_ne
    (σ : AccountMap .EVM) (A C : AccountAddress) (v : UInt256)
    (hAC : A ≠ C) :
    (σ.increaseBalance .EVM A v).find? C = σ.find? C := by
  unfold AccountMap.increaseBalance
  match h : σ.find? A with
  | none =>
    simp only
    exact find?_insert_ne σ A C _ hAC
  | some acc =>
    simp only
    exact find?_insert_ne σ A C _ hAC

/-! ## `balanceOf` frame lemmas -/

/-- If two `AccountMap`s agree on `C`, their `balanceOf` at `C` agrees. -/
theorem balanceOf_of_find?_eq
    {σ σ' : AccountMap .EVM} {C : AccountAddress}
    (h : σ'.find? C = σ.find? C) :
    balanceOf σ' C = balanceOf σ C := by
  unfold balanceOf; rw [h]

/-- Inserting at `k ≠ C` preserves `balanceOf C`. -/
theorem balanceOf_insert_ne
    (σ : AccountMap .EVM) (k C : AccountAddress) (a : Account .EVM)
    (hne : k ≠ C) :
    balanceOf (σ.insert k a) C = balanceOf σ C := by
  exact balanceOf_of_find?_eq (find?_insert_ne σ k C a hne)

/-- Inserting at `C` with a given `acc` makes `balanceOf C = acc.balance.toNat`. -/
theorem balanceOf_insert_self
    (σ : AccountMap .EVM) (C : AccountAddress) (a : Account .EVM) :
    balanceOf (σ.insert C a) C = a.balance.toNat := by
  unfold balanceOf
  rw [RBMap.find?_insert_of_eq σ Std.ReflCmp.compare_self]
  rfl

/-- Erasing at `k ≠ C` preserves `balanceOf C`. -/
theorem balanceOf_erase_ne
    (σ : AccountMap .EVM) (k C : AccountAddress) (hne : k ≠ C) :
    balanceOf (σ.erase k) C = balanceOf σ C :=
  balanceOf_of_find?_eq (find?_erase_ne σ k C hne)

/-- Folded-erase at addresses all `≠ C` preserves `balanceOf C`. -/
theorem balanceOf_erase_fold_ne
    (σ : AccountMap .EVM) (addrs : List AccountAddress) (C : AccountAddress)
    (hCNotIn : ∀ a ∈ addrs, a ≠ C) :
    balanceOf (addrs.foldl RBMap.erase σ) C = balanceOf σ C :=
  balanceOf_of_find?_eq (find?_erase_fold_ne σ addrs C hCNotIn)

/-- `increaseBalance` at `A ≠ C` preserves `balanceOf C`. -/
theorem balanceOf_increaseBalance_ne
    (σ : AccountMap .EVM) (A C : AccountAddress) (v : UInt256)
    (hAC : A ≠ C) :
    balanceOf (σ.increaseBalance .EVM A v) C = balanceOf σ C :=
  balanceOf_of_find?_eq (find?_increaseBalance_ne σ A C v hAC)

/-! ## `balanceOf` monotonicity under `increaseBalance` at `C`

`increaseBalance σ C v` can only *raise* `balanceOf σ C`, modulo
UInt256 wraparound. Under the no-wrap side condition
`balanceOf σ C + v.toNat < 2^256` the raise is strict by `v.toNat`. -/

/-- Without any wrap hypothesis, `increaseBalance σ A v` at the only
    address that matters (`A = C`, or after the generic ne-frame) cannot
    *decrease* balance. This version covers both cases:
    - `A = C`, no-wrap: balance goes up by exactly `v.toNat`.
    - `A = C`, wrap: balance wraps; bound may fail — **not proved here**.
    - `A ≠ C`: balance unchanged, via `balanceOf_increaseBalance_ne`.

    Specialized monotonicity (no-wrap at `C`) is in
    `balanceOf_increaseBalance_self_of_noWrap`. -/
theorem balanceOf_increaseBalance_self_of_noWrap
    (σ : AccountMap .EVM) (C : AccountAddress) (v : UInt256)
    (hNoWrap : balanceOf σ C + v.toNat < UInt256.size) :
    balanceOf (σ.increaseBalance .EVM C v) C
      = balanceOf σ C + v.toNat := by
  unfold AccountMap.increaseBalance
  match h : σ.find? C with
  | none =>
    have h0 : balanceOf σ C = 0 := by unfold balanceOf; rw [h]; rfl
    simp only
    rw [h0, Nat.zero_add, balanceOf_insert_self]
  | some acc =>
    have hB : balanceOf σ C = acc.balance.toNat := by
      unfold balanceOf; rw [h]; rfl
    simp only
    rw [balanceOf_insert_self, hB]
    -- Goal: ({acc with balance := acc.balance + v}).balance.toNat
    --       = acc.balance.toNat + v.toNat
    show (acc.balance + v).toNat = acc.balance.toNat + v.toNat
    show ((acc.balance.val + v.val : Fin _)).val = _
    rw [Fin.val_add]
    apply Nat.mod_eq_of_lt
    show acc.balance.val.val + v.val.val < UInt256.size
    have h1 : acc.balance.val.val = acc.balance.toNat := rfl
    have h2 : v.val.val = v.toNat := rfl
    rw [h1, h2]
    rw [hB] at hNoWrap; omega

/-- Under no-wrap at `C`, `increaseBalance` preserves the lower bound
    `b₀ ≤ balanceOf σ C`. Follows from the identity above + `Nat.le_add_right`. -/
theorem balanceOf_ge_of_increaseBalance_self
    (σ : AccountMap .EVM) (C : AccountAddress) (v : UInt256) (b₀ : ℕ)
    (hB : b₀ ≤ balanceOf σ C)
    (hNoWrap : balanceOf σ C + v.toNat < UInt256.size) :
    b₀ ≤ balanceOf (σ.increaseBalance .EVM C v) C := by
  rw [balanceOf_increaseBalance_self_of_noWrap σ C v hNoWrap]
  exact Nat.le_add_right_of_le hB

/-! ## `codeAt`-style frame -/

/-- `σ.find? C` agreement implies `(·.map (·.code))` agreement. -/
theorem code_of_find?_eq
    {σ σ' : AccountMap .EVM} {C : AccountAddress}
    (h : σ'.find? C = σ.find? C) :
    (σ'.find? C).map (·.code) = (σ.find? C).map (·.code) := by
  rw [h]

end EvmSmith.Layer1Balance
