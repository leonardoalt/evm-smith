import EvmSmith.Framework

/-!
# Layer 0 — UInt256 order-class and subtraction bridges

## Why this file exists

`Batteries.RBMap` needs `[Std.TransCmp cmp]` to apply almost any of its
lemmas (`mem_toList_insert`, `findD_insert_self`, …). `UInt256` in the
upstream derives only `BEq, Ord` — no `TransCmp`, `ReflCmp`, or
`LawfulOrd` anywhere. So every Layer-1 lemma about `totalBalance` would
fail to elaborate without the instances below.

The derived `Ord UInt256` reduces to
`fun ⟨a⟩ ⟨b⟩ => (compare a b).then Ordering.eq` (we recovered the term
via `#check` on the internal `EvmYul.ordUInt256._@...`). `.then .eq` is
the identity on Ordering, so `compare a b = compare a.val b.val` after
destructuring. The one-shot lemma `compare_eq` below is the bridge; all
typeclass instances rewrite with it and defer to `Fin`'s.

Subtraction bridges are the second piece. `Fin.sub` is modular, so
`(a - b).toNat = a.toNat - b.toNat` only holds under `b ≤ a`. The three
lemmas below (`sub_toNat_of_le`, `sub_add_cancel_of_le`,
`sub_le_self_of_le`) are used in the withdraw-step argument.

Exit criterion: `example : Std.TransCmp (compare : UInt256 → UInt256 → Ordering) := inferInstance`
typechecks (see bottom of file).
-/

namespace EvmYul.UInt256

/-- The derived `Ord UInt256` reduces to `compare a.val b.val`. -/
theorem compare_eq (a b : UInt256) : compare a b = compare a.val b.val := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  show (compare a b).then Ordering.eq = compare a b
  cases compare a b <;> rfl

instance : Std.OrientedCmp (compare : UInt256 → UInt256 → Ordering) where
  eq_swap {x y} := by
    rw [compare_eq, compare_eq]
    exact Std.OrientedCmp.eq_swap

instance : Std.TransCmp (compare : UInt256 → UInt256 → Ordering) where
  isLE_trans {x y z} h1 h2 := by
    rw [compare_eq] at h1 h2 ⊢
    exact Std.TransCmp.isLE_trans h1 h2

instance : Std.ReflCmp (compare : UInt256 → UInt256 → Ordering) where
  compare_self {x} := by
    rw [compare_eq]
    exact Std.ReflCmp.compare_self

/-! ## Subtraction bridges (L0-S1..S3) -/

/-- L0-S1: `UInt256.sub` commutes with `Nat.sub` under `b ≤ a`. -/
theorem sub_toNat_of_le {a b : UInt256} (h : b ≤ a) :
    (a - b).toNat = a.toNat - b.toNat := by
  show ((a.val - b.val : Fin _)).val = a.val.val - b.val.val
  exact Fin.sub_val_of_le h

/-- L0-S2: subtraction round-trip under `b ≤ a`. -/
theorem sub_add_cancel_of_le {a b : UInt256} (h : b ≤ a) :
    a - b + b = a := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  show (⟨(a - b) + b⟩ : UInt256) = ⟨a⟩
  congr 1
  apply Fin.eq_of_val_eq
  show ((a - b) + b).val = a.val
  rw [Fin.val_add, Fin.sub_val_of_le h, Nat.sub_add_cancel h,
      Nat.mod_eq_of_lt a.isLt]

/-- L0-S3: `a - b ≤ a` when `b ≤ a`. -/
theorem sub_le_self_of_le {a b : UInt256} (h : b ≤ a) : a - b ≤ a := by
  show (a - b).val ≤ a.val
  show ((a.val - b.val : Fin _)).val ≤ a.val.val
  rw [Fin.sub_val_of_le h]
  exact Nat.sub_le _ _

end EvmYul.UInt256

/-! ## Exit criterion -/

example : Std.TransCmp (compare : EvmYul.UInt256 → EvmYul.UInt256 → Ordering) :=
  inferInstance

example : Std.ReflCmp (compare : EvmYul.UInt256 → EvmYul.UInt256 → Ordering) :=
  inferInstance
