import EvmSmith.Framework

set_option maxRecDepth 4096

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

/-! ## `lnot` injectivity (L0-S4)

The optimized ERC-20 demos (Solidity Solady-side and Vyper Snekmate-
side) replace `sload(addr)` with `sload(not(addr))` as their balance-
slot key. For the optimization to be sound — i.e., for *distinct
addresses to map to distinct storage slots*, so two users can't
alias — we need the slot function `UInt256.lnot` to be injective.

This is the Lean half of the safety story; the other half is
"`UInt256.lnot`'s image avoids the contract's named slots" (a
disjointness fact provable from the high-bit argument: `lnot a >=
2^160` for any 160-bit `a`).

Proof: `lnot a = (size - 1) - a` (concretely, in `Fin size` modular
arithmetic). It's its own inverse: `lnot (lnot a) = a`. Injectivity
then follows by applying `lnot` to both sides of `lnot a = lnot b`. -/

/-- `(ofNat (size - 1)).toNat = size - 1` — the max representable
value as a Nat. Proved separately so the heavy mod-by-size
elaboration only happens once. -/
private lemma ofNat_size_pred_toNat :
    (UInt256.ofNat (UInt256.size - 1)).toNat = UInt256.size - 1 := by
  show (UInt256.size - 1) % UInt256.size = UInt256.size - 1
  apply Nat.mod_eq_of_lt
  have h : (0 : ℕ) < UInt256.size := by
    have : (1 : ℕ) ≤ UInt256.size := by unfold UInt256.size; omega
    omega
  omega

/-- For any `a : UInt256`, `a ≤ ofNat (size - 1)` (the max
representable value bounds every other). -/
private lemma le_ofNat_size_pred (a : UInt256) :
    a ≤ UInt256.ofNat (UInt256.size - 1) := by
  show a.val.val ≤ (UInt256.ofNat (UInt256.size - 1)).val.val
  rw [show (UInt256.ofNat (UInt256.size - 1)).val.val
        = UInt256.size - 1 from ofNat_size_pred_toNat]
  exact Nat.le_sub_one_of_lt a.val.isLt

/-- `(lnot a).toNat = size - 1 - a.toNat` — the cancellation form
that's actually useful. Built on top of `sub_toNat_of_le`. -/
theorem lnot_toNat (a : UInt256) :
    (lnot a).toNat = UInt256.size - 1 - a.toNat := by
  show (UInt256.ofNat (UInt256.size - 1) - a).toNat
      = UInt256.size - 1 - a.toNat
  rw [sub_toNat_of_le (le_ofNat_size_pred a)]
  rw [ofNat_size_pred_toNat]

/-- `lnot` is injective on `UInt256`. Distinct 256-bit values get
distinct complements; used by the optimized ERC-20 demos (Solidity
and Vyper) to argue that distinct addresses map to distinct balance
slots. The orig side gets this from Keccak collision-resistance
(axiom T5); the opt side gets it from this concrete arithmetic
lemma. -/
theorem lnot_injective : Function.Injective (UInt256.lnot) := by
  intro a b h
  have h_toNat : (lnot a).toNat = (lnot b).toNat := congrArg UInt256.toNat h
  rw [lnot_toNat, lnot_toNat] at h_toNat
  have ha : a.toNat < UInt256.size := a.val.isLt
  have hb : b.toNat < UInt256.size := b.val.isLt
  have h_eq_toNat : a.toNat = b.toNat := by omega
  obtain ⟨⟨av, hav⟩⟩ := a
  obtain ⟨⟨bv, hbv⟩⟩ := b
  congr 1
  apply Fin.ext
  exact h_eq_toNat

end EvmYul.UInt256

/-! ## Exit criterion -/

example : Std.TransCmp (compare : EvmYul.UInt256 → EvmYul.UInt256 → Ordering) :=
  inferInstance

example : Std.ReflCmp (compare : EvmYul.UInt256 → EvmYul.UInt256 → Ordering) :=
  inferInstance
