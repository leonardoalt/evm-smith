import EvmSmith.Lemmas.UInt256Order
import Batteries.Data.RBMap.Lemmas
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Perm.Basic

/-!
# Layer 1 — `totalBalance` sum behaviour under `insert` and `erase`

`totalBalance` is a `ℕ`-valued fold over
`RBMap UInt256 UInt256 compare` — summing each stored value after
`.toNat` conversion so modular wraparound isn't a concern. The Weth
invariant compares this sum to `acc.balance.toNat` (also in `ℕ`).

## Constructive splits we lean on

Batteries exposes two RBNode-level permutation witnesses:

    exists_insert_toList_zoom_nil  (zoom = nil root path)
    exists_insert_toList_zoom_node (zoom = node root path, existing key)

Each produces a split `t.toList = L ++ R` (new key) or
`t.toList = L ++ (k', v') :: R` (existing, with `compare k k' = .eq`)
with `(t.insert cmp v).toList = L ++ (k, v) :: R`. The `find?`-level
API on `RBMap` gives us `none`/`some v'` — we marry the two via the
RBNode layer.

## Erase

Batteries has **no** `toList_erase` lemma. We derive it here. First we
prove `append_toList` at the RBNode level (concat of toLists under the
internal `RBNode.append` used in `del .eq`). Then we prove the key
lemma `del_toList_filter`: for sorted `t` and a strict cut,
`(t.del cut).toList = t.toList.filter (cut · ≠ .eq)`. The proof goes
by induction on the node and case-splits on `cut y` at the root, using
`balLeft_toList` / `balRight_toList` / `append_toList`.

Lifted to the RBMap layer, this becomes:
`(t.erase k).toList = t.toList.filter (compare k ·.1 ≠ .eq)`.
The `not_mem` case uses `find?_some` from sortedness; the `mem` case
combines this filter characterization with `mem_toList_unique` +
`Nodup` to isolate the single removed entry.

## Lemmas

- `totalBalance_eq_sum`  L1-G  fold ↔ `List.sum`.
- `totalBalance_insert_of_not_mem`  L1-A.
- `totalBalance_insert_of_mem`  L1-B.
- `totalBalance_erase_of_mem` / `_of_not_mem`  L1-C.
- `findD_toNat_le_totalBalance`  L1-F.
- `totalBalance_insert_sub`  L1-D wrapper.
- `totalBalance_erase_eq`  L1-E wrapper.
-/

namespace EvmSmith.Layer1

open EvmYul Batteries

/-- Sum of stored token balances, taken in `ℕ` after `.toNat`. -/
def totalBalance (t : RBMap UInt256 UInt256 compare) : ℕ :=
  t.foldl (fun acc _k v => acc + v.toNat) 0

/-! ### L1-G: fold ↔ `List.sum` bridge -/

/-- L1-G. `totalBalance t` equals the sum of `.toNat` of each value in
    `t.toList`. -/
theorem totalBalance_eq_sum (t : RBMap UInt256 UInt256 compare) :
    totalBalance t = (t.toList.map (fun p => p.2.toNat)).sum := by
  show t.foldl (fun acc _k v => acc + v.toNat) 0
     = (t.toList.map (fun p => p.2.toNat)).sum
  rw [RBMap.foldl_eq_foldl_toList]
  generalize t.toList = L
  clear t
  suffices h : ∀ (init : ℕ),
      L.foldl (fun init p => init + p.2.toNat) init
        = init + (L.map (fun p => p.2.toNat)).sum by
    simpa using h 0
  intro init
  induction L generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    ring

/-! ### List-sum helpers for concrete `toList` shapes -/

private theorem sum_map_toNat_append (L R : List (UInt256 × UInt256)) :
    ((L ++ R).map (fun p => p.2.toNat)).sum
      = (L.map (fun p => p.2.toNat)).sum + (R.map (fun p => p.2.toNat)).sum := by
  simp [List.map_append, List.sum_append]

private theorem sum_map_toNat_append_cons
    (L R : List (UInt256 × UInt256)) (p : UInt256 × UInt256) :
    ((L ++ p :: R).map (fun q => q.2.toNat)).sum
      = (L.map (fun q => q.2.toNat)).sum + p.2.toNat
          + (R.map (fun q => q.2.toNat)).sum := by
  simp [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  ring

/-! ### Insert: RBNode split based on `zoom` outcome -/

/-- The comparator used at the RBMap (= RBSet of pairs) layer. -/
private abbrev keyCmp : UInt256 × UInt256 → UInt256 × UInt256 → Ordering :=
  Ordering.byKey Prod.fst compare

/-- RBMap-level bridge: `t.find? k = (t.1.find? (compare k ·.1)).map (·.2)`. -/
private theorem find?_eq_rbnode (t : RBMap UInt256 UInt256 compare) (k : UInt256) :
    t.find? k = (t.1.find? (fun p => compare k p.1)).map (·.2) := rfl

/-- Case split for the insert proofs. We extract the `zoom` outcome at the
RBNode level and return a concrete list decomposition. -/
private theorem insert_toList_split
    (t : RBMap UInt256 UInt256 compare) (k v : UInt256) :
    (∃ L R, t.toList = L ++ R
          ∧ (t.insert k v).toList = L ++ (k, v) :: R
          ∧ t.find? k = none) ∨
    (∃ L R k' v',
          t.toList = L ++ (k', v') :: R
          ∧ (t.insert k v).toList = L ++ (k, v) :: R
          ∧ compare k k' = .eq
          ∧ t.find? k = some v') := by
  obtain ⟨_, _, hb⟩ := t.2.out.2
  set cut : UInt256 × UInt256 → Ordering := fun p => compare k p.1 with hcut_def
  match e : RBNode.zoom cut t.1 with
  | (.nil, _) =>
    refine Or.inl ?_
    obtain ⟨L, R, hL, hR⟩ :=
      RBNode.exists_insert_toList_zoom_nil (cmp := keyCmp) (v := (k, v)) hb e
    refine ⟨L, R, ?_, ?_, ?_⟩
    · -- t.toList = L ++ R
      change t.1.toList = L ++ R
      exact hL
    · change (t.1.insert keyCmp (k, v)).toList = L ++ (k, v) :: R
      exact hR
    · -- t.find? k = none
      have hroot : t.1.find? cut = none := by
        rw [RBNode.find?_eq_zoom (p := .root), e]; rfl
      rw [find?_eq_rbnode, hroot]; rfl
  | (.node _ l ⟨k', v'⟩ r, _) =>
    refine Or.inr ?_
    obtain ⟨L, R, hL, hR⟩ :=
      RBNode.exists_insert_toList_zoom_node (cmp := keyCmp) (v := (k, v)) hb e
    -- v' is the root of the zoomed node; by zoom_zoomed₁, cut v' = .eq
    have hkeq : compare k k' = .eq := by
      have hz := RBNode.Path.zoom_zoomed₁ (cut := cut) e
      -- `hz : (node _ l ⟨k', v'⟩ r).OnRoot (cut · = .eq)` ⇒ `cut (k', v') = .eq`
      exact hz
    refine ⟨L, R, k', v', ?_, ?_, hkeq, ?_⟩
    · change t.1.toList = L ++ (k', v') :: R
      exact hL
    · change (t.1.insert keyCmp (k, v)).toList = L ++ (k, v) :: R
      exact hR
    · -- t.find? k = some v'
      have hroot : t.1.find? cut = some (k', v') := by
        rw [RBNode.find?_eq_zoom (p := .root), e]; rfl
      rw [find?_eq_rbnode, hroot]; rfl

/-! ### L1-A: insert a fresh key -/

/-- L1-A. Inserting a new key adds its value (as a `ℕ`) to the total. -/
theorem totalBalance_insert_of_not_mem
    (t : RBMap UInt256 UInt256 compare) (k v : UInt256)
    (hk : t.find? k = none) :
    totalBalance (t.insert k v) = totalBalance t + v.toNat := by
  rcases insert_toList_split t k v with
    ⟨L, R, hT, hIns, _⟩ | ⟨L, R, k', v', _, _, _, hFound⟩
  · rw [totalBalance_eq_sum, totalBalance_eq_sum, hT, hIns]
    rw [sum_map_toNat_append L R, sum_map_toNat_append_cons L R (k, v)]
    ring
  · -- Contradicts hk
    rw [hFound] at hk; cases hk

/-! ### L1-B: insert over an existing key -/

/-- L1-B. Inserting at an existing key swaps the old value for the new. -/
theorem totalBalance_insert_of_mem
    (t : RBMap UInt256 UInt256 compare) (k v v' : UInt256)
    (hk : t.find? k = some v') :
    totalBalance (t.insert k v) + v'.toNat = totalBalance t + v.toNat := by
  rcases insert_toList_split t k v with
    ⟨L, R, _, _, hNone⟩ | ⟨L, R, kExist, vExist, hT, hIns, _, hFound⟩
  · rw [hNone] at hk; cases hk
  · -- vExist = v' from hFound = hk
    have hvEq : vExist = v' := by
      rw [hFound] at hk
      exact Option.some.inj hk
    rw [totalBalance_eq_sum, totalBalance_eq_sum, hT, hIns]
    rw [sum_map_toNat_append_cons L R (k, v),
        sum_map_toNat_append_cons L R (kExist, vExist), hvEq]
    ring

/-! ### Erase: toList permutation via membership + sortedness -/

/-- The pair-level comparator agrees with key-level `compare` on `.1`. -/
private theorem keyCmp_apply (p q : UInt256 × UInt256) :
    keyCmp p q = compare p.1 q.1 := rfl

/-- For RBMap, elements of `toList` are uniquely keyed: if two pairs have
equal keys under `compare`, they are the same pair. -/
private theorem mem_toList_key_unique
    {t : RBMap UInt256 UInt256 compare} {p q : UInt256 × UInt256}
    (hp : p ∈ t.toList) (hq : q ∈ t.toList)
    (he : compare p.1 q.1 = .eq) : p = q :=
  RBMap.mem_toList_unique hp hq he

/-- `Std.TransCmp` for the pair-level key comparator, needed by `cmpLT_iff`. -/
private instance : Std.TransCmp (fun (x y : UInt256 × UInt256) => compare x.1 y.1) :=
  inferInstanceAs (Std.TransCmp (Ordering.byKey Prod.fst (compare : UInt256 → _ → _)))

/-- The list of pairs in a `toList` is `Nodup`. -/
private theorem toList_nodup (t : RBMap UInt256 UInt256 compare) :
    t.toList.Nodup := by
  have hp := RBMap.toList_sorted (t := t)
  -- `Pairwise (cmpLT ...) → Pairwise (· ≠ ·)`
  have : t.toList.Pairwise (fun p q => p ≠ q) := by
    refine hp.imp ?_
    intro a b hab heq
    subst heq
    -- `hab : RBNode.cmpLT (fun x y => compare x.1 y.1) a a`
    -- destructure the `Nonempty` witness directly
    obtain ⟨hab'⟩ := hab
    have hv : compare a.1 a.1 = .lt := hab'
    have hrefl : compare a.1 a.1 = .eq := Std.ReflCmp.compare_self
    rw [hrefl] at hv; cases hv
  exact this

/-! ### Erase: `del_toList_filter` at RBNode level by induction -/

/-- Structural helper: if `∀ x ∈ L, Q x`, then `L.filter Q = L`. -/
private theorem filter_eq_self_of_all {α} {L : List α} {Q : α → Bool}
    (h : ∀ x ∈ L, Q x = true) : L.filter Q = L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ha : Q a = true := h a (by simp)
    have ih' := ih fun x hx => h x (by simp [hx])
    simp [ha, ih']

/-- `append` on RBNodes preserves the concatenation of `toList`. -/
private theorem append_toList {α : Type*} :
    ∀ (l r : Batteries.RBNode α), (l.append r).toList = l.toList ++ r.toList
  | .nil, r => by simp [Batteries.RBNode.append]
  | .node _ _ _ _, .nil => by simp [Batteries.RBNode.append]
  | .node .red a x b, .node .red c y d => by
    have ih := append_toList b c
    unfold Batteries.RBNode.append
    match hbc : b.append c with
    | .node .red b' z c' =>
      have ih' : b'.toList ++ z :: c'.toList = b.toList ++ c.toList := by
        have := ih; rw [hbc] at this; simpa using this
      simp only [Batteries.RBNode.toList_node]
      -- goal: a.toList ++ x :: (b'.toList ++ z :: (c'.toList ++ y :: d.toList))
      --     = a.toList ++ x :: (b.toList ++ (c.toList ++ y :: d.toList))
      have : b'.toList ++ z :: (c'.toList ++ y :: d.toList)
           = b.toList ++ c.toList ++ y :: d.toList := by
        -- `b'.toList ++ z :: (c'.toList ++ y :: d.toList)`
        --  = `(b'.toList ++ z :: c'.toList) ++ y :: d.toList`
        rw [show b'.toList ++ z :: (c'.toList ++ y :: d.toList)
              = (b'.toList ++ z :: c'.toList) ++ y :: d.toList from by
            simp [List.append_assoc], ih']
      simp [this, List.append_assoc]
    | .nil =>
      have ih' : b.toList ++ c.toList = [] := by
        have := ih; rw [hbc] at this; simpa using this
      simp only [Batteries.RBNode.toList_node]
      have hb : b.toList = [] := List.append_eq_nil_iff.mp ih' |>.1
      have hc : c.toList = [] := List.append_eq_nil_iff.mp ih' |>.2
      simp [hb, hc]
    | .node .black a' x' b' =>
      have ih' : (Batteries.RBNode.node .black a' x' b').toList = b.toList ++ c.toList := by
        have := ih; rw [hbc] at this; exact this
      simp only [Batteries.RBNode.toList_node]
      -- goal: a.toList ++ x :: ((node black a' x' b').toList ++ y :: d.toList)
      have : (Batteries.RBNode.node .black a' x' b').toList ++ y :: d.toList
           = b.toList ++ c.toList ++ y :: d.toList := by
        rw [ih']
      simp only [Batteries.RBNode.toList_node] at this
      simp [this, List.append_assoc]
  | .node .black a x b, .node .black c y d => by
    have ih := append_toList b c
    unfold Batteries.RBNode.append
    match hbc : b.append c with
    | .node .red b' z c' =>
      have ih' : b'.toList ++ z :: c'.toList = b.toList ++ c.toList := by
        have := ih; rw [hbc] at this; simpa using this
      simp only [Batteries.RBNode.toList_node]
      have : b'.toList ++ z :: (c'.toList ++ y :: d.toList)
           = b.toList ++ c.toList ++ y :: d.toList := by
        -- `b'.toList ++ z :: (c'.toList ++ y :: d.toList)`
        --  = `(b'.toList ++ z :: c'.toList) ++ y :: d.toList`
        rw [show b'.toList ++ z :: (c'.toList ++ y :: d.toList)
              = (b'.toList ++ z :: c'.toList) ++ y :: d.toList from by
            simp [List.append_assoc], ih']
      simp [this, List.append_assoc]
    | .nil =>
      have ih' : b.toList ++ c.toList = [] := by
        have := ih; rw [hbc] at this; simpa using this
      simp only [Batteries.RBNode.toList_node, Batteries.RBNode.balLeft_toList]
      have hb : b.toList = [] := List.append_eq_nil_iff.mp ih' |>.1
      have hc : c.toList = [] := List.append_eq_nil_iff.mp ih' |>.2
      simp [hb, hc]
    | .node .black a' x' b' =>
      have ih' : (Batteries.RBNode.node .black a' x' b').toList = b.toList ++ c.toList := by
        have := ih; rw [hbc] at this; exact this
      simp only [Batteries.RBNode.toList_node, Batteries.RBNode.balLeft_toList]
      have : (Batteries.RBNode.node .black a' x' b').toList ++ y :: d.toList
           = b.toList ++ c.toList ++ y :: d.toList := by
        rw [ih']
      simp only [Batteries.RBNode.toList_node] at this
      simp [this, List.append_assoc]
  | .node .black a x b, .node .red c y d => by
    unfold Batteries.RBNode.append
    have ih := append_toList (.node .black a x b) c
    simp [Batteries.RBNode.toList_node, ih]
  | .node .red a x b, .node .black c y d => by
    unfold Batteries.RBNode.append
    have ih := append_toList b (.node .black c y d)
    simp [Batteries.RBNode.toList_node, ih]
termination_by l r => l.size + r.size
decreasing_by
  all_goals (simp only [Batteries.RBNode.size]; omega)

/-- Main RBNode-level lemma: `del cut` removes exactly the entries with `cut = .eq`. -/
private theorem del_toList_filter
    {α : Type*} {cmp : α → α → Ordering} {cut : α → Ordering}
    [Std.TransCmp cmp] [Batteries.RBNode.IsStrictCut cmp cut]
    (t : Batteries.RBNode α) (ht : t.Ordered cmp) :
    (t.del cut).toList
      = t.toList.filter (fun p => decide (cut p ≠ .eq)) := by
  induction t with
  | nil => simp [Batteries.RBNode.del]
  | node c a y b iha ihb =>
    obtain ⟨ay, yb, hoa, hob⟩ := ht
    have iha' := iha hoa
    have ihb' := ihb hob
    have hAll_a_lt_y : ∀ z ∈ a.toList, cmp z y = .lt := by
      intro z hz
      have hmem := Batteries.RBNode.mem_toList.mp hz
      have := Batteries.RBNode.All_def.1 ay z hmem
      obtain ⟨h⟩ := this
      exact h
    have hAll_y_lt_b : ∀ z ∈ b.toList, cmp y z = .lt := by
      intro z hz
      have hmem := Batteries.RBNode.mem_toList.mp hz
      have := Batteries.RBNode.All_def.1 yb z hmem
      obtain ⟨h⟩ := this
      exact h
    unfold Batteries.RBNode.del
    simp only [Batteries.RBNode.toList_node, List.filter_append, List.filter_cons]
    match hcy : cut y with
    | .lt =>
      have hbFilter : b.toList.filter (fun p => decide (cut p ≠ .eq)) = b.toList := by
        apply filter_eq_self_of_all
        intro z hz
        have hcz : cut z = .lt :=
          Batteries.RBNode.IsCut.lt_trans (hAll_y_lt_b z hz) hcy
        simp [hcz]
      have hy : decide (cut y ≠ .eq) = true := by simp [hcy]
      simp only []
      split
      all_goals
        simp only [Batteries.RBNode.balLeft_toList, Batteries.RBNode.toList_node,
                   hbFilter, iha']
        simp
    | .gt =>
      have haFilter : a.toList.filter (fun p => decide (cut p ≠ .eq)) = a.toList := by
        apply filter_eq_self_of_all
        intro z hz
        have hcz : cut z = .gt :=
          Batteries.RBNode.IsCut.gt_trans (hAll_a_lt_y z hz) hcy
        simp [hcz]
      have hy : decide (cut y ≠ .eq) = true := by simp [hcy]
      simp only []
      split
      all_goals
        simp only [Batteries.RBNode.balRight_toList, Batteries.RBNode.toList_node,
                   haFilter, ihb']
        simp
    | .eq =>
      have haFilter : a.toList.filter (fun p => decide (cut p ≠ .eq)) = a.toList := by
        apply filter_eq_self_of_all
        intro z hz
        have hcz : cut z = .gt := by
          have hE := Batteries.RBNode.IsStrictCut.exact (cmp := cmp) (y := z) hcy
          have hzy : cmp z y = .lt := hAll_a_lt_y z hz
          have hyz : cmp y z = .gt := Std.OrientedCmp.gt_iff_lt.mpr hzy
          rw [hyz] at hE; exact hE.symm
        simp [hcz]
      have hbFilter : b.toList.filter (fun p => decide (cut p ≠ .eq)) = b.toList := by
        apply filter_eq_self_of_all
        intro z hz
        have hcz : cut z = .lt := by
          have hE := Batteries.RBNode.IsStrictCut.exact (cmp := cmp) (y := z) hcy
          have hyz : cmp y z = .lt := hAll_y_lt_b z hz
          rw [hyz] at hE; exact hE.symm
        simp [hcz]
      have hy : decide (cut y ≠ .eq) = false := by simp [hcy]
      simp only [append_toList, haFilter, hbFilter]
      simp

/-- Simplified variant: `(t.erase cut).toList = t.toList.filter (cut · ≠ .eq)`. -/
theorem erase_toList_filter
    {α : Type*} {cmp : α → α → Ordering} {cut : α → Ordering}
    [Std.TransCmp cmp] [Batteries.RBNode.IsStrictCut cmp cut]
    (t : Batteries.RBNode α) (ht : t.Ordered cmp) :
    (t.erase cut).toList
      = t.toList.filter (fun p => decide (cut p ≠ .eq)) := by
  show (t.del cut).setBlack.toList
      = t.toList.filter (fun p => decide (cut p ≠ .eq))
  rw [Batteries.RBNode.setBlack_toList]
  exact del_toList_filter t ht

/-! ### L1-C: erase lemmas via the filter characterization -/

/-- RBMap-level version of `erase_toList_filter`. -/
private theorem rbmap_erase_toList_filter
    (t : RBMap UInt256 UInt256 compare) (k : UInt256) :
    (t.erase k).toList
      = t.toList.filter (fun p => decide (compare k p.1 ≠ .eq)) := by
  have ho : t.1.Ordered keyCmp := t.2.out.1
  -- The cut `fun p => compare k p.1` is a strict cut for `keyCmp`.
  -- It equals `(keyCmp (k, default))` for any default value's .2.
  have := erase_toList_filter (cmp := keyCmp)
    (cut := fun p => compare k p.1) t.1 ho
  exact this

/-- If `t.find? k = none`, then no `p ∈ t.toList` has `compare k p.1 = .eq`. -/
private theorem no_eq_of_find?_none
    {t : RBMap UInt256 UInt256 compare} {k : UInt256}
    (hk : t.find? k = none) :
    ∀ p ∈ t.toList, compare k p.1 ≠ .eq := by
  intro p hp heq
  -- If `(compare k p.1 = .eq)` then `t.findEntry? k = some p` via sortedness.
  have : t.findEntry? k = some p := RBMap.findEntry?_some.mpr ⟨hp, heq⟩
  have : t.find? k = some p.2 := by
    show (t.findEntry? k).map Prod.snd = some p.2
    rw [this]; rfl
  rw [hk] at this; cases this

theorem totalBalance_erase_of_not_mem
    (t : RBMap UInt256 UInt256 compare) (k : UInt256)
    (hk : t.find? k = none) :
    totalBalance (t.erase k) = totalBalance t := by
  rw [totalBalance_eq_sum, totalBalance_eq_sum, rbmap_erase_toList_filter]
  congr 1
  congr 1
  apply filter_eq_self_of_all
  intro p hp
  have := no_eq_of_find?_none hk p hp
  simp [this]

theorem totalBalance_erase_of_mem
    (t : RBMap UInt256 UInt256 compare) (k v : UInt256)
    (hk : t.find? k = some v) :
    totalBalance (t.erase k) + v.toNat = totalBalance t := by
  -- Find the pair `(k', v)` in `t.toList` with `compare k k' = .eq`.
  obtain ⟨k', ⟨hMem, hKeq⟩⟩ := RBMap.find?_some_mem_toList hk
  -- `t.toList = L ++ (k', v) :: R` via `List.append_of_mem`.
  obtain ⟨L, R, hSplit⟩ := List.append_of_mem hMem
  -- Show that filter removes exactly `(k', v)` and keeps `L ++ R`.
  rw [totalBalance_eq_sum, totalBalance_eq_sum, rbmap_erase_toList_filter,
      hSplit]
  -- Use `mem_toList_unique` (via pair uniqueness) to prove other elements
  -- don't compare-eq to k.
  have hNoEq : ∀ p ∈ L ++ R, compare k p.1 ≠ .eq := by
    intro p hp hpEq
    have hpIn : p ∈ t.toList := by
      rw [hSplit]
      rcases List.mem_append.mp hp with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right L (List.mem_cons_of_mem _ h)
    have h2 : compare p.1 k = .eq := by
      rw [Std.OrientedCmp.eq_comm]; exact hpEq
    have hpk : compare p.1 k' = .eq := Std.TransCmp.eq_trans h2 hKeq
    have hpEq2 : p = (k', v) := RBMap.mem_toList_unique hpIn hMem hpk
    -- p ∈ L ++ R and p = (k', v), but (k', v) ∉ L ++ R by Nodup of t.toList
    have hNodup := toList_nodup t
    rw [hSplit] at hNodup
    -- List.Nodup (L ++ (k', v) :: R) says (k', v) ∉ L ++ R.
    have : (k', v) ∉ L ++ R := by
      rw [List.nodup_append] at hNodup
      obtain ⟨_, hndR, hdisj⟩ := hNodup
      simp only [List.nodup_cons] at hndR
      intro hmem
      rcases List.mem_append.mp hmem with hL | hR
      · exact hdisj (k', v) hL (k', v) (by simp) rfl
      · exact hndR.1 hR
    apply this
    rw [← hpEq2]; exact hp
  -- Now simplify the filter expression
  have hKeyDec : decide (compare k k' ≠ .eq) = false := by simp [hKeq]
  have hLR_ok : (L ++ R).filter (fun p => decide (compare k p.1 ≠ .eq)) = L ++ R := by
    apply filter_eq_self_of_all
    intro p hp
    have := hNoEq p hp
    simp [this]
  rw [show L ++ (k', v) :: R = (L ++ [(k', v)]) ++ R from by simp]
  simp only [List.filter_append, List.filter_cons, hKeyDec, List.filter_nil]
  -- Split L.filter + R.filter; the hLR_ok lemma is about (L ++ R).
  have hL_ok : L.filter (fun p => decide (compare k p.1 ≠ .eq)) = L := by
    apply filter_eq_self_of_all
    intro p hp
    have := hNoEq p (List.mem_append_left R hp)
    simp [this]
  have hR_ok : R.filter (fun p => decide (compare k p.1 ≠ .eq)) = R := by
    apply filter_eq_self_of_all
    intro p hp
    have := hNoEq p (List.mem_append_right L hp)
    simp [this]
  rw [hL_ok, hR_ok]
  -- Goal: ((L ++ [] ++ R).map ...).sum + v.toNat = ((L ++ (k',v) :: R).map ...).sum
  simp [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  ring

/-! ### L1-F -/

theorem findD_toNat_le_totalBalance
    (t : RBMap UInt256 UInt256 compare) (k : UInt256) :
    (t.findD k ⟨0⟩).toNat ≤ totalBalance t := by
  show ((t.find? k).getD ⟨0⟩).toNat ≤ totalBalance t
  cases hfind : t.find? k with
  | none =>
    simp only [Option.getD]
    -- ⟨0⟩.toNat = 0 ≤ anything
    show (⟨0⟩ : UInt256).toNat ≤ totalBalance t
    exact Nat.zero_le _
  | some v =>
    simp only [Option.getD]
    have := totalBalance_erase_of_mem t k v hfind
    omega

/-! ### L1-D / L1-E: withdraw-step wrappers -/

/-- L1-D. Withdraw path when the storage slot strictly dominates `x`. -/
theorem totalBalance_insert_sub
    (t : RBMap UInt256 UInt256 compare) (k x s : UInt256)
    (hk : t.find? k = some s) (hxs : x ≤ s) :
    totalBalance (t.insert k (s - x)) + x.toNat = totalBalance t := by
  have h := totalBalance_insert_of_mem t k (s - x) s hk
  have hsub : (s - x).toNat = s.toNat - x.toNat := UInt256.sub_toNat_of_le hxs
  have hxs_nat : x.toNat ≤ s.toNat := hxs
  omega

/-- L1-E. Withdraw path when the slot is exactly `s`; erase branch. -/
theorem totalBalance_erase_eq
    (t : RBMap UInt256 UInt256 compare) (k s : UInt256)
    (hk : t.find? k = some s) :
    totalBalance (t.erase k) + s.toNat = totalBalance t :=
  totalBalance_erase_of_mem t k s hk

end EvmSmith.Layer1
