# Batteries / Mathlib wishlist — storage-aware EVM proofs

What we'd ideally have from upstream libraries to close slot-level
storage theorems in this repo without hand-rolled instance and lemma
boilerplate. All items are additive and relatively small. We've
worked around all of them locally — this file is the
"please-upstream-this" list, not a blocker list.

## The concrete downstream pain

`EVMYulLean` models contract storage as `Batteries.RBMap UInt256
UInt256 compare` (`EVMYulLean/EvmYul/Maps/StorageMap.lean:33`).
`Account.updateStorage k v` routes through either `RBMap.insert k v`
(if `v ≠ 0`) or `RBMap.erase k` (if `v = 0`). To prove statements
about a slot after `SSTORE`, we need:

- "slot k reads back as v" after `insert k v` (`find?_insert_of_eq`
  composed with `findD`).
- "slot k' ≠ k is unchanged" after `insert k v` (`find?_insert_of_ne`).
- "slot k reads back as 0" after `erase k`.
- "slot k' ≠ k is unchanged" after `erase k`.

Items 1-2 below are still genuine upstream gaps. Item 3 is one-line
derivations once item 2 lands.

## Items needed

### 1. `LawfulOrd` (or at least `TransCmp` + `ReflCmp`) for `UInt256`

`UInt256` is defined in `EVMYulLean/EvmYul/UInt256.lean:23` as a
single-field structure wrapping `Fin 2^256`, with `deriving BEq, Ord`.
Batteries provides `LawfulOrd (Fin n)` at
`Batteries/Classes/Order.lean:277`, but the derived `Ord UInt256`
instance is distinct from Fin's and does **not** automatically inherit
`LawfulOrd`. Without it, the `[Std.TransCmp cmp]` hypothesis of
`Batteries.RBMap.find?_insert_of_eq` cannot be discharged when `cmp =
compare : UInt256 → UInt256 → Ordering`.

**Status downstream:** worked around in
`EvmSmith/Lemmas/UInt256Order.lean` — registers
`OrientedCmp`, `TransCmp`, and `ReflCmp` instances for
`compare : UInt256 → UInt256 → Ordering` via a one-shot
`compare_eq : compare a b = compare a.val b.val` bridge. Doesn't
register `LawfulOrd` itself; `TransCmp` is what `RBMap` actually
needs.

**Proposed upstream fix** — in EVMYulLean (or Batteries itself, as a
`deriving LawfulOrd` handler):

```lean
-- in EVMYulLean/EvmYul/UInt256.lean, after the existing `deriving Ord`
instance : Std.LawfulOrd UInt256 where
  eq_swap {a b} := by cases a; cases b; exact Std.LawfulOrd.eq_swap ..
  eq_lt_iff_lt := by ...
  isLE_iff_le := by ...
  isLE_trans := by ...
```

The pattern from `LawfulOrd (Fin n)` at `Batteries/Classes/Order.lean:
277-281` applies — each field delegates to the corresponding `Fin`
field via `.val` destructuring. ~10 lines.

### 2. Batteries theorems about `RBMap.erase`

At the time of writing, `Batteries/Data/RBMap/Lemmas.lean` contains
**no** theorems about `RBMap.erase` — only `Ordered.erase` and
`Balanced.erase` at the `RBNode.Path.erase` level, which are
well-formedness properties, not what-you-get lemmas.

The four missing lemmas are:

```lean
theorem find?_erase_self [Std.TransCmp cmp] (t : RBMap α β cmp) (k : α) :
    (t.erase k).find? k = none

theorem find?_erase_of_ne [Std.TransCmp cmp] (t : RBMap α β cmp)
    {k k' : α} (h : cmp k' k ≠ .eq) :
    (t.erase k).find? k' = t.find? k'

-- And their findD / contains / mem companions.
```

These parallel the existing `find?_insert_of_eq` / `find?_insert_of_ne`
at lines 1225-1233. Proving them requires reasoning through
`RBNode.del` (the kernel of `erase`), which has `Ordered.del` and
`Balanced.del` lemmas in Batteries (`.lake/packages/batteries/
Batteries/Data/RBMap/WF.lean`) but no `find?` equivalents. Estimated
50-100 lines per theorem.

**Status downstream:** worked around piecemeal:

* `EvmSmith/Lemmas/BalanceOf.lean :: find?_erase_ne` —
  `find?_erase_of_ne` on `AccountMap`. Proven by descending through
  `RBNode.del` directly. Used by Register / WETH frame proofs to
  show that an `erase` on an unrelated key doesn't perturb the
  balance at `C`.
* `EvmSmith/Lemmas/RBMapSum.lean :: del_toList_filter` and friends
  — list-level erase characterisations sufficient for storage-sum
  reasoning over the `(UInt256 × UInt256)` pair-comparator. Used
  by the WETH solvency proof to bound `Σ storage` after an SSTORE
  that erases (i.e. writes 0 to) a slot.
* `EVMYulLean/EvmYul/Frame/StorageSum.lean` — mirrored
  storage-side erase lemmas at the `AccountMap` level for the WETH
  proof.

### 3. `findD_insert_*` / `findD_erase_*` companions

`RBMap.findD` is defined as `t.findD k v₀ = (t.find? k).getD v₀`. The
`find?_*` theorems above combine with this definition to give `findD_*`
companions one-line each:

```lean
theorem findD_insert_of_eq [Std.TransCmp cmp] (t : RBMap α β cmp)
    {k k' : α} (d : β) (h : cmp k' k = .eq) :
    (t.insert k v).findD k' d = v := by
  simp [findD, find?_insert_of_eq _ h]

theorem findD_insert_of_ne [Std.TransCmp cmp] (t : RBMap α β cmp)
    {k k' : α} (d : β) (h : cmp k' k ≠ .eq) :
    (t.insert k v).findD k' d = t.findD k' d := by
  simp [findD, find?_insert_of_ne _ h]
```

(Plus erase variants once item 2 lands.) Each ~3 lines. Trivial
upstream PR once item 2 is in.

## Scope of the upstream ask

- **Item 1** — 10 lines of instance boilerplate in EVMYulLean. Easy
  upstream PR.
- **Item 3** — 6 lines of one-liner derivations in Batteries. Trivial
  upstream PR once item 2 lands; independently mergeable for the
  insert-only variants.
- **Item 2** — 100-200 lines of real proof work. The genuinely
  non-trivial ask. A first-time Batteries contributor could plausibly
  take it on.

If items 1-3 land upstream, the local files
`EvmSmith/Lemmas/UInt256Order.lean`, `EvmSmith/Lemmas/BalanceOf.lean`
(parts of), and `EvmSmith/Lemmas/RBMapSum.lean` could shrink
substantially or disappear.
