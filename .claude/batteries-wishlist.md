# Batteries / Mathlib wishlist — storage-aware EVM proofs

What we'd need from upstream libraries to close slot-level storage
theorems in this repo (and any future storage-using program proofs)
without hand-rolled instance boilerplate. All items are additive and
relatively small.

## The concrete downstream pain

`EVMYulLean` models contract storage as `Batteries.RBMap UInt256
UInt256 compare` (`EVMYulLean/EvmYul/Maps/StorageMap.lean:33`).
`Account.updateStorage k v` routes through either `RBMap.insert k v`
(if `v ≠ 0`) or `RBMap.erase k` (if `v = 0`). To prove statements
about a slot after `SSTORE`, we'd need:

- "slot k reads back as v" after `insert k v` (`find?_insert_of_eq`
  composed with `findD`).
- "slot k' ≠ k is unchanged" after `insert k v` (`find?_insert_of_ne`).
- "slot k reads back as 0" after `erase k`.
- "slot k' ≠ k is unchanged" after `erase k`.

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

**Proposed fix** — upstream in EVMYulLean (or Batteries itself, as a
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

Alternative: a `deriving LawfulOrd` handler in Lean 4 (outside our
scope; deeper tooling work).

### 2. Batteries theorems about `RBMap.erase`

At the time of writing, `Batteries/Data/RBMap/Lemmas.lean` contains
**no** theorems about `RBMap.erase` — only `Ordered.erase` and
`Balanced.erase` at the `RBNode.Path.erase` level, which are well-formedness
properties, not what-you-get lemmas.

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

(Plus erase variants once item 2 lands.) Each ~3 lines.

## What this would unlock in this repo

With items 1-3, `EvmSmith/Demos/Register/Proofs.lean` can add:

- **Slot-level functional correctness**: `storageAt postState
  codeOwner (addressSlot sender) = x`, for all `x` (including `x =
  0`).
- **Slot frame**: for `k ≠ addressSlot sender`, `storageAt postState
  codeOwner k = storageAt s0 codeOwner k`.

Both theorems are currently stated in the file's docstring but not
proved, with this file as the reference for why.

## Scope of the ask

- **Item 1** — 10 lines of instance boilerplate in EVMYulLean. Easy
  upstream PR.
- **Item 3** — 6 lines of one-liner derivations in Batteries. Trivial
  upstream PR once item 2 lands; independently mergeable for the
  insert-only variants.
- **Item 2** — 100-200 lines of real proof work. The genuinely
  non-trivial ask. A first-time Batteries contributor could plausibly
  take it on.

If any of these land, the downstream pattern is straightforward:

```lean
-- becomes provable without sorry or helper boilerplate
theorem program_sets_sender_slot (s0) (x) (...) (hacct : ...)
    : storageAt (postState s0 x) codeOwner (addressSlot sender) = x := by
  rw [program_updates_caller_account ..., Account.updateStorage]
  split_ifs
  · exact Batteries.RBMap.findD_erase_self ...
  · exact Batteries.RBMap.findD_insert_of_eq ...
```
