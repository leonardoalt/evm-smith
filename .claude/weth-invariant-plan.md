# Plan — proving Weth's main invariant in Lean (v2)

**Changes vs v1** (per `weth-invariant-plan-review-1.md`):

- **Added Layer 0** (LawfulOrd / TransCmp UInt256 + UInt256 subtraction
  bridge lemmas) — a silent prerequisite v1 missed. Without these,
  every Batteries RBMap lemma that needs `[Std.TransCmp cmp]` is
  inapplicable.
- Layer 1 recommits to `exists_insert_toList_zoom_{nil,node}`
  (Batteries `RBMap/Lemmas.lean:758,767`) as the permutation
  primitive; Path 2 (direct RBNode induction) is dropped as
  unneeded.
- **L1-F wording clarified**: prevents RHS (balance-side)
  underflow, not LHS.
- **L1-G added**: `RBMap.foldl (+) 0` ↔ `totalBalance` bridge.
- Phase 0 deliverable made concrete: `def I : AccountMap .EVM →
  AccountAddress → Prop`, `def initial_state`, and the main theorem
  quantified over Υ's actual parameters rather than wrapped.
- **L3-D** (dead-account-sweep preserves C) and **L3-E** (tstorage
  wipe trivially preserves I) added.
- **Precompile frame reframed** as a single lemma covering all 10 —
  easier than v1 claimed.
- **runSeq→Ξ migration cost** called out as a named Layer 2
  sub-task — existing `runOp_*` lemmas don't directly lift to Ξ.
- **Ξ-failure / Θ-revert cases** enumerated in Layer 2.


Target theorem:

    I(s) := (Σ k ∈ storage[Weth].keys, storage[Weth].findD k 0)
              ≤ (accountMap.find? Weth).elim 0 (·.balance)

And the end-to-end claim:

    ∀ s tx, I s → I (EVM.Υ f σ H H' blocks tx S_T s).finalState

(modulo the real upstream Υ signature).

This doc lays out a concrete plan per blocker layer, then a combined
phasing that yields an **end-to-end proof skeleton with `sorry`s
early** so we can make measurable progress on one blocker at a time.

## Key design decisions up front

### Decision 1: use Batteries' `RBMap` directly. Don't wrap.

The user asked whether we could wrap the storage in a type that
carries a cached sum field (segment-tree-style). Short answer: **no,
not without forking upstream EVMYulLean**. The contract's storage
field is spelled `Batteries.RBMap UInt256 UInt256 compare` inside
`EvmYul.State.Account`. Any replacement means a fork, which cascades
into every other proof and breaks compatibility with the Yellow-Paper
formalization we rely on.

A "shadow structure maintained in parallel" approach (Lean-only,
with a simulation relation) sounds appealing but doesn't save proof
work: building the simulation still requires the same insert/erase
characterization lemmas about the underlying `RBMap`. It just moves
the difficulty rather than avoiding it.

So: we commit to proving the fold lemmas about `RBMap` directly. If
we upstream them to Batteries as a follow-up PR, great; if not,
they live in this repo's `EvmSmith/Lemmas.lean`.

### Decision 2: the invariant-preservation claim is over `Ξ` (code execution), not `runSeq`.

Weth uses JUMP/JUMPI (control flow) and CALL (recursive), so
`runSeq` on the block list is not a faithful execution model. The
right handle is the upstream `EVM.Ξ` iterator, which actually
respects jumps and dispatches CALL through `Θ`. Proofs about
"running Weth's bytecode preserves I" are proofs about `Ξ` on
our `bytecode`.

### Decision 3: use **fuel induction** to tame CALL's recursion.

`Ξ`, `Θ`, and `EVM.X` all take a `fuel : ℕ` parameter and
decrease it on recursive calls. The invariant-preservation
theorem is stated as `∀ fuel, ...` and proved by strong induction
on fuel. Reentrant calls fall back to the inductive hypothesis.

This is standard rely-guarantee reasoning; the upstream structure
cooperates because of the fuel discipline.

---

## Layer 0 — `LawfulOrd`/`TransCmp` for `UInt256`, + subtraction bridge

### Goal

Provide the typeclass instances every downstream Batteries RBMap
lemma silently expects.

    Std.TransCmp (compare : UInt256 → UInt256 → Ordering)
    Std.ReflCmp  (compare : UInt256 → UInt256 → Ordering)
    Std.LawfulEqCmp (compare : UInt256 → UInt256 → Ordering)

Plus concrete arithmetic bridges for `UInt256.sub` (wraps modulo
`2^256`) that we'll use repeatedly:

    L0-S1: b ≤ a → (a - b).toNat = a.toNat - b.toNat     -- toNat-commute
    L0-S2: b ≤ a → a - b + b = a                         -- round-trip under ≤
    L0-S3: b ≤ a → a - b ≤ a                             -- monotonicity

These don't exist in `EVMYulLean/EvmYul/UInt256.lean` (verified by
grep — zero theorems about `UInt256.sub`).

### Approach

`UInt256 { val : Fin UInt256.size }` is a single-field structure
over `Fin n`, which Batteries already equips with `LawfulOrd`
(`Classes/Order.lean:277`). Delegation pattern:

```lean
instance : Std.LawfulOrd UInt256 where
  eq_swap {a b} := by cases a; cases b; exact Std.LawfulOrd.eq_swap ..
  eq_lt_iff_lt := Std.LawfulLTCmp.eq_lt_iff_lt (α := Fin _) ...
  isLE_iff_le := ...
  isLE_trans  := ...
```

Fields delegate to the `Fin` instance via `.val` destructuring.
Similar to the `LawfulOrd (Fin n)` in Batteries.

For the subtraction lemmas: `UInt256.sub a b = ⟨a.val - b.val⟩`
and `Fin.sub` wraps. With `b ≤ a` (i.e. `b.val ≤ a.val`), the
result's underlying `Nat` is `a.val - b.val`. Proof: unfold
`UInt256.sub`, use `Fin.sub_def` + `Nat.mod_eq_of_lt` on the
non-wrapping case.

### Deliverables

1. `EvmSmith/Lemmas/UInt256Order.lean` (or similar location) —
   LawfulOrd + ReflCmp + TransCmp instances for UInt256.
2. Subtraction bridge lemmas L0-S1..L0-S3.
3. `#guard`s on concrete small values to sanity-check.





### Why this is Layer 0

Layer 1's `exists_insert_toList_zoom_*` lemmas take
`[Std.TransCmp cmp]` and `Ordered cmp t`. `Ordered cmp t` for
`t : Batteries.RBMap UInt256 UInt256 compare` needs TransCmp on
`compare : UInt256 → UInt256 → Ordering`. No instance → no lemma
→ no Layer 1. So Layer 0 genuinely has to come first.

---

## Layer 1 — Sum over the storage RBMap

### Goal

Define `totalBalance : Batteries.RBMap UInt256 UInt256 compare → UInt256`
and prove:

    L1-A: totalBalance ∅ = 0
    L1-B: t.find? k = none → totalBalance (t.insert k v) = totalBalance t + v
    L1-C: t.find? k = some w → totalBalance (t.insert k v) = totalBalance t - w + v
    L1-D: t.find? k = none → totalBalance (t.erase k) = totalBalance t
    L1-E: t.find? k = some w → totalBalance (t.erase k) = totalBalance t - w
    L1-F: ∀ k, totalBalance t ≥ t.findD k 0   — any single entry ≤ sum
    L1-G: t.foldl (fun acc _ v => acc + v) 0 = totalBalance t
                                               — bridge with plain fold

L1-F's role: combined with I, it gives `storage[k] ≤ total ≤
balance`, which prevents **RHS underflow** when Θ transfers `x` wei
out of the contract (not storage-side underflow; that is handled
independently by the bytecode's `LT` gate). Rephrased carefully
from v1 — the previous framing conflated the two underflow
concerns.

L1-G bridges the plan's original expression `RBMap.foldl (+) 0
storage` (how the invariant is naturally stated) with the
`toList`-based `totalBalance` we'll work with below. Derivable from
Batteries' `foldl_eq_foldl_toList` (`RBMap/Lemmas.lean:1130`).

### Approach — via `exists_insert_toList_zoom_*` + `Multiset.sum`

Batteries has **exactly the primitives needed** at
`RBMap/Lemmas.lean:758,767`:

```lean
RBNode.exists_insert_toList_zoom_nil :
    -- new key case:
    ∃ L R, t.toList = L ++ R       ∧ (t.insert cmp v).toList = L ++ v :: R

RBNode.exists_insert_toList_zoom_node :
    -- existing-key case:
    ∃ L R, t.toList = L ++ v' :: R ∧ (t.insert cmp v).toList = L ++ v :: R
```

Combined with `toList_sorted` (`RBMap/Lemmas.lean:1154`) which gives
`Pairwise (cmpLT …)` on `toList`, and with `cmpLT` → uniqueness
of keys (via `LawfulOrd UInt256` from Layer 0), we get:

- `toList_insert_new_perm`: `toList (t.insert k v) ~ (k,v) :: toList t`
  when `k ∉ t`.
- `toList_insert_existing_perm`: `toList (t.insert k v) ~ (k,v) ::
  (toList t).filter (·.1 ≠ k)` when `k ∈ t`.

From there, `totalBalance t := ((t.toList.map Prod.snd) :
Multiset UInt256).sum` and Mathlib's `Multiset.sum_cons`,
`Multiset.sum_filter` close L1-B/C in a few lines each.

**Erase path is harder** — Batteries has no analogue of
`exists_erase_toList_zoom_*`. Options:
- Add the analogue (prove at RBNode level;).
- Or reduce to insert: `t.erase k` can be characterized as
  "the unique tree with `toList` = `(toList t).filter (·.1 ≠ k)`"
  plus uniqueness-from-Ordered. Provable but indirect.

Go with adding `exists_erase_toList_zoom` — clean, upstreamable.

### Deliverables

1. `EvmSmith/Lemmas/RBMapSum.lean` — `totalBalance`, L1-A..L1-G,
   Multiset bridge.
2. `exists_erase_toList_zoom` as a new Batteries-style lemma
   (either local or upstream PR).
3. `#guard`s on concrete small maps.



`exists_insert_toList_zoom` reachable; erase `exists_insert_toList_zoom` reachable; erase
variant needs proving but is mechanically similar.

### Uniqueness of keys — answered

`Ordered cmp t → Pairwise (fun a b => cmpLT cmp a b) (toList t)`
(`toList_sorted`, line 1154). Combined with `LawfulOrd` from Layer
0, cmpLT is strict (`cmpLT a b ↔ a < b` and irreflexive), so
Pairwise cmpLT → Nodup on first-projections. The open question
from v1 is closed: yes, keys are unique.

---

## Layer 2 — CALL semantics and reentrancy reasoning

### Goal

Prove that running Weth's bytecode via `EVM.Ξ` preserves `I`, even
when the code makes a `CALL` to an arbitrary receiver (which can
reenter).

Mathematically the argument is simple and the user's framing is
correct:

1. Before CALL in `withdraw`: `storage[sender] -= x` has already
   fired. So `new_total = old_total - x` on the LHS of `I`. The
   RHS (`accountMap[C].balance`) is unchanged at this point. So
   after the SSTORE, `new_total ≤ balance` iff `old_total ≤
   balance + x`, which holds because `old_total ≤ old_balance`
   (invariant pre-SSTORE) and `x ≥ 0`.

2. During CALL: any code runs. By induction on fuel, any nested
   invocation of our bytecode preserves `I`. Nested invocations of
   OTHER contracts don't touch our storage or balance (frame).

3. After CALL: our contract's balance decreased by `x` (the amount
   sent). So LHS was `old_total - x`, RHS was `old_balance - x`
   (plus whatever deltas from nested reentrant deposits/withdraws
   which themselves preserve I). LHS ≤ RHS still holds.

### Structuring in Lean

**Crucial: `I` is stated over `AccountMap`, not `EVM.State`.**
Cross-frame reasoning would otherwise be ill-formed (the outer
frame's stack/memory/pc are irrelevant across a reentrant call).

```lean
def I : AccountMap .EVM → AccountAddress → Prop :=
  fun σ C =>
    match σ.find? C with
    | none => True    -- vacuous pre-deploy
    | some acc => totalBalance acc.storage ≤ acc.balance
```

The proof goes by fuel induction. The theorem statement:

```lean
theorem Ξ_preserves_I
    (fuel : ℕ) (σ : AccountMap .EVM) (C : AccountAddress)
    (hcode : σ.find? C |>.map (·.code) = some bytecode)
    -- ... other Ξ inputs
    (hI : I σ C)
    (hresult : Ξ fuel ... = .ok (_, σ', _, _)) :
    I σ' C
```

Proved by strong induction on `fuel`. The `hcode` hypothesis is
what lets us conclude that when Θ recurses with target = C, the
callee's code is our bytecode; the inductive hypothesis applies.

The key lemmas needed from upstream (or to be proved locally as
frame/bridge lemmas):

- **L2-Frame**: If a call target `T ≠ C`, then any `Θ`-call to `T`
  with code that doesn't itself reach `C` leaves
  `σ.find? C = σ'.find? C`. **Upstream `Θ` analysis required.**
- **L2-Balance-transfer**: After `Θ` completes with value transfer
  `v` from `C` to receiver `T`:
  - `σ'.find? C |>.elim 0 (·.balance) = σ.find? C |>.elim 0 (·.balance) - v`
  - `σ'.find? T |>.elim 0 (·.balance) = σ.find? T |>.elim 0 (·.balance) + v`
  (modulo the transfer actually executing — needs success conditions).
- **L2-Reentrance-preserves-I**: If the call target IS `C`, then by
  inductive hypothesis on fuel, `I` is preserved.

### Approach

**Phase 2a — `runSeq` → `Ξ` bridge.** Existing `runOp_*` step
lemmas reason about `EvmYul.step` (pure semantics). `Ξ` at
`EVMYulLean/EvmYul/EVM/Semantics.lean:525+` calls into `EVM.step`
(gas-aware, fuel-aware) which calls `EvmYul.step`. For each opcode
Weth uses, state the Ξ-level effect in the shape we need — as a
derived lemma layered on the existing runOp lemmas plus upstream
EVM.step/Ξ's extra plumbing..

**Phase 2b — precompile frame.** Verified all 10 precompiles
(`Ξ_ECREC`, `Ξ_SHA256`, …) thread σ through unchanged on success
and return `∅` on failure; Θ line 809 converts `∅` back to
pre-call σ. **Single lemma** covers all 10. 

**Phase 2c — Θ frame.** Prove L2-Frame: calls to `T ≠ C` where
T's code doesn't reach C leave σ[C] untouched. This is the main
chunk of Layer 2 work. Starting point: Θ body at Semantics.lean:
717, identify all writes to σ, case-split on T vs C..

**Phase 2d — Θ balance-transfer.** L2-Balance-transfer: one or two
lemmas about σ's value-transfer step at Θ's entry. 1 day.

**Phase 2e — reentrance.** State and prove Ξ_preserves_I by fuel
induction, using 2a-2d + Layer 1 in the body. Case-split on what
the bytecode does:
- Non-CALL opcodes: use Phase 2a step lemmas + Layer 1.
- CALL to T ≠ C: use 2c (frame).
- CALL to T = C: use IH (reentrance).
- CALL to precompile: use 2b.
- Ξ revert / OutOfFuel: σ restored (Θ line 801-804), I trivially
  preserved.
2-3 days.

### Risks

- The upstream `Θ` code is dense and has many conditional branches
  (blob-versioned hashes, precompiled contracts, static-mode,
  depth limits, etc.). Frame lemmas need to handle each.
- The fuel induction threads through several upstream types
  (`AccountMap`, `Substate`, `Batteries.RBSet AccountAddress`).
  Casts may be needed.
- Precompiled contracts (`Θ` routes some calls to hard-coded
  precompiles like SHA256 which don't touch storage). Need a frame
  lemma for these too.

### Deliverables

1. `EvmSmith/Lemmas/Theta.lean` — frame, balance-transfer,
   precompile-frame, reentrance lemmas.
2. `EvmSmith/Lemmas/Xi.lean` — the runSeq→Ξ bridge for opcodes
   Weth uses.
3. Extended `EvmSmith/Demos/Weth/Proofs.lean` invoking these to
   prove `Ξ_preserves_I` for Weth's bytecode.


plan — plan-level risk concentrates here.

---

## Layer 3 — Transaction-level induction

### Goal

Lift `Ξ_preserves_I` to the transaction level:

    theorem weth_tx_preserves_I (tx : Transaction) (s : EVM.State) :
      I s → I (EVM.Υ … tx s).finalState

And close:

    theorem weth_always_safe (txs : List Transaction) (s : EVM.State) :
      I (initial_state C) →
      I (apply_all txs (initial_state C))

### Approach

`EVM.Υ` at `EVMYulLean/EvmYul/EVM/Semantics.lean:823` does a few
things the bytecode `Ξ` doesn't: nonce bumping, gas deduction from
sender, block-level accounting, refunds, tip payment to the
beneficiary. None of these touch storage on `C`, but most touch
balances.

Specifically for `I`:

- LHS of `I` (storage sum on C): only changes via `Ξ` → covered by
  Layer 2.
- RHS of `I` (`C.balance`): changes by:
  1. The value the tx itself sends (`T.value`).
  2. Whatever `Ξ` / `Θ` does internally (covered by Layer 2).
  3. Beneficiary / miner fee — **only if C is the beneficiary**,
     which we exclude by hypothesis. Add `C ≠ beneficiary` as a
     precondition.
  4. Refund — again beneficiary-only.

So the Υ-layer work is:

- **L3-A**: Υ with recipient ≠ C and sender ≠ C doesn't modify
  `σ[C]`. (Frame, modulo beneficiary which we exclude.)
- **L3-B**: Υ with recipient = C invokes `Θ` with C as target,
  which by Layer 2 preserves `I`.
- **L3-C**: Υ with sender = C — C is the transaction originator.
  Nonce bump, gas deduction affect `C.balance`. Need a specific
  lemma. In Weth's model, C doesn't send its own transactions
  (it's a contract, not an EOA), so this case can be excluded by
  hypothesis.

Plus two further Υ-layer facts the review caught:

- **L3-D**: Υ preserves `σ.find? C |>.map (·.code) = some
  bytecode`. Υ's dead-account sweep at `Semantics.lean:941-943`
  runs `foldl erase` on accounts that are "dead" (empty code,
  nonce 0, balance 0). Weth has non-empty code → never dead →
  never erased. But the proof needs this as an explicit
  preservation lemma so the dead-sweep passes Weth untouched.
- **L3-E**: Υ wipes `tstorage := .empty` at `Semantics.lean:944`.
  Weth doesn't use TSTORE; `I` only mentions permanent storage.
  Trivially preserved. State for hygiene.

With L3-A through L3-E, the transaction-level theorem follows
from Layer 2 plus case analysis on the tx.

### Deliverables

1. `EvmSmith/Lemmas/Upsilon.lean` — frame + case-analysis lemmas
   for Υ restricted to Weth's deployment scenario, including
   L3-D (code preservation) and L3-E (tstorage wipe).
2. Top-level theorem `weth_always_safe` in `EvmSmith/Demos/Weth/Proofs.lean`.



---

## Combined phasing (skeleton-first, fill in over time)

### Phase 0 — end-to-end skeleton

Goal: the main theorem statement compiles; sorrys mark every
missing piece. Ship this FIRST so we have the shape and can
progress-track.

Concrete deliverables (not just "define things"):

- `def I : AccountMap .EVM → AccountAddress → Prop` — actual
  definition (not sorry). See Layer 2 for the shape.
- `def initial_state : AccountAddress → EVM.State` — actual
  definition. Installs Weth's bytecode at `C` with balance 0 and
  empty storage; default-zero everywhere else.
- `theorem weth_always_safe : ∀ fuel σ H_f H σ₀ blocks T S_T, I σ C
  → let r := EVM.Υ fuel σ H_f H σ₀ blocks T S_T; (r.map (·.1 |>
  I · C)).toOption.getD True` (or the concrete case-analysis
  equivalent). Proof body = `sorry`. Quantifies over Υ's **raw
  parameters** rather than wrapping — avoids having to define
  `apply_all` which would itself need to be concrete.
- A couple of inline lemmas `Layer1_sorry`, `Layer2_sorry`,
  `Layer3_sorry` that the main theorem cites, each individually
  `sorry`, so the proof's dependency graph is explicit.
- A `conservation` `#guard` in `EvmSmith/Tests/Guards.lean` that
  asserts `I` on a concrete two-user scenario by `decide` — smoke
  test.

Commit this as a visible milestone before any layer work starts.

### Phase 0.5 — Layer 0

Before any proofs about sums, close the typeclass gap.

1. `EvmSmith/Lemmas/UInt256Order.lean` — LawfulOrd + TransCmp +
   ReflCmp instances for UInt256, delegating to `Fin n`.
2. Subtraction bridge lemmas L0-S1..L0-S3 in the same file.
3. Commit.

Exit criterion: `example : Std.TransCmp (compare :
UInt256 → UInt256 → Ordering) := inferInstance` typechecks.

### Phase 1 — Layer 1

Close the storage-sum side.

1. Create `EvmSmith/Lemmas/RBMapSum.lean`. Define `totalBalance`
   via `toList.map Prod.snd |>.sum`.
2. Prove L1-A through L1-G using Batteries'
   `exists_insert_toList_zoom_*` + `toList_sorted` +
   `Multiset.sum_*`.
3. Prove a local `exists_erase_toList_zoom` (analogue of the
   insert version) if erase-case lemmas are on the critical path
   for Weth — they are, because withdrawing the full balance
   triggers `storage.erase` via `Account.updateStorage`.
4. Replace the Layer-1 sorrys in `Proofs.lean` with real proofs.
5. Commit.

Exit criterion: `I`'s LHS manipulation is fully proved for deposit
and withdraw SSTORE steps (both `insert` and `erase` paths). Layer
2 and 3 sorrys remain.

### Phase 2 — Layer 2

Close the CALL reasoning. This is the biggest chunk.

1. `EvmSmith/Lemmas/Xi.lean` — runSeq→Ξ bridge for Weth's opcodes.
2. `EvmSmith/Lemmas/Theta.lean` — frame (L2-Frame), balance-transfer
   (L2-Balance-transfer), precompile-frame (trivial — single lemma),
   reentrance via fuel induction.
3. Extend `EvmSmith/Demos/Weth/Proofs.lean` with `Ξ_preserves_I`
   for Weth's bytecode.
4. Enumerate failure paths (revert, out-of-gas, out-of-fuel) —
   Θ restores σ, I preserved trivially.
5. Replace the Layer-2 sorrys.
6. Commit.

Exit criterion: single-transaction safety proved end-to-end.

### Phase 3 — Layer 3

Glue transaction-level.

1. Create `EvmSmith/Lemmas/Upsilon.lean`.
2. Prove L3-A, L3-B, L3-C, **L3-D** (code preservation through
   dead-sweep), **L3-E** (tstorage wipe) case analysis on Υ.
3. Replace final sorrys in `Proofs.lean` — `weth_always_safe` goes
   sorry-free.
4. Commit.

Exit criterion: `#print axioms weth_always_safe` shows only
accepted Lean/Mathlib/Batteries axioms — no project sorrys.

### Phase 4 — cleanup + upstream (optional, 1 week)

1. Extract the Layer-1 RBMap lemmas into a form suitable for a
   Batteries upstream PR.
2. Consider whether Layer-2 frame lemmas should live in EVMYulLean
   (benefits every consumer of the upstream) or stay downstream.
3. Documentation pass.

---

## Risk register

- **Phase 1 Path 1 may fail** if Batteries' `toList` membership
  lemmas aren't enough to extract the permutation. Fallback to
  Path 2 (direct RBNode induction). Budget: +1 week.
- **Phase 2 scope creep**. Θ has many branches (precompiles,
  blob-hashes, static-mode). Can't skip; the frame lemma must
  hold for all of them. Budget: +1 week if branches are gnarly.
- **Phase 3 depends on specific Υ shape**. If `EVM.Υ`'s signature
  changes upstream, our lemmas break. Mitigate by pinning the
  EVMYulLean tag and noting the dependency in comments.
- **Layer 2's reentrance proof may need `C ≠ source` hypothesis**
  (i.e., Weth doesn't call itself via its own transactions). Weth
  is a contract that doesn't originate transactions, so this is
  natural — document it as a precondition.
- **Underflow**. The invariant says `total ≤ balance`. On a
  withdraw-decrement, we need `storage[sender] ≥ x` to avoid
  underflow of both LHS and `balance[sender]`. This is the
  bytecode's `LT` gate, and its correctness is already covered by
  the deposit/withdraw per-call theorems from Phase 1+2. We need a
  supporting lemma: `I s → storage[sender] ≤ total ≤ balance`,
  hence any x ≤ storage[sender] is safely subtractable.

## Acceptance

- `#print axioms weth_always_safe` clean (no project sorrys).
- `forge test` still passes (regression guard).
- Top-level `lake build` clean.
- `.claude/weth-invariant-blockers.md` updated to reflect closed
  blockers.
- Upstream contribution (Layer 1 → Batteries) drafted as a
  separate PR, if appropriate.
