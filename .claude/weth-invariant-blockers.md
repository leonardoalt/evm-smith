# Blockers for proving Weth's main safety invariant in Lean

Framing note: this repo exists to demonstrate **Lean proofs** about
raw EVM bytecode. Foundry-side invariant testing is the fallback we
reach for when Lean is blocked, not the primary objective. For Weth,
the main safety claim

    Σ_{addr} storage[Weth][addressSlot(addr)] ≤ accountMap[Weth].balance

is **not** currently provable in Lean. Foundry fuzzing at 256 × 50 =
12 800 transition checks is not a substitute for a proof. This
document captures what specifically blocks the proof, to inform a
future attack.

## Three nested layers of missing machinery

Each layer is a prerequisite for the next. Nothing below is a
shortcut.

### Layer 1 — `Batteries.RBMap.foldl` lemmas (Batteries PR-sized)

The left-hand side of the invariant is `RBMap.foldl (+) 0
storage`. To prove the deposit step "after `storage[sender] = old +
v`, the sum increased by exactly `v`" we need equations like:

```
foldl f init (t.insert k v) = …  -- in terms of foldl t and v,
                                 -- conditional on whether k ∈ t
foldl f init (t.erase k)    = …  -- similarly
```

Batteries has **zero** theorems about `RBMap.foldl`'s interaction
with `insert` / `erase` at the time of writing (verified by grep).
Proving them from scratch requires reasoning at the `RBNode` level
and handling the `Balanced` / `Ordered` invariants Batteries does
have. Same class of gap that blocks the slot-level theorems in
`EvmSmith/Demos/Register/Proofs.lean`.

Without these, we literally can't write the equation "the sum
changed by `v`" in Lean. Effort: ~1-2 weeks of focused Lean work,
or a Batteries upstream PR.

### Layer 2 — CALL's effect on `accountMap[C].balance` (upstream modeling)

The right-hand side of the invariant is
`accountMap[Weth].balance`. In `withdraw`, this is modified by the
`CALL` opcode transferring `x` wei to the user. That transfer is
**not in our bytecode** — it happens inside `EvmYul.EVM.call` → `Θ`
→ `Ξ` → recursive new-call-frame setup, value transfer, recursive
execution, unwind (see `EVMYulLean/EvmYul/EVM/Semantics.lean:141,
717, 525`).

Our `runSeq`-based proof framework doesn't model any of that;
`EvmYul.step` on `.CALL` just pops 7 values and pushes 1 without
actually moving balances. To reason about
`accountMap[Weth].balance -= x` after CALL, we'd have to prove
theorems about `Θ`, which is ~150 lines of mutually-recursive
message-call + contract-creation semantics threaded through fuel.

Effort: genuinely substantial — this is upstream semantics
modeling, not just a Batteries PR. Reasonable first step: an
axiomatized *specification* of the CALL balance transfer (stated as
a theorem, proved as a `sorry`) so downstream proofs can depend on
it; the actual proof comes later.

### Layer 3 — Transaction-level induction schema (new surface in this repo)

Even with layers 1 and 2 solved, "the invariant holds *across any
sequence* of calls to deposit / withdraw / other" requires a
transaction-level induction. We'd need:

- A predicate `I : EVM.State → Prop` capturing the invariant.
- `I` holds for the initial post-deploy state (trivial).
- `∀ tx, I s → I (EVM.Υ s tx)` — every transaction preserves `I`.

`EVM.Υ` is the upstream transaction-execution function
(`EvmYul/EVM/Semantics.lean:823`). We've **never proved anything at
this level** in this repo — all prior theorems are at the
`runSeq`/single-call-frame level. This is a new modeling surface
requiring reachability reasoning, case analysis over transaction
types, etc.

Effort: weeks of framework-building. Arguably the most
architecturally important missing piece, since it's what makes
"inductive invariants about contract state" expressible at all.

## Realistic plans of attack

In order of increasing completeness:

### (A) Axiomatize layers 2 and 3; prove layer 1 genuinely

Treat CALL's balance effect and the transaction-level schema as
stated-but-unproved axioms. Prove the storage-sum side properly:
layer 1 plus `sstore_accountMap`. This closes the *contribution of
our bytecode* to the invariant. The ETH-balance side and the
cross-transaction induction are axioms that future work can
discharge.

Honest partial result. Demonstrates "our Lean infrastructure
handles sums over maps" and "our bytecode preserves the storage-
side of the invariant". Doesn't demonstrate the end-to-end safety
claim but is an honest step toward it.

Effort: 1-2 weeks (dominated by the RBMap fold proofs).

### (B) Full proof end-to-end

All three layers. Includes upstream contributions to Batteries
(layer 1) and possibly EVMYulLean (layer 2's Θ theorems).

Effort: on the order of months, not weeks, if done correctly.
Appropriate for a serious formal verification project; too heavy
for a demo deliverable.

### (C) Pivot: restrict to contracts we can actually prove

Skip CALL-using contracts entirely. Build a backlog of storage-only
contracts (ERC-20-without-external-calls-during-state-changes, a
counter, a permission registry, etc.) and prove inductive invariants
*for those* using what we can close with RBMap fold lemmas alone.
Demonstrates the "AI writes bytecode + Lean proves it safe" story
on a smaller but fully-proved set of examples.

Effort: 1-2 weeks for one good example (needs layer 1 too); avoids
the CALL machinery entirely.

## Recommendation for next attack

Plan (A) if we want to keep Weth as a showcase and be honest about
what's proved. Plan (C) if we want to actually *prove end-to-end*
what we ship. My read is that (C) is the more defensible path for a
"Lean proofs matter" project, but (A) is the natural continuation
of the current codebase.

Both need layer 1 first. Layer 1 is a good standalone milestone
regardless of which direction we take.
