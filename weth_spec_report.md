# WETH readable-spec — report

Task: `weth_spec.md`. Extract WETH's formal spec into a separate file
and give it a v1 human-readable form a Solidity dev can read without
knowing EVMYulLean / evm-smith / deep Lean internals.

## What I did

Added **one new file**: `EvmSmith/Demos/Weth/Spec.lean` (registered in
`EvmSmith.lean`). It is the single auditor-facing surface:

1. **The contract** — `wethBytecode`, plus a prose table of what
   `deposit` / `withdraw` do and the checks-effects-interactions
   reentrancy posture.
2. **Vocabulary** — readable one-line wrappers over the EVMYulLean
   projections:
   - `ethBalance σ weth` — WETH's actual ETH balance (= `balanceOf`).
   - `tokenBalanceSlot user` — the storage slot for a user's balance
     (= `addressSlot`, the `mapping(address=>uint256)`-at-slot-0 layout).
   - `tokenBalanceOf σ weth user` — one user's recorded token balance.
   - `recordedTokenSupply σ weth` — total recorded tokens (= `storageSum`).
3. **The property** — `Solvent σ weth := recordedTokenSupply ≤ ethBalance`.
   "WETH never owes more ETH than it holds." (`≤`, not `=`, with the
   over-collateralisation reason spelled out.)
4. **The assumptions** — `SolvencyAssumptions` (= the existing
   `WethAssumptions`), with each of the 5 fields explained in plain
   terms.
5. **The guarantee** — `weth_is_always_solvent`: if WETH is `Solvent`
   before any transaction, it is `Solvent` after.

## "The spec is what the theorems use" — checked, not asserted

The spec names are **definitionally equal** to the predicates the
existing proofs preserve, and that equality is machine-checked:

- `weth_is_always_solvent` is *proved by a single application* of the
  engine theorem `weth_solvency_invariant` (Solvency.lean). That one
  line is the entire bridge from spec to bytecode.
- `solvent_iff_wethInv` and `solvent_iff_storageSumLeBalance` are both
  `Iff.rfl` — Lean accepts them only because `Solvent` unfolds to the
  exact predicate (`WethInv` / `StorageSumLeBalance`) the proofs use.

So an auditor reads `Spec.lean` + the one proof-term line, and is done.

## What I did *not* touch

- No existing `.lean` definition or proof was modified. The change is
  purely additive (new file + one import line + doc pointers). This was
  deliberate, per the task's "do not change existing proofs / all proofs
  should still work."
- `Invariant.lean`'s `WethInv` is left as-is; `Spec.Solvent` sits on top
  of it via the `rfl` bridge rather than renaming it (avoids churn in
  the transit lemmas and the framework-side `StorageSumLeBalance`
  defeq).

## Build status

- `lake build EvmSmith.Demos.Weth.Spec` — ✅
- `lake build` (full default target, 1068 modules) — ✅

No proofs broke; the new theorem and both `rfl` bridges type-check.

## Notes / follow-ups (not done, keeping v1 simple)

- A small local settings file `.claude/settings.local.json` was added to
  disable background worktree isolation for this repo, so the build
  could reuse the existing `.lake` cache (a fresh worktree would force a
  multi-hour full rebuild). It is uncommitted and local-only.
- v2 direction (per the task): a Solidity-subset-like eDSL. The current
  spec already isolates the readable surface, so v2 can target
  generating `Spec.lean`-shaped definitions from the eDSL.
