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
     (= `addressSlot`: the address used *directly* as the slot key, a
     deliberate simplification — not Solidity's hashed mapping layout).
   - `tokenBalanceOf σ weth user` — one user's recorded token balance.
   - `recordedTokenSupply σ weth` — total recorded tokens (= `storageSum`).
3. **The property** — `Solvent σ weth := recordedTokenSupply ≤ ethBalance`.
   "WETH never owes more ETH than it holds." (`≤`, not `=`, with the
   over-collateralisation reason spelled out.)
4. **The assumptions** — `SolvencyAssumptions` (= the existing
   `WethAssumptions`), with each of the 5 fields explained in plain
   terms.
5. **Running a transaction** — `ExecContext` (bundles `Υ`'s plumbing:
   fuel, base fee, headers, processed blocks), `runTx` (thin wrapper
   over `EVM.Υ`), `SolventAfter` (hides the `Except`/tuple shape).
6. **The guarantee** — `weth_is_always_solvent`: if WETH is `Solvent`
   before any transaction, it is `Solvent` after. The statement reads:

   ```lean
   theorem weth_is_always_solvent
       (ctx : ExecContext) (σ : AccountMap .EVM)
       (tx : Transaction) (S_T weth : Address)
       (hWellFormed    : StateWF σ)
       (hSolventBefore : Solvent σ weth)
       (hNotSender     : weth ≠ S_T)
       (hNotMiner      : weth ≠ ctx.block.beneficiary)
       (hTxValid       : TxValid σ S_T tx ctx.block ctx.baseFee)
       (hAssumptions   : SolvencyAssumptions ctx σ tx S_T weth) :
       SolventAfter ctx σ tx S_T weth
   ```

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

## Review feedback addressed (round 2)

- **Storage layout corrected.** The earlier text wrongly called the
  layout "Solidity's `mapping` at slot 0". It is not: `addressSlot a =
  UInt256.ofNat a.val` uses the address *directly* as the slot key (no
  `keccak256` hashing) — a deliberate simplification. The spec now says
  so, and notes the proof only needs slot injectivity. (`REPORT_WETH.md`
  already described it correctly. The same outdated wording still lives
  in `Invariant.lean` and `SOLVENCY_INFORMAL.md` docstrings — left
  untouched to avoid editing the proof files, but worth a follow-up.)
- **Headline theorem made readable.** Bundled `Υ`'s five plumbing
  arguments into `ExecContext`, wrapped `EVM.Υ` as `runTx`, and hid the
  `Except`/4-tuple `match` behind `SolventAfter`. The statement now reads
  as `… : SolventAfter ctx σ tx S_T weth` with a short, well-named
  hypothesis list, instead of an inline `match EVM.Υ … with | .ok …`.
  Still proved by the one-line bridge to `weth_solvency_invariant`.

## Notes / follow-ups (not done, keeping v1 simple)

- A small local settings file `.claude/settings.local.json` was added to
  disable background worktree isolation for this repo, so the build
  could reuse the existing `.lake` cache (a fresh worktree would force a
  multi-hour full rebuild). It is uncommitted and local-only.
- v2 direction (per the task): a Solidity-subset-like eDSL. The current
  spec already isolates the readable surface, so v2 can target
  generating `Spec.lean`-shaped definitions from the eDSL.
