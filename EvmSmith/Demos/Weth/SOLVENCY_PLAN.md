# Weth solvency invariant — Lean formalization plan

Maps the informal proof in `SOLVENCY_INFORMAL.md` onto our existing
framework, identifies the reusable pieces, and lists the new work
needed (and where in the framework it should live).

## Headline theorem (target)

In `EvmSmith/Demos/Weth/Solvency.lean` (new):

```lean
theorem weth_solvency_invariant
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress)
    (hWF : StateWF σ)
    (hInv : WethInv σ C)              -- pre-state already solvent
    (hS_T : C ≠ S_T)                  -- Weth not the tx sender
    (hBen : C ≠ H.beneficiary)        -- Weth not the miner
    (hValid : TxValid σ S_T tx H H_f)
    (hAssumptions : WethAssumptions σ fuel H_f H H_gen blocks tx S_T C) :
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => WethInv σ' C
    | .error _ => True
```

where `WethInv σ C := balanceOf σ C ≥ tokenSum σ C` and `tokenSum σ C`
is the storage-sum primitive defined below.

## What we reuse from the Register session

### Out of the box — no new work

* **`Υ_balanceOf_ge`** form (UpsilonFrame.lean): the *consumer entry
  shape* that takes Weth-side preconditions + a contract-specific Ξ
  witness + a tail invariant + a body-factorisation. Same skeleton.
* **`StepShapes` / `PcWalk`**: the 81 shape lemmas and 54 `_at_pc`
  wrappers cover *every* opcode in Weth's bytecode (`PUSH1`, `PUSH2`,
  `PUSH4`, `CALLDATALOAD`, `SHR`, `DUP1..DUP5`, `SWAP1..SWAP3`, `EQ`,
  `JUMPI`, `JUMPDEST`, `LT`, `SUB`, `ADD`, `CALLER`, `CALLVALUE`,
  `SLOAD`, `SSTORE`, `GAS`, `CALL`, `ISZERO`, `POP`, `STOP`,
  `REVERT`). No new shape lemmas needed — the Step-2 coverage we
  did was already aimed at this.
* **`ΞPreservesAtC_of_Reachable`** entry point: same shape applies.
  We define `WethTrace : EVM.State → Prop` analogous to
  `RegisterTrace`, with a much richer per-PC stack/storage clause.
* **`MutualFrame.Θ_balanceOf_ge` / `Λ_balanceOf_ge` / `Ξ_balanceOf_ge_bundled`**
  for the *outer* Ξ frames at codeOwner ≠ C: these directly give us
  "balance at C is monotone across non-Weth frames", which we use in
  the informal proof's "Frames at codeOwner ≠ C" paragraph.
* **`StateWF`** + `boundedTotalDouble` for no-wrap arithmetic.
* **Real-world axioms**: T2 (precompile purity), T5 (Keccak collision)
  used directly as in Register.
* **`DeployedAtC` predicate pattern**: copy-paste with rename to
  `WethDeployedAtC`.
* **`Phase A leaf infrastructure`**: `selfdestruct_preserves_SD_exclude_C`,
  `EvmYul.step_preserves_selfDestructSet`, the 9 precompile
  substate-purity lemmas. We need their analogue for storage
  preservation; see new work below.

### Pattern-reuse — same shape, new content

* **`WethTrace`**: same predicate pattern as `RegisterTrace` — an
  outer disjunction over Weth's reachable PC values. Weth has more
  reachable PCs (~30+ vs Register's 14) and the per-PC stack-shape
  invariants are more elaborate (storage values flow through stack
  positions). ~150 LoC for the predicate definition; ~600-1000 LoC
  for `WethTrace_step_preserves` (the bytecode walk).
* **6 closure lemmas** for `ΞPreservesAtC_of_Reachable`: same
  signatures as Register's `RegisterTrace_*` closures
  (`_Z_preserves`, `_step_preserves`, `_decodeSome`, `_op_in_set`,
  `_v0_at_CALL`, `_initial`).
  - `_v0_at_CALL` is the **interesting** one: Register had stack[2]=0
    at its single CALL. Weth's CALL has stack[2] = `x` (the withdraw
    amount), which is NOT zero. This is the load-bearing change —
    see "New work" below.

### Real-world structural assumptions, mirroring Register

A `WethAssumptions` record (analogous to the assumption pack we'd
have used for Register if we'd bundled them):

```lean
structure WethAssumptions
    (σ : AccountMap .EVM) (fuel H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress) : Prop where
  deployed   : DeployedAtC C
  sdExcl     : WethSDExclusion σ fuel H_f H H_gen blocks tx S_T C
  deadAtσP   : WethDeadAtσP    σ fuel H_f H H_gen blocks tx S_T C
  -- Plus Weth-specific structural facts; see ASSUMPTIONS.md.
```

## Genuinely new work

### A. Storage-sum primitive (new file)

`EVMYulLean/EvmYul/Frame/StorageSum.lean` (new):

```lean
/-- Sum of all entries in C's storage map, mapped to ℕ via `.toNat`. -/
def storageSum (σ : AccountMap .EVM) (C : AccountAddress) : ℕ :=
  ((σ.find? C).map (·.storage)).getD .empty
    |>.foldl (fun acc _ v => acc + v.toNat) 0

theorem storageSum_insert_at_existing_slot ...
theorem storageSum_insert_at_fresh_slot ...
theorem storageSum_account_unchanged ...
```

Pattern: mirrors `Projection.lean`'s `totalETH`/`balanceOf`/`StateWF`
helpers. Estimated ~200-300 LoC. Depends on the
**Batteries-RBMap-foldl wishlist** (`.claude/batteries-wishlist.md`)
that we already documented. If those Batteries lemmas don't exist
yet, we may need a small set of local helpers.

### B. SSTORE storage-sum delta lemma

```lean
theorem sstore_storageSum_delta
    (σ : AccountMap .EVM) (a : AccountAddress) (slot val : UInt256) :
    storageSum (σ.sstoreAt a slot val) C =
      if a = C then storageSum σ C + val.toNat - oldVal.toNat
               else storageSum σ C
```

Lives in `EvmYul.Frame.StorageSum`. Used by every SSTORE step in
Weth's walk. ~50 LoC.

### C. WethInv predicate + transit lemmas

`EvmSmith/Demos/Weth/Invariant.lean` (new):

```lean
def tokenSum := storageSum  -- alias for Weth's terminology
def WethInv (σ : AccountMap .EVM) (C : AccountAddress) : Prop :=
  storageSum σ C ≤ balanceOf σ C
```

Plus transit lemmas: `WethInv` preserved by sender debit at
`S_T ≠ C`, by Θ value transfer in (β credited, S unchanged), etc.
~100 LoC.

### D. Non-zero-value CALL handling (Step 4 of GENERALIZATION_PLAN)

The big new framework piece. Weth's withdraw emits a CALL with
`value = x ≠ 0`. Our `step_CALL_arm_at_C_v0` chain assumes value=0.
For Weth, we need either:

* **Option D.1**: a sibling `step_CALL_arm_at_C_invariant` that takes
  *the invariant* as the bundled output, not balance-monotonicity.
  The proof: the value transfer at the at-C frame debits `value`
  from C; the inner Ξ at recipient ≠ C is monotone-non-decreasing
  on β(C) (existing infrastructure). Net Δβ at C: `≥ -value`. The
  caller of withdraw's CALL pairs this with the SSTORE that
  decremented `storage[C][CALLER]` by `value`, so Δ(β − S) ≥ 0.

* **Option D.2**: instrument the Weth-specific walk to, at the CALL
  step, consume both the SSTORE-decrement-fact AND the CALL-debit-fact
  in a single step-pair lemma `withdraw_CALL_step_preserves_invariant`
  that bypasses the framework's step bundle for this one combined
  pair of bytecode steps.

D.2 is more tractable as a starting point — it bypasses framework
extension and instead handles the value-CALL specifically for Weth.
D.1 is the cleaner long-term design but requires framework changes.

Estimated effort:
- D.2: ~300-500 LoC of Weth-specific reasoning. Sufficient to close
  this proof.
- D.1: ~800-1500 LoC of framework extension; benefits future
  contracts emitting non-zero-value CALLs.

### E. Reentrancy handling for withdraw

Reentrant calls into Weth's withdraw must terminate (eventually) and
preserve I. Two paths:

* **E.1 (clean)**: prove the reentrant invariant via fuel induction
  inside `WethTrace_step_preserves`. Each reentrant withdraw frame
  satisfies the same I via IH at smaller fuel.
* **E.2 (cheaper)**: assume an extra hypothesis "no reentrancy" — but
  this is ugly because reentrancy IS the point.

E.1 is the right answer. The induction structure mirrors Register's
self-call handling (Register's CALL recipient could be C, our infra
handled it via fuel-bounded `ΞAtCFrame`). The new wrinkle is that
storage state is mutated *between* the recursive calls.

### F. Body-factor, tail, and Υ wrapper

Mirror Register's `register_Υ_body_factors` / `register_Υ_tail_invariant`:

* `weth_Υ_tail_preserves_inv`: Υ's pure tail (refund + sweeps +
  wipe) preserves `WethInv` since β and S are both unchanged at C
  (by the per-clause analysis in the informal proof). ~100 LoC.
* `weth_Υ_body_factors`: `(σ_P, A, _) ⟵ Θ/Λ-dispatch σ₀; preserves
  WethInv σ → WethInv σ_P`. Uses the new at-C invariant CALL
  helper (D) and the strong frame outputs (when Phase A.2 lands —
  see fallback). ~200 LoC.
* `weth_solvency_invariant`: top-level composition. ~30 LoC.

## Sequencing

1. **Storage-sum primitive (A) + SSTORE delta (B)** — independent of
   everything else, can land first. ~250-350 LoC.
2. **WethInv + transit lemmas (C)** — depends on (A). ~100 LoC.
3. **WethTrace predicate + 5 of 6 closures (decodeSome, op_in_set,
   initial, Z, _no_sd_at_C)** — `decide` + bytecode walk pattern,
   straight copy from Register. ~400 LoC.
4. **WethTrace_step_preserves** — the 86-byte walk. ~600-1000 LoC.
   Largest single piece; depends on (A)+(B) for SSTORE-step cases.
5. **Withdraw-CALL combined step (D.2)** — Weth-specific
   non-zero-CALL handling. ~300 LoC.
6. **Body-factor + tail + Υ wrapper (F)** — depends on (C)+(D.2).
   ~300 LoC.

Total: ~2000-2500 LoC. Distinct from Register's ~1500 because of
the storage-sum side and the non-zero-CALL handling.

## Fallbacks if framework gaps block progress

* **Storage-sum primitives** depend on Batteries RBMap.foldl lemmas.
  If those don't materialise, we can either:
  - Build minimal local versions in `StorageSum.lean` (probably ~300
    additional LoC).
  - Pin a "storage-sum primitive" axiom-style hypothesis and treat
    the underlying RBMap.foldl reasoning as out-of-scope (analogous
    to T2 — RBMap is a real-world data structure that an AMM dev
    expects to behave correctly).
* **Phase A.2 (SD-set tracking)** is still open. For the Weth proof
  it shows up as `WethSDExclusion` / `WethDeadAtσP` hypotheses,
  same posture as Register. Until A.2 lands, those remain explicit
  hypotheses.
* **Non-zero-CALL framework support (D.1)** — if D.2 (Weth-specific
  workaround) is enough, no framework change required. If D.1 is
  needed, sequence with `GENERALIZATION_PLAN.md` Step 4.

## What does NOT carry over from Register

* Register's `RegisterTrace` was simple because Register has only
  one execution path (linear, no branches). Weth has function
  dispatch (selector match), revert paths, and reentrancy. The
  trace predicate's PC enumeration is more elaborate — likely
  multiple "branch" disjuncts per logical state (e.g., "PC=42 entry
  to withdraw with stack=[]" vs "PC=42 reached via reentry").
* Register's `register_balance_mono` was a pure lower-bound claim
  (`b₀ ≤ balanceOf σ' C`). Weth's invariant is *relative* — both
  sides change in a coordinated way. So the supporting lemmas need
  to track *paired deltas* rather than monotone lower bounds. This
  is the qualitative difference; sequencing (B)+(C) reflects it.

## Estimated total effort

~2000-2500 LoC of new Lean code, multi-day. Should be tractable in
roughly the same effort scale as the original Register proof now
that the framework is in place.
