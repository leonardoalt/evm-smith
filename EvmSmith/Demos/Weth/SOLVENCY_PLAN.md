# Weth solvency invariant — Lean formalization plan (v2)

Maps the informal proof in `SOLVENCY_INFORMAL.md` onto our existing
framework, identifies reusable pieces, and lists new work needed.

> **v2 changes** (post review): generalize the framework's at-C bundle
> to an arbitrary op-whitelist; add a new parallel mutual closure
> tracking the **(β ≥ S)** invariant (the existing one tracks balance
> monotonicity only); retire the Weth-specific D.2 workaround in
> favour of framework extension; update LoC estimate; tabulate JUMPI
> branch enumeration; fix sequencing (CALL handling must precede the
> walk that uses it).

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

where `WethInv σ C := storageSum σ C ≤ balanceOf σ C`.

## What we reuse from the Register session — verified per item

### Out of the box, no new work

* **Step shape lemmas** in `EvmYul.Frame.StepShapes`: cover *all of
  Weth's opcodes except DUP5* (see Pre-A below). The 81 shape lemmas
  + the 4 below cover the full Weth bytecode.
* **`Υ_balanceOf_ge`** as a *tool* (not the consumer entry): used at
  every `codeOwner ≠ C` sub-frame to bound `β(C)` from below by
  `S(σ_entry)`. (See Section H.1 strategy.)
* **MutualFrame's not-at-C balance frames** (`Θ_balanceOf_ge`,
  `Λ_balanceOf_ge`, `Ξ_balanceOf_ge_bundled`, `ΞFrameAtC`): direct
  reuse for the non-Weth frames in the call tree.
* **`StateWF`** + `boundedTotalDouble` for no-wrap arithmetic.
* **Real-world axioms**: T2 (precompile purity), T5 (Keccak collision).
* **`DeployedAtC` predicate**: copy-paste pattern, applied to Weth.
* **Phase A leaf infrastructure**: `selfdestruct_preserves_SD_exclude_C`,
  `EvmYul.step_preserves_selfDestructSet`, the 9 precompile
  substate-purity lemmas — useful for the storage analogue.

### Pattern-reuse (same shape, new content)

* **`WethTrace`**: predicate over Weth's reachable PCs. ~30 PCs vs
  Register's 14, with explicit two-branch disjuncts at each JUMPI
  (see §3.4). ~250 LoC.
* **6 closure obligations**, but *generalised* (Section G replaces
  the 8-op whitelist; the `_v0_at_CALL` closure becomes a
  `_call_constraint` closure that supplies `(h_s, h_vb, h_fs)` for
  `call_balanceOf_ge`).
* **`WethAssumptions`** record (mirroring how we'd bundle Register's
  trust contract): `deployed`, `sdExcl`, `deadAtσP` — all three with
  identical shape to Register's.

### What does NOT reuse — clarified

* `ΞPreservesAtC_of_Reachable` (the Register entry point) is **not**
  reusable as-is. Its conclusion is `balanceOf σ' C ≥ balanceOf σ C`,
  which is *false* for Weth's at-C frames (the withdraw block
  decreases balance). We need a sibling entry point that produces
  the **invariant-preservation** conclusion. See Section H.

* `step_CALL_arm_at_C_v0`, `step_bundled_invariant_at_C_v0`,
  `X_inv_at_C_v0`, `X_inv_at_C_v0_holds` — all hardwired to (a)
  the 8-opcode whitelist and (b) `stack[2]? = some 0` at CALL.
  Both constraints lifted via Sections G + H.

## §1. Genuinely new framework work (EVMYulLean side)

### 1.1 §G — Generalize the at-C bundle to an arbitrary op-whitelist

**Why**: Weth uses ~25 distinct opcodes; Register's bundle is hardwired
to its 8.

**Scope**: refactor in `EVMYulLean/EvmYul/Frame/MutualFrame.lean`.
Add a parameter `OpAllowedSet : Operation .EVM → Prop` and thread it
through:

```
ΞPreservesAtC_of_Reachable_general
  ↓ uses
X_inv_at_C_general / X_inv_at_C_general_holds
  ↓ uses
step_bundled_invariant_at_C_general
  ↓ dispatches to
- handledHelper (for ops in handledByEvmYulStep — covers everything
  in Weth except CALL)
- step_CALL_arm_at_C_general — for at-C CALLs. Two routing modes:
  * **Mode V0** (Register-style): v=0, dispatches to `call_balanceOf_ge`
    via the `Or.inr` discharge of `h_s`, conclusion is balance
    monotonicity. Used by §1.1 alone.
  * **Mode INV** (Weth-style): v ≠ 0 at codeOwner = C, dispatches
    to §H's `call_invariant_preserved` (NEW, not `call_balanceOf_ge`),
    conclusion is `WethInv σ' C`. Used jointly with §H.
```

Mode V0 is a clean parameterization (the existing v0 chain extended
to take an op-whitelist + v=0 specialization). Mode INV requires §H
(see §1.2) to be in place — it cannot route through
`call_balanceOf_ge` because at v ≠ 0 with src = C, neither disjunct
of `call_balanceOf_ge`'s `h_s : C ≠ src ∨ v = 0` is dischargeable.

The existing v0 chain stays as a Mode-V0 special-case instance for
Register (sets `OpAllowedSet := Register's 8`). Register's
`BytecodeFrame.lean` is unchanged.

**Estimated LoC**: ~700 (mechanical for the op-whitelist
parameterization across `step_bundled_invariant_at_C`, `X_inv_at_C`,
and the entry point: each existing case in
`step_bundled_invariant_at_C_v0` becomes a `handledHelper`
invocation parameterised by `OpAllowedSet`. `X_inv_at_C_v0_holds`'s
decode-discharge boilerplate (`MutualFrame.lean:4994–5074`) is
intertwined with the 8-op specialization, which adds bookkeeping to
the refactor; estimating ~700 rather than the original ~600 to
account for it).

### 1.2 §H — Parallel mutual closure tracking the (β ≥ S) invariant

**Why**: the existing balance-frame closure produces `β monotone`,
not `β ≥ S` preservation. For Weth's at-C frames, β can decrease
(by the withdraw value), so balance monotonicity *fails* — only
the relative invariant survives.

**Strategy**: instead of a fully general "track an arbitrary
predicate I" closure (which is large), specialise to the (β ≥ S)
form. Define:

```lean
def ΞPreservesInvariantAtC (C : AccountAddress) : Prop :=
  ∀ ..., StateWF σ → I.codeOwner = C → ... →
    storageSum σ C ≤ balanceOf σ C →   -- I(σ)
    match EVM.Ξ ... with
    | .ok (.success (_, σ', _, _) _) =>
        storageSum σ' C ≤ balanceOf σ' C ∧   -- I(σ')
        StateWF σ' ∧ (∀ a ∈ cA', a ≠ C)
    | _ => True
```

Plus the fuel-bounded sibling `ΞInvariantFrameAtC C maxFuel`. The
parallel chain `Θ_invariant_preserved_bdd` / `Λ_invariant_preserved_bdd`
/ `Ξ_invariant_preserved_bundled_bdd` mirrors the existing balance
chain but tracks `(β − S)` non-negativity through each step.

**Key observation**: most steps don't change S (only SSTORE at the
current codeOwner does). Most steps don't change β (only
CALL/CALLCODE/CREATE/CREATE2/SELFDESTRUCT do, plus the entry-time
value transfer). So the per-step invariant proof is small —
SSTORE-at-C and CALL-with-value are the only steps with non-trivial
ΔS or Δβ at C.

**Strategy refinement** (per reviewer's CR-2 alternate angle): for
sub-frames at `codeOwner ≠ C`, S is unchanged and β is monotone
non-decreasing. So at each non-C sub-frame entry with σ_in
satisfying I, the post-frame σ_out satisfies `β(σ_out) ≥ β(σ_in) ≥
S(σ_in) = S(σ_out)`. We use `Υ_balanceOf_ge`-style helpers (with
b₀ := S(σ_in)) at non-C frames and only need the invariant tracking
at C frames. This factoring reduces the mutual-closure work by
roughly half — the heavy lifting is at C, where SSTORE/CALL are the
only ops affecting both sides.

**Concrete deliverables** in §H (in addition to the mutual closure):

* **`call_invariant_preserved`** — at-C CALL helper analogous to
  `call_balanceOf_ge` but with conclusion `WethInv σ' C` instead of
  balance monotonicity. Operates at the value-transfer level
  (debits v from C, credits v to recipient ≠ C, then dispatches to
  the inner Ξ via `Ξ_invariant_preserved_bundled_bdd`). This is the
  helper that §G's Mode INV (§1.1) routes the at-C CALL through.
  ~250 LoC inside §H's total.
* **`Θ_invariant_preserved_bdd`** / **`Λ_invariant_preserved_bdd`**:
  ~600 LoC.
* **`Ξ_invariant_preserved_bundled_bdd`** + fuel-bounded sibling:
  ~350 LoC.

**Estimated LoC**: ~1200 framework total for §H. Non-C case directly
uses existing balance frames.

### 1.3 New consumer entry point — `Υ_invariant_preserved`

Mirrors `Υ_balanceOf_ge` but conclusion is invariant preservation.

**Deliverables** in `UpsilonFrame.lean`:

* **`Υ_tail_storageSum_eq`** — new helper: storage at C is unchanged
  across the Υ tail (refund + beneficiary fee + SD sweep + dead
  sweep + tstorage wipe — none of which touch persistent storage at
  C since C ∉ SD set, C ∉ dead filter, and tstorage isn't part of
  S). ~80 LoC.
* **`Υ_tail_invariant_preserves`** — combines `Υ_tail_balanceOf_ge`
  (β unchanged at C across tail) with `Υ_tail_storageSum_eq`. ~50 LoC.
* **`Υ_invariant_preserved`** — top-level consumer entry. ~120 LoC.

**Estimated LoC**: ~250 total.

### 1.4 §A — Storage-sum primitives

`EVMYulLean/EvmYul/Frame/StorageSum.lean` (new):

```lean
def storageSum (σ : AccountMap .EVM) (C : AccountAddress) : ℕ :=
  ((σ.find? C).map (·.storage)).getD .empty
    |>.foldl (fun acc _ v => acc + v.toNat) 0

theorem storageSum_unchanged_at_other_account
    (σ : AccountMap .EVM) (C a : AccountAddress) (acc' : Account .EVM)
    (h : a ≠ C) :
    storageSum (σ.insert a acc') C = storageSum σ C

theorem storageSum_sstore_eq
    (σ : AccountMap .EVM) (a C : AccountAddress) (slot val : UInt256)
    (oldVal : UInt256)
    (h_old : ((σ.find? a).map (·.storage)).bind (·.find? slot) = some oldVal
             ∨ ((σ.find? a).map (·.storage)).bind (·.find? slot) = none ∧ oldVal = ⟨0⟩) :
    storageSum (σ.sstoreAt a slot val) C =
      if a = C
      then storageSum σ C + val.toNat - oldVal.toNat
      else storageSum σ C

theorem storageSum_old_le
    (σ : AccountMap .EVM) (C : AccountAddress) (slot oldVal : UInt256)
    (h : ((σ.find? C).map (·.storage)).bind (·.find? slot) = some oldVal) :
    oldVal.toNat ≤ storageSum σ C
```

The `_old_le` companion ensures the truncating ℕ-subtraction in
`_sstore_eq` is safe (per reviewer MI-4).

**Estimated LoC**: ~250.

### 1.5 §B — SSTORE step-level lemma into the bundle

```lean
theorem step_modifies_storage_only_at_codeOwner
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State) (a : AccountAddress)
    (h_handled : handledByEvmYulStep op)
    (h : EvmYul.step op arg s = .ok s')
    (h_ne : a ≠ s.executionEnv.codeOwner) :
    ((s'.accountMap.find? a).map (·.storage)) =
      ((s.accountMap.find? a).map (·.storage))
```

Lives in `EvmYul.Frame.StepFrame`. Used by §1.2's per-step
invariant proof. ~50 LoC. (Cross-ref `ASSUMPTIONS.md`'s "Proof
obligations" section, which lists this at ~30 LoC — the higher
estimate here accounts for the per-op case-dispatch boilerplate.)

### Pre-A. Step shape coverage gaps

Add to `EvmYul.Frame.StepShapes`:
* `step_DUP5_shape` (~30 LoC; Weth uses DUP5 at PC 69).

Add to `EvmYul.Frame.PcWalk`:
* `step_DUP2_at_pc`, `step_DUP3_at_pc`, `step_DUP4_at_pc`,
  `step_DUP5_at_pc` (~15 LoC each).
* `step_SHR_at_pc` (Weth uses SHR at PC 5; ~15 LoC).
* `step_LT_at_pc`, `step_EQ_at_pc`, `step_REVERT_at_pc`,
  `step_ISZERO_at_pc` (each ~15 LoC if not already wrapped).

Total: ~150 LoC, mechanical mirror of existing wrappers.

## §2. Genuinely new contract-side work (Weth's directory)

### 2.1 §C — `WethInv` predicate + transit lemmas

`EvmSmith/Demos/Weth/Invariant.lean` (new):

```lean
def WethInv (σ : AccountMap .EVM) (C : AccountAddress) : Prop :=
  storageSum σ C ≤ balanceOf σ C

structure RegInv (σ : AccountMap .EVM) (C : AccountAddress) where
  inv : WethInv σ C
  -- (no balance lower bound — Weth's monotone bound is S itself)
```

Plus transit lemmas: `WethInv` preserved by sender debit at
`S_T ≠ C` (β unchanged, S unchanged), Θ value transfer in (β
credited, S unchanged → invariant slack increases), etc. ~150 LoC.

### 2.2 §C2 — Storage layout: `addressSlot`

```lean
/-- A user `a`'s token-balance slot. -/
def addressSlot (a : AccountAddress) : UInt256 := UInt256.ofNat a.val

theorem addressSlot_injective : Function.Injective addressSlot := by
  decide
```

`decide`-discharged. ~15 LoC.

### 2.3a — Auxiliary: `weth_caller_ne_C`

A standalone structural lemma needed by §2.5's CALL handling:

```lean
theorem weth_caller_ne_C
    (C : AccountAddress) (s : EVM.State)
    (hReachable : WethTrace C s)
    (hOuter_ne : s.executionEnv.sender ≠ C)
    (hCallerStack : ∃ x, s.stack[1]? = some x ∧
                    AccountAddress.ofUInt256 x = s.executionEnv.sender) :
    AccountAddress.ofUInt256 (s.stack[1]?.getD ⟨0⟩) ≠ C
```

Why we need this: §2.5's CALL constraint requires `recipient ≠ C`
(so `h_s` can be discharged via `Or.inl`). At Weth's PC 72,
recipient = stack[1] = CALLER (pushed by the CALLER op at PC 70).
For the outermost Weth frame, CALLER = S_T ≠ C (boundary
hypothesis). For nested reentry: any reentrant Weth frame is
reached via an intermediate non-Weth frame (since Weth's bytecode
at PC 72 sends to CALLER ≠ self, never C → C directly), and that
intermediate frame's `Iₐ ≠ C` is exactly the recipient. So by
trace-shape induction, every Weth frame's CALLER is ≠ C.

The "outer hypothesis" `hOuter_ne : s.executionEnv.sender ≠ C` is
provided for the outermost frame by `C ≠ S_T` (boundary B1) and is
preserved through reentrant nesting because no Weth bytecode path
produces a `C → C` direct call. ~80 LoC.

### 2.3 §D — `WethTrace` predicate

`EvmSmith/Demos/Weth/BytecodeFrame.lean` (new):

The PC enumeration (each row a disjunct in `WethTrace`):

| PC | Stack length | Specific elements | Notes |
|----|--------------|-------------------|-------|
| 0  | 0            | —                 | entry |
| 2  | 1            | stack[0] = calldata word | post PUSH1 0 + CALLDATALOAD |
| 3  | 2            | stack[1] = calldata word | post PUSH1 0xe0 |
| 5  | 2            | …                 | post SHR (selector in low 4 bytes) |
| 6  | 2            | …                 | post DUP1 → 3 wide stack |
| 7…12 | …          | …                 | dispatch DUP/PUSH4/EQ chain |
| 13 | 2            | stack[0] = match flag | post EQ for deposit selector |
| 16 | 1            | stack[0] = depositLbl | post PUSH2 + JUMPI |
| 17 | 1            | (selector still on stack) | JUMPI not-taken branch |
| 22 | 1            | stack[0] = match flag | post EQ for withdraw selector |
| 23, 26 | …        | …                 | dispatch loop continued |
| 27, 29, 31 | …    | …                 | no-match REVERT path |
| 32 | 1 (selector) | …                 | deposit JUMPDEST (entered via JUMPI) |
| 33…40 | various  | …                 | deposit block |
| 41 | 0            | —                 | post SSTORE; STOP next |
| 42 | 0            | —                 | withdraw JUMPDEST (entered via second JUMPI; selector consumed by EQ) |
| 43, 45 | …        | …                 | PUSH 4 + CALLDATALOAD |
| 46…51 | …        | stack growth via DUP1/DUP3/DUP2 + SLOAD | balance gate setup |
| 52, 55 | …        | stack[0] = (balance < x) | LT result for JUMPI |
| 56…60 | …        | …                 | balance ≥ x branch: SUB + SSTORE-of-decrement |
| 61…71 | …        | stack args for CALL | CALL setup |
| 72 | 7            | stack[2] = x (the withdraw amount) | CALL invocation site |
| 73, 74, 77 | …    | stack[0] = success flag | CALL success check |
| 78, 79 | …        | …                 | POP + STOP success path |
| 80, 81, 83, 85 | … | …                | revert JUMPDEST (entered via JUMPI from PC 55 or PC 77) |

Note: each JUMPI fires both branches. Trace predicate enumerates them
as separate disjuncts (per reviewer MI-7).

**At PC 72**: stack[2] = x where the SSTORE at PC 60 already
decremented `storage[CALLER]` by x. This is the joint
`SSTORE-x-then-CALL-x` discipline that closes the invariant locally
(see §2.5).

Estimated LoC for the predicate: ~250.

### 2.4 §E — `WethTrace_step_preserves` (the bytecode walk)

The 86-byte walk, one case per PC disjunct in §2.3. Each case:
1. Apply matching `step_*_at_pc` wrapper from `PcWalk`.
2. Derive the post-state's pc and stack shape.
3. Land in the next PC's disjunct (using JUMPI tabular branches).
4. For SSTORE steps: invoke `storageSum_sstore_eq` to track ΔS.
5. For CALL step at PC 72: invoke §2.5's combined-step lemma.

Estimated LoC: ~1000 (~30 PCs × ~30 LoC each, with a few special
cases for JUMPI branches and SSTORE/CALL).

### 2.5 §F — Withdraw CALL + SSTORE combined-step lemma

For Weth's CALL at PC 72 with `stack[2] = x`, given that the prior
SSTORE at PC 60 decremented `storage[C][addressSlot CALLER]` by x:

Use Section G's generalised `step_CALL_arm_at_C_general` in
**Mode INV**, which routes through §H's `call_invariant_preserved`
(NOT `call_balanceOf_ge` — that one would require either `C ≠ src`
or `v = 0`, neither of which holds at Weth's at-C CALL).

`call_invariant_preserved`'s precondition closure:
- **Recipient ≠ C**: discharged by §2.3a's `weth_caller_ne_C` lemma.
  At PC 72, recipient = `AccountAddress.ofUInt256 stack[1]` =
  CALLER (pushed at PC 70). The lemma chains through the trace
  predicate to give `CALLER ≠ C` for every reachable Weth frame.
- `h_fs` (source funds): `stack[2] ≤ balanceOf σ (codeOwner)` →
  needs `x ≤ balanceOf σ C`. From the invariant at the prior SSTORE
  state: `S(σ) ≤ β(σ)`, and `S(σ) ≥ storage[C][addressSlot CALLER] ≥
  x` (since the LT check at PC 51 verified pre-decrement balance ≥ x).
  Wait — SSTORE has already decremented; so post-SSTORE
  `storage[C][addressSlot CALLER] = old − x`. The pre-LT check was
  `old ≥ x`, which gives `x ≤ old = (post + x)`, i.e. `x ≤ pre`. We
  need `x ≤ β(σ_post-SSTORE)`. Since SSTORE doesn't change β,
  `β(σ_post-SSTORE) = β(σ_pre-SSTORE) ≥ S(σ_pre-SSTORE) ≥ x`. ✓
- `h_vb` (recipient no-wrap): `acc.balance + x < UInt256.size`. By
  StateWF's totalETH < 2^255 bound, `acc.balance + x ≤ 2 · totalETH
  < 2^256`. (Same `boundedTotalDouble` argument as Register's.)

The combined lemma states: at PC 72, given the trace predicate
(which encodes the SSTORE-decrement-just-happened fact), the post-CALL
state σ' satisfies `WethInv σ' C`. Specifically:
- ΔS at C: `−x` from the SSTORE at PC 60 (already happened before
  this step; tracked in the trace's PC-60 → PC-72 chain).
- Δβ at C: `−x` from CALL's value transfer.
- Plus the recursive Ξ run at the recipient: at codeOwner ≠ C
  (recipient ≠ C), β(C) is monotone non-decreasing and S(C) is
  unchanged. So invariant preserved through the recursion.

Estimated LoC: ~400.

### 2.6 §F-tail — Body factor + tail invariant + Υ wrapper

Mirror Register's structure:

* `weth_Υ_tail_preserves_inv`: Υ's pure tail preserves WethInv (β
  unchanged at C since C ≠ S_T and C ≠ H.beneficiary, and SD/dead
  sweeps exclude C by F1; storage unchanged at C across the tail
  since tail only touches balance and tstorage). Reuses
  `Υ_tail_balanceOf_ge`-style argument plus a new
  `Υ_tail_storageSum_eq` (storage unchanged across tail). ~150 LoC.
* `weth_Υ_body_factors`: post-Θ/Λ-dispatch state σ_P satisfies
  `WethInv σ_P C` given input `WethInv σ C`. Uses §2.5's combined
  CALL-arm. ~200 LoC.
* `weth_solvency_invariant`: top-level composition. ~50 LoC.

## §3. Sequencing (corrected)

Dependency graph (each layer needs the prior):

1. **§1.4 Storage-sum primitives** (`StorageSum.lean`) — independent.
2. **§1.5 SSTORE step-level lemma** (`StepFrame.lean`) — independent.
3. **Pre-A** Step shape coverage gaps (DUP5, SHR, etc.) — independent.
4. **§G** Generalize at-C bundle to op-whitelist — depends on (3).
5. **§H** Invariant-tracking parallel mutual closure — depends on
   (4) + (1) + (2).
6. **§1.3** New consumer entry point `Υ_invariant_preserved` —
   depends on (5).
7. **§2.1 / §2.2** `WethInv` + `addressSlot` — depend on (1).
8. **§2.5** Withdraw-CALL combined-step lemma — depends on (4) +
   (5) + (7).
9. **§2.3 / §2.4** `WethTrace` + bytecode walk — depend on (3) +
   (4) + (8).
10. **§2.6** Body factor + tail + Υ wrapper — depend on (6) + (9).

The reviewer flagged that the original sequencing had "the walk"
before "the CALL combined-step." Corrected: §2.5 (CALL) before §2.4
(walk that uses it).

## §4. Estimated effort (revised)

| Section | Where | LoC |
|---------|-------|-----|
| Pre-A: shape coverage gaps | StepShapes/PcWalk | ~150 |
| §1.4: StorageSum primitives | new file | ~250 |
| §1.5: SSTORE storage-only-at-codeOwner | StepFrame | ~50 |
| §G: at-C bundle generalization | MutualFrame | ~700 |
| §H: invariant-tracking parallel closure (incl. `call_invariant_preserved`) | MutualFrame | ~1200 |
| §1.3: Υ_invariant_preserved (incl. Υ_tail_storageSum_eq) | UpsilonFrame | ~250 |
| §2.1/§2.2: WethInv + addressSlot | new files | ~165 |
| §2.3a: weth_caller_ne_C structural lemma | BytecodeFrame | ~80 |
| §2.5: Withdraw-CALL combined step | BytecodeFrame | ~400 |
| §2.3/§2.4: WethTrace + walk | BytecodeFrame | ~1250 |
| §2.6: body + tail + Υ wrapper | Solvency.lean | ~400 |
| **Total** | — | **~4895** |

Roughly half framework (§G/§H/§1.3-1.5/Pre-A: ~2600 LoC) and half
contract-side (§2.x: ~2295 LoC). Larger than Register's ~1500 LoC
because of (i) the storage-side, (ii) the invariant-tracking parallel
closure, (iii) the larger bytecode (86 vs 20 bytes), (iv) the
non-zero-CALL infrastructure. Realistic uncertainty: ±10-20%
(byttecode walks tend to overrun).

## §5. Fallbacks and risk register

* **§G framework refactor risk**: same shape as the agent-bail-prone
  Phase A.2 closure rewrite (~600 LoC mechanical, but lockstep
  across `step_bundled_invariant_at_C`, `X_inv_at_C_v0`, and the
  consumer entry point). Mitigation: stage in two commits — first
  add a parameterised sibling without removing the v0 chain, then
  refactor Register's BytecodeFrame in a separate commit. Each
  commit must build clean.
* **§H closure risk**: same shape as Phase A.2's open work in
  `GENERALIZATION_PLAN.md`. Genuine multi-day proof effort. The
  framework already has the `ΞFrameAtCStrong` / `ΞAtCFrameStrong`
  scaffolding; reuse it for the invariant-tracking variant.
* **Storage-sum primitives** depend on Batteries RBMap.foldl
  lemmas. If those don't materialise, build local helpers in
  `StorageSum.lean` (~200 additional LoC).
* **F1/F2 (`WethSDExclusion`/`WethDeadAtσP`)** remain hypotheses
  until Phase A.2 lands — same posture as Register.
* **Reentrancy fuel induction**: handled by the framework's
  existing fuel-strong-induction in §H's mutual closure. No
  separate Weth-side induction is added.
