# Review 1 — Weth invariant attack plan

## 1. Layer 1 — `toList` + `Multiset.sum` path

**The plan underspecifies what Batteries actually exposes.** The `mem_toList_insert*` lemmas cited (lines 1204-1212 of `RBMap/Lemmas.lean`) are membership-level only and NOT sufficient to extract a permutation. However, Batteries has **exactly the constructive splits needed** — `RBNode.exists_insert_toList_zoom_nil` (line 758) and `RBNode.exists_insert_toList_zoom_node` (line 767):

```
∃ L R, t.toList = L ++ R       ∧ (t.insert cmp v).toList = L ++ v :: R        -- new key
∃ L R, t.toList = L ++ v' :: R ∧ (t.insert cmp v).toList = L ++ v :: R        -- existing key
```

These are `RBNode`-level under a `Balanced` hypothesis; `RBMap` carries the witness, so lifting is a minor adapter. With `toList_sorted` (line 1154) → `Pairwise (cmpLT …)` → key uniqueness, the Multiset form is reachable.

**Estimate check**: plan's 3-5 days is tight but roughly right; I'd say 5-7 days. Path 2 (direct RBNode induction) is unnecessary — the splits above obviate it. **Plan's fallback is unneeded.**

**Gap the plan doesn't flag**: no `toList_erase` permutation lemma in Batteries (grep-verified). Only `RBNode.Path.Ordered.erase`. L1-D/E are significantly harder than L1-B/C. Worth noting that withdraw to 0-balance triggers `storage.erase` (via `Account.updateStorage`'s zero branch), so L1-D/E **are** on the critical path — keep them.

## 2. L1-F direction

L1-F as stated ("total ≥ findD k 0") is NOT what prevents underflow on the withdraw *storage* decrement. For the storage-slot decrement, the LT gate alone gives `x ≤ storage[sender]`; no global fact needed. L1-F is for the **balance-side** argument: `storage[k] ≤ total ≤ balance`, used when we then subtract `x` from balance via CALL and want to show no underflow there. Plan's framing at line 76 is muddled. **Clarify: L1-F prevents RHS underflow, not LHS.**

## 3. Layer 2 — fuel induction and external receivers

Sound but incomplete. Three cases when Weth CALLs receiver `T`:

- **EOA receiver**: Θ transfers value; no inner Ξ. ✓ trivial.
- **Non-C contract receiver that doesn't reach C**: frame lemma handles. ✓
- **Receiver reaches C**: reentrance; by fuel IH, inner Ξ preserves I. ✓

**Subtlety plan elides**: the fuel IH is "Ξ on C's code preserves I", where `I` must be stated over `AccountMap` (or a `σ`-projection of EVM.State), NOT the whole `EVM.State`. Otherwise the induction is ill-formed across reentrant frames (outer frame's stack/memory are irrelevant). Plan's theorem signature uses `I σ C` — good — but the `I` definition isn't explicitly lifted to AccountMap. **Make this explicit in Phase 0**: `def I : AccountMap .EVM → AccountAddress → Prop`.

## 4. Layer 2 frame lemmas and precompiles

Verified `PrecompiledContracts.lean`. All 10 precompiles (`Ξ_ECREC`, `Ξ_SHA256`, `Ξ_RIP160`, `Ξ_ID`, `Ξ_EXPMOD`, `Ξ_BN_ADD`, `Ξ_BN_MUL`, `Ξ_SNARKV`, `Ξ_BLAKE2_F`, `Ξ_PointEval`) thread `σ` through unchanged on success and return `∅` on failure — which Θ's line 809 converts back to the pre-call σ. **A single lemma covers all 10.** Plan oversells this as difficult — it's half a day at most.

## 5. Layer 3 — direct-send to C and dead-account sweep

**Direct-send to C (raw `.send` with no calldata)**: Weth's dispatcher reverts on unknown selector; Θ's revert path at 803-804 returns pre-call σ. I preserved trivially. Add as explicit case in Phase 2c / 3.

**Plan misses entirely**: **Υ's dead-account sweep at Semantics.lean:941-943** runs `σ'.foldl Batteries.RBMap.erase` for each `dead`. An account is dead iff code empty ∧ nonce = 0 ∧ balance = 0. Weth has non-empty code, so C is never dead — but the proof needs this as an explicit **invariant preserved by Υ**: `σ'.find? C |>.map (·.code) = some bytecode`. Add this to L3 as **L3-D**.

**Also missed**: `tstorage := .empty` wipe at Semantics.lean:944. Weth doesn't use TSTORE. Trivially doesn't affect I, but enumerate as **L3-E** for hygiene.

**Initial state construction**: plan uses `initial_state C` but nowhere defines it. Cheap to specify in Phase 0: `σ.insert C { default with code := weth_bytecode }`.

## 6. Scope realism

Plan's estimates are human-weeks. For an AI agent:

- **Layer 1**: 1-3 days with the `exists_insert_toList_zoom` path. Path 2 never needed.
- **Layer 2**: **5-10 days agent time**. Dense Θ code, many branches. Biggest risk.
- **Layer 3**: 1-2 days given Layer 2 is clean.

**Total agent-time: ~2-3 weeks**. Plan's "months" in the blockers doc is too pessimistic; plan itself (~5-7 weeks) is ballpark. Rough but useful for planning.

## 7. Phase 0 — sorrys-first caveats

Lean accepts sorry for theorem proofs but **not for definitions**. Plan's `apply_all`, `initial_state` are defs — they need concrete bodies or `opaque` declarations. Cleaner: state the theorem as `∀ fuel H H_f σ₀ blocks T S_T, I σ C → I (Υ fuel σ H_f H σ₀ blocks T S_T).fst C` — quantify over Υ's actual parameters rather than wrapping them.

**Spell out the Phase 0 deliverable concretely:**
- `def I : AccountMap .EVM → AccountAddress → Prop` — real definition.
- `def initial_state : AccountAddress → EVM.State` — concrete.
- The main theorem quantifies over all Υ inputs directly, with proof body = `sorry`.

## 8. Other things that will bite

### 8a. The biggest omission — **Layer 0 (LawfulOrd/TransCmp UInt256)**

`UInt256` derives `BEq` + `Ord` but has **no `LawfulBEq`, `LawfulOrd`, `ReflCmp`, or `TransCmp`** anywhere in the repo. All Batteries RBMap lemmas that need `[Std.TransCmp cmp]` (including `mem_toList_insert` at line 1210 — everything Layer 1 depends on) are unusable without these. **This is a silent prerequisite the plan assumes is closed. It isn't.**

**Add Layer 0 explicitly**: prove `Std.TransCmp (compare : UInt256 → UInt256 → Ordering)` and `Std.ReflCmp compare`. `LawfulOrd Fin n` exists in Batteries at `Classes/Order.lean:277`; UInt256 is a 1-field struct over Fin so this should delegate cleanly. **1-3 days.**

Same gap was called out in `.claude/batteries-wishlist.md` as item 1 and `.claude/weth-invariant-blockers.md` implicitly — plan should cite both and elevate Layer 0 as a named phase.

### 8b. UInt256 subtraction wraps

`Fin.sub` is modular. Plan uses `total - x` in several places; Lean only honors this as `Nat` subtraction when `x ≤ total`. No bridge lemmas exist (grep-verified — zero theorems about `UInt256.sub` in `UInt256.lean`). **Add to Layer 0**: `UInt256.sub_eq_nat_sub_of_le : b ≤ a → (a - b).toNat = a.toNat - b.toNat` and neighbors. Half a day.

### 8c. `RBMap.foldl` vs `toList` sum bridge

Invariant's LHS in plan is spelled `RBMap.foldl (+) 0 storage`. `totalBalance` in Layer 1 will be `toList.map Prod.snd |>.sum`. Equal in value, NOT syntactically. **Add L1-G**: `t.foldl (fun acc _ v => acc + v) 0 = totalBalance t`. Derivable via Batteries' `foldl_eq_foldl_toList` at line 1130. Half a day.

### 8d. runSeq vs Ξ migration cost

Existing Weth `Proofs.lean` stubs proofs on `runSeq`. Plan Decision 2 switches to Ξ. **Existing `runOp_*` step lemmas are not directly reusable for Ξ** — they reason about the pure `EvmYul.step`, not the Ξ outer loop. The bridge: Ξ calls EVM.step (which calls EvmYul.step). For each opcode, Ξ does extra work (fuel bookkeeping, JUMPDEST validation, exceptional halting conditions) that runSeq doesn't model. **Flag in the plan**: Layer 2 will require re-stating some opcode effects in Ξ-terms. 2-3 days.

### 8e. Gas-exhaustion and Ξ failure paths

If Ξ fails (OutOfGas, InvalidInstruction, StackUnderflow, …), Θ restores σ (line 801-804). I preserved trivially — but needs explicit case in Layer 2's proof. Enumerate.

## Summary of required revisions

The plan is **structurally sound** but needs these gaps filled before implementation:

1. **Add Layer 0**: LawfulOrd/TransCmp UInt256 + UInt256.sub bridge lemmas. Named phase, 1-3 days.
2. **Add L1-G**: `RBMap.foldl` ↔ `toList.map sum` bridge.
3. **Drop Path 2**: `exists_insert_toList_zoom_*` is sufficient.
4. **Clarify L1-F**: "majorizes any slot → prevents balance-side (RHS) underflow", not storage-side.
5. **Make `I : AccountMap → AccountAddress → Prop` explicit** in Phase 0, not just `I : EVM.State → …`.
6. **Concretize Phase 0 deliverable**: `def I`, `def initial_state`, theorem quantified over Υ's raw parameters.
7. **Add L3-D** (dead-sweep preservation) and **L3-E** (tstorage wipe).
8. **Enumerate revert/failure-propagation case** in Layer 2.
9. **Flag runSeq→Ξ migration cost** as a named sub-task in Layer 2.
10. **Acknowledge precompile frame is easy** — single lemma for all 10.

With these, the plan is implementable. The overall decomposition (Layer 0 → 1 → 2 → 3) is correct and the fuel-induction backbone is the right structural choice.

VERDICT: needs revision
