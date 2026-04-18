# Review 1 — `Register` worked-example plan

*Sub-agent is read-only; review content delivered inline and saved by parent.*

## 1. Invariants well-chosen?

The three-invariant package — functional correctness, slot-frame, account-frame — is the right minimal set. Missing but worth noting:

- **Substate frame is *not* preserved**: `sstore` mutates `substate.refundBalance` and `substate.accessedStorageKeys`. Invariant 3 sidesteps this cleanly by indexing on `accountMap`. The plan should note explicitly that substate fields *are* expected to change.
- No invariant about nonce/balance/code of the target account — these are account sub-fields that `updateStorage` doesn't touch. A tighter "only `.storage` changed in account C" would combine #2+#3; the split is fine.

## 2. `runOp_*` lemmas by `unfold; rfl`?

- `runOp_caller`: fine — same shape as existing env-op lemmas.
- `runOp_stop`: fine — STOP's branch is an inline lambda, direct kernel reduction.
- `runOp_sstore`: **likely fails as stated**. `binaryStateOp` produces `{{ s with toState := sstore s.toState μ₀ μ₁ } with stack := rest, pc := s.pc + 1}`. The plan writes `pc := pc + UInt256.ofNat 1` — `I.pc = pc` definitionally since input state was `{s with pc := pc}`, so this part is fine. `sstore` itself doesn't need to reduce further (it appears by name on both sides). The real risk is the record-update nesting. **Recommendation**: lock in exact form `{ s with stack := rest, pc := s.pc + UInt256.ofNat 1, toState := sstore s.toState key val }` with fallback `by unfold runOp EvmYul.step binaryStateOp replaceStackAndIncrPC incrPC; rfl` if bare `rfl` fails.

## 3. `sstore_*` characterisation helpers

Provable but more work than the plan suggests:

- **`sstore_writes_slot`**: unfold `sstore`, peel `lookupAccount Iₐ |>.option self` (under `hacct`, becomes `.option self f = f acc`), then `setAccount ... (acc.updateStorage key val)` then `addAccessedStorageKey` then refund update. `Account.updateStorage` branches on `val == 0`: zero erases, non-zero inserts. Both cases yield `findD key ⟨0⟩ = val`. Needs `RBMap.findD_insert_self` and `RBMap.findD_erase_self`. `newAᵣ` is inert — doesn't affect the account-map shape.
- **`sstore_preserves_other_slots` / `sstore_preserves_other_accounts`**: need `RBMap.find?_insert_of_ne` / `RBMap.find?_erase_of_ne`. Batteries has `find?_insert` conditional but possibly not the bare `_of_ne` variants. Plan correctly flags as risk.

**Point missed**: Invariant 3 being `accountMap`-only is what makes it compatible with substate changes. Note this explicitly in the proof file's docstring so no one tries to strengthen to full `s.toState = s0.toState`.

## 4. `hacct` precondition

Correct call. Alternatives — initialising the account in setup — would need a `State.initialiseAccount` helper and change `runSeq`'s starting state. Not a precedent in Add3. Stronger unconditional form ("if account exists, slot = x; else state unchanged") is more informative but more typing. Pragmatic version wins.

Document this as a new-convention-for-storage-proofs in AGENTS.md.

## 5. Address representation

Verified. `Semantics.lean:290` — `CALLER → dispatchExecutionEnvOp τ (.ofNat ∘ Fin.val ∘ ExecutionEnv.source)` → pushes `UInt256.ofNat source.val`. Plan's Invariant 1 uses same — consistent. **Recommendation**: name a helper `addressSlot : AccountAddress → UInt256 := fun a => UInt256.ofNat a.val` to make it readable and eliminate ambiguity at use sites.

## 6. Foundry `vm.prank`

Correct. `prank` is single-shot for the next external call including `.call()`. Plan re-pranks before each call — correct.

**Small footgun**: `vm.prank(address(0))` is treated as deployment context. Add `vm.assume(sender != address(0))` to the fuzz test.

## 7. `vm.load` encoding

`bytes32(uint256(uint160(addr)))` produces the address zero-extended to 32 bytes. Matches `UInt256.ofNat (addr : Fin 2^160).val`. Consistent.

## 8. Anything missing or subtly wrong

- **Empty calldata / `x = 0`**: plan's use of `findD` (not `find?`) correctly abstracts the zero-erase convention. Good catch already in plan.
- **`storageAt` helper**: plan defines informally. Define precisely: `fun s a k => (s.accountMap.find? a).elim ⟨0⟩ (fun acc => acc.storage.findD k ⟨0⟩)`. Handles missing account too.
- **`runSeq` over STOP**: `runOp_stop` as stated doesn't advance pc; chaining through `runSeq_cons_ok` still works. Fine.
- **`σ₀` read in `sstore`**: unused by invariants, but `rfl`-style reductions still elaborate the match. Inert — not a correctness issue, may slow kernel.
- **`accountMap.find! Iₐ`** on `StateOps.lean:132`: on missing account returns default Account via `Inhabited`; subsequent `.option self ...` takes the `self` branch making the `σ_Iₐ` bind dead. Under `hacct`, `find!` and `find?` agree. May need helper lemma `find!_eq_get_of_isSome` or similar — flag in plan.
- **Bytecode/program sizes**: 5 ops (PUSH1, CALLDATALOAD, CALLER, SSTORE, STOP) + 6 bytes. Plan item 11 says add guard; spell out both numbers.
- **Submodule for Foundry**: option 1 (duplicate forge-std) is right. Option 2 (symlink) breaks on Windows.
- **Work-order mid-checkpoint**: add one after the `sstore_*` helpers (item 3), since if RBMap coverage stalls the whole plan is blocked.

## Overall

Plan is solid and shows awareness of the failure modes (RBMap coverage, `rfl` depth, zero-erase). Concrete refinements:

1. Lock in the exact record-update form for `runOp_sstore` and spell out the fallback proof.
2. Define `storageAt` precisely with `find? |>.elim`.
3. Introduce `addressSlot : AccountAddress → UInt256` helper.
4. Add `vm.assume(sender != address(0))` to the Foundry fuzz.
5. Add a mid-checkpoint in the work order after the `sstore_*` helpers.
6. Note that substate fields are expected to change; Invariant 3 is deliberately `accountMap`-only.
7. Spell out both size guards (`program.length = 5`, `bytecode.size = 6`).

None are structural. Plan can be implemented as-is with these edits folded in.

VERDICT: accept
