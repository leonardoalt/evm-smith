# Plan — `Register` program: SSTORE + CALLER invariants (v2)

**Refinements vs v1** (per `register-review-1.md`):

- `runOp_sstore` locked to the exact form `binaryStateOp` produces; a
  fallback tactic is named in case bare `rfl` fails.
- `storageAt` helper defined precisely (handles missing-account case).
- New helper `addressSlot : AccountAddress → UInt256` for readability.
- Explicit note that Invariant 3 is deliberately `accountMap`-only,
  since `substate` fields *do* change (refund balance, accessed keys).
- Work order gets a mid-checkpoint after the `sstore_*` helpers —
  those are the highest-risk block.
- Foundry fuzz test adds `vm.assume(sender != address(0))` to avoid
  the deployment-context footgun.
- Size `#guard`s spelled out explicitly.

A second worked example alongside `Add3`. Exercises the storage opcodes
(`SSTORE`) and environment access (`CALLER`), extending
`EvmSmith/Lemmas.lean` with new per-opcode step lemmas along the way.
Goes beyond pure functional correctness into **frame-style invariants**
(what the contract *doesn't* touch), which is where storage-aware
reasoning starts to pay off.

## Goal

Write, encode, and verify a minimal contract:

> Given calldata `x : uint256` (at offset 0), set
> `storage[msg.sender] = x` in the calling contract's own storage.

Then prove three invariants in Lean, extend `Lemmas.lean` with the
required opcode lemmas, and mirror the Foundry-test rig from `Add3`.

## Non-goals

- Reading the stored value back out via `SLOAD` (we don't return
  anything). A later iteration can add this.
- Deployment bytecode / `CREATE` stub.
- Gas / refund accounting beyond what the Lean proofs happen to need.
- Multi-sender orchestration in Lean proofs — that's Foundry's job.

## The contract — `Register`

Lives at `EvmSmith/Demos/Register/`. Minimal assembly:

```
  pc  bytes    mnemonic               effect
  0   60 00    PUSH1 0x00             -- stack: [0]
  2   35       CALLDATALOAD           -- stack: [x]          (x = cd[0:32])
  3   33       CALLER                 -- stack: [sender, x]  (sender = msg.sender)
  4   55       SSTORE                 -- storage[sender] = x; stack: []
  5   00       STOP                   -- halt
```

Six bytes total: `0x60_00_35_33_55_00`.

### Why SSTORE pop order works out

Per the Yellow Paper / EVMYulLean, `SSTORE` pops `(key, value)` where
key is on top. So we push `x` first (becomes second), then the
caller's address (becomes top). The slot index we use is the
sender's 20-byte address zero-extended to a 32-byte UInt256 — the
same convention Solidity uses when it lays out
`mapping(address => uint256)` storage (modulo Solidity's hash-based
slot, which we sidestep by directly keying on the address). This is
not gas-optimal nor Solidity-idiomatic, but it is the simplest thing
that demonstrates per-sender state.

## Invariants to prove

For a fixed input state `s0` whose calldata reads `x` at offset 0
and whose `executionEnv` has `codeOwner = C`, `source = S` (i.e. the
contract is `C` and the caller is `S`):

### Helpers (defined in `Register/Program.lean` or a shared file)

```lean
/-- The storage slot index used for per-sender values. Matches the
    key CALLER pushes and SSTORE consumes. -/
def addressSlot (a : AccountAddress) : UInt256 := UInt256.ofNat a.val

/-- Storage-at-slot lookup. Returns `⟨0⟩` for missing accounts or
    missing slots, consistently with the EVM's "empty = 0" convention
    and with `Account.updateStorage`'s erase-on-zero behaviour. -/
def storageAt (s : EVM.State) (a : AccountAddress) (slot : UInt256) : UInt256 :=
  (s.accountMap.find? a).elim ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)
```

### 1. Functional correctness (headline)

After running the program, the slot indexed by `S` in `C`'s storage
equals `x`:

```lean
theorem program_sets_sender_slot :
  (runSeq program s0).map (fun sf =>
    storageAt sf C (addressSlot S)
  ) = .ok x
```

Using `findD` (not `find?`) sidesteps the subtle `updateStorage`
convention that `v = 0` erases the slot instead of inserting zero —
`findD ⟨0⟩` returns 0 either way.

### 2. Storage frame — same account, other slots

For any slot `k` in `C`'s storage other than the sender slot, the
value is unchanged by the program:

```lean
theorem program_preserves_other_slots
    (k : UInt256) (hk : k ≠ addressSlot S) :
  (runSeq program s0).map (fun sf =>
    storageAt sf C k
  ) = .ok (storageAt s0 C k)
```

This is the **per-user isolation property** — the thing that makes a
`mapping(address => uint256)` safe to share among mutually distrustful
senders. It's what a reviewer looking at the contract most wants to
know.

### 3. Account frame — other accounts untouched

For any account address `a` other than the contract itself, the
account entry in `accountMap` is unchanged:

```lean
theorem program_preserves_other_accounts
    (a : AccountAddress) (ha : a ≠ C) :
  (runSeq program s0).map (fun sf =>
    sf.accountMap.find? a
  ) = .ok (s0.accountMap.find? a)
```

**Deliberately `accountMap`-only.** `substate.refundBalance` and
`substate.accessedStorageKeys` *do* change under SSTORE. Invariant 3
sidesteps them by not mentioning them. Do not try to strengthen
Invariant 3 to `sf.toState = s0.toState` or "all non-accountMap fields
preserved" — it will fail by design.

`SSTORE` only modifies `accountMap[codeOwner]`, so once we have the
step lemma and the `sstore_preserves_other_accounts` helper, this is
straightforward.

### Optional stretch invariants

- **Overwrite idempotence**: running the program twice with the same
  `(s0, x)` leaves the second run's post-state equal (on storage) to
  the first run's post-state. Cheap corollary of (1) + (2).
- **Commutativity of different senders**: if `S₁ ≠ S₂`, running with
  `(S₁, x₁)` then `(S₂, x₂)` yields the same final storage on those
  two slots as running in the reverse order. Would motivate pulling
  multi-call reasoning into Lean, which is a sharp escalation —
  better suited to Foundry for now.

We'll ship (1)–(3) and note the stretch ones as future work.

## New opcode lemmas for `EvmSmith/Lemmas.lean`

### `runOp_caller`

`.CALLER` dispatches to `executionEnvOp (.ofNat ∘ Fin.val ∘
ExecutionEnv.source)`. The effect is to push the caller's address
(as a `UInt256`) and advance PC by 1.

```lean
lemma runOp_caller
    (s : EVM.State) (stk : Stack UInt256) (pc : UInt256) :
    runOp .CALLER { s with stack := stk, pc := pc }
      = .ok { s with
          stack := UInt256.ofNat s.executionEnv.source.val :: stk
          pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl
```

Same shape as the other environment-op lemmas; should close by `rfl`.

### `runOp_sstore`

`.SSTORE` dispatches through `binaryStateOp EvmYul.State.sstore`.
`binaryStateOp` pops 2 words, passes them to the state-transformer,
and pushes nothing. The state-transformer `EvmYul.State.sstore s key
val` is defined in `EVMYulLean/EvmYul/StateOps.lean:130`; it updates
`accountMap[codeOwner].storage` at `key`, touches
`substate.accessedStorageKeys` and `substate.refundBalance`, and is a
no-op if `codeOwner` doesn't exist in `accountMap`.

Exact form (matching what `binaryStateOp` + `replaceStackAndIncrPC`
produce — the nested record update flattens in Lean 4 because update
fields commute):

```lean
lemma runOp_sstore
    (s : EVM.State) (key val : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .SSTORE { s with stack := key :: val :: rest, pc := pc }
      = .ok { s with
          stack := rest
          pc := pc + UInt256.ofNat 1
          toState := EvmYul.State.sstore s.toState key val } := by
  unfold runOp EvmYul.step; rfl
```

**Fallback tactic if bare `rfl` fails**: unfold the wrappers
explicitly:

```lean
  by unfold runOp EvmYul.step EvmYul.EVM.binaryStateOp
       EvmYul.EVM.State.replaceStackAndIncrPC EvmYul.EVM.State.incrPC
     rfl
```

The lemma doesn't itself characterise what `sstore` does — it just
says "the post-state is the input with stack/pc/toState updated the
expected way." The program proofs layer on top of this with
characterisation lemmas about `EvmYul.State.sstore` (below).

### `runOp_stop`

`.STOP` sets `returnData` to empty and doesn't advance PC. For our
flow (where STOP is the last opcode and `runSeq`'s cons-case simply
moves to `[]`), the effect is a small state tweak followed by the
`runSeq []` terminator.

```lean
lemma runOp_stop (s : EVM.State) :
    runOp .STOP s
      = .ok { s with toMachineState :=
          s.toMachineState.setReturnData .empty } := by
  unfold runOp EvmYul.step; rfl
```

Note: no `pc` advance, no stack change, no `toState` change. This
means the prior `toState_update` simp lemma still applies, and so
does reasoning about `toState.accountMap` on the post-STOP state.

### Helper lemmas about `EvmYul.State.sstore`

Separate from the step lemmas, we need a small theory about
`EvmYul.State.sstore`'s effect on `accountMap`. These live alongside
the step lemmas in `EvmSmith/Lemmas.lean` (or in a new
`EvmSmith/LemmasStorage.lean` if the file grows too much):

- **`sstore_writes_slot`**: if `codeOwner` exists in `accountMap`,
  then `(sstore s key val).accountMap.find? codeOwner`'s storage at
  `key` is `val` (via `findD`, handling both zero and non-zero).
- **`sstore_preserves_other_slots`**: for any `k ≠ key`, storage at
  `k` in the post-state equals storage at `k` in the pre-state
  (both in the same `codeOwner` account).
- **`sstore_preserves_other_accounts`**: for any `a ≠ codeOwner`,
  `accountMap.find? a` is unchanged.

Each is proved by unfolding `EvmYul.State.sstore` and reasoning about
`Account.updateStorage` and `Batteries.RBMap.insert` /
`RBMap.erase`. The RBMap side may need one or two small auxiliary
lemmas; we'll stub them and see how far the existing Mathlib/Batteries
coverage takes us.

Proof burden estimate: ~30-60 lines of Lean for all three helpers,
most of it routine RBMap reasoning. If the RBMap API is thin, we
may need to state one or two of the helpers with `sorry` and
explicitly note the gap — but the current plan is to get them
sorry-free.

## Program proof strategy (`Register/Proofs.lean`)

### For Invariant 1 (functional correctness)

1. Hypotheses: `s0.stack = []`, `calldataload s0.toState 0 = x`,
   `s0.accountMap.find? s0.executionEnv.codeOwner ≠ none`
   (SSTORE is a no-op on a missing account — for a real test we'd
   initialise the account, so the hypothesis is natural).
2. Chain the step lemmas through `runSeq_cons_ok`, same pattern as
   Add3:
   - PUSH1 0 → stack [0]
   - CALLDATALOAD → stack [x]
   - CALLER → stack [sender, x]
   - SSTORE → stack [], toState updated via `sstore … sender x`
   - STOP → returnData emptied; everything else unchanged
3. Apply `sstore_writes_slot` to the final `toState` to get
   `storage[sender] = x`.

### For Invariants 2 & 3 (frames)

Same chain up to the post-SSTORE state, then apply
`sstore_preserves_other_slots` or `sstore_preserves_other_accounts`.

### Potential roadblocks

- **`runOp_sstore` by `rfl`** — should work (same shape as existing
  lemmas), but `sstore` is deeper than `UInt256.add`. If `rfl` fails
  because of reduction through `Account.updateStorage`'s `if v == 0
  then … else …`, we may need to unfold manually. Mitigation: if
  `rfl` fails, prove by simp + `unfold`.
- **`toState` is now modified by SSTORE**, so the `toState_update`
  simp lemma (which only handles stack/pc updates) doesn't apply
  past that point. Proofs after SSTORE reason directly about
  `toState = sstore pre_toState ...`. No new simp lemma is needed
  because we stop caring about stack/pc at that point.
- **RBMap insert / erase lemmas** — Batteries has `RBMap.find?_insert`
  and related. If missing we'll prove the one-off lemmas we need.
- **STOP's role** — it modifies `machineState.returnData`. Since the
  invariants only talk about `accountMap`, STOP is irrelevant to
  them. But `runSeq` still needs to step through it, so
  `runOp_stop` is required.
- **Non-trivial pre-condition `hacct`** — the "codeOwner exists in
  accountMap" hypothesis. If the account doesn't exist, `sstore` is
  a silent no-op. We state the theorem under this hypothesis; the
  Foundry test creates a real account so the condition holds in
  practice.

## Foundry tests (`EvmSmith/Demos/Register/foundry/`)

Mirror the Add3 structure:

- `test/Register.bytecode.hex` generated by
  `lake exe register-dump-bytecode`.
- `test/Register.t.sol`:
  - `setUp` — `vm.etch(REGISTER, runtime)`.
  - `test_Register_writes_slot()` — call from `address(0xAA)` with
    `abi.encodePacked(uint256(42))`, then `vm.load(REGISTER,
    bytes32(uint256(uint160(0xAA))))` should equal 42.
  - `test_Register_isolates_senders()` — call from `0xAA` with x=1
    and from `0xBB` with x=2, then both slots reflect their own
    values.
  - `test_Register_overwrites()` — call from `0xAA` with x=1, then
    x=2; slot should hold 2.
  - `test_Register_empty_calldata()` — call with empty calldata;
    the sender's slot should be set to 0 (storage erases zero, so
    `vm.load` should read 0 regardless).
  - `testFuzz_Register(address sender, uint256 x)` — add
    `vm.assume(sender != address(0))` first (otherwise forge treats
    the call as a deployment context), write x from sender via
    `vm.prank(sender)`, assert slot holds x.

These exercise both the stored-value correctness and the
per-sender isolation property proved in Lean.

Senders are chosen via `vm.prank(addr)` before each low-level
`REGISTER.call(...)`. forge-std docs confirm `prank` propagates to
low-level calls.

## File layout

```
EvmSmith/Demos/Register/
├── Program.lean          # bytecode + Program value (~60 LoC)
├── Proofs.lean           # three theorems (~200 LoC)
├── DumpBytecode.lean     # lake exe that emits hex
└── foundry/
    ├── foundry.toml
    ├── lib/forge-std     # submodule, shared with Add3 via separate clone
    ├── src/.gitkeep
    └── test/
        ├── Register.bytecode.hex
        └── Register.t.sol
```

Note on `lib/forge-std`: the Add3 setup pinned it as a submodule at
`EvmSmith/Demos/Add3/foundry/lib/forge-std`. For Register we have
two options:
1. A second, independent submodule registration for Register's
   `lib/forge-std` — duplicates the on-disk clone but is a clean
   mirror of Add3's pattern.
2. A symlink from Register's `lib/forge-std` to Add3's, avoiding
   duplication. Slightly unusual; some platforms (Windows) handle
   symlinks poorly.

Recommend option 1 for clarity / uniformity — forge-std is ~1 MB,
not a real cost.

## Work order

1. Write `EvmSmith/Demos/Register/Program.lean` — `program` value,
   `bytecode` array, `addressSlot` + `storageAt` helpers.
2. Extend `EvmSmith/Lemmas.lean` with `runOp_caller`,
   `runOp_sstore`, `runOp_stop`. Build check:
   `lake build EvmSmith.Lemmas`.
3. **Checkpoint A.** Add the three `sstore_*` characterisation
   helpers to `EvmSmith/Lemmas.lean`. Build check:
   `lake build EvmSmith.Lemmas`.
   If this stalls on missing RBMap lemmas, the whole plan is
   blocked; diagnose and either (a) prove the RBMap lemmas we need,
   or (b) revise the plan to state the invariants differently.
4. Write `EvmSmith/Demos/Register/Proofs.lean` with the three
   theorems. Prove functional correctness first; if it closes, the
   two frame theorems are small variations.
5. **Checkpoint B.** `lake build` full clean build, all three
   theorems `sorry`-free.
6. Add `DumpBytecode.lean` + `lean_exe register-dump-bytecode` in
   the lakefile.
7. `lake exe register-dump-bytecode` → generates the hex file
   (create the `foundry/test/` dir first).
8. `forge init EvmSmith/Demos/Register/foundry`, prune the
   Counter boilerplate, register `lib/forge-std` as a submodule,
   write `foundry.toml` and `Register.t.sol`.
9. `forge test` — verify all tests pass.
10. Add size `#guard`s to `EvmSmith/Tests/Guards.lean`:
    `EvmSmith.Register.program.length == 5` and
    `EvmSmith.Register.bytecode.size == 6`.
11. Update `AGENTS.md` — add Register to "Where to look", list
    the new opcodes covered by `Lemmas.lean`, note the new
    "account exists" precondition convention for storage proofs.
12. Update `README.md` — add Register to "What's already proved".
13. Commit locally. **Do not push** per user instruction.

## Risks

- **`EvmYul.State.sstore` is defined in terms of `substate.refundBalance`
  integer arithmetic** with `ℤ` coercions. If `rfl` on `runOp_sstore`
  gets stuck because the refund math doesn't reduce cleanly, we may
  need to state `runOp_sstore` more loosely (as an `∃ s', runOp =
  .ok s' ∧ <characterisation>`) and prove the characterisation.
- **Batteries RBMap coverage may be thin.** Upstream Batteries has
  `RBMap.find?_insert` and a few companions, but the exact lemma we
  need — "find? after insert at different key = find? before" — may
  or may not be named. Fallback: prove by `simp [RBMap.find?,
  RBMap.insert]` + cases on the comparison result.
- **Account existence precondition.** If I prove the theorems
  unconditionally (without `hacct`), the theorems hold vacuously
  when the account doesn't exist — but then Invariant 1 would
  falsely claim `storage[sender] = x` when actually nothing
  happened. Needs `hacct` as a hypothesis, and AGENTS.md should
  mention this as a common gotcha.
- **`StorageMap.toFinmap` etc.** — we don't need these; flagged
  because they're nearby.

## Acceptance

Done when:
- `lake build` is clean (all theorems proved, `#guard`s pass).
- `forge test` in `Register/foundry/` passes all tests + fuzz.
- The three invariants are stated and proved in `Proofs.lean`
  without `sorry` / `admit`.
- AGENTS.md / README.md reflect the new example.
