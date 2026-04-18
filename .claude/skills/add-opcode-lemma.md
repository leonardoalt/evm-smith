---
name: add-opcode-lemma
description: Add a per-opcode step lemma to `EvmSmith/Lemmas.lean` when proving a program that uses an opcode not yet covered. The existing lemmas cover PUSH1, ADD, CALLDATALOAD; extend the file for any other opcode (MUL, SUB, DIV, DUP1, SWAP1, MLOAD, MSTORE, SLOAD, SSTORE, LT, GT, EQ, ISZERO, AND, OR, XOR, other PUSH widths, etc.).
---

# Adding an opcode step lemma

`EvmSmith/Lemmas.lean` collects per-opcode equations of the form

    runOp <Opcode> { s with stack := <concrete pattern>, pc := pc }
      = .ok { s with stack := <post-state pattern>, pc := pc + <delta> }

These cache the reduction of `EvmYul.step` for a single opcode so that
program proofs can compose them cheaply via `runSeq_cons_ok`. If you
don't have a lemma for an opcode the program uses, add one.

## Why these lemmas exist at all

`EvmYul.step` is one huge dependent match over ~60 opcode constructors,
wrapped in `Id.run do let _ := dbg_trace …; match …`. Reducing it for a
single concrete opcode works by iota, but chaining many unfolds in a
row hits `deterministic timeout at whnf`. The lemmas pre-compute each
branch so downstream proofs use `rw` (cheap) instead of re-reducing
(expensive). See the in-file header of `EvmSmith/Lemmas.lean` for the
full rationale and `EVMYulLean/UPSTREAM_WISHLIST.md` for upstream fixes
that would remove the need for these lemmas entirely.

## Template

Find the opcode's semantics in
`EVMYulLean/EvmYul/Semantics.lean` (the big match in `EvmYul.step`,
around line 219). Note its stack inputs, outputs, and side effects.
Then write a lemma in `EvmSmith/Lemmas.lean`:

```lean
/-- `<OPCODE>` on a state whose stack tops are `<inputs>`: pops them,
    pushes `<outputs>`, advances PC by 1. -/
lemma runOp_<opcode>
    (s : EVM.State) <arg-binders>
    (rest : Stack UInt256) (pc : UInt256) :
    runOp <.OPCODE> { s with stack := <input cons pattern>, pc := pc }
      = .ok { s with
          stack := <output cons pattern>
          pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl
```

The `unfold runOp EvmYul.step; rfl` proof works because we state the
input with a literal cons pattern — the kernel then reduces the giant
match by iota to the correct branch and everything collapses to `rfl`.

## Worked examples already in the file

Look at `EvmSmith/Lemmas.lean` and copy the shape of:

- `runOp_push1` — arity 0→1, takes a push-arg, advances PC by 2.
- `runOp_add` — arity 2→1 (binary op), advances PC by 1.
- `runOp_calldataload` — arity 1→1, reads from a state projection
  (`EvmYul.State.calldataload s.toState offset`).

Most arithmetic/comparison/bitwise opcodes (MUL, SUB, DIV, LT, GT, EQ,
AND, OR, XOR, SHL, SHR) have the same shape as `runOp_add` — binary op,
stack 2→1, PC+1. Unary ones (ISZERO, NOT) follow `runOp_calldataload`'s
shape minus the state projection.

Special cases:

- **Push widths other than 1**: PC advance is `UInt256.ofNat (1 + n)`
  where `n` is the immediate width. Copy `runOp_push1` and change the
  pattern + PC delta.
- **DUP<n> / SWAP<n>**: require stack with at least `n` (or `n+1`)
  elements in concrete cons form. Copy the pattern from `runOp_add`
  and extend the cons.
- **MLOAD / MSTORE / SLOAD / SSTORE**: these touch `.toState`
  (storage) or `.toMachineState` (memory). Follow `runOp_calldataload`
  for the state projection but route through the relevant field.
- **RETURN / REVERT**: halt; the post-state has `H_return` set and the
  caller no longer runs subsequent opcodes. Proving these requires
  reasoning about halting semantics; it may not close by `rfl` alone.

## State-modifying opcodes need a *second* lemma

Stack-only opcodes (ADD, PUSH1, DUP) have a single `runOp_*` lemma
that nails the post-state exactly. State-modifying opcodes — SSTORE,
MSTORE, SELFDESTRUCT, the log opcodes — are deeper: their post-state
runs the input through a non-trivial upstream function
(`EvmYul.State.sstore`, `MachineState.mstore`, etc.) that has its
own semantics.

For those opcodes the pattern is **two lemmas**:

1. **`runOp_<opcode>`** — the mechanical one. Says "the post-state is
   the input with `toState`/`toMachineState` routed through
   `upstream_fn`". Proof: `unfold runOp EvmYul.step; rfl`. See
   `runOp_sstore` for the canonical example.

2. **`<upstream_fn>_<property>`** — one or more
   characterisation lemmas that say what `upstream_fn` actually does
   to the relevant field, stripped of its orthogonal mutations. See
   `sstore_accountMap` — it reduces `sstore`'s complex body (which
   also touches `substate.refundBalance` and
   `substate.accessedStorageKeys`) to a single `accountMap.insert`
   equation, under the precondition that the code owner exists.

A program proof composes: step lemma → structural post-state, then
characterisation lemma → property of the field you care about. The
separation lets the structural post-state stay `rfl`-closeable while
the field-level reasoning is free to use `simp` / `unfold` /
manual RBMap reasoning.

## After adding the lemma

Build to verify:

```bash
lake build EvmSmith.Lemmas
```

Then use it in the program proof via `runSeq_cons_ok _ _ _ _ _
(runOp_<opcode> …)`.

## If `unfold … ; rfl` doesn't close

- Check that your stack pattern is literally in cons form
  (`a :: b :: rest`, not `a :: stk` where `stk` is abstract).
- Check the pc argument is passed explicitly, not inferred.
- If the opcode has exotic semantics (mutates account map, calls out
  via FFI, etc.), the proof will need more than `rfl`. Start by
  looking at the actual semantics in `EvmYul/Semantics.lean` and see
  what it needs. Consider asking for help or writing the lemma as a
  `theorem` with an explicit proof rather than the one-line template.
