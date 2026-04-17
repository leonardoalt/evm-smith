---
name: debug-proof
description: Diagnose and fix common proof failures in the evm-smith repo — `deterministic timeout at whnf`, `simp made no progress`, `rewrite failed, did not find instance of the pattern`, or calldata/storage hypotheses that don't apply after structure updates. Use when a theorem in `EvmSmith/Demos/*/Proofs.lean` or `EvmSmith/Lemmas.lean` won't close.
---

# Debugging proof failures

Common failure modes and what to do.

## Symptom: `deterministic timeout at whnf, maximum number of heartbeats (200000)`

**Cause.** You are trying to reduce a chain of `EvmYul.step` unfolds.
Each unfold materialises the full 60-branch normal form and Lean
drags it forward, so after a few opcodes the term becomes too big to
normalise.

**Fix.** Don't unfold `EvmYul.step` directly in a chain. Instead:

1. Prove each opcode's effect as a separate `have` using a
   pre-existing `runOp_<opcode>` lemma from `EvmSmith.Lemmas`.
2. Chain the `have`s via `rw [runSeq_cons_ok _ _ _ _ _ hN]`.

See `EvmSmith/Demos/Add3/Proofs.lean` for the full pattern. The
`prove-program` skill has the template.

If a lemma you need isn't in `EvmSmith/Lemmas.lean`, use the
`add-opcode-lemma` skill to add it — don't inline the reduction.

## Symptom: `simp made no progress`

**Cause.** You invoked `simp` expecting it to reduce through a match
on `Except.ok`, but `runSeq`'s do-notation elaborates to a form that
simp can't iota-reduce in place.

**Fix.** Use `runSeq_cons_ok` instead of bare `simp only [runSeq]` for
stepping through the program. `runSeq_cons_ok` does the iota
reduction inside its own proof body (via a `show (do …) = _` + `rw` +
`rfl`) and exposes a clean rewrite rule to callers.

## Symptom: `rewrite failed, did not find instance of the pattern in the target expression`

**Cause.** Your helper lemma's LHS doesn't syntactically match the
goal. The per-opcode lemmas require the state to be literally
`{ s with stack := <cons pattern>, pc := <pc> }`. After `simp only
[runSeq]`, the state inside the first `runOp` call matches
`{ s0 with … }` only if `s0`'s stack has been normalised to a concrete
cons pattern.

**Fix.** Use

```lean
have hs0 : s0 = { s0 with stack := [], pc := s0.pc } := by
  cases s0; cases hs; rfl
rw [hs0]
-- then: exact runOp_<opcode> s0 … [] s0.pc
```

to normalise `s0`'s shape before invoking the step lemmas.

## Symptom: calldata/storage hypothesis `h0` isn't applying

**Cause.** After an opcode runs, the state is
`{ s0 with stack := …, pc := … }`. The hypothesis is about
`s0.toState`. Simp needs to know that
`{ s0 with stack := …, pc := … }.toState = s0.toState` so it can
rewrite `calldataload ({…}).toState offset` to
`calldataload s0.toState offset` and then apply `h0`.

**Fix.** `EvmSmith.Lemmas` provides `toState_update` tagged `@[simp]`
for exactly this. Make sure you've imported `EvmSmith.Lemmas`, and
invoke with `simp [h0]` (not `simp only [h0]` — you need the default
simp set to pull in `toState_update` too, or add it explicitly).

## Symptom: `abel` closes but Lean hints `Try this: abel_nf`

**Cause.** After your preceding `congr 1`, both sides of the goal are
already in a form where normalisation alone closes — you don't need
the full equality-check phase of `abel`.

**Fix.** Replace `abel` with `abel_nf`. Same result, silences the hint,
slightly cheaper.

## Symptom: `unknown constant 'Fin.add_comm'` (or similar renaming)

**Cause.** A lemma name changed in Mathlib or is in a namespace you
don't expect.

**Fix.** Use the typeclass-dispatched name instead. For commutativity,
`add_comm _ _` works for any `AddCommMonoid`, which `Fin n` with
`NeZero n` has. Similarly `add_assoc`, `mul_comm`, etc.

## Symptom: can't prove a byte-level property (e.g. `H_return = (a+b+c).toByteArray`)

**Cause.** This requires a round-trip through
`readWithPadding ∘ writeBytes`, both of which call
`ffi.ByteArray.zeroes`, declared `opaque` in
`EVMYulLean/EvmYul/FFI/ffi.lean`. Opaque declarations are irreducible
in the kernel by design, so no `rfl`/`simp` closure is possible.

**Fix.** Don't prove byte-level properties. Prove the stack-level (or
storage-level) property instead — functionally equivalent for most
safety claims — and demonstrate the byte-level behaviour via
`#guard` at elaboration time or `#eval` at runtime (noting that
`#guard` can't run code that calls the FFI, so runtime demos go in
`EvmSmith/Demos/Demos.lean` invoked via `lake exe`).

See the docstring at the top of `EvmSmith/Demos/Add3/Proofs.lean` for
the canonical phrasing of this limitation.

## Escalation

If none of the above fit and the proof still won't close, the shape of
the goal is probably telling you which step reduced to something
unexpected. Insert a temporary `sorry` to make the build pass, view
the intermediate goal in the editor (or inspect the build log), and
adjust the chain.

If the problem is structural — the opcode's semantics are more
complex than `unfold; rfl` can handle (e.g. `CALL`, `CREATE`,
`KECCAK256`, anything involving account-map mutation or cryptography)
— it may not be provable with the current machinery. Check
`EVMYulLean/UPSTREAM_WISHLIST.md` for context on what's currently
possible.
