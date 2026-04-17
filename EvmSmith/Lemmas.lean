import EvmSmith.Framework

/-!
# Opcode step lemmas

Reusable per-opcode equations of the form "running this opcode on a state
with stack/pc in concrete shape produces this post-state". Any program
proof that wants to chain `runOp` calls into a single equation needs these.

Each lemma is stated with the state's stack in explicit cons form and the
pc passed as an argument, so the giant dependent match in `EvmYul.step`
reduces by iota and the proof closes by `rfl`.

**What lives here vs. elsewhere:**

- `Framework.lean` — runtime surface (`runOp`, `runSeq`, state builders).
- `Lemmas.lean` (this file) — the proof-time shims for those definitions.
  Grow this file as you prove new programs: each new opcode the program
  uses gets one `runOp_<opcode>` lemma, proved the same way.
- `Demos/<Program>/Proofs.lean` — program-specific proofs that chain these.

Currently covers `PUSH1`, `ADD`, `CALLDATALOAD`. Extend as needed.

## Why these lemmas are needed

Upstream `EvmYul.step` is one huge dependent match over ~60 opcode
constructors, wrapped in `Id.run do let _ := dbg_trace …; match …`. For
a *single* concrete opcode, `unfold EvmYul.step; rfl` works: the kernel
finds the matching branch by iota. But two things hurt in longer proofs:

1. **Each unfold produces a giant term.** Reducing through a 60-branch
   match leaves behind a normalised expression Lean carries around.
   Chaining 8+ unfolds through `runSeq` deterministically timeouts at
   `whnf` (we hit this directly during the Add3 proof).
2. **The `Id.run do`/`dbg_trace` wrapping** is definitionally transparent
   but interacts awkwardly with `simp`'s iota-reduction when composed
   with `runSeq`'s own do-notation match.

Each lemma here caches one branch's reduction under a descriptive name.
At the use site `rw [runOp_push1]` is a cheap term substitution instead
of re-reducing the whole match, and proofs of long programs actually
terminate.

The downside is that as program proofs grow we accumulate ~one lemma per
opcode used, which is effectively rewriting `step` one branch at a time.
See `EVMYulLean/UPSTREAM_WISHLIST.md` for the upstream changes that
would eliminate the need for this file entirely.
-/

namespace EvmSmith
open EvmYul EvmYul.EVM

/-! ## Per-opcode step lemmas -/

/-- `PUSH1 v` on a state with stack `stk`: pops nothing, pushes `v`, and
    advances PC by 2 (one byte for the opcode + one byte for the immediate). -/
lemma runOp_push1
    (s : EVM.State) (v : UInt256) (stk : Stack UInt256) (pc : UInt256) :
    runOp (.Push .PUSH1) { s with stack := stk, pc := pc } (some (v, 1))
      = .ok { s with stack := v :: stk, pc := pc + UInt256.ofNat 2 } := by
  unfold runOp EvmYul.step; rfl

/-- `ADD` on a state whose stack tops are `a :: b :: rest`: pops both,
    pushes their `UInt256`-sum, advances PC by 1. Note the pop order —
    `a` was on top (pushed last), `b` below it. -/
lemma runOp_add
    (s : EVM.State) (a b : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .ADD { s with stack := a :: b :: rest, pc := pc }
      = .ok { s with stack := (a + b) :: rest, pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-- `CALLDATALOAD` on a state whose stack top is `offset`: pops the offset,
    reads 32 bytes from calldata starting at `offset` (zero-padded if the
    calldata is shorter), pushes the UInt256 big-endian decoding, and
    advances PC by 1. The result is expressed symbolically via
    `EvmYul.State.calldataload s.toState offset`; a program proof then
    substitutes that using a hypothesis about the calldata. -/
lemma runOp_calldataload
    (s : EVM.State) (offset : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .CALLDATALOAD { s with stack := offset :: rest, pc := pc }
      = .ok { s with
          stack := EvmYul.State.calldataload s.toState offset :: rest
          pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-! ## Structural lemmas about `EVM.State` and `runSeq` -/

/-- Updating only the `stack` and `pc` fields of an `EVM.State` leaves its
    parent `toState` projection (calldata, executionEnv, accountMap, …)
    unchanged. Tagged `@[simp]` so that calldata / storage hypotheses
    continue to apply after any number of stack/pc updates. -/
@[simp] lemma toState_update
    (s : EVM.State) (stk : Stack UInt256) (pc : UInt256) :
    ({ s with stack := stk, pc := pc } : EVM.State).toState = s.toState := rfl

/-- Fusion lemma for `runSeq`: if we know that `runOp op s arg = .ok s'`,
    then stepping one cons-cell off `runSeq` simply advances the state to
    `s'`. Used to chain opcode equations without fighting the do-notation
    match that generic `simp` struggles to iota-reduce. -/
lemma runSeq_cons_ok
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (rest : Program) (s s' : EVM.State)
    (h : runOp op s arg = .ok s') :
    runSeq ((op, arg) :: rest) s = runSeq rest s' := by
  show (do let s' ← runOp op s arg; runSeq rest s') = _
  rw [h]
  rfl

end EvmSmith
