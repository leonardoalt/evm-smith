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

Covers a working subset of the EVM (pushes, arithmetic, comparisons,
DUP/SWAP, JUMPI/JUMPDEST, POP/STOP, CALLER/CALLVALUE, SLOAD/SSTORE,
CALLDATALOAD, REVERT). The Add3 / Register / Weth proofs use these
directly; the Frame library
(`EVMYulLean/EvmYul/Frame/StepShapes.lean`, `PcWalk.lean`) is the
place to look for *frame-aware* per-opcode lemmas (post-state
shape preservation under `EVM.step`). Extend this file when a new
program needs a `runOp` equation for an opcode not listed below.

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
The framework's `EvmYul.Frame.StepShapes.lean` is the equivalent layer
on the `EVM.step` (frame-aware) side; together they give bytecode-walk
proofs a stable substitution surface that doesn't fight the kernel.
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

/-- `CALLER` pushes the caller's address (stored in
    `executionEnv.source`) as a `UInt256`, advances PC by 1. -/
lemma runOp_caller
    (s : EVM.State) (stk : Stack UInt256) (pc : UInt256) :
    runOp .CALLER { s with stack := stk, pc := pc }
      = .ok { s with
          stack := UInt256.ofNat s.executionEnv.source.val :: stk
          pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-- `SSTORE` pops a `(key, value)` pair and threads them through
    `EvmYul.State.sstore`, which writes `storage[key] = value` in the
    contract's own account (`codeOwner`), flips substate bits
    (`accessedStorageKeys`, `refundBalance`), and advances PC by 1.

    This lemma is purely mechanical — it says "the post-state is the
    input with `toState` run through `sstore`." Characterising what
    `sstore` actually does to `accountMap` is the job of the helper
    lemmas below (`sstore_writes_slot`, etc.). -/
lemma runOp_sstore
    (s : EVM.State) (key val : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .SSTORE { s with stack := key :: val :: rest, pc := pc }
      = .ok { s with
          stack := rest
          pc := pc + UInt256.ofNat 1
          toState := EvmYul.State.sstore s.toState key val } := by
  unfold runOp EvmYul.step; rfl

/-- `CALLVALUE` pushes `executionEnv.weiValue` (the `msg.value`
    transferred into this call-frame), advances PC by 1. -/
lemma runOp_callvalue
    (s : EVM.State) (stk : Stack UInt256) (pc : UInt256) :
    runOp .CALLVALUE { s with stack := stk, pc := pc }
      = .ok { s with
          stack := s.executionEnv.weiValue :: stk
          pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-- `SLOAD` pops a key, pushes the result of
    `EvmYul.State.sload toState key` (which is `(toState,
    storage[key])`), advances PC by 1. -/
lemma runOp_sload
    (s : EVM.State) (key : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .SLOAD { s with stack := key :: rest, pc := pc }
      = .ok { s with
          stack := (EvmYul.State.sload s.toState key).2 :: rest
          pc := pc + UInt256.ofNat 1
          toState := (EvmYul.State.sload s.toState key).1 } := by
  unfold runOp EvmYul.step; rfl

/-- `LT` on stack `[a, b, rest]`: pops both, pushes `a < b` as
    `UInt256` (1 if true, 0 if false), advances PC by 1. -/
lemma runOp_lt
    (s : EVM.State) (a b : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .LT { s with stack := a :: b :: rest, pc := pc }
      = .ok { s with
          stack := UInt256.lt a b :: rest
          pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-- `ISZERO` on `[a, rest]`: pops `a`, pushes `1` if `a = 0` else
    `0`, PC + 1. -/
lemma runOp_iszero
    (s : EVM.State) (a : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .ISZERO { s with stack := a :: rest, pc := pc }
      = .ok { s with
          stack := UInt256.isZero a :: rest
          pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-- `SUB` on `[a, b, rest]`: pops both, pushes `a - b`, PC + 1. -/
lemma runOp_sub
    (s : EVM.State) (a b : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .SUB { s with stack := a :: b :: rest, pc := pc }
      = .ok { s with
          stack := (a - b) :: rest
          pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-- `JUMPDEST` is a no-op mark; it advances PC by 1. -/
lemma runOp_jumpdest
    (s : EVM.State) :
    runOp .JUMPDEST s = .ok { s with pc := s.pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step
  rfl

/-- `JUMPI` (taken branch): stack `[dest, cond, rest]` with `cond ≠ 0`
    sets `pc := dest`, pops both operands. -/
lemma runOp_jumpi_taken
    (s : EVM.State) (dest cond : UInt256) (rest : Stack UInt256) (pc : UInt256)
    (hcond : (cond != (⟨0⟩ : UInt256)) = true) :
    runOp .JUMPI { s with stack := dest :: cond :: rest, pc := pc }
      = .ok { s with stack := rest, pc := dest } := by
  unfold runOp EvmYul.step
  show Except.ok { s with
    pc := (if (cond != (⟨0⟩ : UInt256)) = true then dest else pc + UInt256.ofNat 1)
    stack := rest } = _
  rw [if_pos hcond]

/-- `JUMPI` (not-taken branch): `cond = 0` leaves PC at `pc + 1`,
    pops both operands. -/
lemma runOp_jumpi_not_taken
    (s : EVM.State) (dest : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .JUMPI { s with stack := dest :: (⟨0⟩ : UInt256) :: rest, pc := pc }
      = .ok { s with stack := rest, pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step
  rfl

/-- `REVERT` at the pure `EvmYul.step` level actually produces `.ok`
    (setting `H_return`); the `X` iterator at higher levels is what
    interprets the revert for message-call purposes. For block-level
    proofs this means we treat REVERT as a tail opcode that produces
    a concrete post-state, then separately note "the outer
    interpretation is a revert". -/
lemma runOp_revert
    (s : EVM.State) (offset size : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .REVERT { s with stack := offset :: size :: rest, pc := pc }
      = .ok { s with
          stack := rest
          pc := pc + UInt256.ofNat 1
          toMachineState := MachineState.evmRevert s.toMachineState offset size } := by
  unfold runOp EvmYul.step; rfl

/-! ### DUPn / SWAPn (spike ahead of Weth's withdraw block) -/

/-- `DUP1` duplicates the top element. -/
lemma runOp_dup1
    (s : EVM.State) (a : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .DUP1 { s with stack := a :: rest, pc := pc }
      = .ok { s with stack := a :: a :: rest, pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-- `DUP2` duplicates the 2nd element from the top. -/
lemma runOp_dup2
    (s : EVM.State) (a b : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .DUP2 { s with stack := a :: b :: rest, pc := pc }
      = .ok { s with stack := b :: a :: b :: rest, pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-- `DUP3` duplicates the 3rd element from the top. -/
lemma runOp_dup3
    (s : EVM.State) (a b c : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .DUP3 { s with stack := a :: b :: c :: rest, pc := pc }
      = .ok { s with stack := c :: a :: b :: c :: rest, pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-- `DUP5` duplicates the 5th element from the top. -/
lemma runOp_dup5
    (s : EVM.State) (a b c d e : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .DUP5 { s with stack := a :: b :: c :: d :: e :: rest, pc := pc }
      = .ok { s with stack := e :: a :: b :: c :: d :: e :: rest
                     pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-- `SWAP1` swaps the top two elements. -/
lemma runOp_swap1
    (s : EVM.State) (a b : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .SWAP1 { s with stack := a :: b :: rest, pc := pc }
      = .ok { s with stack := b :: a :: rest, pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-- `SWAP2` swaps the top and 3rd elements. -/
lemma runOp_swap2
    (s : EVM.State) (a b c : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .SWAP2 { s with stack := a :: b :: c :: rest, pc := pc }
      = .ok { s with stack := c :: b :: a :: rest, pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-- `POP` removes the top element. -/
lemma runOp_pop
    (s : EVM.State) (a : UInt256) (rest : Stack UInt256) (pc : UInt256) :
    runOp .POP { s with stack := a :: rest, pc := pc }
      = .ok { s with stack := rest, pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-- `STOP` sets `machineState.returnData` to empty. No stack change, no
    PC advance, no `accountMap` / `toState` change. In `runSeq` flow
    STOP is typically the last opcode; this lemma just pushes the
    chain through. -/
lemma runOp_stop (s : EVM.State) :
    runOp .STOP s
      = .ok { s with toMachineState :=
          s.toMachineState.setReturnData .empty } := by
  unfold runOp EvmYul.step; rfl

/-! ## Structural lemmas about `EVM.State` and `runSeq` -/

/-- Updating only the `stack` and `pc` fields of an `EVM.State` leaves its
    parent `toState` projection (calldata, executionEnv, accountMap, …)
    unchanged. Tagged `@[simp]` so that calldata / storage hypotheses
    continue to apply after any number of stack/pc updates. -/
@[simp] lemma toState_update
    (s : EVM.State) (stk : Stack UInt256) (pc : UInt256) :
    ({ s with stack := stk, pc := pc } : EVM.State).toState = s.toState := rfl

/-! ## Characterising `EvmYul.State.sstore`

`runOp_sstore` exposes the post-state as `toState := sstore s.toState
key val` but doesn't say what `sstore` does. `sstore_accountMap`
reduces it to one insert on the account map, under the hypothesis
that the account exists. That one equation is enough to drive
program-level storage invariants; deriving slot-level and
other-account corollaries from it is RBMap-lemma work that we leave
to program proofs (so the dependency on Batteries' RBMap API is
localised there, not here).

Note on substate: `sstore` also mutates `substate.refundBalance` and
`substate.accessedStorageKeys`. These are orthogonal to the account
map; program invariants about storage phrase themselves on
`accountMap` only and sidestep substate. -/

/-- `sstore`'s effect on `accountMap`: when the code owner exists,
    it's exactly one `insert` of `acc.updateStorage key val` at the
    code-owner address. -/
lemma sstore_accountMap
    (s : EvmYul.State .EVM) (key val : UInt256)
    (acc : Account .EVM)
    (hacct : s.accountMap.find? s.executionEnv.codeOwner = some acc) :
    (EvmYul.State.sstore s key val).accountMap =
    s.accountMap.insert s.executionEnv.codeOwner (acc.updateStorage key val) := by
  unfold EvmYul.State.sstore Option.option
  simp [EvmYul.State.lookupAccount, hacct, EvmYul.State.setAccount,
        EvmYul.State.addAccessedStorageKey]

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
