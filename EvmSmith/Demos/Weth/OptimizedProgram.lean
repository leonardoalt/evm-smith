import EvmSmith.Lemmas
import EvmSmith.Demos.Weth.Program

/-!
# Optimized Weth bytecode + per-block equivalence proofs

A single optimized runtime (74 bytes vs the original 86) layering two
classes of peephole optimizations on `Weth.bytecode`. Each is observably
equivalent to the original; `weth_solvency_invariant` (proved against
the original `Weth.bytecode`) carries over via the equivalence theorems
below — every reachable state of the optimized bytecode coincides with
the corresponding state of the original on `(stack, toState,
toMachineState)`, with PCs differing only by the saved bytes.

## Class 1 — PUSH0 swaps (EIP-3855, Shanghai)

Every `PUSH1 0` (`60 00`, 2 bytes) becomes `PUSH0` (`5f`, 1 byte). Nine
sites across the runtime:

* PC 0           — selector-load offset
* PCs 26, 27     — no-selector REVERT args
* PCs 56, 57, 58, 59 — CALL retSize / retOff / argsSize / argsOff
* PCs 71, 72     — final REVERT args

`PUSH0` is implemented in EVMYulLean (`EvmYul/Semantics.lean:516`):
pushes `⟨0⟩` onto the stack and advances PC by 1.

## Class 2 — CALLER-twice + drop POP (runtime gas)

Three runtime-gas wins on the deposit and withdraw bodies:

1. **Deposit body**: drop `DUP1` after the first `CALLER`; replace the
   trailing `SWAP1` before `SSTORE` with a second `CALLER`. `CALLER`
   is BASE (2 gas); `DUP1` / `SWAP1` are VERYLOW (3 gas each).
   −4 gas, −1 byte.
2. **Withdraw body**: same trick. `DUP3` collapses to `DUP2` since
   sender no longer sits between `bal` and `x` on the stack.
   −4 gas success, −3 gas insufficient-balance revert, −1 byte.
3. **Drop the dead `POP` before `STOP`** on withdraw success: the
   leftover `x` is discarded with the call frame on halt anyway.
   −2 gas, −1 byte.

## Layout: 86 → 74 bytes, label shifts

| label              | original | optimized |
|--------------------|---------:|----------:|
| `depositLblOpt`    |       32 |        29 |
| `withdrawLblOpt`   |       42 |        38 |
| `revertLblOpt`     |       80 |        70 |

## Equivalence proofs

Each peephole site is closed by a block-level equivalence: both
`runSeq` invocations land in `.ok` of an explicit shared post-state
helper, parameterised over the differing `pcEnd`. Observable
corollaries derive `r_orig.{stack,toState,toMachineState} = r_opt.{...}`
by `rfl`, hiding the PC difference.

Class 1 sites (intermediate stacks coincide pointwise):
* `selectorLoad_equiv`     `[PUSH1 0; CALLDATALOAD]` ≡ `[PUSH0; CALLDATALOAD]`
* `noSelectorRevert_equiv` `[PUSH1 0; PUSH1 0; REVERT]` ≡ `[PUSH0; PUSH0; REVERT]`
* `callPushes_equiv`       four `PUSH1 0`s ≡ four `PUSH0`s
* `revertBlock_equiv`      `[JUMPDEST; PUSH1 0; PUSH1 0; REVERT]` ≡ `[JUMPDEST; PUSH0; PUSH0; REVERT]`

Class 2 sites (intermediate stacks differ; only end-of-block agrees):
* `depositBlock_equiv`             — full state mod PC for the deposit body.
* `withdrawPreCallBlock_run` +
  `withdrawPreCallBlockOpt_run`    — both pre-CALL success paths land
                                     at the same SSTORE post-state
                                     under `UInt256.lt bal x = 0`.
* `postCallSuccessTail_equiv`      — halt-state agreement after the
                                     post-CALL `POP` drop (stacks
                                     differ but are unobservable
                                     post-frame).
-/

namespace EvmSmith.Weth
open EvmYul EvmYul.EVM EvmSmith

/-! ## PUSH0 step lemma -/

/-- `PUSH0` pushes `⟨0⟩` onto the stack and advances PC by 1.
Companion to `runOp_push1` for the EIP-3855 zero-byte push. -/
lemma runOp_push0
    (s : EVM.State) (stk : Stack UInt256) (pc : UInt256) :
    runOp (.Push .PUSH0) { s with stack := stk, pc := pc } none
      = .ok { s with stack := UInt256.ofNat 0 :: stk, pc := pc + UInt256.ofNat 1 } := by
  unfold runOp EvmYul.step; rfl

/-! ## Updated label values -/

/-- `depositLbl` shifted from 32 to 29: 3 bytes saved by the three
`PUSH1 0` → `PUSH0` swaps before deposit's JUMPDEST. -/
def depositLblOpt : UInt256 := UInt256.ofNat 29

/-- `withdrawLbl` shifted from 42 to 38: 3 bytes from PUSH0 swaps in
dispatch + 1 byte from the deposit body's dropped `DUP1`. -/
def withdrawLblOpt : UInt256 := UInt256.ofNat 38

/-- `revertLbl` shifted from 80 to 70: 3 (dispatch PUSH0s) + 1 (deposit
DUP1) + 1 (withdraw DUP1) + 4 (CALL-arg PUSH0s) + 1 (post-CALL POP) =
10 bytes. -/
def revertLblOpt : UInt256 := UInt256.ofNat 70

/-! ## Optimized full bytecode (74 bytes) -/

/-- The optimized WETH runtime bytecode (PUSH0 swaps + CALLER-twice +
dropped POP). -/
def bytecodeOpt : ByteArray := ⟨#[
  -- Dispatch (PCs 0..28, was 0..31)
  0x5f,                            -- 0:    PUSH0          (was: PUSH1 0)
  0x35,                            -- 1:    CALLDATALOAD
  0x60, 0xe0,                      -- 2:    PUSH1 0xe0
  0x1c,                            -- 4:    SHR
  0x80,                            -- 5:    DUP1
  0x63, 0xd0, 0xe3, 0x0d, 0xb0,    -- 6:    PUSH4 depositSelector
  0x14,                            -- 11:   EQ
  0x61, 0x00, 0x1d,                -- 12:   PUSH2 depositLblOpt = 29
  0x57,                            -- 15:   JUMPI
  0x63, 0x2e, 0x1a, 0x7d, 0x4d,    -- 16:   PUSH4 withdrawSelector
  0x14,                            -- 21:   EQ
  0x61, 0x00, 0x26,                -- 22:   PUSH2 withdrawLblOpt = 38
  0x57,                            -- 25:   JUMPI
  0x5f, 0x5f, 0xfd,                -- 26:   PUSH0; PUSH0; REVERT
  -- Deposit block (PCs 29..37, was 32..41)
  0x5b,                            -- 29:   JUMPDEST
  0x50,                            -- 30:   POP
  0x33,                            -- 31:   CALLER
  0x54,                            -- 32:   SLOAD
  0x34, 0x01,                      -- 33:   CALLVALUE; ADD
  0x33,                            -- 35:   CALLER         (was: SWAP1)
  0x55,                            -- 36:   SSTORE
  0x00,                            -- 37:   STOP
  -- Withdraw block (PCs 38..69, was 42..79)
  0x5b,                            -- 38:   JUMPDEST
  0x60, 0x04, 0x35,                -- 39:   PUSH1 4; CALLDATALOAD
  0x33,                            -- 42:   CALLER
  0x54,                            -- 43:   SLOAD          (no DUP1)
  0x81, 0x81, 0x10,                -- 44:   DUP2; DUP2; LT (was DUP3; DUP2)
  0x61, 0x00, 0x46, 0x57,          -- 47:   PUSH2 revertLblOpt = 70; JUMPI
  0x81, 0x90, 0x03,                -- 51:   DUP2; SWAP1; SUB (was DUP3 …)
  0x33, 0x55,                      -- 54:   CALLER; SSTORE   (was: SWAP1; SSTORE)
  0x5f, 0x5f,                      -- 56:   PUSH0; PUSH0     (retSize, retOff)
  0x5f, 0x5f,                      -- 58:   PUSH0; PUSH0     (argsSize, argsOff)
  0x84, 0x33, 0x5a,                -- 60:   DUP5; CALLER; GAS
  0xf1,                            -- 63:   CALL
  0x15,                            -- 64:   ISZERO
  0x61, 0x00, 0x46, 0x57,          -- 65:   PUSH2 revertLblOpt; JUMPI
  0x00,                            -- 69:   STOP   (POP dropped)
  -- Revert block (PCs 70..73, was 80..85)
  0x5b,                            -- 70:   JUMPDEST
  0x5f, 0x5f, 0xfd                 -- 71:   PUSH0; PUSH0; REVERT
]⟩

/-! ## Site A: selector-load prefix `PUSH1 0; CALLDATALOAD` (PC 0) -/

/-- Original two-op selector-load prefix at PC 0. -/
def selectorLoad : EvmSmith.Program :=
  [ (.Push .PUSH1,  some (UInt256.ofNat 0, 1))
  , (.CALLDATALOAD, none) ]

/-- PUSH0-optimized selector-load prefix. -/
def selectorLoadOpt : EvmSmith.Program :=
  [ (.Push .PUSH0,  none)
  , (.CALLDATALOAD, none) ]

/-- Shared post-state of the selector-load prefix. PC differs between
the two blocks; everything else (specifically, the loaded calldata
word on top of the stack) is identical. -/
private def selectorLoadPost (s : EVM.State) (pcEnd : UInt256) : EVM.State :=
  { s with
      stack := EvmYul.State.calldataload s.toState (UInt256.ofNat 0) :: s.stack
      pc    := pcEnd }

theorem selectorLoad_equiv (s : EVM.State) :
    runSeq selectorLoad s
      = .ok (selectorLoadPost s (s.pc + UInt256.ofNat 2 + UInt256.ofNat 1)) ∧
    runSeq selectorLoadOpt s
      = .ok (selectorLoadPost s (s.pc + UInt256.ofNat 1 + UInt256.ofNat 1)) := by
  have hs : s = { s with stack := s.stack, pc := s.pc } := by cases s; rfl
  have e1_orig := runOp_push1 s (UInt256.ofNat 0) s.stack s.pc
  have e1_opt  := runOp_push0 s s.stack s.pc
  have e2_orig :=
    runOp_calldataload s (UInt256.ofNat 0) s.stack
      (s.pc + UInt256.ofNat 2)
  have e2_opt :=
    runOp_calldataload s (UInt256.ofNat 0) s.stack
      (s.pc + UInt256.ofNat 1)
  refine ⟨?_, ?_⟩
  · show runSeq selectorLoad s = .ok _
    conv_lhs =>
      rw [hs]; unfold selectorLoad
      rw [runSeq_cons_ok _ _ _ _ _ e1_orig, runSeq_cons_ok _ _ _ _ _ e2_orig]
      unfold runSeq
    rfl
  · show runSeq selectorLoadOpt s = .ok _
    conv_lhs =>
      rw [hs]; unfold selectorLoadOpt
      rw [runSeq_cons_ok _ _ _ _ _ e1_opt, runSeq_cons_ok _ _ _ _ _ e2_opt]
      unfold runSeq
    rfl

/-! ## Site B: no-selector REVERT (PCs 27-31 in original; 26-28 in opt) -/

/-- Original three-op no-selector REVERT block. -/
def noSelectorRevert : EvmSmith.Program :=
  [ (.Push .PUSH1, some (UInt256.ofNat 0, 1))
  , (.Push .PUSH1, some (UInt256.ofNat 0, 1))
  , (.REVERT,      none) ]

/-- PUSH0-optimized no-selector REVERT block. -/
def noSelectorRevertOpt : EvmSmith.Program :=
  [ (.Push .PUSH0, none)
  , (.Push .PUSH0, none)
  , (.REVERT,      none) ]

/-- Shared post-state of any of the WETH revert paths: stack
restored, REVERT-machine-state set with offset = size = 0. -/
private def revertPost (s : EVM.State) (pcEnd : UInt256) : EVM.State :=
  { s with
      stack := s.stack
      pc    := pcEnd
      toMachineState := MachineState.evmRevert s.toMachineState
        (UInt256.ofNat 0) (UInt256.ofNat 0) }

theorem noSelectorRevert_equiv (s : EVM.State) :
    runSeq noSelectorRevert s
      = .ok (revertPost s (s.pc + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 1)) ∧
    runSeq noSelectorRevertOpt s
      = .ok (revertPost s (s.pc + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1)) := by
  have hs : s = { s with stack := s.stack, pc := s.pc } := by cases s; rfl
  have e1_orig := runOp_push1 s (UInt256.ofNat 0) s.stack s.pc
  have e1_opt  := runOp_push0 s s.stack s.pc
  have e2_orig :=
    runOp_push1 s (UInt256.ofNat 0) (UInt256.ofNat 0 :: s.stack)
      (s.pc + UInt256.ofNat 2)
  have e2_opt :=
    runOp_push0 s (UInt256.ofNat 0 :: s.stack)
      (s.pc + UInt256.ofNat 1)
  have e3_orig :=
    runOp_revert s (UInt256.ofNat 0) (UInt256.ofNat 0) s.stack
      (s.pc + UInt256.ofNat 2 + UInt256.ofNat 2)
  have e3_opt :=
    runOp_revert s (UInt256.ofNat 0) (UInt256.ofNat 0) s.stack
      (s.pc + UInt256.ofNat 1 + UInt256.ofNat 1)
  refine ⟨?_, ?_⟩
  · show runSeq noSelectorRevert s = .ok _
    conv_lhs =>
      rw [hs]; unfold noSelectorRevert
      rw [runSeq_cons_ok _ _ _ _ _ e1_orig, runSeq_cons_ok _ _ _ _ _ e2_orig,
          runSeq_cons_ok _ _ _ _ _ e3_orig]
      unfold runSeq
    rfl
  · show runSeq noSelectorRevertOpt s = .ok _
    conv_lhs =>
      rw [hs]; unfold noSelectorRevertOpt
      rw [runSeq_cons_ok _ _ _ _ _ e1_opt, runSeq_cons_ok _ _ _ _ _ e2_opt,
          runSeq_cons_ok _ _ _ _ _ e3_opt]
      unfold runSeq
    rfl

/-! ## Site C: CALL setup prefix (four `PUSH1 0`s before CALL's args)

Four `PUSH1 0`s pushed before the CALL's three remaining args
(`DUP5`, `CALLER`, `GAS`). The equivalence is just over the four
pushes; the downstream CALL is byte-identical and runs identically
on the matching post-stack. -/

/-- Original four `PUSH1 0`s pushed before CALL's args. -/
def callPushes : EvmSmith.Program :=
  [ (.Push .PUSH1, some (UInt256.ofNat 0, 1))
  , (.Push .PUSH1, some (UInt256.ofNat 0, 1))
  , (.Push .PUSH1, some (UInt256.ofNat 0, 1))
  , (.Push .PUSH1, some (UInt256.ofNat 0, 1)) ]

/-- PUSH0-optimized four-zero prefix. -/
def callPushesOpt : EvmSmith.Program :=
  [ (.Push .PUSH0, none)
  , (.Push .PUSH0, none)
  , (.Push .PUSH0, none)
  , (.Push .PUSH0, none) ]

/-- Post-state after pushing four zeros: stack has four `0`s on top
of the original; only PC differs between the two blocks. -/
private def fourZerosPost (s : EVM.State) (pcEnd : UInt256) : EVM.State :=
  { s with
      stack := UInt256.ofNat 0 :: UInt256.ofNat 0 ::
               UInt256.ofNat 0 :: UInt256.ofNat 0 :: s.stack
      pc    := pcEnd }

theorem callPushes_equiv (s : EVM.State) :
    runSeq callPushes s
      = .ok (fourZerosPost s
              (s.pc + UInt256.ofNat 2 + UInt256.ofNat 2
                    + UInt256.ofNat 2 + UInt256.ofNat 2)) ∧
    runSeq callPushesOpt s
      = .ok (fourZerosPost s
              (s.pc + UInt256.ofNat 1 + UInt256.ofNat 1
                    + UInt256.ofNat 1 + UInt256.ofNat 1)) := by
  have hs : s = { s with stack := s.stack, pc := s.pc } := by cases s; rfl
  -- Original: 4 × PUSH1 0, each advances PC by 2.
  have o1 := runOp_push1 s (UInt256.ofNat 0) s.stack s.pc
  have o2 :=
    runOp_push1 s (UInt256.ofNat 0) (UInt256.ofNat 0 :: s.stack)
      (s.pc + UInt256.ofNat 2)
  have o3 :=
    runOp_push1 s (UInt256.ofNat 0)
      (UInt256.ofNat 0 :: UInt256.ofNat 0 :: s.stack)
      (s.pc + UInt256.ofNat 2 + UInt256.ofNat 2)
  have o4 :=
    runOp_push1 s (UInt256.ofNat 0)
      (UInt256.ofNat 0 :: UInt256.ofNat 0 :: UInt256.ofNat 0 :: s.stack)
      (s.pc + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2)
  -- Optimized: 4 × PUSH0, each advances PC by 1.
  have p1 := runOp_push0 s s.stack s.pc
  have p2 :=
    runOp_push0 s (UInt256.ofNat 0 :: s.stack)
      (s.pc + UInt256.ofNat 1)
  have p3 :=
    runOp_push0 s (UInt256.ofNat 0 :: UInt256.ofNat 0 :: s.stack)
      (s.pc + UInt256.ofNat 1 + UInt256.ofNat 1)
  have p4 :=
    runOp_push0 s
      (UInt256.ofNat 0 :: UInt256.ofNat 0 :: UInt256.ofNat 0 :: s.stack)
      (s.pc + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1)
  refine ⟨?_, ?_⟩
  · show runSeq callPushes s = .ok _
    conv_lhs =>
      rw [hs]; unfold callPushes
      rw [runSeq_cons_ok _ _ _ _ _ o1, runSeq_cons_ok _ _ _ _ _ o2,
          runSeq_cons_ok _ _ _ _ _ o3, runSeq_cons_ok _ _ _ _ _ o4]
      unfold runSeq
    rfl
  · show runSeq callPushesOpt s = .ok _
    conv_lhs =>
      rw [hs]; unfold callPushesOpt
      rw [runSeq_cons_ok _ _ _ _ _ p1, runSeq_cons_ok _ _ _ _ _ p2,
          runSeq_cons_ok _ _ _ _ _ p3, runSeq_cons_ok _ _ _ _ _ p4]
      unfold runSeq
    rfl

/-! ## Site D: final REVERT block (PCs 80-85 orig; 70-73 opt) -/

/-- Original four-op final REVERT block (with leading `JUMPDEST`). -/
def revertBlock : EvmSmith.Program :=
  [ (.JUMPDEST,    none)
  , (.Push .PUSH1, some (UInt256.ofNat 0, 1))
  , (.Push .PUSH1, some (UInt256.ofNat 0, 1))
  , (.REVERT,      none) ]

/-- PUSH0-optimized final REVERT block. -/
def revertBlockOpt : EvmSmith.Program :=
  [ (.JUMPDEST,    none)
  , (.Push .PUSH0, none)
  , (.Push .PUSH0, none)
  , (.REVERT,      none) ]

theorem revertBlock_equiv (s : EVM.State) :
    runSeq revertBlock s
      = .ok (revertPost s
              (s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 1)) ∧
    runSeq revertBlockOpt s
      = .ok (revertPost s
              (s.pc + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1)) := by
  have hs : s = { s with stack := s.stack, pc := s.pc } := by cases s; rfl
  have e1 :
      runOp .JUMPDEST { s with stack := s.stack, pc := s.pc }
        = .ok { s with stack := s.stack, pc := s.pc + UInt256.ofNat 1 } := by
    unfold runOp EvmYul.step; rfl
  have e2_orig :=
    runOp_push1 s (UInt256.ofNat 0) s.stack (s.pc + UInt256.ofNat 1)
  have e2_opt :=
    runOp_push0 s s.stack (s.pc + UInt256.ofNat 1)
  have e3_orig :=
    runOp_push1 s (UInt256.ofNat 0) (UInt256.ofNat 0 :: s.stack)
      (s.pc + UInt256.ofNat 1 + UInt256.ofNat 2)
  have e3_opt :=
    runOp_push0 s (UInt256.ofNat 0 :: s.stack)
      (s.pc + UInt256.ofNat 1 + UInt256.ofNat 1)
  have e4_orig :=
    runOp_revert s (UInt256.ofNat 0) (UInt256.ofNat 0) s.stack
      (s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 2)
  have e4_opt :=
    runOp_revert s (UInt256.ofNat 0) (UInt256.ofNat 0) s.stack
      (s.pc + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1)
  refine ⟨?_, ?_⟩
  · show runSeq revertBlock s = .ok _
    conv_lhs =>
      rw [hs]; unfold revertBlock
      rw [runSeq_cons_ok _ _ _ _ _ e1, runSeq_cons_ok _ _ _ _ _ e2_orig,
          runSeq_cons_ok _ _ _ _ _ e3_orig, runSeq_cons_ok _ _ _ _ _ e4_orig]
      unfold runSeq
    rfl
  · show runSeq revertBlockOpt s = .ok _
    conv_lhs =>
      rw [hs]; unfold revertBlockOpt
      rw [runSeq_cons_ok _ _ _ _ _ e1, runSeq_cons_ok _ _ _ _ _ e2_opt,
          runSeq_cons_ok _ _ _ _ _ e3_opt, runSeq_cons_ok _ _ _ _ _ e4_opt]
      unfold runSeq
    rfl

/-! ## Site E: Deposit block (CALLER twice instead of DUP1 + SWAP1)

Original deposit block:
`[JUMPDEST, POP, CALLER, DUP1, SLOAD, CALLVALUE, ADD, SWAP1, SSTORE, STOP]`
holds `sender` on the stack across the SLOAD/ADD by `DUP1`-ing it and
then `SWAP1`-ing it under `bal+val` so SSTORE sees `[sender, bal+val]`.

Optimized variant reloads `sender` via a second `CALLER` right before
SSTORE. Saves 4 gas (one VERYLOW removed, one VERYLOW→BASE swap) and
1 byte.

Both blocks halt at `STOP` with the same observable state: stack
restored to its pre-`POP` tail, storage at `sender` set to
`sload(s.toState, sender).2 + s.executionEnv.weiValue`, and the
machine state's `returnData` cleared. -/

/-- Optimized deposit block. -/
def depositBlockOpt : EvmSmith.Program :=
  [ (.JUMPDEST,     none)
  , (.POP,          none)
  , (.CALLER,       none)
  , (.SLOAD,        none)
  , (.CALLVALUE,    none)
  , (.ADD,          none)
  , (.CALLER,       none)
  , (.SSTORE,       none)
  , (.STOP,         none)
  ]

/-- Sender as a `UInt256` (this contract's `msg.sender` for the call). -/
private abbrev senderU (s : EVM.State) : UInt256 :=
  UInt256.ofNat s.executionEnv.source.val
/-- Storage state after `SLOAD`-ing slot `senderU s`. -/
private abbrev sloadedState (s : EVM.State) : EvmYul.State .EVM :=
  (EvmYul.State.sload s.toState (senderU s)).1
/-- Pre-existing balance of `senderU s` at slot `senderU s`. -/
private abbrev loadedBal (s : EVM.State) : UInt256 :=
  (EvmYul.State.sload s.toState (senderU s)).2

/-- Shared post-state of the original and optimized deposit blocks.
Both produce this state from an entry whose stack tops a stale `top`
element (the dispatch-leftover selector). PC differs (original walks
10 opcodes, optimized walks 9). -/
private abbrev depositPost
    (s : EVM.State) (rest : Stack UInt256) (pcEnd : UInt256) : EVM.State :=
  { s with
      stack := rest
      pc := pcEnd
      toState := EvmYul.State.sstore (sloadedState s) (senderU s)
                   (s.executionEnv.weiValue + loadedBal s)
      toMachineState := s.toMachineState.setReturnData .empty }

theorem depositBlock_equiv
    (s : EVM.State) (top : UInt256) (rest : Stack UInt256) (pc0 : UInt256) :
    runSeq Weth.depositBlock { s with stack := top :: rest, pc := pc0 }
      = .ok (depositPost s rest
              (pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1)) ∧
    runSeq depositBlockOpt { s with stack := top :: rest, pc := pc0 }
      = .ok (depositPost s rest
              (pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1)) := by
  refine ⟨?_, ?_⟩
  · -- Original: 10 opcodes (extra DUP1 + SWAP1)
    show runSeq Weth.depositBlock _ = .ok _
    have h1 : runOp .JUMPDEST { s with stack := top :: rest, pc := pc0 }
            = .ok { s with stack := top :: rest, pc := pc0 + UInt256.ofNat 1 } := by
      unfold runOp EvmYul.step; rfl
    have h2 := runOp_pop s top rest (pc0 + UInt256.ofNat 1)
    have h3 := runOp_caller s rest (pc0 + UInt256.ofNat 1 + UInt256.ofNat 1)
    have h4 := runOp_dup1 s (senderU s) rest
                 (pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1)
    have h5 := runOp_sload s (senderU s) (senderU s :: rest)
                 (pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                  UInt256.ofNat 1)
    have h6 :
      runOp .CALLVALUE
        { s with stack := loadedBal s :: senderU s :: rest
                 pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1 + UInt256.ofNat 1
                 toState := sloadedState s }
      = .ok { s with stack := s.executionEnv.weiValue :: loadedBal s :: senderU s :: rest
                     pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
                     toState := sloadedState s } := by
      unfold runOp EvmYul.step; rfl
    have h7 :
      runOp .ADD
        { s with stack := s.executionEnv.weiValue :: loadedBal s :: senderU s :: rest
                 pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
                 toState := sloadedState s }
      = .ok { s with stack := (s.executionEnv.weiValue + loadedBal s) :: senderU s :: rest
                     pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1
                     toState := sloadedState s } := by
      unfold runOp EvmYul.step; rfl
    have h8 :
      runOp .SWAP1
        { s with stack := (s.executionEnv.weiValue + loadedBal s) :: senderU s :: rest
                 pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1
                 toState := sloadedState s }
      = .ok { s with stack := senderU s :: (s.executionEnv.weiValue + loadedBal s) :: rest
                     pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1
                     toState := sloadedState s } := by
      unfold runOp EvmYul.step; rfl
    have h9 :
      runOp .SSTORE
        { s with stack := senderU s :: (s.executionEnv.weiValue + loadedBal s) :: rest
                 pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1 + UInt256.ofNat 1
                 toState := sloadedState s }
      = .ok { s with stack := rest
                     pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
                     toState := EvmYul.State.sstore (sloadedState s) (senderU s)
                                  (s.executionEnv.weiValue + loadedBal s) } := by
      unfold runOp EvmYul.step; rfl
    have h10 :
      runOp .STOP
        { s with stack := rest
                 pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
                 toState := EvmYul.State.sstore (sloadedState s) (senderU s)
                              (s.executionEnv.weiValue + loadedBal s) }
      = .ok { s with stack := rest
                     pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
                     toState := EvmYul.State.sstore (sloadedState s) (senderU s)
                                  (s.executionEnv.weiValue + loadedBal s)
                     toMachineState := s.toMachineState.setReturnData .empty } := by
      unfold runOp EvmYul.step; rfl
    conv_lhs =>
      unfold Weth.depositBlock
      rw [runSeq_cons_ok _ _ _ _ _ h1, runSeq_cons_ok _ _ _ _ _ h2,
          runSeq_cons_ok _ _ _ _ _ h3, runSeq_cons_ok _ _ _ _ _ h4,
          runSeq_cons_ok _ _ _ _ _ h5, runSeq_cons_ok _ _ _ _ _ h6,
          runSeq_cons_ok _ _ _ _ _ h7, runSeq_cons_ok _ _ _ _ _ h8,
          runSeq_cons_ok _ _ _ _ _ h9, runSeq_cons_ok _ _ _ _ _ h10]
      unfold runSeq
  · -- Optimized: 9 opcodes (no DUP1, SWAP1→CALLER)
    show runSeq depositBlockOpt _ = .ok _
    have h1 : runOp .JUMPDEST { s with stack := top :: rest, pc := pc0 }
            = .ok { s with stack := top :: rest, pc := pc0 + UInt256.ofNat 1 } := by
      unfold runOp EvmYul.step; rfl
    have h2 := runOp_pop s top rest (pc0 + UInt256.ofNat 1)
    have h3 := runOp_caller s rest (pc0 + UInt256.ofNat 1 + UInt256.ofNat 1)
    have h4 := runOp_sload s (senderU s) rest
                 (pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1)
    have h5 :
      runOp .CALLVALUE
        { s with stack := loadedBal s :: rest
                 pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1
                 toState := sloadedState s }
      = .ok { s with stack := s.executionEnv.weiValue :: loadedBal s :: rest
                     pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1
                     toState := sloadedState s } := by
      unfold runOp EvmYul.step; rfl
    have h6 :
      runOp .ADD
        { s with stack := s.executionEnv.weiValue :: loadedBal s :: rest
                 pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1 + UInt256.ofNat 1
                 toState := sloadedState s }
      = .ok { s with stack := (s.executionEnv.weiValue + loadedBal s) :: rest
                     pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
                     toState := sloadedState s } := by
      unfold runOp EvmYul.step; rfl
    have h7 :
      runOp .CALLER
        { s with stack := (s.executionEnv.weiValue + loadedBal s) :: rest
                 pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
                 toState := sloadedState s }
      = .ok { s with stack := senderU s :: (s.executionEnv.weiValue + loadedBal s) :: rest
                     pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1
                     toState := sloadedState s } := by
      unfold runOp EvmYul.step; rfl
    have h8 :
      runOp .SSTORE
        { s with stack := senderU s :: (s.executionEnv.weiValue + loadedBal s) :: rest
                 pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1
                 toState := sloadedState s }
      = .ok { s with stack := rest
                     pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1
                     toState := EvmYul.State.sstore (sloadedState s) (senderU s)
                                  (s.executionEnv.weiValue + loadedBal s) } := by
      unfold runOp EvmYul.step; rfl
    have h9 :
      runOp .STOP
        { s with stack := rest
                 pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                       UInt256.ofNat 1 + UInt256.ofNat 1
                 toState := EvmYul.State.sstore (sloadedState s) (senderU s)
                              (s.executionEnv.weiValue + loadedBal s) }
      = .ok { s with stack := rest
                     pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                           UInt256.ofNat 1 + UInt256.ofNat 1
                     toState := EvmYul.State.sstore (sloadedState s) (senderU s)
                                  (s.executionEnv.weiValue + loadedBal s)
                     toMachineState := s.toMachineState.setReturnData .empty } := by
      unfold runOp EvmYul.step; rfl
    conv_lhs =>
      unfold depositBlockOpt
      rw [runSeq_cons_ok _ _ _ _ _ h1, runSeq_cons_ok _ _ _ _ _ h2,
          runSeq_cons_ok _ _ _ _ _ h3, runSeq_cons_ok _ _ _ _ _ h4,
          runSeq_cons_ok _ _ _ _ _ h5, runSeq_cons_ok _ _ _ _ _ h6,
          runSeq_cons_ok _ _ _ _ _ h7, runSeq_cons_ok _ _ _ _ _ h8,
          runSeq_cons_ok _ _ _ _ _ h9]
      unfold runSeq

/-! ## Site F: Withdraw success path (JUMPDEST → SSTORE)

Original `Weth.withdrawPreCallBlock`:
`[JUMPDEST, PUSH1 4, CALLDATALOAD, CALLER, DUP1, SLOAD,`
`  DUP3, DUP2, LT, PUSH2 revertLbl, JUMPI,`
`  DUP3, SWAP1, SUB, SWAP1, SSTORE]` — 16 ops.

Optimized `withdrawPreCallBlockOpt`:
`[JUMPDEST, PUSH1 4, CALLDATALOAD, CALLER, SLOAD,`
`  DUP2, DUP2, LT, PUSH2 revertLblOpt, JUMPI,`
`  DUP2, SWAP1, SUB, CALLER, SSTORE]` — 15 ops.

Both produce the same observable end state on the success path: stack
ends `[x]` (the calldata-loaded withdrawal amount), storage at
`sender` is updated to `bal - x`. Intermediate stacks differ — the
original holds `sender` on stack across the LT/JUMPI; the optimized
reloads `sender` via the trailing `CALLER`.

The proof is conditioned on a *sufficient-balance* hypothesis: the
LT result is zero, so the JUMPI falls through to the success
continuation. The insufficient-balance branch is dispatched via
`Weth.revertBlock`-style PUSH0 PUSH0 REVERT and reaches `revertLbl`
with the right stack. -/

/-- Optimized withdraw pre-CALL block (the success path body). -/
def withdrawPreCallBlockOpt : EvmSmith.Program :=
  [ (.JUMPDEST,     none)
  , (.Push .PUSH1,  some (UInt256.ofNat 4, 1))
  , (.CALLDATALOAD, none)
  , (.CALLER,       none)
  , (.SLOAD,        none)
  , (.DUP2,         none)
  , (.DUP2,         none)
  , (.LT,           none)
  , (.Push .PUSH2,  some (revertLblOpt, 2))
  , (.JUMPI,        none)
  , (.DUP2,         none)
  , (.SWAP1,        none)
  , (.SUB,          none)
  , (.CALLER,       none)
  , (.SSTORE,       none)
  ]

/-- The withdrawal amount `x` as it appears on the stack — reads the
calldata word at offset 4 (where `withdraw(uint256)` places its
argument). -/
private abbrev calldataX (s : EVM.State) : UInt256 :=
  EvmYul.State.calldataload s.toState (UInt256.ofNat 4)

/-- Shared post-state of both withdraw pre-CALL blocks at SSTORE
under the sufficient-balance hypothesis: stack `[x]`, storage at
`sender` decremented by `x`. PC differs by 1 (original has the extra
`DUP1` byte). -/
private abbrev withdrawPost (s : EVM.State) (pcEnd : UInt256) : EVM.State :=
  { s with
      stack := calldataX s :: []
      pc := pcEnd
      toState := EvmYul.State.sstore (sloadedState s) (senderU s)
                   (loadedBal s - calldataX s) }

/-- Original withdraw pre-CALL success path lands at the shared post-state.

PC advance: 19 ticks (10 single-byte ops + PUSH1 4 = +2 + PUSH2 lbl = +3
+ 2 single-byte = total `1+2+1+1+1+1+1+1+1+3+1+1+1+1+1+1 = 19`). -/
theorem withdrawPreCallBlock_run
    (s : EVM.State) (pc0 : UInt256)
    (hLt : UInt256.lt (loadedBal s) (calldataX s) = (⟨0⟩ : UInt256)) :
    runSeq Weth.withdrawPreCallBlock { s with stack := [], pc := pc0 }
      = .ok (withdrawPost s
              (pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 3 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1)) := by
  show runSeq Weth.withdrawPreCallBlock _ = .ok _
  -- 1. JUMPDEST
  have h1 : runOp .JUMPDEST { s with stack := [], pc := pc0 }
          = .ok { s with stack := [], pc := pc0 + UInt256.ofNat 1 } := by
    unfold runOp EvmYul.step; rfl
  -- 2. PUSH1 4
  have h2 := runOp_push1 s (UInt256.ofNat 4) [] (pc0 + UInt256.ofNat 1)
  -- 3. CALLDATALOAD
  have h3 := runOp_calldataload s (UInt256.ofNat 4) []
               (pc0 + UInt256.ofNat 1 + UInt256.ofNat 2)
  -- 4. CALLER
  have h4 := runOp_caller s (calldataX s :: [])
               (pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1)
  -- 5. DUP1
  have h5 := runOp_dup1 s (senderU s) (calldataX s :: [])
               (pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                UInt256.ofNat 1)
  -- 6. SLOAD (key=sender) — modifies toState
  have h6 := runOp_sload s (senderU s) (senderU s :: calldataX s :: [])
               (pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                UInt256.ofNat 1 + UInt256.ofNat 1)
  -- From here on, intermediate states carry `toState := sloadedState s`.
  -- 7. DUP3 (push x)
  have h7 :
    runOp .DUP3
      { s with stack := loadedBal s :: senderU s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := calldataX s :: loadedBal s :: senderU s :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 8. DUP2 (push bal)
  have h8 :
    runOp .DUP2
      { s with stack := calldataX s :: loadedBal s :: senderU s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := loadedBal s :: calldataX s :: loadedBal s :: senderU s ::
                            calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 9. LT — using hLt to substitute (UInt256.lt bal x) → ⟨0⟩
  have h9 :
    runOp .LT
      { s with stack := loadedBal s :: calldataX s :: loadedBal s :: senderU s ::
                        calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := (⟨0⟩ : UInt256) :: loadedBal s :: senderU s :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
                   toState := sloadedState s } := by
    rw [← hLt]; unfold runOp EvmYul.step; rfl
  -- 10. PUSH2 revertLbl
  have h10 :
    runOp (.Push .PUSH2)
      { s with stack := (⟨0⟩ : UInt256) :: loadedBal s :: senderU s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
               toState := sloadedState s }
      (some (Weth.revertLbl, 2))
    = .ok { s with stack := Weth.revertLbl :: (⟨0⟩ : UInt256) :: loadedBal s ::
                            senderU s :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 3
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 11. JUMPI (not taken because cond = ⟨0⟩)
  have h11 :
    runOp .JUMPI
      { s with stack := Weth.revertLbl :: (⟨0⟩ : UInt256) :: loadedBal s ::
                        senderU s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 3
               toState := sloadedState s }
    = .ok { s with stack := loadedBal s :: senderU s :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 3 + UInt256.ofNat 1
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 12. DUP3 (push x)
  have h12 :
    runOp .DUP3
      { s with stack := loadedBal s :: senderU s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 3 + UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := calldataX s :: loadedBal s :: senderU s :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 3 + UInt256.ofNat 1 + UInt256.ofNat 1
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 13. SWAP1
  have h13 :
    runOp .SWAP1
      { s with stack := calldataX s :: loadedBal s :: senderU s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 3 + UInt256.ofNat 1 + UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := loadedBal s :: calldataX s :: senderU s :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 3 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 14. SUB (bal - x)
  have h14 :
    runOp .SUB
      { s with stack := loadedBal s :: calldataX s :: senderU s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 3 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := (loadedBal s - calldataX s) :: senderU s :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 3 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 15. SWAP1
  have h15 :
    runOp .SWAP1
      { s with stack := (loadedBal s - calldataX s) :: senderU s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 3 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := senderU s :: (loadedBal s - calldataX s) :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 3 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 16. SSTORE
  have h16 :
    runOp .SSTORE
      { s with stack := senderU s :: (loadedBal s - calldataX s) :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 3 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 3 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1
                   toState := EvmYul.State.sstore (sloadedState s) (senderU s)
                                (loadedBal s - calldataX s) } := by
    unfold runOp EvmYul.step; rfl
  conv_lhs =>
    unfold Weth.withdrawPreCallBlock
    rw [runSeq_cons_ok _ _ _ _ _ h1, runSeq_cons_ok _ _ _ _ _ h2,
        runSeq_cons_ok _ _ _ _ _ h3, runSeq_cons_ok _ _ _ _ _ h4,
        runSeq_cons_ok _ _ _ _ _ h5, runSeq_cons_ok _ _ _ _ _ h6,
        runSeq_cons_ok _ _ _ _ _ h7, runSeq_cons_ok _ _ _ _ _ h8,
        runSeq_cons_ok _ _ _ _ _ h9, runSeq_cons_ok _ _ _ _ _ h10,
        runSeq_cons_ok _ _ _ _ _ h11, runSeq_cons_ok _ _ _ _ _ h12,
        runSeq_cons_ok _ _ _ _ _ h13, runSeq_cons_ok _ _ _ _ _ h14,
        runSeq_cons_ok _ _ _ _ _ h15, runSeq_cons_ok _ _ _ _ _ h16]
    unfold runSeq

/-- The optimized `withdrawPreCallBlockOpt` lands at the shared
post-state under the same sufficient-balance hypothesis. PC advance:
18 ticks (one fewer than the original, reflecting the dropped `DUP1`
byte). -/
theorem withdrawPreCallBlockOpt_run
    (s : EVM.State) (pc0 : UInt256)
    (hLt : UInt256.lt (loadedBal s) (calldataX s) = (⟨0⟩ : UInt256)) :
    runSeq withdrawPreCallBlockOpt { s with stack := [], pc := pc0 }
      = .ok (withdrawPost s
              (pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1)) := by
  show runSeq withdrawPreCallBlockOpt _ = .ok _
  -- 1. JUMPDEST
  have h1 : runOp .JUMPDEST { s with stack := [], pc := pc0 }
          = .ok { s with stack := [], pc := pc0 + UInt256.ofNat 1 } := by
    unfold runOp EvmYul.step; rfl
  -- 2. PUSH1 4
  have h2 := runOp_push1 s (UInt256.ofNat 4) [] (pc0 + UInt256.ofNat 1)
  -- 3. CALLDATALOAD
  have h3 := runOp_calldataload s (UInt256.ofNat 4) []
               (pc0 + UInt256.ofNat 1 + UInt256.ofNat 2)
  -- 4. CALLER
  have h4 := runOp_caller s (calldataX s :: [])
               (pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1)
  -- 5. SLOAD (no DUP1)
  have h5 := runOp_sload s (senderU s) (calldataX s :: [])
               (pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                UInt256.ofNat 1)
  -- 6. DUP2 (push x)
  have h6 :
    runOp .DUP2
      { s with stack := loadedBal s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := calldataX s :: loadedBal s :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 7. DUP2 (push bal)
  have h7 :
    runOp .DUP2
      { s with stack := calldataX s :: loadedBal s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := loadedBal s :: calldataX s :: loadedBal s :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 8. LT (with hLt)
  have h8 :
    runOp .LT
      { s with stack := loadedBal s :: calldataX s :: loadedBal s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := (⟨0⟩ : UInt256) :: loadedBal s :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1
                   toState := sloadedState s } := by
    rw [← hLt]; unfold runOp EvmYul.step; rfl
  -- 9. PUSH2 revertLblOpt
  have h9 :
    runOp (.Push .PUSH2)
      { s with stack := (⟨0⟩ : UInt256) :: loadedBal s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1
               toState := sloadedState s }
      (some (revertLblOpt, 2))
    = .ok { s with stack := revertLblOpt :: (⟨0⟩ : UInt256) :: loadedBal s ::
                            calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 10. JUMPI not taken
  have h10 :
    runOp .JUMPI
      { s with stack := revertLblOpt :: (⟨0⟩ : UInt256) :: loadedBal s ::
                        calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3
               toState := sloadedState s }
    = .ok { s with stack := loadedBal s :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3 +
                         UInt256.ofNat 1
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 11. DUP2 (push x)
  have h11 :
    runOp .DUP2
      { s with stack := loadedBal s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3 +
                     UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := calldataX s :: loadedBal s :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3 +
                         UInt256.ofNat 1 + UInt256.ofNat 1
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 12. SWAP1
  have h12 :
    runOp .SWAP1
      { s with stack := calldataX s :: loadedBal s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3 +
                     UInt256.ofNat 1 + UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := loadedBal s :: calldataX s :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 13. SUB (bal - x)
  have h13 :
    runOp .SUB
      { s with stack := loadedBal s :: calldataX s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := (loadedBal s - calldataX s) :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 14. CALLER (the reload — replaces the original SWAP1)
  have h14 :
    runOp .CALLER
      { s with stack := (loadedBal s - calldataX s) :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := senderU s :: (loadedBal s - calldataX s) :: calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 15. SSTORE
  have h15 :
    runOp .SSTORE
      { s with stack := senderU s :: (loadedBal s - calldataX s) :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1
               toState := sloadedState s }
    = .ok { s with stack := calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
                   toState := EvmYul.State.sstore (sloadedState s) (senderU s)
                                (loadedBal s - calldataX s) } := by
    unfold runOp EvmYul.step; rfl
  conv_lhs =>
    unfold withdrawPreCallBlockOpt
    rw [runSeq_cons_ok _ _ _ _ _ h1, runSeq_cons_ok _ _ _ _ _ h2,
        runSeq_cons_ok _ _ _ _ _ h3, runSeq_cons_ok _ _ _ _ _ h4,
        runSeq_cons_ok _ _ _ _ _ h5, runSeq_cons_ok _ _ _ _ _ h6,
        runSeq_cons_ok _ _ _ _ _ h7, runSeq_cons_ok _ _ _ _ _ h8,
        runSeq_cons_ok _ _ _ _ _ h9, runSeq_cons_ok _ _ _ _ _ h10,
        runSeq_cons_ok _ _ _ _ _ h11, runSeq_cons_ok _ _ _ _ _ h12,
        runSeq_cons_ok _ _ _ _ _ h13, runSeq_cons_ok _ _ _ _ _ h14,
        runSeq_cons_ok _ _ _ _ _ h15]
    unfold runSeq

/-! ## Site G: Drop the dead `POP` before `STOP` on withdraw success

After `CALL` succeeds and the post-CALL `ISZERO; PUSH2 lbl; JUMPI`
falls through, the stack has the leftover `x` (the value DUP5'd into
the CALL args). The original dispatches a `POP; STOP` cleanup; the
optimized just `STOP`s.

Both halt with the same `toState` (no further mutation between
fallthrough and halt) and `toMachineState.returnData = ∅`. They
*differ* in stack at halt (orig = `rest`, opt = `x :: rest`), but the
stack is unobservable beyond the call frame: it's discarded on halt.
-/

/-- Original success-path tail. -/
def postCallSuccessTail : EvmSmith.Program :=
  [ (.POP,  none)
  , (.STOP, none) ]

/-- Optimized success-path tail (POP dropped). -/
def postCallSuccessTailOpt : EvmSmith.Program :=
  [ (.STOP, none) ]

theorem postCallSuccessTail_equiv
    (s : EVM.State) (x : UInt256) (rest : Stack UInt256) (pc0 : UInt256) :
    runSeq postCallSuccessTail { s with stack := x :: rest, pc := pc0 }
      = .ok { s with
                stack := rest
                pc := pc0 + UInt256.ofNat 1
                toMachineState := s.toMachineState.setReturnData .empty } ∧
    runSeq postCallSuccessTailOpt { s with stack := x :: rest, pc := pc0 }
      = .ok { s with
                stack := x :: rest
                pc := pc0
                toMachineState := s.toMachineState.setReturnData .empty } := by
  refine ⟨?_, ?_⟩
  · -- Original: POP then STOP
    show runSeq postCallSuccessTail _ = .ok _
    have h1 := runOp_pop s x rest pc0
    have h2 : runOp .STOP { s with stack := rest, pc := pc0 + UInt256.ofNat 1 }
            = .ok { s with stack := rest, pc := pc0 + UInt256.ofNat 1
                           toMachineState := s.toMachineState.setReturnData .empty } := by
      unfold runOp EvmYul.step; rfl
    conv_lhs =>
      unfold postCallSuccessTail
      rw [runSeq_cons_ok _ _ _ _ _ h1, runSeq_cons_ok _ _ _ _ _ h2]
      unfold runSeq
  · -- Optimized: just STOP
    show runSeq postCallSuccessTailOpt _ = .ok _
    have h1 : runOp .STOP { s with stack := x :: rest, pc := pc0 }
            = .ok { s with stack := x :: rest, pc := pc0
                           toMachineState := s.toMachineState.setReturnData .empty } := by
      unfold runOp EvmYul.step; rfl
    conv_lhs =>
      unfold postCallSuccessTailOpt
      rw [runSeq_cons_ok _ _ _ _ _ h1]
      unfold runSeq

/-! ## Observable equivalence corollaries

For each site, the explicit-post-state form above immediately yields
that the two `runSeq` invocations land in `.ok` of records that
agree on stack, toState, and toMachineState (only PC differs — and
for `postCallSuccessTail_halt_equiv`, stack also differs but is
unobservable post-halt). -/

theorem selectorLoad_observable_equiv (s : EVM.State) :
    ∃ r_orig r_opt,
      runSeq selectorLoad    s = .ok r_orig ∧
      runSeq selectorLoadOpt s = .ok r_opt ∧
      r_orig.stack          = r_opt.stack ∧
      r_orig.toState        = r_opt.toState ∧
      r_orig.toMachineState = r_opt.toMachineState := by
  obtain ⟨h_orig, h_opt⟩ := selectorLoad_equiv s
  exact ⟨_, _, h_orig, h_opt, rfl, rfl, rfl⟩

theorem noSelectorRevert_observable_equiv (s : EVM.State) :
    ∃ r_orig r_opt,
      runSeq noSelectorRevert    s = .ok r_orig ∧
      runSeq noSelectorRevertOpt s = .ok r_opt ∧
      r_orig.stack          = r_opt.stack ∧
      r_orig.toState        = r_opt.toState ∧
      r_orig.toMachineState = r_opt.toMachineState := by
  obtain ⟨h_orig, h_opt⟩ := noSelectorRevert_equiv s
  exact ⟨_, _, h_orig, h_opt, rfl, rfl, rfl⟩

theorem callPushes_observable_equiv (s : EVM.State) :
    ∃ r_orig r_opt,
      runSeq callPushes    s = .ok r_orig ∧
      runSeq callPushesOpt s = .ok r_opt ∧
      r_orig.stack          = r_opt.stack ∧
      r_orig.toState        = r_opt.toState ∧
      r_orig.toMachineState = r_opt.toMachineState := by
  obtain ⟨h_orig, h_opt⟩ := callPushes_equiv s
  exact ⟨_, _, h_orig, h_opt, rfl, rfl, rfl⟩

theorem revertBlock_observable_equiv (s : EVM.State) :
    ∃ r_orig r_opt,
      runSeq revertBlock    s = .ok r_orig ∧
      runSeq revertBlockOpt s = .ok r_opt ∧
      r_orig.stack          = r_opt.stack ∧
      r_orig.toState        = r_opt.toState ∧
      r_orig.toMachineState = r_opt.toMachineState := by
  obtain ⟨h_orig, h_opt⟩ := revertBlock_equiv s
  exact ⟨_, _, h_orig, h_opt, rfl, rfl, rfl⟩

/-- Observable equivalence of original and optimized deposit blocks.
Both halt with identical `toState`, `toMachineState`, and `stack`;
only PC differs (optimized saves 1 byte = 1 PC tick). -/
theorem depositBlock_observable_equiv
    (s : EVM.State) (top : UInt256) (rest : Stack UInt256) (pc0 : UInt256) :
    ∃ r_orig r_opt,
      runSeq Weth.depositBlock { s with stack := top :: rest, pc := pc0 } = .ok r_orig ∧
      runSeq depositBlockOpt    { s with stack := top :: rest, pc := pc0 } = .ok r_opt ∧
      r_orig.stack          = r_opt.stack ∧
      r_orig.toState        = r_opt.toState ∧
      r_orig.toMachineState = r_opt.toMachineState := by
  obtain ⟨h_orig, h_opt⟩ := depositBlock_equiv s top rest pc0
  exact ⟨_, _, h_orig, h_opt, rfl, rfl, rfl⟩

/-- Observable equivalence of original and optimized withdraw success
paths. Both end at SSTORE with stack `[x]`, identical `toState`
(storage updated to `bal - x` at `sender`), and identical
`toMachineState`. PC differs by one tick (optimized saves a byte). -/
theorem withdrawPreCallBlock_observable_equiv
    (s : EVM.State) (pc0 : UInt256)
    (hLt : UInt256.lt (loadedBal s) (calldataX s) = (⟨0⟩ : UInt256)) :
    ∃ r_orig r_opt,
      runSeq Weth.withdrawPreCallBlock { s with stack := [], pc := pc0 } = .ok r_orig ∧
      runSeq withdrawPreCallBlockOpt    { s with stack := [], pc := pc0 } = .ok r_opt ∧
      r_orig.stack          = r_opt.stack ∧
      r_orig.toState        = r_opt.toState ∧
      r_orig.toMachineState = r_opt.toMachineState := by
  have h_orig := withdrawPreCallBlock_run s pc0 hLt
  have h_opt  := withdrawPreCallBlockOpt_run s pc0 hLt
  exact ⟨_, _, h_orig, h_opt, rfl, rfl, rfl⟩

/-- Halt-observability for the `POP STOP` → `STOP` swap: both runs
halt with identical `toState` and identical `toMachineState`
(`returnData` cleared). Stack and pc differ but are unobservable
post-halt — the call frame is gone, the caller sees neither.

This is the strict version of equivalence: a halted EVM frame's
externally-visible footprint is exactly `(toState, returnData)`,
since the stack/pc/memory belong to the dying frame. -/
theorem postCallSuccessTail_halt_equiv
    (s : EVM.State) (x : UInt256) (rest : Stack UInt256) (pc0 : UInt256) :
    ∃ r_orig r_opt,
      runSeq postCallSuccessTail    { s with stack := x :: rest, pc := pc0 } = .ok r_orig ∧
      runSeq postCallSuccessTailOpt { s with stack := x :: rest, pc := pc0 } = .ok r_opt ∧
      r_orig.toState        = r_opt.toState ∧
      r_orig.toMachineState = r_opt.toMachineState := by
  obtain ⟨h_orig, h_opt⟩ := postCallSuccessTail_equiv s x rest pc0
  exact ⟨_, _, h_orig, h_opt, rfl, rfl⟩

end EvmSmith.Weth
