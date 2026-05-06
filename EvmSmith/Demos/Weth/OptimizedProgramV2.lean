import EvmSmith.Lemmas
import EvmSmith.Demos.Weth.OptimizedProgram

/-!
# V2-optimized Weth bytecode + per-block equivalence proofs

Layered on top of `OptimizedProgram.lean` (which made the PUSH0 swap).
This pass applies three runtime-gas optimizations whose savings are
observable in the EVM gas schedule.

## The three changes

1. **Deposit body: `CALLER` twice instead of `DUP1` + `SWAP1`.**
   `CALLER` is BASE (2 gas), `DUP1`/`SWAP1` are VERYLOW (3 gas each).
   Calling `CALLER` a second time when sender is needed again is
   cheaper than holding it on stack via `DUP1` and `SWAP1`-ing it
   under the new value before `SSTORE`.
   * V1: `… CALLER DUP1 SLOAD CALLVALUE ADD SWAP1 SSTORE …`
   * V2: `… CALLER     SLOAD CALLVALUE ADD CALLER SSTORE …`
   Saves 4 gas + 1 byte per deposit.

2. **Withdraw body: same trick** — drop `DUP1` after the first
   `CALLER`, replace the trailing `SWAP1` before the SSTORE with
   `CALLER`. `DUP3` becomes `DUP2` since `sender` no longer sits
   between `bal` and `x` on the stack.
   Saves 4 gas on success, 3 gas on insufficient-balance revert,
   and 1 byte.

3. **Drop the dead `POP` before `STOP`** on withdraw success.
   `POP` was clearing the leftover `x` (kept by `DUP5` for value).
   `STOP` halts the call frame regardless of stack contents — the
   `POP` is purely cosmetic.
   Saves 2 gas + 1 byte per successful withdraw.

## Bytecode size

77 → 74 bytes. Labels shift:
* `depositLblV2`   = 29 (unchanged)
* `withdrawLblV2`  = 38 (was 39)
* `revertLblV2`    = 70 (was 73)

## Equivalence proofs

Unlike the V1 PUSH0 round (where corresponding stacks matched
pointwise), the V2 changes give intermediate stacks that *differ*
between V1 and V2 (V1 holds `sender` on stack longer; V2 reloads via
`CALLER`). The end-of-block states still agree, so the proofs are
"both blocks produce the same observable post-state" — full state
equivalence modulo PC for deposit, full state modulo PC for the
withdraw success path (under a sufficient-balance hypothesis), and
state-modulo-stack for the post-CALL POP drop (where stacks at halt
genuinely differ but are unobservable post-frame).
-/

namespace EvmSmith.Weth
open EvmYul EvmYul.EVM EvmSmith

/-! ## Updated label values -/

/-- `depositLbl` unchanged from V1: deposit block still starts at PC 29. -/
def depositLblV2  : UInt256 := UInt256.ofNat 29

/-- `withdrawLbl` shifted from 39 to 38: deposit block is 1 byte
    shorter (DUP1 dropped). -/
def withdrawLblV2 : UInt256 := UInt256.ofNat 38

/-- `revertLbl` shifted from 73 to 70: deposit shorter by 1 + withdraw
    pre-CALL shorter by 1 + POP-drop saves 1 = 3 bytes total. -/
def revertLblV2   : UInt256 := UInt256.ofNat 70

/-! ## V2-optimized full bytecode (74 bytes) -/

/-- The V2-optimized WETH runtime bytecode. -/
def bytecodeV2 : ByteArray := ⟨#[
  -- Dispatch (PCs 0..28, unchanged from V1 except withdrawLbl immediate)
  0x5f,                            -- 0:    PUSH0
  0x35,                            -- 1:    CALLDATALOAD
  0x60, 0xe0,                      -- 2:    PUSH1 0xe0
  0x1c,                            -- 4:    SHR
  0x80,                            -- 5:    DUP1
  0x63, 0xd0, 0xe3, 0x0d, 0xb0,    -- 6:    PUSH4 depositSelector
  0x14,                            -- 11:   EQ
  0x61, 0x00, 0x1d,                -- 12:   PUSH2 depositLblV2 = 29
  0x57,                            -- 15:   JUMPI
  0x63, 0x2e, 0x1a, 0x7d, 0x4d,    -- 16:   PUSH4 withdrawSelector
  0x14,                            -- 21:   EQ
  0x61, 0x00, 0x26,                -- 22:   PUSH2 withdrawLblV2 = 38
  0x57,                            -- 25:   JUMPI
  0x5f, 0x5f, 0xfd,                -- 26:   PUSH0; PUSH0; REVERT
  -- Deposit block (PCs 29..37, was 29..38)
  0x5b,                            -- 29:   JUMPDEST
  0x50,                            -- 30:   POP
  0x33,                            -- 31:   CALLER
  0x54,                            -- 32:   SLOAD
  0x34, 0x01,                      -- 33:   CALLVALUE; ADD
  0x33,                            -- 35:   CALLER
  0x55,                            -- 36:   SSTORE
  0x00,                            -- 37:   STOP
  -- Withdraw block (PCs 38..69, was 39..72)
  0x5b,                            -- 38:   JUMPDEST
  0x60, 0x04, 0x35,                -- 39:   PUSH1 4; CALLDATALOAD
  0x33,                            -- 42:   CALLER
  0x54,                            -- 43:   SLOAD
  0x81, 0x81, 0x10,                -- 44:   DUP2; DUP2; LT
  0x61, 0x00, 0x46, 0x57,          -- 47:   PUSH2 revertLblV2 = 70; JUMPI
  0x81, 0x90, 0x03,                -- 51:   DUP2; SWAP1; SUB
  0x33, 0x55,                      -- 54:   CALLER; SSTORE
  0x5f, 0x5f,                      -- 56:   PUSH0; PUSH0
  0x5f, 0x5f,                      -- 58:   PUSH0; PUSH0
  0x84, 0x33, 0x5a,                -- 60:   DUP5; CALLER; GAS
  0xf1,                            -- 63:   CALL
  0x15,                            -- 64:   ISZERO
  0x61, 0x00, 0x46, 0x57,          -- 65:   PUSH2 revertLblV2; JUMPI
  0x00,                            -- 69:   STOP   (POP dropped!)
  -- Revert block (PCs 70..73, unchanged shape, just relocated)
  0x5b,                            -- 70:   JUMPDEST
  0x5f, 0x5f, 0xfd                 -- 71:   PUSH0; PUSH0; REVERT
]⟩

/-! ## Site E: Deposit block

V1's deposit block:
`[JUMPDEST, POP, CALLER, DUP1, SLOAD, CALLVALUE, ADD, SWAP1, SSTORE, STOP]`
holds `sender` on the stack across the SLOAD/ADD by `DUP1`-ing it and
then `SWAP1`-ing it under `bal+val` so SSTORE sees `[sender, bal+val]`.

V2 instead reloads `sender` via a second `CALLER` right before SSTORE.
Saves 4 gas (one VERYLOW removed, one VERYLOW→BASE swap) and 1 byte.

Both blocks halt at `STOP` with the same observable state: stack
restored to its pre-`POP` tail, storage at `sender` set to
`sload(s.toState, sender).2 + s.executionEnv.weiValue`, and the
machine state's `returnData` cleared. -/

/-- V2-optimized deposit block. -/
def depositBlockV2 : EvmSmith.Program :=
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

/-- Shared post-state of the V1 and V2 deposit blocks. Both produce
this state from an entry whose stack tops a stale `top` element
(the dispatch-leftover selector). PC differs (V1 walks 10 opcodes,
V2 walks 9). -/
private abbrev depositPost
    (s : EVM.State) (rest : Stack UInt256) (pcEnd : UInt256) : EVM.State :=
  { s with
      stack := rest
      pc := pcEnd
      toState := EvmYul.State.sstore (sloadedState s) (senderU s)
                   (s.executionEnv.weiValue + loadedBal s)
      toMachineState := s.toMachineState.setReturnData .empty }

theorem depositBlock_v2_equiv
    (s : EVM.State) (top : UInt256) (rest : Stack UInt256) (pc0 : UInt256) :
    runSeq Weth.depositBlock { s with stack := top :: rest, pc := pc0 }
      = .ok (depositPost s rest
              (pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1)) ∧
    runSeq depositBlockV2 { s with stack := top :: rest, pc := pc0 }
      = .ok (depositPost s rest
              (pc0 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1)) := by
  refine ⟨?_, ?_⟩
  · -- V1: 10 opcodes (extra DUP1 + SWAP1)
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
  · -- V2: 9 opcodes (no DUP1, SWAP1→CALLER)
    show runSeq depositBlockV2 _ = .ok _
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
      unfold depositBlockV2
      rw [runSeq_cons_ok _ _ _ _ _ h1, runSeq_cons_ok _ _ _ _ _ h2,
          runSeq_cons_ok _ _ _ _ _ h3, runSeq_cons_ok _ _ _ _ _ h4,
          runSeq_cons_ok _ _ _ _ _ h5, runSeq_cons_ok _ _ _ _ _ h6,
          runSeq_cons_ok _ _ _ _ _ h7, runSeq_cons_ok _ _ _ _ _ h8,
          runSeq_cons_ok _ _ _ _ _ h9]
      unfold runSeq

/-- Observable equivalence of V1 and V2 deposit blocks. Both halt
with identical `toState`, `toMachineState`, and `stack`; only PC
differs (V2 saves 1 byte = 1 PC tick). -/
theorem depositBlock_v2_observable_equiv
    (s : EVM.State) (top : UInt256) (rest : Stack UInt256) (pc0 : UInt256) :
    ∃ rV1 rV2,
      runSeq Weth.depositBlock { s with stack := top :: rest, pc := pc0 } = .ok rV1 ∧
      runSeq depositBlockV2     { s with stack := top :: rest, pc := pc0 } = .ok rV2 ∧
      rV1.stack          = rV2.stack ∧
      rV1.toState        = rV2.toState ∧
      rV1.toMachineState = rV2.toMachineState := by
  obtain ⟨h1, h2⟩ := depositBlock_v2_equiv s top rest pc0
  exact ⟨_, _, h1, h2, rfl, rfl, rfl⟩

/-! ## Site G: Withdraw success path (JUMPDEST → SSTORE)

V1's withdraw pre-CALL block (`Weth.withdrawPreCallBlock`):
`[JUMPDEST, PUSH1 4, CALLDATALOAD, CALLER, DUP1, SLOAD,`
`  DUP3, DUP2, LT, PUSH2 revertLbl, JUMPI,`
`  DUP3, SWAP1, SUB, SWAP1, SSTORE]` — 16 ops.

V2's `withdrawPreCallBlockV2`:
`[JUMPDEST, PUSH1 4, CALLDATALOAD, CALLER, SLOAD,`
`  DUP2, DUP2, LT, PUSH2 revertLblV2, JUMPI,`
`  DUP2, SWAP1, SUB, CALLER, SSTORE]` — 15 ops.

Both produce the same observable end state on the success path: stack
ends `[x]` (the calldata-loaded withdrawal amount), storage at
`sender` is updated to `bal - x`. Intermediate stacks differ — V1 holds
`sender` on stack across the LT/JUMPI; V2 reloads `sender` via the
trailing `CALLER`.

The proof is conditioned on a *sufficient-balance* hypothesis: the
LT result is zero, so the JUMPI falls through to the success
continuation. The insufficient-balance branch is dispatched via
`Weth.revertBlock` (already proved equivalent in `OptimizedProgram`)
and reaches `revertLbl` with the right stack for `PUSH0; PUSH0; REVERT`. -/

/-- V2-optimized withdraw pre-CALL block (the success path body). -/
def withdrawPreCallBlockV2 : EvmSmith.Program :=
  [ (.JUMPDEST,     none)
  , (.Push .PUSH1,  some (UInt256.ofNat 4, 1))
  , (.CALLDATALOAD, none)
  , (.CALLER,       none)
  , (.SLOAD,        none)
  , (.DUP2,         none)
  , (.DUP2,         none)
  , (.LT,           none)
  , (.Push .PUSH2,  some (revertLblV2, 2))
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
`sender` decremented by `x`. PC differs by 1 (V1 has the extra
`DUP1` byte, V2's `CALLER`-reload doesn't compensate for it
byte-wise). -/
private abbrev withdrawPost (s : EVM.State) (pcEnd : UInt256) : EVM.State :=
  { s with
      stack := calldataX s :: []
      pc := pcEnd
      toState := EvmYul.State.sstore (sloadedState s) (senderU s)
                   (loadedBal s - calldataX s) }

/-- V1's withdraw pre-CALL success path lands at the shared post-state.

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

/-- V2's `withdrawPreCallBlockV2` lands at the shared post-state
under the same sufficient-balance hypothesis. PC advance: 18 ticks
(one fewer than V1, reflecting the dropped `DUP1` byte). -/
theorem withdrawPreCallBlockV2_run
    (s : EVM.State) (pc0 : UInt256)
    (hLt : UInt256.lt (loadedBal s) (calldataX s) = (⟨0⟩ : UInt256)) :
    runSeq withdrawPreCallBlockV2 { s with stack := [], pc := pc0 }
      = .ok (withdrawPost s
              (pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
               UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1)) := by
  show runSeq withdrawPreCallBlockV2 _ = .ok _
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
  -- 5. SLOAD (V2 skips DUP1)
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
  -- 9. PUSH2 revertLblV2
  have h9 :
    runOp (.Push .PUSH2)
      { s with stack := (⟨0⟩ : UInt256) :: loadedBal s :: calldataX s :: []
               pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                     UInt256.ofNat 1 + UInt256.ofNat 1
               toState := sloadedState s }
      (some (revertLblV2, 2))
    = .ok { s with stack := revertLblV2 :: (⟨0⟩ : UInt256) :: loadedBal s ::
                            calldataX s :: []
                   pc := pc0 + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
                         UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 3
                   toState := sloadedState s } := by
    unfold runOp EvmYul.step; rfl
  -- 10. JUMPI not taken
  have h10 :
    runOp .JUMPI
      { s with stack := revertLblV2 :: (⟨0⟩ : UInt256) :: loadedBal s ::
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
  -- 14. CALLER (V2's reload — replaces the V1 SWAP1)
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
    unfold withdrawPreCallBlockV2
    rw [runSeq_cons_ok _ _ _ _ _ h1, runSeq_cons_ok _ _ _ _ _ h2,
        runSeq_cons_ok _ _ _ _ _ h3, runSeq_cons_ok _ _ _ _ _ h4,
        runSeq_cons_ok _ _ _ _ _ h5, runSeq_cons_ok _ _ _ _ _ h6,
        runSeq_cons_ok _ _ _ _ _ h7, runSeq_cons_ok _ _ _ _ _ h8,
        runSeq_cons_ok _ _ _ _ _ h9, runSeq_cons_ok _ _ _ _ _ h10,
        runSeq_cons_ok _ _ _ _ _ h11, runSeq_cons_ok _ _ _ _ _ h12,
        runSeq_cons_ok _ _ _ _ _ h13, runSeq_cons_ok _ _ _ _ _ h14,
        runSeq_cons_ok _ _ _ _ _ h15]
    unfold runSeq

/-- Observable equivalence of V1 and V2 withdraw success paths. Both
end at SSTORE with stack `[x]`, identical `toState` (storage updated
to `bal - x` at `sender`), and identical `toMachineState`. PC differs
by one tick (V2 saves a byte). -/
theorem withdrawPreCallBlock_v2_observable_equiv
    (s : EVM.State) (pc0 : UInt256)
    (hLt : UInt256.lt (loadedBal s) (calldataX s) = (⟨0⟩ : UInt256)) :
    ∃ rV1 rV2,
      runSeq Weth.withdrawPreCallBlock { s with stack := [], pc := pc0 } = .ok rV1 ∧
      runSeq withdrawPreCallBlockV2     { s with stack := [], pc := pc0 } = .ok rV2 ∧
      rV1.stack          = rV2.stack ∧
      rV1.toState        = rV2.toState ∧
      rV1.toMachineState = rV2.toMachineState := by
  have hV1 := withdrawPreCallBlock_run s pc0 hLt
  have hV2 := withdrawPreCallBlockV2_run s pc0 hLt
  exact ⟨_, _, hV1, hV2, rfl, rfl, rfl⟩

/-! ## Site H: Drop the dead `POP` before `STOP` on withdraw success

After `CALL` succeeds and the post-CALL `ISZERO; PUSH2 lbl; JUMPI`
falls through, the stack has the leftover `x` (the value DUP5'd into
the CALL args). V1 dispatches a `POP; STOP` cleanup to drop it; V2
just `STOP`s.

Both halt with the same `toState` (no further mutation between
fallthrough and halt) and `toMachineState.returnData = ∅`. They
*differ* in stack at halt (V1 = `rest`, V2 = `x :: rest`), but the
stack is unobservable beyond the call frame: it's discarded on halt.
-/

/-- V1 success-path tail. -/
def postCallSuccessTail : EvmSmith.Program :=
  [ (.POP,  none)
  , (.STOP, none) ]

/-- V2 success-path tail (POP dropped). -/
def postCallSuccessTailV2 : EvmSmith.Program :=
  [ (.STOP, none) ]

theorem postCallSuccessTail_v2_equiv
    (s : EVM.State) (x : UInt256) (rest : Stack UInt256) (pc0 : UInt256) :
    runSeq postCallSuccessTail { s with stack := x :: rest, pc := pc0 }
      = .ok { s with
                stack := rest
                pc := pc0 + UInt256.ofNat 1
                toMachineState := s.toMachineState.setReturnData .empty } ∧
    runSeq postCallSuccessTailV2 { s with stack := x :: rest, pc := pc0 }
      = .ok { s with
                stack := x :: rest
                pc := pc0
                toMachineState := s.toMachineState.setReturnData .empty } := by
  refine ⟨?_, ?_⟩
  · -- V1: POP then STOP
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
  · -- V2: just STOP
    show runSeq postCallSuccessTailV2 _ = .ok _
    have h1 : runOp .STOP { s with stack := x :: rest, pc := pc0 }
            = .ok { s with stack := x :: rest, pc := pc0
                           toMachineState := s.toMachineState.setReturnData .empty } := by
      unfold runOp EvmYul.step; rfl
    conv_lhs =>
      unfold postCallSuccessTailV2
      rw [runSeq_cons_ok _ _ _ _ _ h1]
      unfold runSeq

/-- Halt-observability for the `POP STOP` → `STOP` swap: both runs
halt with identical `toState` and identical `toMachineState`
(`returnData` cleared). Stack and pc differ but are unobservable
post-halt — the call frame is gone, the caller sees neither.

This is the strict version of equivalence: a halted EVM frame's
externally-visible footprint is exactly `(toState, returnData)`,
since the stack/pc/memory belong to the dying frame. -/
theorem postCallSuccessTail_v2_halt_equiv
    (s : EVM.State) (x : UInt256) (rest : Stack UInt256) (pc0 : UInt256) :
    ∃ rV1 rV2,
      runSeq postCallSuccessTail   { s with stack := x :: rest, pc := pc0 } = .ok rV1 ∧
      runSeq postCallSuccessTailV2 { s with stack := x :: rest, pc := pc0 } = .ok rV2 ∧
      rV1.toState        = rV2.toState ∧
      rV1.toMachineState = rV2.toMachineState := by
  obtain ⟨h1, h2⟩ := postCallSuccessTail_v2_equiv s x rest pc0
  exact ⟨_, _, h1, h2, rfl, rfl⟩

end EvmSmith.Weth
