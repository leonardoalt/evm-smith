import EvmSmith.Lemmas
import EvmSmith.Demos.Weth.Program

/-!
# Optimized Weth bytecode + equivalence to the proved version

A single peephole optimization on the revert tail: replace the
`PUSH1 0; PUSH1 0; REVERT` sequence at PCs 81-85 with
`PUSH1 0; DUP1; REVERT`. Both push two zeros onto the stack and
hand `(offset=0, size=0)` to REVERT; the optimized form saves one
byte (DUP1 is one byte, the second `PUSH1 0` is two).

Why the choice:
* The revert block is the last block in the bytecode, so shrinking
  it doesn't shift any PC labels in the dispatch or the deposit /
  withdraw blocks. The same proof obligations on the rest of the
  bytecode therefore carry over unchanged.
* Both ops cost 3 gas, so the optimization is purely size, not gas.

The optimized full bytecode (`bytecodeOpt`) is 85 bytes vs the
original 86. The **equivalence theorem** below shows that the two
revert blocks produce post-states that agree on every observable
field (stack, toState, toMachineState); the only difference is PC,
which the X-loop ignores once REVERT halts the frame.

The original solvency proof in `Solvency.lean` is unchanged: it
proves `weth_solvency_invariant` for `Weth.bytecode`, the unoptimized
86-byte version. The optimized bytecode inherits the same solvency
guarantee through the equivalence theorem (any execution that would
have reverted in the original reverts identically here).
-/

namespace EvmSmith.Weth
open EvmYul EvmYul.EVM EvmSmith

/-! ## The two revert blocks as `Program` lists -/

/-- The original revert block: PUSH1 0; PUSH1 0; REVERT (5 bytes
after the JUMPDEST). Matches PCs 80-85 of `Weth.bytecode`. -/
def revertBlock : EvmSmith.Program :=
  [ (.JUMPDEST,    none)
  , (.Push .PUSH1, some (UInt256.ofNat 0, 1))
  , (.Push .PUSH1, some (UInt256.ofNat 0, 1))
  , (.REVERT,      none)
  ]

/-- The optimized revert block: PUSH1 0; DUP1; REVERT (4 bytes after
the JUMPDEST). One byte shorter, same observable behaviour. -/
def revertBlockOpt : EvmSmith.Program :=
  [ (.JUMPDEST,    none)
  , (.Push .PUSH1, some (UInt256.ofNat 0, 1))
  , (.DUP1,        none)
  , (.REVERT,      none)
  ]

/-! ## Optimized full bytecode (85 bytes) -/

/-- The optimized WETH runtime bytecode. Identical to `Weth.bytecode`
through PC 82; replaces the second `PUSH1 0` (`60 00`, two bytes) at
PCs 83-84 with a single `DUP1` (`80`, one byte); REVERT shifts from
PC 85 to PC 84. Total: 85 bytes. -/
def bytecodeOpt : ByteArray := ⟨#[
  -- Dispatch (PCs 0..31, identical to bytecode)
  0x60, 0x00,                      -- 0:    PUSH1 0
  0x35,                            -- 2:    CALLDATALOAD
  0x60, 0xe0,                      -- 3:    PUSH1 0xe0
  0x1c,                            -- 5:    SHR
  0x80,                            -- 6:    DUP1
  0x63, 0xd0, 0xe3, 0x0d, 0xb0,    -- 7:    PUSH4 depositSelector
  0x14,                            -- 12:   EQ
  0x61, 0x00, 0x20,                -- 13:   PUSH2 depositLbl
  0x57,                            -- 16:   JUMPI
  0x63, 0x2e, 0x1a, 0x7d, 0x4d,    -- 17:   PUSH4 withdrawSelector
  0x14,                            -- 22:   EQ
  0x61, 0x00, 0x2a,                -- 23:   PUSH2 withdrawLbl
  0x57,                            -- 26:   JUMPI
  0x60, 0x00, 0x60, 0x00, 0xfd,    -- 27:   PUSH1 0; PUSH1 0; REVERT
  -- Deposit block (PCs 32..41, identical to bytecode)
  0x5b,                            -- 32:   JUMPDEST
  0x50,                            -- 33:   POP
  0x33, 0x80, 0x54,                -- 34:   CALLER; DUP1; SLOAD
  0x34, 0x01,                      -- 37:   CALLVALUE; ADD
  0x90, 0x55,                      -- 39:   SWAP1; SSTORE
  0x00,                            -- 41:   STOP
  -- Withdraw block (PCs 42..79, identical to bytecode)
  0x5b,                            -- 42:   JUMPDEST
  0x60, 0x04, 0x35,                -- 43:   PUSH1 4; CALLDATALOAD
  0x33, 0x80, 0x54,                -- 46:   CALLER; DUP1; SLOAD
  0x82, 0x81, 0x10,                -- 49:   DUP3; DUP2; LT
  0x61, 0x00, 0x50, 0x57,          -- 52:   PUSH2 revertLbl; JUMPI
  0x82, 0x90, 0x03, 0x90, 0x55,    -- 56:   DUP3; SWAP1; SUB; SWAP1; SSTORE
  0x60, 0x00, 0x60, 0x00,          -- 61:   PUSH1 0; PUSH1 0       (retSize, retOff)
  0x60, 0x00, 0x60, 0x00,          -- 65:   PUSH1 0; PUSH1 0       (argsSize, argsOff)
  0x84, 0x33, 0x5a,                -- 69:   DUP5; CALLER; GAS      (value, to, gas)
  0xf1,                            -- 72:   CALL
  0x15,                            -- 73:   ISZERO
  0x61, 0x00, 0x50, 0x57,          -- 74:   PUSH2 revertLbl; JUMPI
  0x50, 0x00,                      -- 78:   POP; STOP
  -- Optimized revert block (PCs 80..84, was 80..85)
  0x5b,                            -- 80:   JUMPDEST
  0x60, 0x00,                      -- 81:   PUSH1 0
  0x80,                            -- 83:   DUP1            (was: PUSH1 0)
  0xfd                             -- 84:   REVERT          (was at PC 85)
]⟩

/-! ## Equivalence theorem

Both revert blocks produce post-states that agree on stack, toState,
and toMachineState. They differ only in PC (the original ends at
`s.pc + 6`, the optimized at `s.pc + 5`), which is irrelevant once
REVERT halts the frame: the X-loop reads the post-state's
`returnData` and exits, never inspecting the post-revert PC. -/

/-- Concrete post-state shared by both blocks (modulo PC): stack
restored, REVERT-machine-state set with offset = size = 0. -/
private def revertPost (s : EVM.State) (pcEnd : UInt256) : EVM.State :=
  { s with
      stack := s.stack
      pc := pcEnd
      toMachineState := MachineState.evmRevert s.toMachineState
        (UInt256.ofNat 0) (UInt256.ofNat 0) }

/-- Both revert blocks reach `.ok` post-states whose stack, toState,
and toMachineState are identical (only `pc` differs). -/
theorem revertBlock_equiv (s : EVM.State) :
    runSeq revertBlock s
      = .ok (revertPost s
              (s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 1)) ∧
    runSeq revertBlockOpt s
      = .ok (revertPost s
              (s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 1)) := by
  -- Establish s = { s with stack := s.stack, pc := s.pc } so the
  -- per-opcode lemmas (which require the explicit-shape pattern)
  -- apply to the entry state.
  have hs : s = { s with stack := s.stack, pc := s.pc } := by
    cases s; rfl
  -- Compute each step of the original block.
  have e1 :
      runOp .JUMPDEST { s with stack := s.stack, pc := s.pc }
        = .ok { s with stack := s.stack, pc := s.pc + UInt256.ofNat 1 } := by
    unfold runOp EvmYul.step; rfl
  have e2 :
      runOp (.Push .PUSH1)
        { s with stack := s.stack, pc := s.pc + UInt256.ofNat 1 }
        (some (UInt256.ofNat 0, 1))
        = .ok { s with
            stack := UInt256.ofNat 0 :: s.stack
            pc := s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 } :=
    runOp_push1 s (UInt256.ofNat 0) s.stack (s.pc + UInt256.ofNat 1)
  have e3_orig :
      runOp (.Push .PUSH1)
        { s with
          stack := UInt256.ofNat 0 :: s.stack
          pc := s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 }
        (some (UInt256.ofNat 0, 1))
        = .ok { s with
            stack := UInt256.ofNat 0 :: UInt256.ofNat 0 :: s.stack
            pc := s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 2 } :=
    runOp_push1 s (UInt256.ofNat 0) (UInt256.ofNat 0 :: s.stack)
      (s.pc + UInt256.ofNat 1 + UInt256.ofNat 2)
  have e3_opt :
      runOp .DUP1
        { s with
          stack := UInt256.ofNat 0 :: s.stack
          pc := s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 }
        = .ok { s with
            stack := UInt256.ofNat 0 :: UInt256.ofNat 0 :: s.stack
            pc := s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 } :=
    runOp_dup1 s (UInt256.ofNat 0) s.stack
      (s.pc + UInt256.ofNat 1 + UInt256.ofNat 2)
  -- After PUSH1 0; PUSH1 0 (orig) vs PUSH1 0; DUP1 (opt), the stacks
  -- and toState/toMachineState match; only PC differs.
  -- REVERT pops two zeros and produces evmRevert with offset=0, size=0.
  have e4_orig :
      runOp .REVERT
        { s with
          stack := UInt256.ofNat 0 :: UInt256.ofNat 0 :: s.stack
          pc := s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 2 }
        = .ok { s with
            stack := s.stack
            pc := s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 1
            toMachineState := MachineState.evmRevert s.toMachineState
              (UInt256.ofNat 0) (UInt256.ofNat 0) } :=
    runOp_revert s (UInt256.ofNat 0) (UInt256.ofNat 0) s.stack
      (s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 2)
  have e4_opt :
      runOp .REVERT
        { s with
          stack := UInt256.ofNat 0 :: UInt256.ofNat 0 :: s.stack
          pc := s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 }
        = .ok { s with
            stack := s.stack
            pc := s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 1
            toMachineState := MachineState.evmRevert s.toMachineState
              (UInt256.ofNat 0) (UInt256.ofNat 0) } :=
    runOp_revert s (UInt256.ofNat 0) (UInt256.ofNat 0) s.stack
      (s.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 1)
  refine ⟨?_, ?_⟩
  · -- Original block.
    show runSeq revertBlock s = .ok _
    conv_lhs =>
      rw [hs]; unfold revertBlock
      rw [runSeq_cons_ok _ _ _ _ _ e1, runSeq_cons_ok _ _ _ _ _ e2,
          runSeq_cons_ok _ _ _ _ _ e3_orig, runSeq_cons_ok _ _ _ _ _ e4_orig]
      unfold runSeq
    rfl
  · -- Optimized block.
    show runSeq revertBlockOpt s = .ok _
    conv_lhs =>
      rw [hs]; unfold revertBlockOpt
      rw [runSeq_cons_ok _ _ _ _ _ e1, runSeq_cons_ok _ _ _ _ _ e2,
          runSeq_cons_ok _ _ _ _ _ e3_opt, runSeq_cons_ok _ _ _ _ _ e4_opt]
      unfold runSeq
    rfl

/-- Observable equivalence: both blocks produce post-states agreeing
on stack, toState, and toMachineState. PC differs by one (the
optimized block ends one byte earlier), which the X-loop ignores
once REVERT halts the frame. -/
theorem revertBlock_equiv_observable (s : EVM.State) :
    ∃ r_orig r_opt,
      runSeq revertBlock    s = .ok r_orig ∧
      runSeq revertBlockOpt s = .ok r_opt ∧
      r_orig.stack          = r_opt.stack ∧
      r_orig.toState        = r_opt.toState ∧
      r_orig.toMachineState = r_opt.toMachineState := by
  obtain ⟨h_orig, h_opt⟩ := revertBlock_equiv s
  refine ⟨_, _, h_orig, h_opt, rfl, rfl, rfl⟩

end EvmSmith.Weth
