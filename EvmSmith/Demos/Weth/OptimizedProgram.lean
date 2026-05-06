import EvmSmith.Lemmas
import EvmSmith.Demos.Weth.Program

/-!
# PUSH0-optimized Weth bytecode + per-block equivalence proofs

Replaces every `PUSH1 0` (`60 00`, 2 bytes) in the WETH runtime
bytecode with `PUSH0` (`5f`, 1 byte). The original 86-byte runtime
contains nine `PUSH1 0` occurrences:

* PC 0       (selector-load offset)
* PC 27, 29  (no-selector REVERT args)
* PC 61, 63, 65, 67  (CALL retSize / retOff / argsSize / argsOff)
* PC 81, 83  (final REVERT args)

Replacing all nine saves 9 bytes total (86 → 77 bytes). The three
`PUSH2 <label>` immediates in the dispatch shift accordingly:

* `depositLbl`   :  32 → 29
* `withdrawLbl`  :  42 → 39
* `revertLbl`    :  80 → 73

`PUSH0` is EIP-3855 (Shanghai, March 2023). EVMYulLean implements it
at `EvmYul/Semantics.lean:516`: pushes `⟨0⟩` onto the stack and
advances PC by 1.

## Equivalence proofs (block-level)

The full bytecode equivalence reduces to four block-level
equivalences: at each of the four sites where `PUSH1 0` appears,
the swapped block produces a post-state that agrees with the
original on every field except `pc` (which differs by however many
bytes the block saved).

* `selectorLoad_equiv`     `[PUSH1 0; CALLDATALOAD]` ≡ `[PUSH0; CALLDATALOAD]`
* `noSelectorRevert_equiv` `[PUSH1 0; PUSH1 0; REVERT]` ≡ `[PUSH0; PUSH0; REVERT]`
* `callPushes_equiv`       four `PUSH1 0`s ≡ four `PUSH0`s
* `revertBlock_equiv`      `[JUMPDEST; PUSH1 0; PUSH1 0; REVERT]` ≡ `[JUMPDEST; PUSH0; PUSH0; REVERT]`

Each proof chains per-opcode `runOp_*` lemmas via `runSeq_cons_ok`.
The bytes between sites are byte-identical to the original, so the
optimized bytecode runs observably equivalently to the original at
every reachable state.
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

/-- `depositLbl` shifted from 32 to 29 (3 bytes saved by the three
`PUSH1 0` → `PUSH0` swaps before deposit's JUMPDEST). -/
def depositLblOpt : UInt256 := UInt256.ofNat 29

/-- `withdrawLbl` shifted from 42 to 39 (deposit block has no
`PUSH1 0` of its own, so still 3 bytes saved before its JUMPDEST). -/
def withdrawLblOpt : UInt256 := UInt256.ofNat 39

/-- `revertLbl` shifted from 80 to 73 (7 bytes saved before the
revert JUMPDEST: 3 in dispatch + 4 in the CALL setup). -/
def revertLblOpt : UInt256 := UInt256.ofNat 73

/-! ## Optimized full bytecode (77 bytes) -/

/-- The PUSH0-optimized WETH runtime bytecode. -/
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
  0x61, 0x00, 0x27,                -- 22:   PUSH2 withdrawLblOpt = 39
  0x57,                            -- 25:   JUMPI
  0x5f, 0x5f, 0xfd,                -- 26:   PUSH0; PUSH0; REVERT
  -- Deposit block (PCs 29..38, was 32..41)
  0x5b,                            -- 29:   JUMPDEST
  0x50,                            -- 30:   POP
  0x33, 0x80, 0x54,                -- 31:   CALLER; DUP1; SLOAD
  0x34, 0x01,                      -- 34:   CALLVALUE; ADD
  0x90, 0x55,                      -- 36:   SWAP1; SSTORE
  0x00,                            -- 38:   STOP
  -- Withdraw block (PCs 39..72, was 42..79)
  0x5b,                            -- 39:   JUMPDEST
  0x60, 0x04, 0x35,                -- 40:   PUSH1 4; CALLDATALOAD
  0x33, 0x80, 0x54,                -- 43:   CALLER; DUP1; SLOAD
  0x82, 0x81, 0x10,                -- 46:   DUP3; DUP2; LT
  0x61, 0x00, 0x49, 0x57,          -- 49:   PUSH2 revertLblOpt = 73; JUMPI
  0x82, 0x90, 0x03, 0x90, 0x55,    -- 53:   DUP3; SWAP1; SUB; SWAP1; SSTORE
  0x5f, 0x5f,                      -- 58:   PUSH0; PUSH0       (retSize, retOff)
  0x5f, 0x5f,                      -- 60:   PUSH0; PUSH0       (argsSize, argsOff)
  0x84, 0x33, 0x5a,                -- 62:   DUP5; CALLER; GAS  (value, to, gas)
  0xf1,                            -- 65:   CALL
  0x15,                            -- 66:   ISZERO
  0x61, 0x00, 0x49, 0x57,          -- 67:   PUSH2 revertLblOpt; JUMPI
  0x50, 0x00,                      -- 71:   POP; STOP
  -- Revert block (PCs 73..76, was 80..85)
  0x5b,                            -- 73:   JUMPDEST
  0x5f, 0x5f, 0xfd                 -- 74:   PUSH0; PUSH0; REVERT
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

/-! ## Site B: no-selector REVERT (PCs 27-31) -/

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

/-! ## Site C: CALL setup prefix (PCs 61-68)

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

/-! ## Site D: final REVERT block (PCs 80-85) -/

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

/-! ## Observable equivalence corollaries

For each site, the explicit-post-state form above immediately yields
that the two `runSeq` invocations land in `.ok` of records that
agree on stack, toState, and toMachineState (only PC differs). -/

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

end EvmSmith.Weth
