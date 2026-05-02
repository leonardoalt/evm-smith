import EvmSmith.Framework
import EvmSmith.Demos.Add3.Program
import EvmSmith.Demos.Register.Program
import EvmSmith.Demos.Weth.Program

/-!
# Tests for the EvmSmith framework

These tests run at elaboration time via `#guard` — any failure aborts
`lake build`. No executable, no FFI linking required.

Run with `lake build EvmSmith.Demos.Tests`.
-/

namespace EvmSmith.Demos.Tests
open EvmYul EvmYul.EVM

private def ofN (n : Nat) : UInt256 := UInt256.ofNat n
private def natStack : Except EVM.ExecutionException EVM.State → Option (List Nat)
  | .ok s => some (s.stack.map UInt256.toNat)
  | .error _ => none

/-- Look up the operation at index `i` of a `Program`, dropping the
    optional immediate. Returns `Option (Operation .EVM)` so `.fst`-style
    dotted notation has its expected type pinned for `#guard`. -/
private def opAt (p : EvmSmith.Program) (i : Nat) : Option (Operation .EVM) :=
  p[i]?.map (·.fst)

/-! ## Arithmetic -/

#guard natStack (runOp .ADD (mkState [ofN 3, ofN 4])) == some [7]
#guard natStack (runOp .ADD (mkState [ofN 0, ofN 0])) == some [0]
#guard natStack (runOp .MUL (mkState [ofN 6, ofN 7])) == some [42]
#guard natStack (runOp .SUB (mkState [ofN 10, ofN 3])) == some [7]
#guard natStack (runOp .DIV (mkState [ofN 20, ofN 4])) == some [5]
#guard natStack (runOp .MOD (mkState [ofN 10, ofN 3])) == some [1]
#guard natStack (runOp .DIV (mkState [ofN 1, ofN 0])) == some [0]  -- EVM: div by zero = 0

/-! ## Comparison and bitwise -/

#guard natStack (runOp .LT  (mkState [ofN 1, ofN 2])) == some [1]
#guard natStack (runOp .LT  (mkState [ofN 2, ofN 1])) == some [0]
#guard natStack (runOp .GT  (mkState [ofN 2, ofN 1])) == some [1]
#guard natStack (runOp .EQ  (mkState [ofN 5, ofN 5])) == some [1]
#guard natStack (runOp .EQ  (mkState [ofN 5, ofN 6])) == some [0]
#guard natStack (runOp .ISZERO (mkState [ofN 0])) == some [1]
#guard natStack (runOp .ISZERO (mkState [ofN 42])) == some [0]
#guard natStack (runOp .AND (mkState [ofN 0b1100, ofN 0b1010])) == some [0b1000]
#guard natStack (runOp .OR  (mkState [ofN 0b1100, ofN 0b1010])) == some [0b1110]
#guard natStack (runOp .XOR (mkState [ofN 0b1100, ofN 0b1010])) == some [0b0110]

/-! ## Stack manipulation -/

#guard natStack (runOp .POP  (mkState [ofN 1, ofN 2, ofN 3])) == some [2, 3]
#guard natStack (runOp .DUP1 (mkState [ofN 7, ofN 8])) == some [7, 7, 8]
#guard natStack (runOp .DUP2 (mkState [ofN 7, ofN 8, ofN 9])) == some [8, 7, 8, 9]
#guard natStack (runOp .SWAP1 (mkState [ofN 1, ofN 2, ofN 3])) == some [2, 1, 3]
#guard natStack (runOp .SWAP2 (mkState [ofN 1, ofN 2, ofN 3, ofN 4])) == some [3, 2, 1, 4]

/-! ## PUSH -/

#guard natStack (runOp (.Push .PUSH0) (mkState [])) == some [0]
#guard natStack (runOp (.Push .PUSH1) (mkState []) (arg := some (ofN 255, 1))) == some [255]
#guard natStack (runOp (.Push .PUSH1) (mkState [ofN 9]) (arg := some (ofN 42, 1))) == some [42, 9]
#guard natStack (runOp (.Push .PUSH32) (mkState []) (arg := some (ofN 1000000, 32))) == some [1000000]

/-! ## Error paths -/

private def isUnderflow : Except EVM.ExecutionException EVM.State → Bool
  | .error .StackUnderflow => true
  | _ => false

#guard isUnderflow (runOp .ADD (mkState []))
#guard isUnderflow (runOp .ADD (mkState [ofN 1]))     -- ADD needs 2 items
#guard isUnderflow (runOp .MUL (mkState []))
#guard isUnderflow (runOp .ISZERO (mkState []))
#guard isUnderflow (runOp .POP (mkState []))
#guard isUnderflow (runOp .DUP1 (mkState []))
#guard isUnderflow (runOp .SWAP1 (mkState [ofN 1]))   -- SWAP1 needs 2 items

/-! ## PC increment -/

private def pcOf : Except EVM.ExecutionException EVM.State → Option Nat
  | .ok s => some s.pc.toNat
  | .error _ => none

#guard pcOf (runOp .ADD (mkState [ofN 1, ofN 2])) == some 1
#guard pcOf (runOp (.Push .PUSH1) (mkState []) (arg := some (ofN 5, 1))) == some 2    -- 1 + argWidth (1)
#guard pcOf (runOp (.Push .PUSH32) (mkState []) (arg := some (ofN 5, 32))) == some 33 -- 1 + argWidth (32)

/-! ## Parity: runOp and runOpFull agree on stack + pc -/

private def stackAndPc : Except EVM.ExecutionException EVM.State → Option (List Nat × Nat)
  | .ok s => some (s.stack.map UInt256.toNat, s.pc.toNat)
  | .error _ => none

#guard
  stackAndPc (runOp     .ADD (mkState [ofN 3, ofN 4]))
    == stackAndPc (runOpFull .ADD (mkState [ofN 3, ofN 4]))

#guard
  stackAndPc (runOp     .MUL (mkState [ofN 6, ofN 7]))
    == stackAndPc (runOpFull .MUL (mkState [ofN 6, ofN 7]))

#guard
  stackAndPc (runOp     .DUP1 (mkState [ofN 9]))
    == stackAndPc (runOpFull .DUP1 (mkState [ofN 9]))

/-! ## Structural checks on the `add3` program

End-to-end `#guard` on `add3` would need `UInt256.toByteArray`, which
calls the opaque FFI primitive `ffi.ByteArray.zeroes` — unavailable at
elaboration time. See `demoAdd3` in `EvmSmith/Demos/Demos.lean` for
end-to-end runs via `lake exe`. Here we only check structural invariants. -/

#guard EvmSmith.Add3.program.length == 13
#guard EvmSmith.Add3.compute.length == 8
-- Bytecode size: the Foundry test harness
-- (`EvmSmith/Demos/Add3/foundry/test/Add3.bytecode.hex`) is generated
-- from this definition by `lake exe add3-dump-bytecode`. If this guard
-- fires because the length changed, re-run the dumper.
#guard EvmSmith.Add3.bytecode.size == 19

/-! ## Structural checks on the `Register` program -/

#guard EvmSmith.Register.program.length == 14
#guard EvmSmith.Register.bytecode.size == 20

/-! ## Structural checks on the `Weth` program -/

#guard EvmSmith.Weth.depositBlock.length == 10
#guard EvmSmith.Weth.withdrawPreCallBlock.length == 16
#guard EvmSmith.Weth.bytecode.size == 86
#guard EvmSmith.Weth.depositSelector == UInt256.ofNat 0xd0e30db0
#guard EvmSmith.Weth.withdrawSelector == UInt256.ofNat 0x2e1a7d4d
#guard EvmSmith.Weth.depositLbl == UInt256.ofNat 32
#guard EvmSmith.Weth.withdrawLbl == UInt256.ofNat 42
#guard EvmSmith.Weth.revertLbl == UInt256.ofNat 80

/-! ### Weth bytecode byte-level invariants

These pin specific bytes at known PCs against the documented assembly
in `EvmSmith/Demos/Weth/Program.lean`. If any of these guards fires,
the Lean walks (`WethTrace_step_at_*`) almost certainly need updating
to match the new layout. -/

#guard EvmSmith.Weth.bytecode.get! 0  == 0x60   -- PUSH1 (selector load)
#guard EvmSmith.Weth.bytecode.get! 2  == 0x35   -- CALLDATALOAD
#guard EvmSmith.Weth.bytecode.get! 5  == 0x1c   -- SHR
#guard EvmSmith.Weth.bytecode.get! 12 == 0x14   -- EQ (deposit selector check)
#guard EvmSmith.Weth.bytecode.get! 16 == 0x57   -- JUMPI to depositLbl
#guard EvmSmith.Weth.bytecode.get! 22 == 0x14   -- EQ (withdraw selector check)
#guard EvmSmith.Weth.bytecode.get! 26 == 0x57   -- JUMPI to withdrawLbl
#guard EvmSmith.Weth.bytecode.get! 31 == 0xfd   -- REVERT (no selector match)
#guard EvmSmith.Weth.bytecode.get! 32 == 0x5b   -- JUMPDEST (deposit entry)
#guard EvmSmith.Weth.bytecode.get! 36 == 0x54   -- SLOAD (deposit: read balance)
#guard EvmSmith.Weth.bytecode.get! 38 == 0x01   -- ADD (deposit: balance + msg.value)
#guard EvmSmith.Weth.bytecode.get! 40 == 0x55   -- SSTORE (deposit: write balance)
#guard EvmSmith.Weth.bytecode.get! 41 == 0x00   -- STOP
#guard EvmSmith.Weth.bytecode.get! 42 == 0x5b   -- JUMPDEST (withdraw entry)
#guard EvmSmith.Weth.bytecode.get! 48 == 0x54   -- SLOAD (withdraw: read balance)
#guard EvmSmith.Weth.bytecode.get! 51 == 0x10   -- LT (balance < x check)
#guard EvmSmith.Weth.bytecode.get! 55 == 0x57   -- JUMPI to revertLbl
#guard EvmSmith.Weth.bytecode.get! 58 == 0x03   -- SUB (balance - x)
#guard EvmSmith.Weth.bytecode.get! 60 == 0x55   -- SSTORE (withdraw: write decremented)
#guard EvmSmith.Weth.bytecode.get! 72 == 0xf1   -- CALL
#guard EvmSmith.Weth.bytecode.get! 79 == 0x00   -- STOP (withdraw success)
#guard EvmSmith.Weth.bytecode.get! 80 == 0x5b   -- JUMPDEST (revert entry)
#guard EvmSmith.Weth.bytecode.get! 85 == 0xfd   -- REVERT

/-! ### Weth selector-byte invariants

The 4-byte function selectors as bytes (BE order) match
`keccak256("deposit()")[0..4]` and `keccak256("withdraw(uint256)")[0..4]`. -/

#guard EvmSmith.Weth.depositSelector.toNat == 0xd0e30db0
#guard EvmSmith.Weth.withdrawSelector.toNat == 0x2e1a7d4d
#guard EvmSmith.Weth.depositSelector ≠ EvmSmith.Weth.withdrawSelector

/-! ### Weth control-flow label invariants -/

#guard EvmSmith.Weth.depositLbl.toNat == 32
#guard EvmSmith.Weth.withdrawLbl.toNat == 42
#guard EvmSmith.Weth.revertLbl.toNat == 80
#guard EvmSmith.Weth.depositLbl < EvmSmith.Weth.withdrawLbl
#guard EvmSmith.Weth.withdrawLbl < EvmSmith.Weth.revertLbl
-- The dispatch at PC 13 / 23 pushes these as PUSH2 args; their toNat
-- must fit in 2 bytes (≤ 0xffff) for the encoding to be correct.
#guard EvmSmith.Weth.depositLbl.toNat ≤ 0xffff
#guard EvmSmith.Weth.withdrawLbl.toNat ≤ 0xffff
#guard EvmSmith.Weth.revertLbl.toNat ≤ 0xffff

/-! ### Weth program-list invariants

These pin per-block opcode layouts. Mismatches indicate the Lean walks
(`WethTrace_step_at_*`) and the on-chain bytecode have drifted. -/

#guard opAt EvmSmith.Weth.depositBlock 0 == some .JUMPDEST
#guard opAt EvmSmith.Weth.depositBlock 1 == some .POP
#guard opAt EvmSmith.Weth.depositBlock 2 == some .CALLER
#guard opAt EvmSmith.Weth.depositBlock 3 == some .DUP1
#guard opAt EvmSmith.Weth.depositBlock 4 == some .SLOAD
#guard opAt EvmSmith.Weth.depositBlock 5 == some .CALLVALUE
#guard opAt EvmSmith.Weth.depositBlock 6 == some .ADD
#guard opAt EvmSmith.Weth.depositBlock 7 == some .SWAP1
#guard opAt EvmSmith.Weth.depositBlock 8 == some .SSTORE
#guard opAt EvmSmith.Weth.depositBlock 9 == some .STOP

/-! ### Add3 program-list invariants -/

#guard opAt EvmSmith.Add3.program 0 == some (.Push .PUSH1)
#guard opAt EvmSmith.Add3.program 1 == some .CALLDATALOAD
#guard opAt EvmSmith.Add3.program 4 == some .ADD
#guard opAt EvmSmith.Add3.program 7 == some .ADD
#guard opAt EvmSmith.Add3.program 12 == some .RETURN

/-! ## More framework arithmetic — overflow & wrapping

EVM arithmetic is mod 2^256. These guards document the wrap behavior
and that it doesn't error. -/

#guard
  let max : UInt256 := UInt256.ofNat (UInt256.size - 1)
  natStack (runOp .ADD (mkState [max, ofN 1])) == some [0]   -- max + 1 wraps to 0

#guard
  natStack (runOp .SUB (mkState [ofN 0, ofN 1]))
    == some [UInt256.size - 1]                                -- 0 - 1 wraps to max

#guard
  let big : UInt256 := UInt256.ofNat (UInt256.size / 2 + 1)
  natStack (runOp .ADD (mkState [big, big]))
    == some [(2 * (UInt256.size / 2 + 1)) % UInt256.size]     -- 2·big mod 2^256

/-! ## More framework comparison — signed / unsigned -/

#guard natStack (runOp .GT (mkState [ofN 5, ofN 5])) == some [0]    -- not strict
#guard natStack (runOp .LT (mkState [ofN 5, ofN 5])) == some [0]    -- not strict
#guard natStack (runOp .EQ (mkState [ofN 0, ofN 0])) == some [1]
#guard natStack (runOp .ISZERO (mkState [ofN (UInt256.size - 1)])) == some [0]

/-! ## More stack manipulation — DUP/SWAP edge cases -/

#guard natStack (runOp .DUP3 (mkState [ofN 1, ofN 2, ofN 3])) == some [3, 1, 2, 3]
#guard natStack (runOp .DUP4 (mkState [ofN 1, ofN 2, ofN 3, ofN 4])) == some [4, 1, 2, 3, 4]
#guard natStack (runOp .DUP5 (mkState [ofN 1, ofN 2, ofN 3, ofN 4, ofN 5])) == some [5, 1, 2, 3, 4, 5]
#guard natStack (runOp .SWAP3 (mkState [ofN 1, ofN 2, ofN 3, ofN 4])) == some [4, 2, 3, 1]

/-! ## More error paths -/

#guard isUnderflow (runOp .DUP3 (mkState [ofN 1, ofN 2]))   -- DUP3 needs 3 items
#guard isUnderflow (runOp .DUP5 (mkState [ofN 1, ofN 2, ofN 3, ofN 4]))
#guard isUnderflow (runOp .SWAP3 (mkState [ofN 1, ofN 2, ofN 3]))
#guard isUnderflow (runOp .SUB (mkState [ofN 1]))
#guard isUnderflow (runOp .DIV (mkState [ofN 1]))
#guard isUnderflow (runOp .EQ  (mkState []))
#guard isUnderflow (runOp .LT  (mkState [ofN 1]))

/-! ## More PC increment checks — multi-byte PUSHes -/

#guard pcOf (runOp (.Push .PUSH2)  (mkState []) (arg := some (ofN 5, 2)))  == some 3
#guard pcOf (runOp (.Push .PUSH4)  (mkState []) (arg := some (ofN 5, 4)))  == some 5
#guard pcOf (runOp (.Push .PUSH16) (mkState []) (arg := some (ofN 5, 16))) == some 17

/-! ## More runOp/runOpFull parity -/

#guard
  stackAndPc (runOp     .SUB (mkState [ofN 10, ofN 3]))
    == stackAndPc (runOpFull .SUB (mkState [ofN 10, ofN 3]))
#guard
  stackAndPc (runOp     .ISZERO (mkState [ofN 0]))
    == stackAndPc (runOpFull .ISZERO (mkState [ofN 0]))
#guard
  stackAndPc (runOp     .DUP3 (mkState [ofN 1, ofN 2, ofN 3]))
    == stackAndPc (runOpFull .DUP3 (mkState [ofN 1, ofN 2, ofN 3]))
#guard
  stackAndPc (runOp     .SWAP1 (mkState [ofN 7, ofN 8, ofN 9]))
    == stackAndPc (runOpFull .SWAP1 (mkState [ofN 7, ofN 8, ofN 9]))

end EvmSmith.Demos.Tests
