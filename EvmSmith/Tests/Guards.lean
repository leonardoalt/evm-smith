import EvmSmith.Framework
import EvmSmith.Demos.Add3.Program
import EvmSmith.Demos.Register.Program
import EvmSmith.Demos.Weth.Program

/-!
# Tests for the EvmSmith framework

These tests run at elaboration time via `#guard` — any failure aborts
`lake build`. No executable, no FFI linking required.

Run with `lake build EvmSmith.Tests.Guards`.
-/

namespace EvmSmith.Tests
open EvmYul EvmYul.EVM

private def ofN (n : Nat) : UInt256 := UInt256.ofNat n
private def natStack : Except EVM.ExecutionException EVM.State → Option (List Nat)
  | .ok s => some (s.stack.map UInt256.toNat)
  | .error _ => none

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

end EvmSmith.Tests
