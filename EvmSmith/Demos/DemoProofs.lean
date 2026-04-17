import EvmSmith.Framework

/-!
# Demo proofs — safety properties of single opcodes

Five small theorems that show what "prove your bytecode safe" looks like
at the single-opcode level. They're the template for program-level proofs
like the one in `EvmSmith/Demos/Add3/Proofs.lean`.

1. `add_underflow` — ADD on an empty stack is a `StackUnderflow` error.
2. `add_spec` — ADD on `[a, b, rest]` yields a post-stack `[a+b, rest]`.
3. `add_pc` — ADD increments the program counter by 1.
4. `uint256_add_comm` — `a + b = b + a` over `UInt256`.
5. `push_push_add_peephole` — a constant-folding optimizer is sound:
   `PUSH32 b ; PUSH32 a ; ADD` and `PUSH32 (a+b)` leave the same stack.
-/

namespace EvmSmith
open EvmYul EvmYul.EVM

/-! ## 1. Error path -/

theorem add_underflow : runOp .ADD (mkState []) = .error .StackUnderflow := by
  unfold runOp EvmYul.step mkState
  rfl

/-! ## 2. Functional correctness of ADD -/

theorem add_spec (a b : UInt256) (rest : Stack UInt256) :
    (runOp .ADD (mkState (a :: b :: rest))).map (·.stack)
      = .ok ((a + b) :: rest) := by
  unfold runOp EvmYul.step mkState
  rfl

/-! ## 3. PC increment -/

theorem add_pc (a b : UInt256) (rest : Stack UInt256) :
    (runOp .ADD (mkState (a :: b :: rest))).map (·.pc)
      = .ok (UInt256.ofNat 1) := by
  unfold runOp EvmYul.step mkState
  rfl

/-! ## 4. Commutativity lemma on UInt256 -/

lemma uint256_add_comm (a b : UInt256) : a + b = b + a := by
  show UInt256.add a b = UInt256.add b a
  unfold UInt256.add
  congr 1
  exact add_comm _ _

/-! ## 5. Peephole-optimization safety

`PUSH32 b ; PUSH32 a ; ADD` and `PUSH32 (a+b)` leave the same stack top on
`rest`. This is the literal soundness statement of a constant-folding
`push; push; add → push sum` optimizer pass. -/

theorem push_push_add_peephole
    (a b : UInt256) (rest : Stack UInt256) :
    (do
      let s1 ← runOp (.Push .PUSH32) (mkState rest) (some (b, 32))
      let s2 ← runOp (.Push .PUSH32) s1             (some (a, 32))
      let s3 ← runOp .ADD s2
      pure s3.stack
    : Except EVM.ExecutionException (Stack UInt256))
    =
    (do
      let t1 ← runOp (.Push .PUSH32) (mkState rest) (some (a + b, 32))
      pure t1.stack
    : Except EVM.ExecutionException (Stack UInt256)) := by
  unfold runOp EvmYul.step mkState
  rfl

end EvmSmith
