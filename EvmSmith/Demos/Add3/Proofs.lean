import EvmSmith.Lemmas
import EvmSmith.Demos.Add3.Program

/-!
# Correctness of the `add3` program

We prove that the compute prefix of `add3` (the 8 opcodes that read three
words from calldata and sum them) leaves `a + b + c` on top of the stack,
for *any* initial state whose `CALLDATALOAD` at offsets 0, 32, 64 yields
`a`, `b`, `c`.

The per-opcode lemmas this proof uses (`runOp_push1`, `runOp_add`,
`runOp_calldataload`, `runSeq_cons_ok`, `toState_update`) are not
specific to `add3` — they live in `EvmSmith/Lemmas.lean` and are reusable
by any other program proof.

## Why we don't prove `H_return = (a+b+c).toByteArray`

The bytecode ends with `MSTORE ; PUSH1 0x20 ; PUSH1 0x00 ; RETURN`. Proving
that the 32 returned bytes equal `(a + b + c).toByteArray` would require a
round-trip lemma both halves of which route through `ffi.ByteArray.zeroes`
(see `EVMYulLean/EvmYul/FFI/ffi.lean:18`, an `opaque` declaration). `opaque`
definitions are irreducible in the kernel by design. We'd need to axiomatize
the FFI round-trip, which is out of scope.

Instead we prove the arithmetic claim — the program computes `a + b + c` on
the stack — and demonstrate end-to-end behavior via `#guard` on concrete
inputs.
-/

namespace EvmSmith.Add3Proofs
open EvmYul EvmYul.EVM EvmSmith

/-! ## Correctness of `Add3.compute`

Proof strategy: build the post-state of each opcode as a `have` using the
opcode step lemmas from `EvmSmith.Lemmas`, then chain them with
`runSeq_cons_ok`. At every intermediate state the `toState` component is
unchanged (only `stack` and `pc` move), so the calldata hypotheses
`h0`/`h1`/`h2` continue to apply after each step via the `toState_update`
simp lemma. -/

/-- After running the compute prefix, the top of the stack is `a + b + c`. -/
theorem compute_correct
    (s0 : EVM.State)
    (a b c : UInt256)
    (hs : s0.stack = [])
    (h0 : EvmYul.State.calldataload s0.toState (UInt256.ofNat 0)  = a)
    (h1 : EvmYul.State.calldataload s0.toState (UInt256.ofNat 32) = b)
    (h2 : EvmYul.State.calldataload s0.toState (UInt256.ofNat 64) = c) :
    (runSeq Add3.compute s0).map (·.stack.head?)
      = .ok (some (a + b + c)) := by
  -- Normalise `s0` so its stack is literally `[]` (the step lemmas demand
  -- a stack that matches a concrete cons pattern; we'd rather not re-prove
  -- that after every step).
  have hs0 : s0 = { s0 with stack := [], pc := s0.pc } := by
    cases s0; cases hs; rfl
  -- Now build up the eight post-states one opcode at a time.
  -- e1..e8 are "what runOp does at step i" as equations.

  -- Step 1. PUSH1 0 → stack [0], pc += 2.
  have e1 :
      runOp (.Push .PUSH1) s0 (some (UInt256.ofNat 0, 1))
        = .ok { s0 with stack := [UInt256.ofNat 0], pc := s0.pc + UInt256.ofNat 2 } := by
    rw [hs0]; exact runOp_push1 s0 (UInt256.ofNat 0) [] s0.pc

  -- Step 2. CALLDATALOAD → pops 0, reads calldata[0..32] = a, pushes a.
  have e2 :
      runOp .CALLDATALOAD
          { s0 with stack := [UInt256.ofNat 0], pc := s0.pc + UInt256.ofNat 2 }
        = .ok { s0 with stack := [a], pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 } := by
    rw [runOp_calldataload]; simp [h0]

  -- Step 3. PUSH1 32 → stack [32, a], pc += 2.
  have e3 :
      runOp (.Push .PUSH1)
          { s0 with stack := [a], pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 }
          (some (UInt256.ofNat 32, 1))
        = .ok { s0 with
            stack := [UInt256.ofNat 32, a]
            pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 } :=
    runOp_push1 s0 (UInt256.ofNat 32) [a] _

  -- Step 4. CALLDATALOAD → pops 32, reads calldata[32..64] = b, pushes b.
  have e4 :
      runOp .CALLDATALOAD
          { s0 with
              stack := [UInt256.ofNat 32, a]
              pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2 }
        = .ok { s0 with
            stack := [b, a]
            pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
                   + UInt256.ofNat 1 } := by
    rw [runOp_calldataload]; simp [h1]

  -- Step 5. ADD → stack [b + a] (first addend was on top, so μ₀ = b, μ₁ = a).
  have e5 :
      runOp .ADD { s0 with
          stack := [b, a]
          pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
                 + UInt256.ofNat 1 }
        = .ok { s0 with
            stack := [b + a]
            pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
                   + UInt256.ofNat 1 + UInt256.ofNat 1 } :=
    runOp_add s0 b a [] _

  -- Step 6. PUSH1 64 → stack [64, b+a], pc += 2.
  have e6 :
      runOp (.Push .PUSH1)
          { s0 with
              stack := [b + a]
              pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
                     + UInt256.ofNat 1 + UInt256.ofNat 1 }
          (some (UInt256.ofNat 64, 1))
        = .ok { s0 with
            stack := [UInt256.ofNat 64, b + a]
            pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
                   + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 2 } :=
    runOp_push1 s0 (UInt256.ofNat 64) [b + a] _

  -- Step 7. CALLDATALOAD → pops 64, reads calldata[64..96] = c, pushes c.
  have e7 :
      runOp .CALLDATALOAD
          { s0 with
              stack := [UInt256.ofNat 64, b + a]
              pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
                     + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 2 }
        = .ok { s0 with
            stack := [c, b + a]
            pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
                   + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 2
                   + UInt256.ofNat 1 } := by
    rw [runOp_calldataload]; simp [h2]

  -- Step 8. ADD → stack [c + (b + a)]. This is the final sum; the rest of
  -- the theorem is arithmetic cleanup to show it equals `a + b + c`.
  have e8 :
      runOp .ADD { s0 with
          stack := [c, b + a]
          pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
                 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 2
                 + UInt256.ofNat 1 }
        = .ok { s0 with
            stack := [c + (b + a)]
            pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 2
                   + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 2
                   + UInt256.ofNat 1 + UInt256.ofNat 1 } :=
    runOp_add s0 c (b + a) [] _

  -- Chain the eight equations through `runSeq` via the fusion lemma.
  show (runSeq Add3.compute s0).map _ = _
  simp only [Add3.compute]
  rw [runSeq_cons_ok _ _ _ _ _ e1]
  rw [runSeq_cons_ok _ _ _ _ _ e2]
  rw [runSeq_cons_ok _ _ _ _ _ e3]
  rw [runSeq_cons_ok _ _ _ _ _ e4]
  rw [runSeq_cons_ok _ _ _ _ _ e5]
  rw [runSeq_cons_ok _ _ _ _ _ e6]
  rw [runSeq_cons_ok _ _ _ _ _ e7]
  rw [runSeq_cons_ok _ _ _ _ _ e8]

  -- `runSeq []` is `.ok s`; then `.map (·.stack.head?)` peels to
  -- `.ok (some (c + (b + a)))`.
  simp only [runSeq, Except.map, List.head?]

  -- Left with `Except.ok (some (c + (b + a))) = Except.ok (some (a + b + c))`.
  -- Peel off `Except.ok`, then `some`, then prove the modular-arithmetic
  -- equality via commutativity/associativity on `Fin UInt256.size`.
  show Except.ok (some (c + (b + a))) = Except.ok (some (a + b + c))
  congr 1
  congr 1
  show UInt256.add c (UInt256.add b a) = UInt256.add (UInt256.add a b) c
  unfold UInt256.add
  congr 1
  abel_nf

end EvmSmith.Add3Proofs
