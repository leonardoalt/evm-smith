import EvmYul.Frame
import EvmSmith.Demos.Weth.Invariant

/-!
# Weth — bytecode-specific Ξ preservation (B2 / §2.x)

This file is the Weth analogue of Register's `BytecodeFrame.lean`. It
collects the Weth-specific lemmas needed to discharge the Ξ closure
obligations consumed by `ΞPreservesInvariantAtC_of_Reachable_general`
(§H.2's entry point) for Weth's bytecode.

Currently it contains the §2.3a auxiliary lemma `weth_caller_ne_C`
in its **state-local** form: a structural fact about the relationship
between `executionEnv.sender`, `stack[1]?`, and `AccountAddress.ofUInt256`
that does not yet reference the (not-yet-defined) `WethTrace`
predicate.

The full §2.3 / §2.4 (`WethTrace` + bytecode walk) and §2.5 (CALL +
SSTORE combined-step lemma) live in subsequent commits. -/

namespace EvmSmith.Weth

open EvmYul EvmYul.EVM EvmYul.Frame

/-! ## §2.3a — `weth_caller_ne_C` (state-local form)

Per the plan: when Weth's withdraw block reaches the CALL site at
PC 72, the recipient is `AccountAddress.ofUInt256 stack[1]`, i.e.
the value pushed by the CALLER opcode at PC 70.

CALLER pushes `(.ofNat ∘ Fin.val ∘ ExecutionEnv.source)` (see
`EvmYul.Semantics`'s CALLER arm). Round-tripping through
`AccountAddress.ofUInt256` recovers the original sender (since
`AccountAddress.size = 2^160 < 2^256 = UInt256.size`, the embedding
is injective and the round-trip is the identity).

The §H.2 CALL-arm closure obligation requires `recipient ≠ C`.
Combined with the round-trip identity, this reduces to
`s.executionEnv.sender ≠ C` — a hypothesis the consumer
(`weth_solvency_invariant`'s outer wrapper) discharges from the
boundary hypothesis `C ≠ S_T` and the (future) trace-shape induction
that no Weth bytecode path produces a direct `C → C` call.

For now, the §2.3a deliverable is the state-local fact: given that
`stack[1]?` is `some` of a UInt256 that round-trips back to
`s.executionEnv.sender`, the recipient address differs from `C`. -/

/-- **§2.3a structural lemma.** State-local form: if the executionEnv's
sender differs from `C` and `stack[1]?` is `some senderAsUInt256` such
that `AccountAddress.ofUInt256 senderAsUInt256 = sender`, then the
recipient address (`AccountAddress.ofUInt256` of `stack[1]?.getD ⟨0⟩`)
is also `≠ C`.

This is the form that doesn't depend on the (not-yet-defined)
`WethTrace` predicate. Once §2.3 lands, the bytecode-walk consumer
will discharge the `hStack` hypothesis from the trace-shape invariant
that PC 70's CALLER push leaves the sender at `stack[1]?`. -/
theorem weth_caller_ne_C
    (C : AccountAddress) (s : EVM.State)
    (hOuter_ne : s.executionEnv.sender ≠ C)
    (hStack : ∃ x, s.stack[1]? = some x ∧
                   AccountAddress.ofUInt256 x = s.executionEnv.sender) :
    AccountAddress.ofUInt256 (s.stack[1]?.getD ⟨0⟩) ≠ C := by
  obtain ⟨x, hSome, hRound⟩ := hStack
  -- Reduce `getD` of `some x`.
  rw [hSome]
  -- Goal: AccountAddress.ofUInt256 ((some x).getD ⟨0⟩) ≠ C, i.e.
  -- AccountAddress.ofUInt256 x ≠ C. Use the round-trip identity.
  rw [Option.getD_some]
  rw [hRound]
  exact hOuter_ne

end EvmSmith.Weth
