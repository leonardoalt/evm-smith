import EvmSmith.Demos.Groth16.Spec
import EvmSmith.Demos.Groth16.EntryPoints

/-!
# Groth16 verifier — attempted witness for `Groth16Spec`

Unlike `Demos/Weth/SpecProofs.lean`'s `weth_spec` (complete), this is
**deliberately incomplete** — `sorry`s mark exactly where this demo's
scaffolding runs out, and each is commented with *why*, distinguishing two
different kinds of gap:

* `groth16_verifies` is blocked on **missing framework infrastructure**:
  `Spec/Dsl.lean`'s `ReachesCall` reasons about *one* `CALL` boundary; this
  contract makes three in sequence. Closing this `sorry` means extending the
  framework, not writing more WETH-style casework.
* `groth16_no_storage_effects` / `groth16_fallback` are blocked on **plain
  mechanical effort**: `EntryPoints.lean`'s `program_has_no_sstore` is
  already proved outright (no `sorry`, no precompile assumption); lifting
  it through `evmRun` is the same `*_run_impl` step-chasing
  `Demos/Weth/Behaviour.lean` does for WETH, just over ~120 instructions
  instead of ~10.
-/

namespace EvmSmith.Groth16

open EvmYul EvmYul.EVM EvmYul.Frame Batteries EvmSmith.Spec

/-- `verifyProof` relays the `SNARKV` pairing check, given that the three
precompile calls behave as assumed. -/
theorem groth16_verifies (s : EVM.State) (call : Calls .verifyProof s)
    (hmul : BnMulSucceeds) (hadd : BnAddSucceeds) (hsnarkv : SnarkvCorrect) :
    ensures
      (∃ vkx : G1,
        returndata =
          boolWord (PairingProductHolds
            (pairingInput
              (proofAx, negYOf proofAy) (proofBx1, proofBx0, proofBy1, proofBy0)
              (alphaX, alphaY)          (betaX1, betaX0, betaY1, betaY0)
              vkx                      (gammaX1, gammaX0, gammaY1, gammaY0)
              (proofCx, proofCy)        (deltaX1, deltaX0, deltaY1, deltaY0))))
      ∧ storage = old storage := by
  obtain ⟨hcode, hpc0, hstk0, hsel⟩ := call
  intro s' o ⟨callFuel, N, hrun⟩
  sorry
  -- See module docstring: needs an `evmRunToCall` generalised to the Nth
  -- `CALL`, threading BN_MUL's post-state into BN_ADD's pre-state into
  -- SNARKV's pre-state. `hmul`/`hadd`/`hsnarkv` are exactly the hypotheses
  -- such a proof would discharge each call boundary with.

/-- This contract never writes storage, on any entry, whatever the
precompiles return. -/
theorem groth16_no_storage_effects (s : EVM.State) (e : Entry) (call : Calls e s) :
    ensures storage = old storage := by
  intro s' o ⟨callFuel, N, hrun⟩
  sorry
  -- See module docstring: `program_has_no_sstore` (`EntryPoints.lean`) is
  -- proved, unconditionally. What's missing is the step-by-step lemma
  -- "no opcode in this program's repertoire (PUSH*, CALLDATALOAD, MSTORE,
  -- DUP/SWAP, EQ/ISZERO/SUB, JUMP/JUMPI/JUMPDEST, GAS, CALL-with-value-0,
  -- ISZERO, RETURN/REVERT) changes `accountMap`" pushed through `evmRun`.

/-- An unknown selector reverts, changing no account. -/
theorem groth16_fallback (s : EVM.State) (call : Calls .unknown s) :
    ensures storage = old storage :=
  groth16_no_storage_effects s .unknown call

/-- **This contract's bytecode is meant to satisfy `Groth16Spec`** — named
`_sorry` (cf. `weth_spec`) because two of its three fields still are. -/
def groth16_spec_sorry : Groth16Spec where
  verifies           := groth16_verifies
  no_storage_effects := groth16_no_storage_effects
  fallback           := groth16_fallback

end EvmSmith.Groth16
