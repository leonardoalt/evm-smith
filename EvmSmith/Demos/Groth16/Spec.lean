import EvmSmith.Demos.Groth16.SpecDSL

/-!
# Groth16 verifier — the spec, as an interface

In the style of `Demos/Weth/Spec.lean`: a single `structure Groth16Spec`
whose fields *are* this contract's guarantees, with **no proofs** — the
witness lives in `SpecProofs.lean` (`groth16_spec_sorry`, named to flag
that, unlike `weth_spec`, it is not yet a complete proof). Vocabulary
(`Calls`, `ensures`, `PairingProductHolds`, `SnarkvCorrect`, …) is in
`SpecDSL.lean` / `Spec/Dsl.lean`.

## The contract (861 bytes of runtime code, one public input)

| Selector     | Shape                                                                | Behaviour |
|--------------|-----------------------------------------------------------------------|-----------|
| `0x43753b4d` | `verifyProof(uint256[2],uint256[2][2],uint256[2],uint256[1])`        | relays the `alt_bn128` pairing check for this proof/verifying-key |

`Calls .verifyProof s` means `s` is the entry of a call to `verifyProof`;
`ensures …` is the postcondition of running to halt.
-/

namespace EvmSmith.Groth16

open EvmYul EvmYul.EVM EvmYul.Frame Batteries EvmSmith.Spec

/-- **This contract's guarantees, as an interface.** Each field is a
behaviour the bytecode is meant to obey. Unlike `WethSpec`, the headline
field (`verifies`) is *conditional* on an explicit, named, and — per the
module docstring in `SpecDSL.lean` — **unprovable-in-this-repo** assumption
about the `SNARKV` precompile. That is the honest ceiling for a tool that
proves bytecode-to-spec correctness without a BN254 pairing formalisation:
it can show the contract *correctly relays* `SNARKV`'s answer, not that
`SNARKV`'s answer is cryptographically meaningful. -/
structure Groth16Spec where
  /-- **`verifyProof` relays the pairing check, given that the precompiles
  behave.** If `BN_MUL` and `BN_ADD` succeed on the (well-formed) inputs this
  contract feeds them, and `SNARKV` answers correctly (`SnarkvCorrect`), then
  the returned boolean is exactly the pairing-product check over the eight
  points this contract assembles: `(-A, B), (alpha, beta), (vk_x, gamma),
  (C, delta)` — where `vk_x` is whatever `BN_ADD` computed (its arithmetic
  is *not* characterised here, only that it didn't fail; see
  `SpecDSL.lean`). -/
  verifies : ∀ (s : EVM.State), Calls .verifyProof s →
    BnMulSucceeds → BnAddSucceeds → SnarkvCorrect →
    ensures
      (∃ vkx : G1,
        returndata =
          boolWord (PairingProductHolds
            (pairingInput
              (proofAx, negYOf proofAy) (proofBx1, proofBx0, proofBy1, proofBy0)
              (alphaX, alphaY)          (betaX1, betaX0, betaY1, betaY0)
              vkx                      (gammaX1, gammaX0, gammaY1, gammaY0)
              (proofCx, proofCy)        (deltaX1, deltaX0, deltaY1, deltaY0))))
      ∧ storage = old storage

  /-- **This contract never writes storage**, on *any* call (matching
  selector or not), regardless of what the precompiles return — it is a
  `view` function from its first instruction to its last. Needs no
  precompile assumption (see `EntryPoints.lean`'s `program_has_no_sstore`,
  which is proved outright, no `sorry`); only the lifting of that bytecode
  fact through `evmRun`'s step-by-step execution is left as the engineering
  work tracked by `groth16_spec_sorry`. -/
  no_storage_effects : ∀ (s : EVM.State) (e : Entry), Calls e s →
    ensures storage = old storage

  /-- **Unknown selector reverts**, changing no account (no fallback /
  `receive`; this view function has no payable path either). -/
  fallback : ∀ (s : EVM.State), Calls .unknown s →
    ensures storage = old storage

end EvmSmith.Groth16
