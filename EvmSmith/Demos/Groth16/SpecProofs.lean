import EvmSmith.Demos.Groth16.Spec
import EvmSmith.Demos.Groth16.EntryPoints

/-!
# Groth16 verifier — attempted witness for `Groth16Spec`

Unlike `Demos/Weth/SpecProofs.lean`'s `weth_spec` (complete), this is
**deliberately incomplete** — `sorry`s mark exactly where this demo's
scaffolding runs out, and each is commented with *why*, distinguishing
different kinds of gap:

* `groth16_no_storage_effects` / `groth16_fallback` are blocked on **plain
  mechanical effort**: `EntryPoints.lean`'s `program_has_no_sstore` is
  already proved outright (no `sorry`, no precompile assumption); lifting
  it through `evmRun` is the same `*_run_impl` step-chasing
  `Demos/Weth/Behaviour.lean` does for WETH, just over ~120 instructions
  instead of ~10. Crucially, this one does **not** hit the wall below: it
  only needs "no opcode here touches `accountMap`", never "what bytes does
  memory hold" — `accountMap` and `MachineState`/`memory` are separate
  fields of `EVM.State`, and the per-opcode shape lemmas
  (`step_MSTORE_shape` etc.) already make clear `MSTORE`/`PUSH`/etc. only
  ever touch the latter.

* `groth16_verifies` is blocked on **two distinct, independent obstacles**,
  one of framework scope, one of foundations. Both must be resolved (in
  either order) to close it; resolving only one leaves the other.

  **(1) Multi-call chaining (framework scope, not depth).**
  `Spec/Dsl.lean`'s `ReachesCall`/`evmRunToCall` only run a program up to
  its *first* `CALL`; this contract makes three in sequence (`BN_MUL` →
  `BN_ADD` → `SNARKV`). Nothing today threads the post-state of call *N*
  into the pre-state of call *N+1*. Since the count is fixed at 3 (no
  dynamic public-input loop — see `Program.lean`'s docstring on why
  `nPublic = 1` was chosen precisely to avoid that other, harder problem),
  this needs no induction: either inline the three boundaries by hand, or
  add an `evmRunToCall`-for-the-Nth-call generalisation other multi-call
  contracts could reuse.

  **(2) `ffi.ByteArray.zeroes` is `opaque` with no semantic axiom
  (foundations, not scope).** This is the deeper one, found while
  attempting (1): `UInt256.toByteArray`
  (`EVMYulLean/EvmYul/Wheels.lean:12`) — the function describing what
  bytes `MSTORE` writes for a given value — is defined as
  `ffi.ByteArray.zeroes ⟨32 - b.size⟩ ++ b`, and
  `ffi.ByteArray.zeroes` (`EVMYulLean/EvmYul/FFI/ffi.lean:18`) is declared
  `opaque` with **no body and no semantic axiom** — it's backed by a real
  `memset_zero` C function for *execution* (so `native_decide` on fully
  concrete inputs works fine), but Lean's logic has no defining equation
  for it. That's invisible as long as every `ffi.ByteArray.zeroes` call
  has a *concrete* numeral size argument — true for all the offset/length
  bookkeeping in `ByteArray.write`, since that only depends on sizes, not
  values. It stops being invisible the moment the *value being written* is
  an abstract/symbolic `UInt256` (`proof.A.x`, `vk_x`, …, exactly what
  `verifyProof`'s `∀ s, Calls .verifyProof s → …` quantifies over): then
  `b.size` is symbolic too, `32 - b.size` is a non-ground term, and
  `toByteArray`'s value is permanently opaque — no lemma-writing gets
  around an `opaque` declaration with no axiom.

  This is *why* this is the first demo to hit this wall: WETH never
  `MSTORE`s an abstract value (its one `CALL` has `retSize = 0`; everything
  else lives in clean `UInt256` stack/storage arithmetic or is *read* back
  out of existing concrete bytes via `CALLDATALOAD`, never *written* via
  `toByteArray`). `verifyProof` is the first contract in this repo whose
  correctness depends on the byte-encoding of a value nobody pinned down
  in advance.

  **The fix, if anyone wants to pick this up**: one new axiom in
  `EVMYulLean` (not `EvmSmith` — `ffi.ByteArray.zeroes` lives in the
  vendored framework, so this is a project-level trust-base decision, not
  a demo-local one):
  `∀ n, ffi.ByteArray.zeroes n = ⟨Array.replicate n.toNat 0⟩` — obviously
  true of `memset_zero`, one line, and it would unblock `toByteArray`,
  `ByteArray.write`'s padding, and `readWithPadding`'s padding
  project-wide, not just here.
-/

namespace EvmSmith.Groth16

open EvmYul EvmYul.EVM EvmYul.Frame Batteries EvmSmith.Spec

/-- `verifyProof` relays the `SNARKV` pairing check, given that the three
precompile calls behave as assumed and the public input is canonical
(`< r`) — see `Spec.lean`'s `verifies` field docstring on why that
precondition is needed now that `checkField` (`Program.lean`) rejects
`input ≥ r` instead of letting it through. -/
theorem groth16_verifies (s : EVM.State) (call : Calls .verifyProof s)
    (hfield : publicInput < r)
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
  -- See module docstring's two-part breakdown: (1) the missing
  -- multi-call-chaining infrastructure in `Spec/Dsl.lean`
  -- (`hmul`/`hadd`/`hsnarkv` are exactly the hypotheses such chaining would
  -- discharge each call boundary with), and, underneath that, (2) the
  -- `ffi.ByteArray.zeroes`-is-`opaque`-with-no-axiom wall, which blocks
  -- reasoning about the byte-encoding of any abstract `UInt256` written to
  -- memory (every value this proof needs to track through the 40-odd
  -- `MSTORE`s feeding `SNARKV`'s input buffer).

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
