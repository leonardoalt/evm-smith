import EvmSmith.Demos.Groth16.Program
import EvmSmith.Spec.Dsl

/-!
# Groth16-specific spec vocabulary

The `Groth16` layer on top of the contract-agnostic `EvmSmith/Spec/Dsl.lean`
(`evmRun`/`Halts`/`ensures`/`sender`/`returndata`/`storage`). Here live the
pieces that mention this contract: its one entry point, its ABI argument
decoding (`proofA`/`proofB`/`proofC`/`publicInput`), and — the load-bearing
part — the **explicit trust boundary** around the three precompiles it calls.

## The trust boundary

`BnMulSucceeds`/`BnAddSucceeds`/`SnarkvCorrect` below play exactly the role
`NoReentrancy` plays in `Demos/Weth/SpecDSL.lean`: a named, explicit
assumption a guarantee is conditional on, not a proved fact. The difference
in *kind* is worth being honest about. `NoReentrancy` assumes away the
behaviour of an adversarial recipient contract — something that could, in
principle, be discharged for any *specific* recipient by proving its
bytecode meets a spec, just like this one. `SnarkvCorrect` assumes the
mathematical correctness of `Ξ_SNARKV`'s answer relative to the actual
`alt_bn128` pairing equation — and `Ξ_SNARKV` (`EVMYulLean/EvmYul/SNARKV.lean`)
shells out to a Python `py_ecc` process at evaluation time, so this is not a
fact Lean's logic can ever derive from the definitions in this repo; no
formalisation of BN254 pairings exists here (or in mathlib). So this demo's
ceiling is: **prove the bytecode correctly relays whatever `SNARKV` answers**
(ABI decoding, memory wiring, control flow), **assuming `SNARKV` answers
correctly**. Proving the latter is a different (and much larger) undertaking
— formalising the Groth16 protocol's soundness — that is out of scope for a
bytecode-correctness tool by design, not by oversight.

Even *granting* `SnarkvCorrect`/`BnMulSucceeds`/`BnAddSucceeds`, actually
discharging `Groth16Spec.verifies` is still blocked — by a multi-call-
chaining gap in `Spec/Dsl.lean`, and beneath that, by a foundational
`EVMYulLean` issue (`ffi.ByteArray.zeroes` is `opaque` with no semantic
axiom, which blocks reasoning about the byte-encoding of any abstract
value written to memory). See the module docstring in `SpecProofs.lean`
for the full breakdown and the one-line fix that would unblock the second
issue project-wide.
-/

namespace EvmSmith.Groth16

open EvmYul EvmYul.EVM EvmYul.Frame Batteries EvmSmith.Spec

/-! ## Entry points -/

/-- This contract's one ABI entry point, plus the catch-all for any other
selector. -/
inductive Entry | verifyProof | unknown
deriving DecidableEq

/-! ## ABI selector extraction (generic: `shr(224, calldataload(0))`) -/

def selectorOf (calldata : ByteArray) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (calldata.readBytes 0 32)) (UInt256.ofNat 0xe0)

def functionSelector (calldata : ByteArray) : UInt256 :=
  selectorOf calldata

/-! ## "This is a call to f" -/

/-- `Calls e s` bundles the genuine call-entry conditions: we start at the
contract's first instruction (`pc = 0`, empty stack), the code is this
contract's, and the ABI selector matches entry point `e`. Unlike WETH this
contract never touches storage, so — deliberately — `Calls` does not require
an account to exist at `codeOwner`. -/
def Calls (e : Entry) (s : EVM.State) : Prop :=
  s.executionEnv.code = bytecode
  ∧ s.pc = UInt256.ofNat 0
  ∧ s.stack = []
  ∧ (match e with
     | .verifyProof => functionSelector s.executionEnv.calldata = verifySelector
     | .unknown      => functionSelector s.executionEnv.calldata ≠ verifySelector)

/-! ## ABI argument decoding

Each argument is `calldataload` at its fixed offset — see `Program.lean`'s
calldata-layout table. Bound, by convention, to a pre-state `s` (same
convention `Demos/Weth/SpecDSL.lean` uses for `amount`). -/

set_option hygiene false in
section
notation "proofAx" => EvmYul.State.calldataload s.toState (UInt256.ofNat 4)
notation "proofAy" => EvmYul.State.calldataload s.toState (UInt256.ofNat 36)
notation "proofBx1" => EvmYul.State.calldataload s.toState (UInt256.ofNat 68)
notation "proofBx0" => EvmYul.State.calldataload s.toState (UInt256.ofNat 100)
notation "proofBy1" => EvmYul.State.calldataload s.toState (UInt256.ofNat 132)
notation "proofBy0" => EvmYul.State.calldataload s.toState (UInt256.ofNat 164)
notation "proofCx" => EvmYul.State.calldataload s.toState (UInt256.ofNat 196)
notation "proofCy" => EvmYul.State.calldataload s.toState (UInt256.ofNat 228)
notation "publicInput" => EvmYul.State.calldataload s.toState (UInt256.ofNat 260)
end

/-! ## `ECPAIRING`/`SNARKV` input encoding

Pure byte-layout helpers — no curve arithmetic — matching the precompile's
ABI (EIP-197): each pair is `G1 ++ G2`, `G2`'s four words in `(x.c1, x.c0,
y.c1, y.c0)` order, and the whole input is the four pairs concatenated. Used
to state `Groth16Spec.verifies` without needing to talk about the contract's
intermediate memory state. -/

abbrev G1 := UInt256 × UInt256
abbrev G2 := UInt256 × UInt256 × UInt256 × UInt256

def encodeG1 (p : G1) : ByteArray := p.1.toByteArray ++ p.2.toByteArray
def encodeG2 (p : G2) : ByteArray :=
  p.1.toByteArray ++ p.2.1.toByteArray ++ p.2.2.1.toByteArray ++ p.2.2.2.toByteArray
def encodePair (g1 : G1) (g2 : G2) : ByteArray := encodeG1 g1 ++ encodeG2 g2

def pairingInput (p0g1 : G1) (p0g2 : G2) (p1g1 : G1) (p1g2 : G2)
    (p2g1 : G1) (p2g2 : G2) (p3g1 : G1) (p3g2 : G2) : ByteArray :=
  encodePair p0g1 p0g2 ++ encodePair p1g1 p1g2 ++ encodePair p2g1 p2g2 ++ encodePair p3g1 p3g2

/-- `-A`'s `y`-coordinate: `0` if `A.y = 0` (point at infinity), else `Q -
A.y` — mirrors the `if (proof.A.Y != 0) negA.Y = Q - (proof.A.Y % Q)` guard
real Groth16 verifiers use, and exactly what the `negA` block in
`Program.lean` computes. -/
def negYOf (ay : UInt256) : UInt256 :=
  if ay = UInt256.ofNat 0 then UInt256.ofNat 0 else Q - ay

/-- The 32-byte big-endian encoding of a boolean, matching `SNARKV`'s
(and Solidity `bool`'s) ABI encoding. -/
def boolWord (b : Bool) : ByteArray :=
  if b then (UInt256.ofNat 1).toByteArray else (UInt256.ofNat 0).toByteArray

/-! ## The trust boundary -/

/-- The opaque mathematical meaning of a (multiple-of-192-byte) `SNARKV`
input buffer: "the product, over the encoded `(G1, G2)` pairs, of their
`alt_bn128` pairings equals `1` in `Fp12`." Left **uninterpreted** — see the
module docstring. `Bool`-valued (rather than `Prop`-valued) purely so it can
be compared directly against the precompile's `Bool`/word output below with
no separate decidability instance needed. -/
opaque PairingProductHolds (input : ByteArray) : Bool := true

/-- **The precompile-correctness assumption for `SNARKV`.** `Ξ_SNARKV`'s
32-byte output word is `1` exactly when its input satisfies
`PairingProductHolds`, and `0` otherwise, for any well-formed
(192-byte-multiple) input. Assumed, not proved — see the module docstring.
(`Ξ_SNARKV`/`Ξ_BN_MUL`/`Ξ_BN_ADD` below are top-level names from
`EVMYulLean/EvmYul/EVM/PrecompiledContracts.lean`, not under `EvmYul.`.) -/
def SnarkvCorrect : Prop :=
  ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM),
    I.calldata.size % 192 = 0 →
    (Ξ_SNARKV σ g A I).2.2.2.2 = boolWord (PairingProductHolds I.calldata)

/-- **`BN_MUL` does not fail** on the 96-byte, well-formed input this
contract supplies (`IC1 ++ input`). A success-only assumption: we never need
to know *which* point it returns, only that the call doesn't revert — see
the module docstring on why `SnarkvCorrect`'s relay property doesn't need to
characterise `BN_MUL`/`BN_ADD`'s arithmetic, only that they succeed. -/
def BnMulSucceeds : Prop :=
  ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM),
    I.calldata.size = 96 → (Ξ_BN_MUL σ g A I).1 = true

/-- **`BN_ADD` does not fail** on the 128-byte, well-formed input this
contract supplies (`vk_x_partial ++ IC0`). -/
def BnAddSucceeds : Prop :=
  ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM),
    I.calldata.size = 128 → (Ξ_BN_ADD σ g A I).1 = true

end EvmSmith.Groth16
