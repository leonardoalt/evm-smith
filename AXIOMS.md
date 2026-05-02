# Axioms

The EVM-Smith proofs rely on the EVMYulLean framework
([`leonardoalt/EVMYulLean`](https://github.com/leonardoalt/EVMYulLean)),
which is mostly composed of mechanically-checked theorems. Two facts
are stated as **explicit axioms** because formally proving them is
out of scope.

These are the only `axiom` declarations in the codebase that EVM-Smith
proofs depend on (apart from Lean's own foundational logical axioms,
which are standard).

## T2 — `precompile_preserves_accountMap`

**Location**: `EVMYulLean/EvmYul/Frame/MutualFrame.lean`.

**Statement** (informal): every EVM precompile, when executed, returns
a state whose `accountMap` is either equal to the input `σ` or empty
`∅`. In particular, no precompile inserts new accounts or modifies
existing accounts in arbitrary ways.

**In Lean**:

```lean
axiom precompile_preserves_accountMap
    (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (f : AccountMap .EVM → UInt256 → Substate → ExecutionEnv .EVM
          → (Bool × AccountMap .EVM × UInt256 × Substate × ByteArray)) :
    let result := f σ g A I
    result.2.1 = σ ∨ result.2.1 = ∅
```

**Why it's an axiom**: provable by case inspection of the ten
precompile bodies in `EVMYulLean/EvmYul/EVM/PrecompiledContracts.lean`
(SHA256, RIPEMD160, ECRECOVER, IDENTITY, MODEXP, ECADD, ECMUL, ECPAIRING,
BLAKE2F, KZG-POINT-EVAL). None of them touch `accountMap` — they
either pass it through unchanged on success or return `∅` on
gas-failure. The axiom captures this without doing the per-precompile
proof.

**Risk if false**: if some precompile *did* modify `accountMap` in a
way that contradicts the axiom (e.g., an upgrade that lets a
precompile mint accounts), the framework's per-frame invariant
preservation lemmas would silently admit invalid post-states. In
practice the axiom is true for the current EVM precompiles by
inspection.

**Path to discharging it**: case-split on the `f` argument across the
ten precompile arms, observe that each returns either `(_, σ, _, _, _)`
or `(_, ∅, _, _, _)`. Mechanical work; not started.

---

## T5 — `lambda_derived_address_ne_C`

**Location**: `EVMYulLean/EvmYul/Frame/MutualFrame.lean`.

**Statement** (informal): the address derived by `CREATE` /
`CREATE2` (computed as `keccak256(rlp(sender, nonce))` for CREATE or
`keccak256(0xff || sender || salt || keccak256(initcode))` for
CREATE2, then truncated to 20 bytes) never equals an arbitrary
pre-existing contract address `C`.

**In Lean**:

```lean
axiom lambda_derived_address_ne_C
    (s : AccountAddress) (n : UInt256)
    (ζ : Option ByteArray) (i : ByteArray) (C : AccountAddress) :
    let lₐ := EVM.Lambda.L_A s n ζ i
    let aByteArray := (ffi.KEC (lₐ.getD default)).extract 12 32
    let aNat := fromByteArrayBigEndian aByteArray
    let a : AccountAddress := Fin.ofNat _ aNat
    a ≠ C
```

**Why it's an axiom**: this is **Keccak's collision resistance** —
formally proving it would require formalising the cryptographic
properties of Keccak-256, which is far beyond the scope of an EVM
formalization. Every formal-methods project working with hash-derived
addresses takes some equivalent of this as an assumption.

**Risk if false**: if a `CREATE` or `CREATE2` could be made to derive
an address matching some target contract `C` (i.e., a Keccak preimage
attack), the attacker could overwrite `C`'s account with arbitrary
storage and code. This would invalidate any safety property about
`C`. In practice, finding a Keccak collision would also break a
substantial portion of Ethereum's security model — far beyond the
specific consequences for any individual contract proof.

**Path to discharging it**: requires a formalization of Keccak's
collision resistance, which is an open research problem. The axiom
is the standard real-world assumption.

---

## Standard Lean foundational axioms

In addition to the two EVM-specific axioms above, all Lean proofs
depend on Lean 4's foundational logical framework. These are not
specific to EVM-Smith; they are the same axioms used by every Lean
4 proof in the wider community. They are:

- **Propositional extensionality** (`propext`): logically equivalent
  propositions are equal.
- **Quotient construction** (`Quot.sound`, `Quot.mk`, `Quot.lift`):
  the standard quotient-type axioms.
- **Choice** (`Classical.choice`): used for non-constructive
  case-splits.

These are part of the Lean 4 core and are accepted by the entire
Lean / Mathlib ecosystem. Listing them here for completeness; they
are not facts that EVM-Smith specifically asks you to take on faith.

---

## Summary

| Axiom | What it says | Why it's an axiom | Risk if false |
|---|---|---|---|
| `precompile_preserves_accountMap` (T2) | Precompiles don't mutate `accountMap` arbitrarily. | Provable by case inspection; not yet done. | A precompile mutating accounts arbitrarily would break per-frame invariants. |
| `lambda_derived_address_ne_C` (T5) | CREATE/CREATE2 don't derive an existing contract's address. | Equivalent to Keccak collision resistance. | Keccak collision attack would break this and most of Ethereum. |
