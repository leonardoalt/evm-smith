import Mathlib.Logic.Function.Basic
import EvmSmith.Framework
import EvmSmith.Lemmas.UInt256Order

/-!
# Abstract ERC-20 spec + refinement framework

A small abstract ERC-20 (a balance map) and a **refinement relation**
linking it to a concrete storage layout via a `SlotAbstraction` — a
slot function bundled with its injectivity proof.

## The injectivity obligation, made structural

The peephole / observable-equivalence theorems in `Equivalence.lean`
and `EquivalenceVyper.lean` prove orig-vs-opt loaded-value agreement
under a per-address relation `R`. They take `R` as a precondition;
they don't check whether the slot function chosen by the opt side
*can actually maintain* `R` across a sequence of mints / transfers /
burns. A non-injective slot function would silently make the relation
degenerate, and the proofs would still go through. That was the
soundness gap the user flagged.

This file closes it at the *structure* level. The refinement relation
is parameterised by a `SlotAbstraction` that **bundles the slot
function with `Function.Injective` as a proof obligation**. To
instantiate `SlotAbstraction`, you must produce an injectivity
proof — a non-injective slot function cannot be lifted to a
`SlotAbstraction`, so the refinement preservation theorems
literally cannot be applied to it.

For `UInt256.lnot`: injectivity is `EvmYul.UInt256.lnot_injective`,
proved end-to-end sorry-free in `EvmSmith/Lemmas/UInt256Order.lean`.

For the orig Solady keccak slot function: injectivity follows from
Keccak's collision-resistance, the existing evm-smith T5 axiom.

For a hypothetical bad function like `addr mod 2^32`: no injectivity
proof exists, so no `SlotAbstraction` value can be constructed —
*the bad design fails to type-check.*

## Scope of the model

We deliberately work with concrete storage as a total function
`UInt256 → UInt256` rather than `EvmYul.State`. The reason is purely
tactical: `EvmYul.State.sstore` and `sload` go through
`Batteries.RBMap` insert / find, and the round-trip lemmas there
need a slice of the upstream RBMap API that isn't currently
exposed — orthogonal to the soundness argument we want to make.
`Function.update`-on-a-total-function gives clean equational
reasoning (`Function.update_self`, `Function.update_of_ne`) that
matches `sstore` / `sload`'s observable behaviour exactly.

What's covered:
- Per-address balance preservation across `mint`, `burn`, `transfer`,
  including the self-transfer special case.
- Each preservation theorem uses `sa.inj` in the "different
  address" branch. With a non-injective slot function, that branch
  is literally unprovable.

What's not in this file (intentional):
- TotalSupply / named-slot disjointness. That's a separate
  domain-restricted property of the slot function (`~addr` is
  disjoint from low-named slots only when `addr` is a valid
  160-bit address, since `~` is bijective on all of `UInt256`).
  A second framework layer parameterised on a "valid address"
  predicate would discharge it. Out of scope for this pass.
- The bridge from this abstract model down to `EvmYul.State.sload`
  / `sstore`. That's the storage-round-trip ergonomics gap noted
  throughout the demo. Same shape; same path to closing.

## Note on identifier naming

The Lean parser reserves `to` and `from` as keywords, so we use
`src` and `dst` ("source" / "destination") for the transfer
parameters throughout this file.
-/

namespace EvmSmith.ERC20.Spec
open EvmYul

/-! ## Slot abstraction -/

/-- The bridge between abstract and concrete. Bundles a slot function
with its injectivity proof so the latter can't be forgotten. -/
structure SlotAbstraction where
  slotFn : UInt256 → UInt256
  inj    : Function.Injective slotFn

/-! ## Refinement relation

A concrete storage refines an abstract balance map under a slot
abstraction iff every address's abstract balance can be read out of
the concrete storage at the corresponding slot. -/

def refines (σ : UInt256 → UInt256) (bal : UInt256 → UInt256)
    (sa : SlotAbstraction) : Prop :=
  ∀ a, σ (sa.slotFn a) = bal a

/-! ## Operations

Concrete operations write the storage; abstract operations update the
balance map. The slot function maps an "address" (key in the abstract
map) to a "storage slot" (key in the concrete storage). -/

/-- Concrete mint: add `amt` to the storage cell at `slotFn dst`. -/
def concreteMint (σ : UInt256 → UInt256) (sa : SlotAbstraction)
    (dst amt : UInt256) : UInt256 → UInt256 :=
  Function.update σ (sa.slotFn dst) (σ (sa.slotFn dst) + amt)

/-- Concrete burn: subtract `amt` from the storage cell at `slotFn src`. -/
def concreteBurn (σ : UInt256 → UInt256) (sa : SlotAbstraction)
    (src amt : UInt256) : UInt256 → UInt256 :=
  Function.update σ (sa.slotFn src) (σ (sa.slotFn src) - amt)

/-- Concrete transfer: decrement source, then increment destination. -/
def concreteTransfer (σ : UInt256 → UInt256) (sa : SlotAbstraction)
    (src dst amt : UInt256) : UInt256 → UInt256 :=
  let σ1 := Function.update σ (sa.slotFn src) (σ (sa.slotFn src) - amt)
  Function.update σ1 (sa.slotFn dst) (σ1 (sa.slotFn dst) + amt)

def absMint (bal : UInt256 → UInt256) (dst amt : UInt256) : UInt256 → UInt256 :=
  Function.update bal dst (bal dst + amt)

def absBurn (bal : UInt256 → UInt256) (src amt : UInt256) : UInt256 → UInt256 :=
  Function.update bal src (bal src - amt)

def absTransfer (bal : UInt256 → UInt256) (src dst amt : UInt256) : UInt256 → UInt256 :=
  let bal1 := Function.update bal src (bal src - amt)
  Function.update bal1 dst (bal1 dst + amt)

/-! ## Refinement preservation

Each theorem's "different address" case uses `sa.inj`. Take it out
and the proof breaks. -/

theorem mint_refines
    (σ : UInt256 → UInt256) (bal : UInt256 → UInt256) (sa : SlotAbstraction)
    (h : refines σ bal sa) (dst amt : UInt256) :
    refines (concreteMint σ sa dst amt) (absMint bal dst amt) sa := by
  intro a
  unfold concreteMint absMint
  by_cases ha : a = dst
  · subst ha
    rw [Function.update_self, Function.update_self]
    exact congrArg (· + amt) (h a)
  · have hSlotNe : sa.slotFn a ≠ sa.slotFn dst := fun heq => ha (sa.inj heq)
    rw [Function.update_of_ne hSlotNe, Function.update_of_ne ha]
    exact h a

theorem burn_refines
    (σ : UInt256 → UInt256) (bal : UInt256 → UInt256) (sa : SlotAbstraction)
    (h : refines σ bal sa) (src amt : UInt256) :
    refines (concreteBurn σ sa src amt) (absBurn bal src amt) sa := by
  intro a
  unfold concreteBurn absBurn
  by_cases ha : a = src
  · subst ha
    rw [Function.update_self, Function.update_self]
    exact congrArg (· - amt) (h a)
  · have hSlotNe : sa.slotFn a ≠ sa.slotFn src := fun heq => ha (sa.inj heq)
    rw [Function.update_of_ne hSlotNe, Function.update_of_ne ha]
    exact h a

theorem transfer_refines
    (σ : UInt256 → UInt256) (bal : UInt256 → UInt256) (sa : SlotAbstraction)
    (h : refines σ bal sa) (src dst amt : UInt256) :
    refines (concreteTransfer σ sa src dst amt) (absTransfer bal src dst amt) sa := by
  intro a
  unfold concreteTransfer absTransfer
  by_cases hDst : a = dst
  · subst hDst
    rw [Function.update_self, Function.update_self]
    by_cases hSrc : a = src
    · -- Self-transfer.
      subst hSrc
      rw [Function.update_self, Function.update_self]
      show σ (sa.slotFn a) - amt + amt = bal a - amt + amt
      rw [h a]
    · have hSlotNe : sa.slotFn a ≠ sa.slotFn src := fun heq => hSrc (sa.inj heq)
      rw [Function.update_of_ne hSlotNe, Function.update_of_ne hSrc]
      show σ (sa.slotFn a) + amt = bal a + amt
      rw [h a]
  · have hSlotDstNe : sa.slotFn a ≠ sa.slotFn dst := fun heq => hDst (sa.inj heq)
    rw [Function.update_of_ne hSlotDstNe, Function.update_of_ne hDst]
    by_cases hSrc : a = src
    · subst hSrc
      rw [Function.update_self, Function.update_self]
      show σ (sa.slotFn a) - amt = bal a - amt
      rw [h a]
    · have hSlotSrcNe : sa.slotFn a ≠ sa.slotFn src := fun heq => hSrc (sa.inj heq)
      rw [Function.update_of_ne hSlotSrcNe, Function.update_of_ne hSrc]
      exact h a

/-! ## Concrete instantiations

These exist as *type-level* checks: the framework refuses to admit a
slot function without an injectivity witness, so writing these lines
forces the witness to exist. -/

/-- The opt-side slot abstraction: `~addr`, with injectivity from
`UInt256.lnot_injective`. -/
def lnotSlotAbstraction : SlotAbstraction where
  slotFn := UInt256.lnot
  inj    := EvmYul.UInt256.lnot_injective

/-- Sanity: the original buggy slot function (`slotFn := id`) IS
injective, so it CAN be lifted to a `SlotAbstraction`. Injectivity
alone doesn't catch the named-slot collision — the disjointness
obligation noted in the file header would. Including this definition
makes it clear that injectivity is *necessary but not sufficient*. -/
def idSlotAbstraction : SlotAbstraction where
  slotFn := id
  inj    := Function.injective_id

/-! A hypothetical non-injective slot function — e.g.
`fun a => UInt256.ofNat (a.toNat % 2^32)` — would NOT type-check
here. Try to instantiate it and Lean rejects the value: the `inj`
field can't be proved without a sorry, because there exist `a ≠ b`
with the same image. -/

end EvmSmith.ERC20.Spec
