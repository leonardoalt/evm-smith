import Mathlib.Logic.Function.Basic
import EvmSmith.Framework
import EvmSmith.Lemmas.UInt256Order

/-!
# Abstract ERC-20 spec + refinement framework

A small abstract ERC-20 (a balance map + named state) and a
**refinement relation** linking it to a concrete storage layout via a
`SlotAbstraction` — a slot function bundled with proofs of all the
obligations its soundness rests on.

## What the structure enforces

```lean
structure SlotAbstraction where
  ValidAddr : UInt256 → Prop          -- which inputs are "addresses"
  NamedSlot : UInt256 → Prop          -- which slots the contract uses
                                       -- for non-balance state
                                       -- (`_name`/`_symbol`/etc.)
  slotFn    : UInt256 → UInt256
  inj       : ∀ a b, ValidAddr a → ValidAddr b →
              slotFn a = slotFn b → a = b
  disjoint  : ∀ a, ValidAddr a → ¬ NamedSlot (slotFn a)
```

Two soundness obligations, both load-bearing:

- `inj` — distinct valid addresses map to distinct slots. Without it,
  two users alias and one's `mint` silently changes the other's
  `balanceOf`. The peephole proofs are robust to a non-injective
  slot function (the relation just becomes degenerate); the
  refinement preservation theorems below are *not* — they use `inj`
  in every "different address" case.

- `disjoint` — no valid address's slot lands on a named slot. Without
  it, `mint(addr, v)` could overwrite the contract's `_name`,
  `_symbol`, or `totalSupply`. The original `sload(addr)` bug was
  exactly this. The refinement preservation theorems use `disjoint`
  in every "named slot must remain untouched" step.

A non-injective or named-slot-colliding slot function literally
cannot be elevated to a `SlotAbstraction` — the field proofs can't
be discharged — so the preservation theorems can't be applied to it.

## Instances

- `lnotSlotAbstraction` (sorry-free): `slotFn := UInt256.lnot`,
  `ValidAddr := a.toNat < 2^160` (real 160-bit addresses),
  `NamedSlot := s ∈ {0, 1, 2, _TOTAL_SUPPLY_SLOT}` (Solidity
  Solady's mock layout). `inj` from `lnot_injective`; `disjoint`
  from the high-bit argument (`lnot a >= 2^256 - 2^160` for any
  160-bit `a`, well above each named slot).

- `keccakSlotAbstraction`: hypothetical instance for Solady's
  keccak layout. Stated; `inj` would discharge from Keccak T5
  collision-resistance (axiom), `disjoint` from the high-entropy
  argument. Not constructed here (out of scope; the orig side
  doesn't need a separate instance to demonstrate the framework).

- `idSlotAbstraction` is **deliberately removed** in this version of
  the file: `id` is injective but fails `disjoint` against
  `NamedSlot := s ∈ {0, 1, 2, ...}` because `id 0 = 0 ∈ named`. So
  the buggy original optimization fails to type-check.

## Scope

Concrete storage is a total function `UInt256 → UInt256`. The bridge
to `EvmYul.State.sload`/`sstore` lives in the companion module
`Spec.Bridge` (work in progress; see the file header).

The Lean parser reserves `to`/`from` — we use `src`/`dst`.
-/

namespace EvmSmith.ERC20.Spec
open EvmYul

/-! ## Slot abstraction -/

/-- The bridge between abstract and concrete. Bundles the slot
function with the two soundness obligations the refinement
preservation theorems use load-bearingly: injectivity and named-slot
disjointness. -/
structure SlotAbstraction where
  /-- Which `UInt256` values count as "addresses". The slot function
      is only required to be injective and disjoint from named slots
      *on this subset*, not on all of `UInt256`. -/
  ValidAddr : UInt256 → Prop
  /-- Which storage slots hold non-balance state (metadata, etc.).
      The optimization's slot function must avoid them. -/
  NamedSlot : UInt256 → Prop
  /-- The slot derivation. Maps a valid address to its storage slot
      in the optimized layout. -/
  slotFn    : UInt256 → UInt256
  /-- **Injectivity** on valid addresses. Distinct valid addresses
      get distinct slots, so users can't alias. -/
  inj       : ∀ a b, ValidAddr a → ValidAddr b →
              slotFn a = slotFn b → a = b
  /-- **Disjointness** from named slots. The slot derivation for a
      valid address never lands on a named slot, so a balance write
      can't corrupt metadata. -/
  disjoint  : ∀ a, ValidAddr a → ¬ NamedSlot (slotFn a)

/-! ## Refinement relation

Concrete storage refines an abstract (balance-map, named-values)
pair iff:
- every valid address's abstract balance is readable from concrete
  storage at the corresponding slot;
- every named slot's concrete value matches its expected value.
-/

def refines (σ : UInt256 → UInt256)
    (bal namedVal : UInt256 → UInt256) (sa : SlotAbstraction) : Prop :=
  (∀ a, sa.ValidAddr a → σ (sa.slotFn a) = bal a) ∧
  (∀ s, sa.NamedSlot s → σ s = namedVal s)

/-! ## Operations

Concrete operations write storage; abstract operations update the
balance map. Operations *don't* touch named slots — that's the
disjointness obligation. -/

def concreteMint (σ : UInt256 → UInt256) (sa : SlotAbstraction)
    (dst amt : UInt256) : UInt256 → UInt256 :=
  Function.update σ (sa.slotFn dst) (σ (sa.slotFn dst) + amt)

def concreteBurn (σ : UInt256 → UInt256) (sa : SlotAbstraction)
    (src amt : UInt256) : UInt256 → UInt256 :=
  Function.update σ (sa.slotFn src) (σ (sa.slotFn src) - amt)

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

Each theorem uses `sa.inj` in the "different valid address" branch
(without it, a write at one user's slot could leak into another's
balance) and `sa.disjoint` in the "named slot must remain untouched"
branch (without it, a balance write could corrupt metadata).

The theorems require `ValidAddr` on every operation's address
inputs — this is the explicit precondition the bytecode patcher /
contract caller has to discharge before invoking. -/

theorem mint_refines
    (σ : UInt256 → UInt256) (bal namedVal : UInt256 → UInt256)
    (sa : SlotAbstraction)
    (h : refines σ bal namedVal sa)
    (dst amt : UInt256) (hDst : sa.ValidAddr dst) :
    refines (concreteMint σ sa dst amt) (absMint bal dst amt) namedVal sa := by
  obtain ⟨hBal, hNamed⟩ := h
  refine ⟨?_, ?_⟩
  · -- Per-address balance.
    intro a hA
    unfold concreteMint absMint
    by_cases hEq : a = dst
    · subst hEq
      rw [Function.update_self, Function.update_self]
      exact congrArg (· + amt) (hBal a hA)
    · have hSlotNe : sa.slotFn a ≠ sa.slotFn dst :=
        fun heq => hEq (sa.inj a dst hA hDst heq)
      rw [Function.update_of_ne hSlotNe, Function.update_of_ne hEq]
      exact hBal a hA
  · -- Named-slot preservation.
    intro s hS
    unfold concreteMint
    -- slotFn dst ≠ s, because slotFn dst is disjoint from named slots.
    have hSlotDisj : sa.slotFn dst ≠ s := by
      intro hEq; exact (sa.disjoint dst hDst) (hEq ▸ hS)
    rw [Function.update_of_ne hSlotDisj.symm]
    exact hNamed s hS

theorem burn_refines
    (σ : UInt256 → UInt256) (bal namedVal : UInt256 → UInt256)
    (sa : SlotAbstraction)
    (h : refines σ bal namedVal sa)
    (src amt : UInt256) (hSrc : sa.ValidAddr src) :
    refines (concreteBurn σ sa src amt) (absBurn bal src amt) namedVal sa := by
  obtain ⟨hBal, hNamed⟩ := h
  refine ⟨?_, ?_⟩
  · intro a hA
    unfold concreteBurn absBurn
    by_cases hEq : a = src
    · subst hEq
      rw [Function.update_self, Function.update_self]
      exact congrArg (· - amt) (hBal a hA)
    · have hSlotNe : sa.slotFn a ≠ sa.slotFn src :=
        fun heq => hEq (sa.inj a src hA hSrc heq)
      rw [Function.update_of_ne hSlotNe, Function.update_of_ne hEq]
      exact hBal a hA
  · intro s hS
    unfold concreteBurn
    have hSlotDisj : sa.slotFn src ≠ s := by
      intro hEq; exact (sa.disjoint src hSrc) (hEq ▸ hS)
    rw [Function.update_of_ne hSlotDisj.symm]
    exact hNamed s hS

theorem transfer_refines
    (σ : UInt256 → UInt256) (bal namedVal : UInt256 → UInt256)
    (sa : SlotAbstraction)
    (h : refines σ bal namedVal sa)
    (src dst amt : UInt256)
    (hSrc : sa.ValidAddr src) (hDst : sa.ValidAddr dst) :
    refines (concreteTransfer σ sa src dst amt) (absTransfer bal src dst amt)
            namedVal sa := by
  obtain ⟨hBal, hNamed⟩ := h
  refine ⟨?_, ?_⟩
  · intro a hA
    unfold concreteTransfer absTransfer
    by_cases hToEq : a = dst
    · subst hToEq
      rw [Function.update_self, Function.update_self]
      by_cases hFromEq : a = src
      · subst hFromEq
        rw [Function.update_self, Function.update_self]
        show σ (sa.slotFn a) - amt + amt = bal a - amt + amt
        rw [hBal a hA]
      · have hSlotNe : sa.slotFn a ≠ sa.slotFn src :=
          fun heq => hFromEq (sa.inj a src hA hSrc heq)
        rw [Function.update_of_ne hSlotNe, Function.update_of_ne hFromEq]
        show σ (sa.slotFn a) + amt = bal a + amt
        rw [hBal a hA]
    · have hSlotToNe : sa.slotFn a ≠ sa.slotFn dst :=
        fun heq => hToEq (sa.inj a dst hA hDst heq)
      rw [Function.update_of_ne hSlotToNe, Function.update_of_ne hToEq]
      by_cases hFromEq : a = src
      · subst hFromEq
        rw [Function.update_self, Function.update_self]
        show σ (sa.slotFn a) - amt = bal a - amt
        rw [hBal a hA]
      · have hSlotFromNe : sa.slotFn a ≠ sa.slotFn src :=
          fun heq => hFromEq (sa.inj a src hA hSrc heq)
        rw [Function.update_of_ne hSlotFromNe, Function.update_of_ne hFromEq]
        exact hBal a hA
  · intro s hS
    unfold concreteTransfer
    have hSlotDisjSrc : sa.slotFn src ≠ s := by
      intro hEq; exact (sa.disjoint src hSrc) (hEq ▸ hS)
    have hSlotDisjDst : sa.slotFn dst ≠ s := by
      intro hEq; exact (sa.disjoint dst hDst) (hEq ▸ hS)
    rw [Function.update_of_ne hSlotDisjDst.symm,
        Function.update_of_ne hSlotDisjSrc.symm]
    exact hNamed s hS

/-! ## The `~addr` instance, with all four obligations discharged

`ValidAddr a := a.toNat < 2^160`         (real 160-bit address)
`NamedSlot s := s ∈ {0, 1, 2, _TOTAL_SUPPLY_SLOT}` (Solady's layout)
`slotFn   := UInt256.lnot`
`inj`      from `lnot_injective`
`disjoint` from `lnot a >= 2^256 - 2^160` for any 160-bit `a`,
           and every named slot is `< 2^160`. -/

/-- Solady's `_TOTAL_SUPPLY_SLOT`. Pinned for the disjointness proof. -/
def soladyTotalSupplySlot : UInt256 := UInt256.ofNat 0x05345cdf77eb68f44c

/-- "Real address" predicate: low-160-bits-clean. -/
def IsValidAddress (a : UInt256) : Prop := a.toNat < 2^160

/-- The set of named slots Solidity / Solady puts non-balance state at. -/
def IsSoladyNamedSlot (s : UInt256) : Prop :=
  s = ⟨0⟩ ∨ s = UInt256.ofNat 1 ∨ s = UInt256.ofNat 2
  ∨ s = soladyTotalSupplySlot

/-- For any 160-bit address, `(lnot a).toNat ≥ 2^256 - 2^160`. -/
private lemma lnot_toNat_ge_of_valid (a : UInt256) (h : IsValidAddress a) :
    (UInt256.lnot a).toNat ≥ UInt256.size - 2^160 := by
  rw [EvmYul.UInt256.lnot_toNat]
  -- size - 1 - a.toNat ≥ size - 2^160
  unfold IsValidAddress at h
  -- a.toNat < 2^160, so size - 1 - a.toNat > size - 1 - 2^160 ≥ size - 2^160 - 1
  -- And size - 1 - (2^160 - 1) = size - 2^160. So we need:
  --   size - 1 - a.toNat ≥ size - 2^160
  -- ⟺ size - 2^160 ≤ size - 1 - a.toNat
  -- ⟺ a.toNat + 1 ≤ 2^160      (subtracting both from size - 1)
  -- ⟺ a.toNat < 2^160          ✓
  have : 2^160 ≤ UInt256.size := by unfold UInt256.size; decide
  omega

/-- Every Solady named slot is `< 2^160`. -/
private lemma soladyNamedSlot_lt_2_160 (s : UInt256) (h : IsSoladyNamedSlot s) :
    s.toNat < 2^160 := by
  unfold IsSoladyNamedSlot at h
  rcases h with h | h | h | h
  all_goals subst h
  all_goals decide

/-- The disjointness obligation: `~a ∉ namedSlots` for any 160-bit `a`. -/
private lemma lnot_disjoint_from_named (a : UInt256) (hA : IsValidAddress a) :
    ¬ IsSoladyNamedSlot (UInt256.lnot a) := by
  intro hN
  have h1 : (UInt256.lnot a).toNat ≥ UInt256.size - 2^160 :=
    lnot_toNat_ge_of_valid a hA
  have h2 : (UInt256.lnot a).toNat < 2^160 :=
    soladyNamedSlot_lt_2_160 _ hN
  have : UInt256.size ≤ 2^160 + 2^160 := by omega
  -- UInt256.size = 2^256, which is way bigger than 2^161. Contradiction.
  have hsize : UInt256.size > 2^160 + 2^160 := by
    unfold UInt256.size; decide
  omega

/-- `lnot` restricted to 160-bit inputs is injective (specialisation
of the full injectivity). -/
private lemma lnot_injective_on_valid :
    ∀ a b, IsValidAddress a → IsValidAddress b →
           UInt256.lnot a = UInt256.lnot b → a = b := by
  intros a b _ _ h
  exact EvmYul.UInt256.lnot_injective h

/-- **The opt-side slot abstraction, fully discharged.** All four
fields constructed without sorries. Type-checks iff the slot function
is injective on valid addresses AND disjoint from the named slots.
A bad slot function would fail one or both proofs. -/
def lnotSlotAbstraction : SlotAbstraction where
  ValidAddr := IsValidAddress
  NamedSlot := IsSoladyNamedSlot
  slotFn    := UInt256.lnot
  inj       := lnot_injective_on_valid
  disjoint  := lnot_disjoint_from_named

/-! ## Why `id` is rejected by the framework

A would-be `idSlotAbstraction` (the original buggy version):

```lean
def idSlotAbstraction : SlotAbstraction where
  ValidAddr := IsValidAddress
  NamedSlot := IsSoladyNamedSlot
  slotFn    := id
  inj       := -- ✓ id is injective
  disjoint  := -- ✗ id 0 = 0 ∈ named, so no proof exists
```

The `disjoint` field requires `∀ a, IsValidAddress a → ¬ IsSoladyNamedSlot (id a)`,
i.e., for any 160-bit address `a`, `a ∉ {0, 1, 2, _TOTAL_SUPPLY_SLOT}`.
This is **false** at `a = 0` (which has `0.toNat = 0 < 2^160`,
so `IsValidAddress 0`, and `IsSoladyNamedSlot 0`). The structure
cannot be instantiated. The bad optimization is type-rejected.
-/

end EvmSmith.ERC20.Spec
