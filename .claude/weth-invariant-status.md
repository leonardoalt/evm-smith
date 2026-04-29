# Weth invariant: paused status

**Paused on 2026-04-19** to refocus on a simpler balance-monotonicity
invariant for the Register demo (`.claude/register-balance-plan.md`).
The Weth skeleton compiles; 11 named `sorry`s remain at known
attack-surface boundaries. Branch `main` is clean.

## What got closed

- **Layer 0** (`EvmSmith/Lemmas/UInt256Order.lean`): `Std.TransCmp` /
  `OrientedCmp` / `ReflCmp` instances for `UInt256` (bridged through
  `.val` to the `Fin UInt256.size` Batteries instance), plus three
  subtraction bridge lemmas (`sub_toNat_of_le`, `sub_add_cancel_of_le`,
  `sub_le_self_of_le`) under `b ≤ a`. Sorry-free.
- **Layer 1** (`EvmSmith/Lemmas/RBMapSum.lean`): `ℕ`-valued
  `totalBalance` + insert/erase sum behaviour (L1-A..G), including a
  from-scratch `del_toList_filter` since Batteries has no upstream
  erase permutation lemma. Sorry-free.
- **Shared defs** (`EvmSmith/Demos/Weth/Invariant.lean`): `I`,
  `totalBalance` (re-export), `codeAt`, `initial_state`, and the base
  cases `I_initial` / `codeAt_initial`. Sorry-free.
- **Layer 3 frame lemmas** (`EvmSmith/Demos/Weth/Upsilon.lean`):
  `increaseBalance_find?_ne` (+ `I` / `codeAt` corollaries),
  `find?_erase_ne` (via Layer 1's `erase_toList_filter` bridged to
  `AccountMap`), `erase_fold_frame`, `C_not_dead_of_codeAt`,
  `I_of_tstorage_wipe` / `codeAt_of_tstorage_wipe`.
- **Layer 2 helpers** (`EvmSmith/Demos/Weth/Theta.lean`): `I_σ'₁` /
  `codeAt_σ'₁` (recipient-update preserves both; uses the no-overflow
  hypothesis for `r = C`), `I_σ₁_of_ne` / `codeAt_σ₁_of_ne` (sender-
  update when `s ≠ C`), and precompile-frame for 4 of 10 (ECREC,
  SHA256, RIP160, ID).

## What remains open (11 sorries)

- `Weth_Ξ_preserves_I` — the program-specific bytecode walk (actual
  content of the proof).
- `Ξ_frame_preserves_I` — reentrance case; needs joint fuel IH with Θ.
- `Θ_preserves_I` succ case — mechanical case dispatch (~25 leaves).
- `Υ_preserves_I` — same do-block unfold obstacle as Θ.
- `find?_tstorage_wipe` — RBMap.map's fold+insert has no upstream
  lemma; need a from-scratch argument like Layer 1's erase bridge.
- `Ξ_*_returns_input_or_empty` for 6 precompiles (EXPMOD, BN_ADD,
  BN_MUL, SNARKV, BLAKE2_F, PointEval). See "why this is wrong scope"
  below.

## Key discoveries

1. **`simp only [Θ]` unfolds Θ even though `unfold Θ` fails.** Same
   should apply to `Υ`, `Ξ`, `X`, etc. `Θ.eq_def` fails to generate
   with "failed to generate unfold theorem" but `simp only [Θ]` just
   works. This unblocked the agent attempts at case analysis.
2. **The proof framing has been too bottom-up.** We ended up dragging
   in precompile-internals reasoning because we tried to prove
   `Θ_preserves_I` by walking every branch of Θ's dispatch. The right
   framing is two claims:
   - **Local:** Weth's bytecode, running under `Ξ` at `codeOwner = C`,
     preserves `I σ C`. This is the only program-specific content.
   - **Frame:** Θ / Ξ running at `codeOwner ≠ C` (or at a precompile
     address ≠ C) yields `σ'.find? C = σ.find? C`. This is a purely
     generic claim — it never inspects what precompiles or other
     contracts compute, only that they don't touch C's slot.

   Under this framing, the 6 precompile internals sorries disappear —
   they were proving properties we don't need. Likewise, the 10-way
   dispatch on precompile number collapses into a single "precompile
   address ≠ C ⇒ frame" claim.

3. **`ℕ`-valued totalBalance sidesteps UInt256 modular wrap.** A
   design pivot during Layer 1 implementation. Without it, the "sum ≤
   balance" comparison is meaningless when the sum wraps.

## When we resume Weth

The planned refactor is:
- **Delete** the 6 unclosed precompile input-or-empty sorries. Replace
  with a single generic frame argument.
- **Re-state** Layer 2 as: (1) `Weth_Ξ_preserves_I` (local, program-
  specific); (2) `Ξ_frame_preserves_I` + `Θ_preserves_find?_C` (purely
  generic frame, no bytecode introspection).
- **Reuse** what we learned on Register (see
  `.claude/register-balance-plan.md`) — the balance-monotonicity
  invariant there is structurally easier and will force us to build
  the right tooling (generic frames, bytecode-walk helpers) before
  bringing them back to Weth.

## Upstreamable

Everything proved here could in principle be upstreamed to EVMYulLean
(semantic-spec lemmas like `Θ_zero = .error .OutOfFuel`, precompile
frame lemmas, `simp [Θ]`-style equations). We're keeping them local
per user decision (`.claude/weth-invariant-plan-review-1.md` §7
context).
