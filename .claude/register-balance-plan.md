# Register balance-monotonicity — plan (v2)

## Goal

Prove that after any transaction, the Register contract's balance
never decreases. "Our contract never spends ETH" — regardless of what
external contracts do, regardless of reentrance.

This is a simpler proof than Weth's sum-over-storage invariant and
should build reusable tooling (generic frame lemmas, `simp [Θ]` unfold
pattern, precompile one-shot frame) that we can bring back to Weth.

## Program modification

Extend Register's bytecode to make a `CALL` to `CALLER` with value = 0
and forwarded gas *after* the `SSTORE`. This exercises reentrance.

Proposed new program (20 bytes):

```
pc  bytes        mnemonic          effect
0   60 00        PUSH1 0           calldata offset
2   35           CALLDATALOAD      x = cd[0..32]
3   33           CALLER            sender
4   55           SSTORE            storage[sender] = x
5   60 00        PUSH1 0           retSize   (pushed first → bottom of call-args)
7   60 00        PUSH1 0           retOffset
9   60 00        PUSH1 0           argsSize
11  60 00        PUSH1 0           argsOffset
13  60 00        PUSH1 0           value = 0
15  33           CALLER            addr
16  5a           GAS               gas   (pushed last → top; matches pop7 order)
17  f1           CALL
18  50           POP               discard success flag
19  00           STOP
```

Stack-top ordering verified: CALL's `pop7` pops head-first from the
cons-list stack, and `push v s = v :: s` puts new values on top. So
last-pushed `GAS` is popped first as the CALL's `gas` operand, and
first-pushed `retSize` is popped last — matches EVM spec order
`gas, to, value, inOff, inSize, outOff, outSize`.

The value pushed at pc 13 is hard-coded to 0 — this is the structural
fact that makes balance-monotonicity hold.

### Existing Proofs.lean theorems

The current `EvmSmith/Demos/Register/Proofs.lean` theorems assert
specific post-states of a 5-step `runSeq` on the old 6-byte program.
They will not compile against the new bytecode. **Plan: delete them**
and replace with a single `sstore_block_result` theorem about the
SSTORE-preceding prefix that `register_balance_mono` can reuse if
needed. If the prefix isn't directly useful, delete entirely.

Foundry-side: update the test contract's etched bytecode; add one
invariant test asserting `address(register).balance` never decreases
under fuzzing.

## Inductive invariant

Use ℕ-valued balance to avoid UInt256 modular-wrap pitfalls:

```lean
def balanceOf (σ : AccountMap .EVM) (C : AccountAddress) : ℕ :=
  (σ.find? C).elim 0 (·.balance.toNat)

def codeAt (σ : AccountMap .EVM) (C : AccountAddress) : Prop :=
  (σ.find? C).map (·.code) = some bytecode
```

**Full inductive invariant (five conjuncts — all load-bearing):**

```lean
structure RegInv (σ : AccountMap .EVM) (A : Substate) (C : AccountAddress)
                 (b₀ : ℕ) : Prop where
  code         : codeAt σ C                  -- code never changes
  bal          : b₀ ≤ balanceOf σ C           -- balance monotone lower bound
  notSD        : C ∉ A.selfDestructSet        -- C never added to self-destruct set
  totalBounded : totalETH σ < UInt256.size    -- sum of all balances bounded

-- The additional boundary hypotheses (NOT part of the inductive invariant,
-- supplied once at transaction entry):
--   C ≠ S_T
--   C ≠ H.beneficiary
--   ∀ a ∈ createdAccounts, a ≠ C          -- C existed before this tx
```

Rationale for each conjunct:
- `code`: needed because Lambda can install bytecode at a newly created
  address; preservation ensures C's code doesn't get overwritten.
  External code can't change C's code (only SELFDESTRUCT→recreate via
  CREATE2-collision, ruled out by the createdAccounts hypothesis).
- `bal`: the thing we're proving.
- `notSD`: if `C` ever entered `A.selfDestructSet`, Υ's equation (87)
  erases it, breaking `bal` and `code`. `SELFDESTRUCT` at Semantics.lean
  adds `Iₐ` (NOT the recipient) to the set, so as long as C's code is
  never the executing `Iₐ` except under Register's own bytecode (which
  contains no `SELFDESTRUCT`), C stays out.
- `notCreate`: CREATE/CREATE2 install code at a newly derived address
  `a`. If `a` happened to equal C, Lambda overwrites C's code. We rule
  this out via the `createdAccounts` hypothesis, stated at transaction
  entry — the caller guarantees that no address created during this tx
  is C. (The addresses CREATE/CREATE2 produce are deterministic
  functions of `Iₐ` and nonce or salt, so the user of the theorem can
  discharge this.)
- `noOverflow`: the ℕ-valued `balanceOf` comparison is unsound if any
  balance wraps. Maintained because: (a) total ETH supply is bounded,
  but Lean doesn't know that; (b) the `addBalance` function
  (`State/AccountOps.lean:37`) is a checked `Option`, returning `.none`
  on overflow — but Θ does a raw `acc.balance + v` insert (no check),
  so we must assume initial σ is well-formed and every value-transfer
  maintains it. Preservation is an obligation every Θ/Lambda step must
  discharge.

## Main theorem

```lean
theorem register_balance_mono
    (fuel : ℕ) (σ σ' : AccountMap .EVM) (A_subst : Substate)
    (H_f : ℕ) (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress) (b₀ : ℕ)
    (hInv : RegInv σ (default : Substate) C b₀)
    (hCS  : C ≠ S_T)
    (hCH  : C ≠ H.beneficiary)
    (hRun : EVM.Υ fuel σ H_f H H_gen blocks tx S_T
              = .ok (σ', _, _, _)) :
    b₀ ≤ balanceOf σ' C
```

## Proof structure — four layers

### Layer 0 — reused from Weth

`EvmSmith/Lemmas/UInt256Order.lean` already provides `Std.TransCmp`,
`ReflCmp`, and `UInt256.sub` bridges. Nothing new.

### Layer 1 — balance / frame lookup helpers

`EvmSmith/Lemmas/BalanceOf.lean`:

- `balanceOf_insert_ne` / `balanceOf_erase_ne` / `balanceOf_increaseBalance_ne`
- `balanceOf_increaseBalance_self` — under no-overflow, gives `balanceOf σ' C = balanceOf σ C + v.toNat`.
- `balanceOf_increaseBalance_ge` — the weaker monotonic form: `balanceOf σ' C ≥ balanceOf σ C` (under no-overflow hypothesis on `σ[A].balance + v`).

Promote from Weth's `Upsilon.lean`: `find?_erase_ne` and the list-of-
addresses fold-erase frame — move to `BalanceOf.lean` or a shared
`FrameOf.lean`.

### Layer 2 — Ξ / Θ preservation of `RegInv`

Joint fuel induction. Each of Ξ, Θ, Lambda preserves `RegInv` at lower
fuel given the IH.

**`Θ_preserves_RegInv`** — the generic-on-code claim:
```lean
theorem Θ_preserves_RegInv
    (fuel : ℕ) ... (C : AccountAddress) (b₀ : ℕ)
    (hInv : RegInv σ A C b₀) (hsC : s ≠ C)
    (hNewC : ∀ a ∈ createdAccounts, a ≠ C) :
    match Θ fuel ... σ A s o r c ... with
    | .ok (createdAccs', σ', _, A', _, _) =>
        RegInv σ' A' C b₀ ∧ (∀ a ∈ createdAccs', a ≠ C)
    | .error _ => True
```

Reasoning (all branches):
- σ'₁ construction:
  - r = C: `balanceOf σ'₁ C = balanceOf σ C + v.toNat` (under RegInv's
    noOverflow for the updated slot). `code` unchanged. `notSD`
    unchanged (Θ never touches `A.selfDestructSet`). `noOverflow`
    preserved at the updated slot by hypothesis (need a `v + balance
    C < 2^256` precondition, which the caller threads in via
    hv_noOverflow on Θ's signature, derived from the transaction's
    gas/value bounds).
  - r ≠ C: frame — σ'₁[C] = σ[C].
- σ₁: `s ≠ C` → σ₁[C] = σ'₁[C].
- Dispatch:
  - Precompile (1..10): single lemma "σ'' ∈ {σ₁, ∅}"; case (a) σ'' = σ₁ gives RegInv monotonic; case (b) σ'' = ∅ → σ' = σ by eq 127, RegInv preserved by hInv.
  - Precompile (≠ 1..10): Θ returns `.ok default` — `default` for the relevant Except is `.ok default tuple`; the default σ'' = ∅ so σ' = σ. RegInv preserved.
  - Code: Ξ runs. .error OutOfFuel throws; other errors and .revert give σ' = σ. .success gives Ξ-returned σ — apply Ξ_preserves_RegInv at fuel-1.

**`Ξ_preserves_RegInv`** — split by codeOwner:

```lean
theorem Ξ_preserves_RegInv
    (fuel : ℕ) ... (C : AccountAddress) (b₀ : ℕ)
    (hInv : RegInv σ A C b₀)
    (hOwnerCode : I_env.codeOwner = C → I_env.code = bytecode)
    (hNewC : ∀ a ∈ createdAccounts, a ≠ C) :
    match Ξ fuel ... σ A ... I_env with
    | .ok (.success (createdAccs', σ', _, A') _) =>
        RegInv σ' A' C b₀ ∧ (∀ a ∈ createdAccs', a ≠ C)
    | .ok (.revert _ _)               => True
    | .error _                        => True
```

Sub-cases:
- `I_env.codeOwner ≠ C`: **generic step-level argument.** Every opcode
  either:
  - Doesn't touch `AccountMap` or `A.selfDestructSet` (most).
  - CALL: goes through Θ at lower fuel — Θ IH.
  - CREATE/CREATE2: goes through Lambda at lower fuel — need
    `Lambda_preserves_RegInv`, same statement as Ξ but for contract
    creation. The `hNewC` conjunct forbids spawning a collision with C.
  - SELFDESTRUCT: adds `Iₐ` (= I_env.codeOwner ≠ C) to
    `A.selfDestructSet`, transfers `Iₐ`'s balance to recipient r. If
    `r = C`: `balanceOf σ' C ≥ balanceOf σ C` (monotonic). If `r ≠ C`:
    unchanged. `C ∉ selfDestructSet` preserved because we add `Iₐ ≠ C`
    (not `r`). `code` preserved. `noOverflow` preserved (Iₐ's new
    balance is 0; r's balance goes up — need a no-overflow precondition
    which the step-level proof must discharge).
  - STATICCALL / DELEGATECALL / CALLCODE: route through `call` which
    calls Θ. Θ IH.
  - BALANCE / SELFBALANCE / EXTCODEHASH / EXTCODESIZE: read-only on
    balance/code; add to accessed-accounts set (which is not in
    selfDestructSet). RegInv untouched.
- `I_env.codeOwner = C ∧ I_env.code = bytecode`: **Register-specific.**
  Register's 20-byte bytecode, walked opcode by opcode:
  - PUSH1 / CALLDATALOAD / CALLER / SSTORE / GAS / POP / STOP: no
    AccountMap or selfDestructSet effect. `code` trivially preserved
    (no SELFDESTRUCT or CREATE). `bal` trivially preserved (balance
    untouched).
  - The single `CALL` at pc 17: goes through Θ at lower fuel with
    `s = C, r = CALLER, v = 0`. But wait — `s = C` violates Θ's
    `hsC : s ≠ C` precondition! This needs careful handling. Options:
    - (A) Widen Θ's claim to allow `s = C`, but add `v = 0` as an
      extra precondition that kicks in when `s = C`.
    - (B) Add a separate Θ-balance-mono variant specifically for the
      "sender = C, value = 0" case: with v = 0, σ₁[C] = σ'₁[C] = σ[C]
      anyway (subtracting 0 is a no-op).
    - Plan: go with (A). Restate Θ's hypothesis as `s ≠ C ∨ v = 0` or
      equivalently `s = C → v = 0`.

**`Lambda_preserves_RegInv`** — same shape as Ξ, for the contract-
creation path. Lambda: (1) increment creator nonce; (2) subtract v
from creator; (3) install account at `a` with balance v (plus any
existing balance); (4) run init code via Ξ; (5) deposit returned bytes
as code. Each step's effect on `RegInv` at C tracked through. `hNewC`
(a ≠ C) rules out the catastrophic code-overwrite.

### Layer 3 — Υ case analysis

```lean
theorem Υ_preserves_RegInv ...
    : RegInv σ default C b₀ → ... → RegInv σ' A' C b₀
```

- Sender prep (Semantics.lean:856): `S_T.balance -= gasLimit*p + blobFee`, nonce += 1. S_T ≠ C → frame.
- Θ / Lambda dispatch: Layer 2.
- Gas refund: `increaseBalance S_T (gStar * p)`. Frame (S_T ≠ C).
- Beneficiary fee: `increaseBalance H.beneficiary fee`. Frame (H.beneficiary ≠ C).
- Selfdestruct sweep (Semantics.lean:941): `A.selfDestructSet.foldl erase`. Layer-2's `notSD` gives `C ∉ selfDestructSet`, so the erase never touches C.
- Dead-account sweep (Semantics.lean:943): `codeAt σ C` implies `C.code = bytecode ≠ empty`, so C is not dead and the erase skips it.
- Tstorage wipe (Semantics.lean:944): `σ.map` that only changes `.tstorage`. `balanceOf` / `codeAt` unchanged; `notSD` is about Substate, also unchanged; `noOverflow` unchanged (balances untouched).

### Proof methodology

Same skeleton-first, progressive-sorry pattern as Weth:
1. State the main theorem and all layer dependencies with sorry.
2. Close Layer 1 (cheap).
3. Layer 2 as joint fuel induction — state all three (Ξ, Θ, Lambda)
   then close them together.
4. Layer 3.
5. Main theorem.

## What we DELIBERATELY avoid

- **Precompile internals.** We prove ONE lemma: "for any precompile,
  `σ'' ∈ {σ₁, ∅}`" by case-split on the precompile index — same form
  as the 4 we already closed on Weth.
- **Walking Θ's entire do-block.** Use `simp only [Θ]` (verified —
  Weth proved this works despite `unfold Θ` / `Θ.eq_def` failing).
- **Storage reasoning.** SSTORE is irrelevant to balance monotonicity.

## Generic tooling that benefits Weth

- `Ξ_preserves_balance_at_non_codeOwner` — generic step-level balance
  frame for any code. Reusable with different invariants.
- Single-shot precompile-frame lemma (σ'' ∈ {σ₁, ∅}). Reusable.
- `simp only [Θ]` / `simp only [Υ]` unfolding patterns. Reusable.
- Joint Ξ / Θ / Lambda fuel induction template. Adapts to Weth's
  `Θ_preserves_I`.
- The `RegInv` bundle pattern (code + invariant + notSD + notCreate +
  noOverflow) — same bundle needed for Weth.

## Files

- `EvmSmith/Demos/Register/Program.lean` — modify bytecode (20 bytes).
- `EvmSmith/Demos/Register/Proofs.lean` — delete existing theorems (they target the old 6-byte program); replace with at most a small `sstore_block_result` if directly reused.
- `EvmSmith/Demos/Register/Invariant.lean` — new: `balanceOf`, `codeAt`, `RegInv`, statement.
- `EvmSmith/Demos/Register/Theta.lean` — new: `Θ_preserves_RegInv` + `Lambda_preserves_RegInv`.
- `EvmSmith/Demos/Register/Xi.lean` — new: `Ξ_preserves_RegInv` with the two codeOwner sub-cases.
- `EvmSmith/Demos/Register/Upsilon.lean` — new: `Υ_preserves_RegInv`.
- `EvmSmith/Demos/Register/BalanceMono.lean` — new: main theorem assembly.
- `EvmSmith/Lemmas/BalanceOf.lean` — new: generic balance-lookup helpers.
- Reuse: `EvmSmith/Lemmas/UInt256Order.lean`.

## Addressing review items

- **(a)** SELFDESTRUCT handled explicitly in Ξ_preserves_RegInv's
  generic sub-case (Layer 2). Not routed through Θ.
- **(b)** `hNewC : ∀ a ∈ createdAccounts, a ≠ C` added as hypothesis
  of Ξ / Θ / Lambda claims, threaded through all frames.
- **(c)** `C ∉ A.selfDestructSet` elevated to the inductive invariant
  `RegInv.notSD`. Preserved in every frame.
- **(d)** `totalBounded : totalETH σ < UInt256.size` added as
  `RegInv.totalBounded`. Inductive because Θ / Lambda / SELFDESTRUCT
  all conserve the ℕ sum of balances. Reuses Weth's Layer 1
  infrastructure for RBMap fold/insert/erase lemmas. See "No-overflow
  mechanism" below for the per-call no-wrap derivation from this
  bound.
- **(e)** Existing `Proofs.lean` theorems will be deleted.
- **CALL-from-C at value=0:** Θ's hypothesis relaxed to `s ≠ C ∨ v = 0`.

## No-overflow mechanism

Per-call no-wrap isn't inductive on its own (Θ can grow a single
balance arbitrarily by repeated value transfers). We resolve this
with a **total-ETH bound** that is monotonically **non-increasing**:

```lean
def totalETH (σ : AccountMap .EVM) : ℕ :=
  σ.foldl (fun acc _a v => acc + v.balance.toNat) 0

-- RegInv's noOverflow replaced by:
totalBounded : totalETH σ < UInt256.size
```

The invariant is **non-increase of `totalETH`**, not conservation. EVM
burns ETH in several places (base-fee portion of gas, blob fee,
same-tx SELFDESTRUCT of self) — all of these only decrease `totalETH`,
so `totalBounded` (a `<` bound) is preserved. Enumeration:

- **Θ value transfer** (`s ≠ s₁`): if `s ∈ σ` and `r ∈ σ` and both
  inserts don't wrap, net zero. Under wrap: `(σ[r].balance + v).toNat`
  can be `< σ[r].balance.toNat + v.toNat`, giving net **decrease**
  (the wrap "burns" by truncation). Either way, non-increase.
- **Θ with `r ∉ σ` and `v ≠ 0`** (Semantics.lean:747-749): Θ inserts a
  **fresh account with balance := v**, with no matching subtract. This
  would *inflate* `totalETH` by `v.toNat` — breaks non-increase. We
  block this by adding a **threaded Θ precondition**:
  `sInSigmaOrZero : s ∈ σ ∨ v = ⟨0⟩`. Under this hypothesis:
  - If `v = 0`: the fresh-r-with-balance-v branch has `σ'₁ = σ`, and
    the subsequent subtract is also a no-op. `totalETH` unchanged.
  - If `s ∈ σ` and `v ≠ 0`: the fresh-r-insert still adds v to total,
    but the subsequent `σ₁.insert s {acc with balance -= v}` subtracts
    v from `s`'s existing balance — net zero (assuming no wrap, which
    we guarantee via the inductive `totalBounded`).
  This precondition is always met inside normal execution because
  CALL's sender is always the executing codeOwner (which is in σ with
  its code installed) and Υ's initial `s = S_T` is in σ by tx
  validity.
- **Lambda (contract creation)**: subtracts v from creator, installs
  new account at `a` with balance := existing + v. Net zero under
  `creator ∈ σ`.
- **SELFDESTRUCT, `r ≠ Iₐ`** (Semantics.lean): transfers `Iₐ`'s
  balance to r, zeros `Iₐ`. Net zero.
- **SELFDESTRUCT, `r = Iₐ`, same-tx** (Semantics.lean:429-431): both
  balances set to 0 — `Iₐ`'s balance is **burned**. Net decrease.
- **Υ sender-prep** (Semantics.lean:856): `S_T.balance -= gasLimit*p +
  calcBlobFee H T`. The blob fee is burned per EIP-4844; the
  `gasLimit*p` is partially refunded (gStar*p) and partially paid to
  beneficiary ((gasLimit - gStar)*f at priority fee `f`), with the
  base-fee component `(gasLimit-gStar)*(p-f)` burned per EIP-1559.
  Both burns mean net decrease of totalETH over the full transaction.
- **Gas refund** (Semantics.lean:934): `increaseBalance S_T (gStar*p)`.
  Offsets part of the prior debit — accounting catches up, totalETH
  partially recovers (still ≤ post-sender-prep bound).
- **Beneficiary fee** (Semantics.lean:939): `increaseBalance
  H.beneficiary ((gasLimit - gStar) * f)`. Again partial recovery.
  The burned base-fee portion is gone — net decrease over sender-prep
  + refund + fee combined.
- **Dead-account sweep** (Semantics.lean:943): erases accounts where
  `Account.emptyAccount = true`, i.e., balance = 0 ∧ nonce = 0 ∧ code
  empty. Balance is 0 → erase removes 0 from the sum. Net zero.
- **Tstorage wipe** (Semantics.lean:944): modifies `tstorage` only;
  balance untouched. Net zero.

So `totalETH` is monotonically non-increasing across Υ, and
`totalBounded` (`totalETH σ < UInt256.size`) is inductive.

**Per-call no-wrap from `totalBounded`:** for any pair `a, b` in σ:
`σ[a].balance.toNat + σ[b].balance.toNat ≤ totalETH σ < UInt256.size`.
When Θ transfers from `s ∈ σ` to `r ∈ σ`:
- `v.toNat ≤ σ[s].balance.toNat`.
- `σ[r].balance.toNat + v.toNat ≤ σ[r].balance.toNat + σ[s].balance.toNat
   ≤ totalETH σ < 2^256` — no wrap.

**Layer 1 reuse:** proving `totalETH` non-increase requires the RBMap
foldl/insert/erase lemma infrastructure already in
`EvmSmith/Lemmas/RBMapSum.lean` (Weth Layer 1, sorry-free). The
definitions are structurally identical to Weth's `totalBalance`;
either generalize the existing file or add a parallel
`totalETH_ofAccountMap` using the same machinery.

## Threaded Θ preconditions

Accumulated list that every caller of Θ (Υ and Ξ) must discharge:

- `sInSigmaOrZero : s ∈ σ ∨ v = ⟨0⟩` — see above. Υ provides via tx
  validity; Ξ provides because CALL always has s = codeOwner ∈ σ.
- `hNewC : ∀ a ∈ createdAccounts, a ≠ C` — prevents CREATE collision
  with C.
- (Boundary, for the `r = C` balance-add step) no-wrap: derived
  locally from `totalBounded`.
