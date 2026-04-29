# Review 1 — `Weth` plan

## 1. Bytecode correctness — real bug

**Dispatch stack bug at withdraw entry.** Tracing dispatch:
- After DUP1: `[selector, selector]`
- After PUSH4 depositSel / EQ: `[eq?, selector]` (EQ consumed one selector + the PUSH4 value)
- After PUSH2 / JUMPI for deposit: both branches leave `[selector]`
- Fall-through: `[selector]`. PUSH4 withdrawSel / EQ consumes the sole remaining selector → `[eq?]`
- PUSH2 / JUMPI for withdraw: both branches leave `[]`

**So deposit entry stack is `[selector]` (correct); withdraw entry stack is `[]`**. The plan's `POP` on line 86 (withdraw block) is a stack underflow. Fix: remove the POP from withdraw entry. Alternatively add a second DUP1 before the withdraw EQ to preserve symmetry, but that wastes a byte.

Also: the plan's `deposit_block_success` (line 279-291) takes `hs : s0.stack = selector :: stk_tail`. It should be `hs : s0.stack = [selector]` (exactly one element), since nothing is underneath after dispatch.

Other bytecode items verified correct: SSTORE arg order in deposit (SWAP1 is load-bearing); LT gate in withdraw; 7-arg CALL push order (retSize, retOff, argsSize, argsOff, value, to, gas — top of stack last); checks-effects-interactions ordering (SSTORE before CALL).

## 2. Reentrancy — correct reasoning, make the test mandatory

The reasoning is right: a reentrant call sees already-decremented `storage[attacker]`, so `LT` on `(balance, x')` for any `x' > remainingBalance` triggers revert. The EIP-150 63/64 rule still caps gas available to the reentrant call but doesn't help the attacker.

Recommend promoting the Foundry reentrancy test from "worth adding" (plan line 488) to **mandatory**: a concrete `test_Weth_reentrancy_does_not_drain` that deploys a malicious fallback contract and attempts recursive withdraw. Currently aspirational.

## 3. Conservation invariant — overstated Lean feasibility

### Storage half
The plan claims it's "provable — the storage write is straightforward" (line 195). It isn't. Conservation's storage half requires `RBMap.foldl_insert` / `foldl_erase` lemmas:
- `foldl f init (t.insert k v)` when `k ∈ t`: replaces old value.
- `foldl f init (t.insert k v)` when `k ∉ t`: adds v.
- Similar for erase.

None of these exist in Batteries (verified with `grep`). This is another Batteries-PR-sized gap, not lines.

**Recommendation**: drop the full Conservation invariant from Lean. Replace with a narrower proved statement:

> `deposit` and `withdraw_success` change exactly one slot (the sender's) by exactly the expected delta, other slots unchanged.

That's provable today (the `program_updates_caller_account` + `program_preserves_other_accounts` pattern from Register). The Foundry invariant test then takes responsibility for the cross-transaction multi-user conservation claim — which is what invariant testing is *for*.

### ETH-balance half
Correct to declare out of scope. Alternative (reviewer's option): don't state Conservation in Lean at all; rely on Foundry. **Recommend this.**

## 4. Scope blowups

### `runOp_jumpi_{taken,not_taken}`
Checked upstream at `EvmYul/Semantics.lean:528`. μ₀ = destination, μ₁ = condition. Two lemma variants (for condition = 0 vs non-zero) should each close by `rfl` on the concrete-shape input. **Fine.**

Real novelty the plan understates: after a taken JUMPI, `pc` is NOT `s0.pc + 1` but the destination. Block-level theorems must take the block-start `pc` as a *parameter* and output equations of the form "the post-pc equals the destination address" rather than the `s0.pc + offset` pattern Register uses everywhere. The plan does flag `hpc : s0.pc = <blockStartPc>` at line 285, good, but should explicitly say block proofs work with arbitrary starting `pc` and don't accumulate offsets across JUMPI.

### DUP5 / SWAP2 on deep stacks
Upstream `EvmYul.step`'s `dup n` / `swap n` at `Semantics.lean:119-134` use `List.getLast!`, `List.tail!.dropLast`, `List.head!` — partial ops. Concrete-shape lemmas should close by `rfl` since the list is a concrete cons-list, but the normal form may be larger than usual. **Recommendation**: prove `runOp_dup3`, `runOp_dup5`, `runOp_swap2` as a spike BEFORE chaining them in the withdraw block proof. If `rfl` falters, fall back to `unfold; simp`.

### Chain depth
Withdraw-precall is ~17 ops. Register's chain was 5. Step-lemma `runSeq_cons_ok`-based chains should scale linearly. Flag: `whnf` timeout at Lean's defaults is 200000 heartbeats; a 17-step chain with a large state structure could push it. **Mitigation**: `set_option maxHeartbeats 400000` locally if needed.

## 5. Dispatch decoding — correct

`SHR` order in `Semantics.lean:276`: `dispatchBinary τ (flip UInt256.shiftRight)`. So on `[0xe0, word]`, pops μ₀=0xe0, μ₁=word, result = `shiftRight word 0xe0` = word >> 224. Correct. `PUSH4 0xd0e30db0` pushes uint256 `0x00…00d0e30db0`. EQ compares. Correct.

## 6. Foundry invariant testing — plan missing the handler pattern

The plan at lines 357-367 proposes `invariant_sum_balances_equals_contract_balance` but doesn't specify how the fuzzer generates calls against the etched bytecode. Without a Solidity ABI for the etched address, `targetContract(wethAddress)` doesn't work — the fuzzer can't discover selectors.

Standard pattern: a **handler contract** with `deposit(uint256 v)` / `withdraw(uint256 x)` methods that do the low-level `.call{value:v}(selector)` + accounting into ghost variables. `targetContract(handler)` in setUp. Example:

```solidity
contract WethHandler is Test {
    address public immutable weth;
    address[] public actors;
    mapping(address => uint256) public ghostBalance;
    uint256 public ghostTotalDeposited;

    function deposit(uint256 amtRaw, uint256 actorSeed) public {
        uint256 amt = _bound(amtRaw, 0, 100 ether);
        address a = _pickActor(actorSeed);
        vm.deal(a, amt);
        vm.prank(a);
        (bool ok,) = weth.call{value: amt}(hex"d0e30db0");
        if (ok) { ghostBalance[a] += amt; ghostTotalDeposited += amt; }
    }
    // ... withdraw similar ...
}
```

Then the invariant is:
```solidity
function invariant_conservation() public view {
    uint256 sum;
    for (uint256 i = 0; i < handler.actorCount(); i++) {
        sum += uint256(vm.load(weth, bytes32(uint256(uint160(handler.actors(i))))));
    }
    assertLe(sum, weth.balance);  // weakened to ≤, see §7
}
```

**Add this to the plan explicitly.**

## 7. Force-fed ETH — weaken Invariant 4 to `≤`

Anyone can `SELFDESTRUCT` into an address to increase its balance without triggering the contract's receive. Post-Cancun, SELFDESTRUCT still transfers value in-same-tx. Coinbase beneficiaries similarly. These break `Σ storage[a] = accountMap[C].balance` as equality.

The defensible safety property is `Σ storage[a] ≤ accountMap[C].balance` — **user funds are never lost**, the contract always has at least enough ETH to honor all withdrawals. **Change the stated invariant from equality to `≤`** and fix the Foundry invariant test accordingly.

## 8. Selector endianness — correct, no issue.

## 9. Other

- **Gas**: plan should explicitly state Lean proofs are gas-unaware (Foundry covers gas behaviour).
- **`runOp_revert`**: REVERT in `runSeq` produces `.error`; the `runSeq_cons_ok` fusion lemma only handles `.ok`. Need either a `runSeq_cons_err` fusion lemma or stop the chain at the branch taking REVERT and conclude with a direct equality. Plan doesn't mention this — flag.
- **Contract funding**: contract starts with 0 ETH; users deposit. Implied, should be stated.

## Summary

The plan is substantive and mostly correct. Fixes before implementation:

1. **Bytecode bug**: remove `POP` at withdraw entry (stack is `[]`, not `[selector]`). Fix `deposit_block_success` signature to `hs : s0.stack = [selector]`.
2. **Conservation invariant**: drop the Lean statement; rely on Foundry invariant testing. Replace in Lean with narrower per-call storage-delta theorems.
3. **Foundry invariant test**: specify the **handler contract pattern** with ghost variables and `targetContract(handler)`. Without this, the fuzzer doesn't exercise the bytecode.
4. **Weaken Invariant 4 to `≤`** to handle force-fed ETH.
5. **Mandatory reentrancy test** (not aspirational).
6. **Spike DUP5 / SWAP2 lemmas first** before relying on them in the withdraw block chain.
7. **Clarify block-level pc parametrization** after JUMPI.
8. **Mention REVERT chain termination** (separate from `runSeq_cons_ok`).
9. **Explicit gas-unaware disclaimer** on the Lean side.

None are architectural. With these the plan is implementable.

VERDICT: needs revision
