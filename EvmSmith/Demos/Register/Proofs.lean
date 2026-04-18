import EvmSmith.Lemmas
import EvmSmith.Demos.Register.Program

/-!
# Correctness of the `Register` program

## Theorems (all proved, no `sorry`)

1. **`program_result`** — exact post-state of `runSeq program s0`.
   Structural equation; every other theorem follows.
2. **`program_updates_caller_account`** — after the call,
   `accountMap[codeOwner] = some (acc.updateStorage (addressSlot
   sender) x)`. The "the write happened" claim at the map level.
3. **`program_preserves_other_accounts`** — for any address `a ≠
   codeOwner`, `accountMap.find? a` is unchanged.

## Why no slot-level theorems here

A natural fourth theorem would be "`storageAt postState codeOwner
(addressSlot sender) = x`" — a surface restatement of (2) pushing
through `Account.updateStorage` and `RBMap.findD`. It is **not**
provable with the current Batteries API:

- The RBMap lemmas `find?_insert_of_eq` and `find?_insert_of_ne` are
  parameterised on `[Std.TransCmp cmp]` — they need a
  `LawfulOrd`-like instance on the key type.
- For `AccountAddress = Fin 2^160`, Batteries registers
  `LawfulOrd (Fin n)` (`Batteries/Classes/Order.lean:277`), so
  theorem 3 closes via `find?_insert_of_ne` directly.
- For `UInt256` (a single-field structure wrapping `Fin 2^256`),
  the derived `Ord` instance exists (`UInt256.lean:25: deriving
  BEq, Ord`) but **no `LawfulOrd UInt256`** is registered — neither
  by the upstream repo nor by the derivation itself. Without it,
  the `TransCmp` synthesis fails and the slot-level lemmas are
  unreachable.
- Additionally, `RBMap.erase` has **no theorems at all** in
  Batteries, so the `x = 0` case (which routes through
  `Account.updateStorage`'s erase branch) would need to be proved
  from scratch even with a working `LawfulOrd UInt256`.

See `.claude/batteries-wishlist.md` for the two specific items a
Batteries upstream PR would need to add to unblock the slot-level
theorems here (plus ours in `EvmSmith/Lemmas.lean`). For now, a
downstream who needs slot-level claims can either provide
`LawfulOrd UInt256` themselves and derive the slot lemmas, or
reason about the account via `program_updates_caller_account` and
inspect `Account.updateStorage` directly.

## How theorems 2 and "slot-level functional correctness" relate

`program_updates_caller_account` is strictly stronger at the
account-map level: it tells you the account is `acc.updateStorage
sender x`. Every slot-level claim follows once you can reason
about `updateStorage`'s effect on `storage`:

- For `x ≠ 0`: `updateStorage sender x = {acc with storage :=
  storage.insert sender x}`, so `storage.findD sender ⟨0⟩ = x` via
  `find?_insert_of_eq` — needs `TransCmp compare` on `UInt256`.
- For `x = 0`: `updateStorage sender x = {acc with storage :=
  storage.erase sender}`, so `storage.findD sender ⟨0⟩ = ⟨0⟩ = x`
  via `find?_erase_self` — needs that lemma to exist upstream.

So the slot-level claim is not vacuous given theorem 2, but closing
it requires infrastructure we don't have.

## Precondition

Theorems 2 and 3 take `hacct : s0.accountMap.find? codeOwner = some
acc`. `SSTORE` is a silent no-op if the account doesn't exist; the
Foundry tests install a real account via `vm.etch`.

## What's deliberately not preserved

Theorem 3 (account frame) is stated on `accountMap` only, not on
the full `toState`. `EvmYul.State.sstore` mutates
`substate.refundBalance` and `substate.accessedStorageKeys`, which
are orthogonal to storage and not covered here by design.
-/

namespace EvmSmith.RegisterProofs
open EvmYul EvmYul.EVM EvmSmith EvmSmith.Register

/-- The exact post-state `runSeq program` produces, given empty
    starting stack. Named once so multiple theorems can refer to it. -/
def postState (s0 : EVM.State) (x : UInt256) : EVM.State :=
  let s1 : EVM.State :=
    { s0 with
        stack := []
        pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 1
                 + UInt256.ofNat 1
        toState := EvmYul.State.sstore s0.toState
                     (addressSlot s0.executionEnv.source) x }
  { s1 with toMachineState := s1.toMachineState.setReturnData .empty }

/-! ## 1. Structural post-state -/

theorem program_result
    (s0 : EVM.State)
    (x : UInt256)
    (hs : s0.stack = [])
    (hx : EvmYul.State.calldataload s0.toState (UInt256.ofNat 0) = x) :
    runSeq program s0 = .ok (postState s0 x) := by
  have hs0 : s0 = { s0 with stack := [], pc := s0.pc } := by cases s0; cases hs; rfl
  have e1 : runOp (.Push .PUSH1) s0 (some (UInt256.ofNat 0, 1))
      = .ok { s0 with stack := [UInt256.ofNat 0], pc := s0.pc + UInt256.ofNat 2 } := by
    rw [hs0]; exact runOp_push1 s0 (UInt256.ofNat 0) [] s0.pc
  have e2 : runOp .CALLDATALOAD
      { s0 with stack := [UInt256.ofNat 0], pc := s0.pc + UInt256.ofNat 2 }
      = .ok { s0 with stack := [x], pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 } := by
    rw [runOp_calldataload]; simp [hx]
  have e3 : runOp .CALLER
      { s0 with stack := [x], pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 }
      = .ok { s0 with
          stack := UInt256.ofNat s0.executionEnv.source.val :: [x]
          pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 1 } :=
    runOp_caller s0 [x] _
  have e4 : runOp .SSTORE
      { s0 with
          stack := UInt256.ofNat s0.executionEnv.source.val :: [x]
          pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 1 }
      = .ok { s0 with
          stack := []
          pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
          toState := EvmYul.State.sstore s0.toState
                       (UInt256.ofNat s0.executionEnv.source.val) x } :=
    runOp_sstore s0 (UInt256.ofNat s0.executionEnv.source.val) x [] _
  have e5 := runOp_stop
    ({ s0 with
         stack := []
         pc := s0.pc + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1
         toState := EvmYul.State.sstore s0.toState
                      (UInt256.ofNat s0.executionEnv.source.val) x } : EVM.State)
  show runSeq program s0 = _
  simp only [program]
  rw [runSeq_cons_ok _ _ _ _ _ e1]
  rw [runSeq_cons_ok _ _ _ _ _ e2]
  rw [runSeq_cons_ok _ _ _ _ _ e3]
  rw [runSeq_cons_ok _ _ _ _ _ e4]
  rw [runSeq_cons_ok _ _ _ _ _ e5]
  simp only [runSeq]
  rfl

/-! ## 2. Caller account update (functional correctness) -/

/-- Note: this theorem is a claim about `postState s0 x` (a pure
    definition), so it doesn't need `s0.stack = []` or a calldata
    hypothesis. Chain it through `program_result` to get the
    corresponding `runSeq program s0`-level statement. -/
theorem program_updates_caller_account
    (s0 : EVM.State)
    (x : UInt256)
    (acc : Account .EVM)
    (hacct : s0.accountMap.find? s0.executionEnv.codeOwner = some acc) :
    (postState s0 x).accountMap.find? s0.executionEnv.codeOwner =
    some (acc.updateStorage (addressSlot s0.executionEnv.source) x) := by
  unfold postState
  show (EvmYul.State.sstore s0.toState
          (addressSlot s0.executionEnv.source) x).accountMap.find?
         s0.executionEnv.codeOwner = _
  rw [sstore_accountMap s0.toState (addressSlot s0.executionEnv.source) x acc hacct]
  exact Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self

/-! ## 3. Account frame -/

/-- Like `program_updates_caller_account`, this is a property of
    `postState s0 x` and doesn't need the stack/calldata hypotheses. -/
theorem program_preserves_other_accounts
    (s0 : EVM.State)
    (x : UInt256)
    (acc : Account .EVM)
    (hacct : s0.accountMap.find? s0.executionEnv.codeOwner = some acc)
    (addr : AccountAddress) (ha : addr ≠ s0.executionEnv.codeOwner) :
    (postState s0 x).accountMap.find? addr = s0.accountMap.find? addr := by
  unfold postState
  show (EvmYul.State.sstore s0.toState
          (addressSlot s0.executionEnv.source) x).accountMap.find? addr =
        s0.accountMap.find? addr
  rw [sstore_accountMap s0.toState (addressSlot s0.executionEnv.source) x acc hacct]
  apply Batteries.RBMap.find?_insert_of_ne
  intro h
  exact ha (Std.LawfulEqCmp.eq_of_compare h)

end EvmSmith.RegisterProofs
