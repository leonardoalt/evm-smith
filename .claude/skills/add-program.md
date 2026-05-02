---
name: add-program
description: Add a new EVM bytecode program (sequence of opcodes) to the evm-smith repo. Creates `EvmSmith/Demos/<Name>/Program.lean` and wires it into the library index. Use when introducing a new example contract or a target for verification; pair with the `prove-program` skill to write its correctness proof.
---

# Adding a new program

A program is a Lean value of type `EvmSmith.Program` — a list of
`(Operation .EVM × Option (UInt256 × Nat))` pairs. Optionally you can
also emit the raw bytecode as a `ByteArray` for documentation or for
feeding to a real EVM interpreter.

The worked example is `EvmSmith/Demos/Add3/Program.lean`. Copy its shape.

## Steps

1. **Pick a name.** Use PascalCase, e.g. `MulThree`, `SafeTransfer`.
   The directory is `EvmSmith/Demos/<Name>/` and the namespace is
   `EvmSmith.<Name>`.

2. **Create `EvmSmith/Demos/<Name>/Program.lean`.** Skeleton:

   ```lean
   import EvmSmith.Framework

   /-! # The <name> program

       Short description of what it does.

       Assembly (with PCs):
       ```
         pc  bytes              mnemonic
         0   60 00              PUSH1 0x00
         …
       ```
   -/

   namespace EvmSmith.<Name>
   open EvmYul EvmYul.EVM

   /-- One-liner describing `program`. -/
   def program : EvmSmith.Program :=
     [ (.Push .PUSH1, some (UInt256.ofNat 0, 1))
     , (.CALLDATALOAD, none)
     , …
     ]

   /-- Optional: raw bytecode matching the assembly listing. -/
   def bytecode : ByteArray := ⟨#[
     0x60, 0x00,   -- PUSH1 0
     0x35,         -- CALLDATALOAD
     …
   ]⟩

   end EvmSmith.<Name>
   ```

   If the program naturally splits into phases (e.g. compute vs.
   store-and-return, as in Add3), define each phase as a separate
   `Program` value and compose with `++`. The compute-only prefix is
   often the part you can actually prove correctness of; see the
   `prove-program` skill for why.

3. **Register in `EvmSmith.lean`** (the library index) by adding
   `import EvmSmith.Demos.<Name>.Program`.

4. **Build to check:**
   ```bash
   lake build EvmSmith.Demos.<Name>.Program
   ```

5. **Optional: add a `#guard` structural check** in
   `EvmSmith/Demos/Tests.lean`:
   ```lean
   #guard EvmSmith.<Name>.program.length == <expected>
   #guard EvmSmith.<Name>.bytecode.size == <expected>
   ```

## Opcode reference

Common opcodes, with their constructor in `Operation .EVM`:

| Mnemonic       | Constructor              | Arg?                  |
|----------------|--------------------------|-----------------------|
| `STOP`         | `.STOP`                  | none                  |
| `ADD`/`MUL`/…  | `.ADD` / `.MUL` / …      | none                  |
| `LT`/`GT`/`EQ` | `.LT` / `.GT` / `.EQ`    | none                  |
| `ISZERO`       | `.ISZERO`                | none                  |
| `AND`/`OR`/… | `.AND` / `.OR` / `.XOR`  | none                  |
| `SHL`/`SHR`    | `.SHL` / `.SHR`          | none                  |
| `POP`          | `.POP`                   | none                  |
| `MLOAD`/`MSTORE`| `.MLOAD` / `.MSTORE`    | none                  |
| `SLOAD`/`SSTORE`| `.SLOAD` / `.SSTORE`    | none                  |
| `CALLDATALOAD` | `.CALLDATALOAD`          | none                  |
| `RETURN`/`REVERT`| `.RETURN` / `.REVERT`  | none                  |
| `PUSH0`..`PUSH32`| `.Push .PUSH0..PUSH32` | some (value, width)   |
| `DUP1`..`DUP16`| `.Dup .DUP1..DUP16`      | none                  |
| `SWAP1`..`SWAP16`| `.Exchange .SWAP1..SWAP16` | none              |
| `JUMP`/`JUMPI` | `.JUMP` / `.JUMPI`       | none                  |
| `JUMPDEST`     | `.JUMPDEST`              | none                  |

The full list is in `EVMYulLean/EvmYul/Operations.lean`. For `PUSH<n>`,
the `arg` is `(value, n)` where `n` is the immediate width in bytes.

## After the program compiles

Use the `prove-program` skill to write its correctness theorem. If your
program uses an opcode not yet covered by `EvmSmith/Lemmas.lean`, use
the `add-opcode-lemma` skill first.
