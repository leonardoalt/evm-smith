import EvmYul.Wheels
import EvmSmith.Demos.Groth16.Program

/-!
# Dump `Groth16.bytecode` as hex

Writes the runtime bytecode to `EvmSmith/Demos/Groth16/Groth16.bytecode.hex`
— useful for poking at it outside Lean (e.g. `evm disassemble`, an `anvil`
deployment with `cast send --create`, or a `cast call` with hand-built
calldata) once the placeholder verifying-key constants in `Program.lean`
are replaced with a real one.

Run from the repo root: `lake exe groth16-dump-bytecode`.
-/

open EvmSmith

def main : IO Unit :=
  IO.FS.writeFile
    "EvmSmith/Demos/Groth16/Groth16.bytecode.hex"
    ("0x" ++ EvmYul.toHex Groth16.bytecode ++ "\n")
