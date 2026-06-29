import EvmYul.Wheels
import EvmSmith.Demos.Groth16.Program

/-!
# Dump `Groth16.bytecode` as hex for the Foundry tests

Writes the runtime bytecode into
`EvmSmith/Demos/Groth16/foundry/test/Groth16.bytecode.hex`, the same
pattern `Demos/Weth/DumpBytecode.lean` uses — `foundry/test/Groth16.t.sol`
reads this file with `vm.etch` to deploy the bytecode for testing.

Run from the repo root: `lake exe groth16-dump-bytecode`.
-/

open EvmSmith

def main : IO Unit :=
  IO.FS.writeFile
    "EvmSmith/Demos/Groth16/foundry/test/Groth16.bytecode.hex"
    ("0x" ++ EvmYul.toHex Groth16.bytecode ++ "\n")
