import EvmYul.Wheels
import EvmSmith.Demos.Weth.Program

/-!
# Dump `Weth.bytecode` as hex for the Foundry tests

Writes the runtime bytecode into
`EvmSmith/Demos/Weth/foundry/test/Weth.bytecode.hex`.

Run from the repo root: `lake exe weth-dump-bytecode`.
-/

open EvmSmith

def main : IO Unit :=
  IO.FS.writeFile
    "EvmSmith/Demos/Weth/foundry/test/Weth.bytecode.hex"
    ("0x" ++ EvmYul.toHex Weth.bytecode ++ "\n")
