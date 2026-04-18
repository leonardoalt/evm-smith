import EvmYul.Wheels
import EvmSmith.Demos.Register.Program

/-!
# Dump `Register.bytecode` as hex for the Foundry tests

Writes the runtime bytecode from `Program.lean` as a `0x`-prefixed hex
string into `EvmSmith/Demos/Register/foundry/test/Register.bytecode.hex`.

Run from the repo root: `lake exe register-dump-bytecode`.
-/

open EvmSmith

def main : IO Unit :=
  IO.FS.writeFile
    "EvmSmith/Demos/Register/foundry/test/Register.bytecode.hex"
    ("0x" ++ EvmYul.toHex Register.bytecode ++ "\n")
