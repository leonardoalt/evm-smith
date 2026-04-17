import Lake
open Lake DSL

package «evmSmith» where
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]

require evmyul from "EVMYulLean"

@[default_target]
lean_lib «EvmSmith»

lean_exe «evm-smith» where
  root := `EvmSmith.Demos.Main
