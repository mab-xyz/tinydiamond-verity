import Lake
open Lake DSL

package «tinydiamond-verity» where
  version := v!"0.1.0"

-- Verity: upstream main (lfglabs-dev/verity, 45578f33a). TinyDiamond needs none of the fork features.
require verity from git
  "https://github.com/lfglabs-dev/verity.git"@"45578f33a29bf27d391a0b53719cc980cc69ee5c"

@[default_target]
lean_lib «TinyDiamond» where
  globs := #[.andSubmodules `TinyDiamond]

/-- Emits Yul + ABI for TinyDiamond: `lake exe tinydiamond-compile OUT_DIR`. -/
lean_exe «tinydiamond-compile» where
  root := `TinyDiamondCompile
  supportInterpreter := true
