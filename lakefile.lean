import Lake
open Lake DSL

package «tinydiamond-verity» where
  version := v!"0.1.0"

-- Verity: upstream main (lfglabs-dev/verity, bc161da0b). TinyDiamond needs none of the fork features.
require verity from git
  "https://github.com/lfglabs-dev/verity.git"@"bc161da0bafab296e54d9918b56a3d9018de5916"

@[default_target]
lean_lib «TinyDiamond» where
  globs := #[.andSubmodules `TinyDiamond]

/-- Emits Yul + ABI for TinyDiamond: `lake exe tinydiamond-compile OUT_DIR`. -/
lean_exe «tinydiamond-compile» where
  root := `TinyDiamondCompile
  supportInterpreter := true
