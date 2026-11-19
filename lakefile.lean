import Lake
open Lake DSL

package «tinydiamond-verity» where
  version := v!"0.1.0"

-- Verity: upstream main 76d25f370 plus the mab-xyz fork features (branch int/upstream-2026-11-19).
require verity from git
  "https://github.com/mab-xyz/verity.git"@"96f7c02f1d63c4e999052fcbc31be6208a5baf2d"

@[default_target]
lean_lib «TinyDiamond» where
  globs := #[.andSubmodules `TinyDiamond]

/-- Emits Yul + ABI for TinyDiamond: `lake exe tinydiamond-compile OUT_DIR`. -/
lean_exe «tinydiamond-compile» where
  root := `TinyDiamondCompile
  supportInterpreter := true
