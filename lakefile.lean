import Lake
open Lake DSL

package «tinydiamond-verity» where
  version := v!"0.1.0"

-- Verity with the mab-xyz fork fixes (same pin as dex-verity).
require verity from git
  "https://github.com/mab-xyz/verity.git"@"262375bd947ac371cf0a1ec59944a1379818a608"

@[default_target]
lean_lib «TinyDiamond» where
  globs := #[.andSubmodules `TinyDiamond]

/-- Emits Yul + ABI for TinyDiamond: `lake exe tinydiamond-compile OUT_DIR`. -/
lean_exe «tinydiamond-compile» where
  root := `TinyDiamondCompile
  supportInterpreter := true
