import Compiler.CompileDriver
import TinyDiamond

/-! `lake exe tinydiamond-compile OUT_DIR`: Yul, ABI and storage layout of TinyDiamond. -/

open Compiler.CompilationModel in
/-- The `fallback` entrypoint syntax carries neither `payable` nor a reentrancy disposition.
Solidity's fallback is `payable`; its `delegatecall` runs the facet *as* the diamond, so
reentrancy is not a cross-contract question here: the facet is trusted with the whole
storage (README, Security). -/
def patchFallback (spec : CompilationModel) : CompilationModel :=
  { spec with functions := spec.functions.map fun f =>
      if f.name == "fallback" then { f with isPayable := true, reentrancyTrusted := true }
      else f }

def main (args : List String) : IO UInt32 := do
  let out := args.headD "out"
  IO.FS.createDirAll out
  Compiler.compileSpecsWithOptions [patchFallback Diamond.TinyDiamond.spec] out false [] {}
    none none none (some out)
  pure 0
