import Compiler.CompileDriver
import TinyDiamond

/-! `lake exe tinydiamond-compile OUT_DIR`: Yul, ABI and storage layout of TinyDiamond. -/

def main (args : List String) : IO UInt32 := do
  let out := args.headD "out"
  IO.FS.createDirAll out
  Compiler.compileSpecsWithOptions [Diamond.TinyDiamond.spec] out false [] {}
    none none none (some out)
  pure 0
