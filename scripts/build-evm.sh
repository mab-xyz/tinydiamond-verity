#!/bin/bash
# Compile TinyDiamond from Verity to Yul (lake exe tinydiamond-compile) and the Yul to EVM
# creation bytecode in out/TinyDiamond.bin, which the Foundry tests deploy (test/VerityDeploy.sol).
set -euo pipefail
cd "$(dirname "$0")/.."
SOLC=${SOLC:-$HOME/.svm/0.8.33/solc-0.8.33}
lake exe tinydiamond-compile out >/dev/null 2>out/compile.log || { cat out/compile.log >&2; echo "tinydiamond-compile failed" >&2; exit 1; }
for yul in out/*.yul; do
  name=$(basename "$yul" .yul)
  "$SOLC" --strict-assembly --evm-version cancun --optimize --bin "$yul" \
    2>/dev/null | awk '/Binary representation:/{getline; print; exit}' | tr -d '\n' > "out/$name.bin"
  [ -s "out/$name.bin" ] || { echo "no bytecode for $name" >&2; exit 1; }
done
