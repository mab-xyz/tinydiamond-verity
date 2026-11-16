#!/bin/bash
# Mutation testing of the Foundry suites against the compiled TinyDiamond: each mutant edits
# out/TinyDiamond.yul (sed), rebuilds out/TinyDiamond.bin, and must make at least one test fail.
# Prints one line per mutant: KILLED, SURVIVED or INVALID (sed changed nothing / Yul rejected).
# Exit 1 if any mutant is not KILLED.
set -uo pipefail
cd "$(dirname "$0")/.."
SOLC=${SOLC:-$HOME/.svm/0.8.33/solc-0.8.33}
scripts/build-evm.sh || exit 1
forge build -q || exit 1
cp out/TinyDiamond.yul out/TinyDiamond.yul.orig
cp out/TinyDiamond.bin out/TinyDiamond.bin.orig
bad=0
mutant() {
  local name=$1 expr=$2
  sed "$expr" out/TinyDiamond.yul.orig > out/TinyDiamond.yul
  if cmp -s out/TinyDiamond.yul out/TinyDiamond.yul.orig; then echo "INVALID $name (no change)"; bad=1; return; fi
  "$SOLC" --strict-assembly --evm-version cancun --optimize --bin out/TinyDiamond.yul 2>/dev/null \
    | awk '/Binary representation:/{getline; print; exit}' | tr -d '\n' > out/TinyDiamond.bin
  if [ ! -s out/TinyDiamond.bin ]; then echo "INVALID $name (Yul rejected)"; bad=1; return; fi
  if forge test >/dev/null 2>&1; then echo "SURVIVED $name"; bad=1; else echo "KILLED $name"; fi
}
mutant admin-check-removed     's/if iszero(or(iszero(iszero(eq(sender, adm))), iszero(iszero(eq(sender, me))))) {/if 0 {/'
mutant self-not-admin          's/iszero(iszero(eq(sender, me)))/0/'
mutant immutable-check-removed 's/if iszero(eq(builtin, 0)) {/if 0 {/'
mutant builtin-list-short      's/iszero(iszero(eq(key, 115585352413088217508186738910231190654473486319250918280203599598957117833216)))/0/'
mutant not-found-check-removed 's/if iszero(iszero(eq(target, 0))) {/if 0 {/'
mutant restriction-ignored     's/if iszero(or(iszero(iszero(eq(r, 0))), iszero(iszero(eq(r, sender))))) {/if 0 {/'
mutant restriction-blocks-all  's/iszero(iszero(eq(r, sender)))/0/'
mutant revert-payload-dropped  's/revert(0, __returndata_size)/revert(0, 0)/'
mutant return-payload-dropped  's/return(0, returndatasize())/return(0, 0)/'
mutant selector-unmasked       's/let key := and(calldataload(0), [0-9]*)/let key := calldataload(0)/'
mutant fallback-not-payable    's/let key := and(calldataload(0)/if callvalue() { revert(0, 0) }\n&/'
mutant receive-reverts         's/if __is_empty_calldata {/& revert(0, 0)/'
mutant swap-skipped            's/if iszero(eq(index, lastIndex)) {/if 0 {/'
mutant position-off-by-one     's/__ret0 := add(n, 1)/__ret0 := n/'
mutant pop-bits-not-cleared    's/internal_internal_setSelectorAt(lastIndex, 0)//'
mutant packing-shift-lost      's/or(cleared, shl(s, v))/or(cleared, v)/'
mutant noop-cut-emits          's/if iszero(eq(old, target)) {/if 1 {/'
mutant cut-action-wrong        's/internal_internal_emitCut(target, 1, key)/internal_internal_emitCut(target, 0, key)/'
mutant restrict-not-stored     's/sstore(mappingSlot(4856191523366929523863144626492751294936335913391771255401221336565096728322, key), target)/sstore(mappingSlot(4856191523366929523863144626492751294936335913391771255401221336565096728322, key), 0)/'
mutant calldata-truncated      's/calldatacopy(0, 0, calldatasize())/calldatacopy(0, 0, sub(calldatasize(), 1))/'
mutant call-not-delegatecall   's/let ok := delegatecall(\([0-9]*\), target,/let ok := call(\1, target, 0,/'
mutant constructor-no-admin    's/and(deployer, 0xffffffffffffffffffffffffffffffffffffffff)/0/'
mutant constructor-no-event    's/log1(512, 512, /pop(/'
cp out/TinyDiamond.yul.orig out/TinyDiamond.yul
cp out/TinyDiamond.bin.orig out/TinyDiamond.bin
rm -f out/TinyDiamond.yul.orig out/TinyDiamond.bin.orig
exit $bad
