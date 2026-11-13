#!/bin/bash
# usage: scratch/hodge-bc2/ctail.sh PART  -- compile `import HBCPrefix` + PART against the prefix olean
cd ~/dzq-wt/hodge-bc2
d=scratch/hodge-bc2
{ echo "import HBCPrefix"; cat "$1"; } > $d/Tail.lean
LP=$(lake env printenv LEAN_PATH)
LEAN_PATH=$d/olean:$LP timeout 1500 lean $d/Tail.lean 2>&1 | grep -v "^Note:\|^Hint:\|^$\|linter\|^  \[apply\]" 
