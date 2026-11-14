#!/bin/bash
# Generate the library modules ZInQKernel/OneProof/H/*.lean from the newest leaf fold's olean chain (scratch/$FOLD/olean,
# made by scratch/$FOLD/assemble.sh; module order from scratch/$FOLD/chain.sh) and ZInQKernel/OneProof/TopChain.lean from
# scratch/frontier/TopChain.lean. Sources are copied verbatim; only the import lines naming chain modules change
# (`import TailA` becomes `import ZInQKernel.OneProof.H.TailA`), and TopChain loses its #print lines.
# FOLD=leaf-fold4: the H chain proves HDec.HSyn.sixContactMin_of_open4 (TailK).
set -euo pipefail
cd "$(dirname "$0")/../.."
FOLD=${FOLD:-leaf-fold4}
S=scratch/$FOLD/olean
O=ZInQKernel/OneProof
MODS=$(sed -n 's/^MODS="\(.*\)"$/\1/p' scratch/$FOLD/chain.sh)
[ -n "$MODS" ] || { echo "no MODS in scratch/$FOLD/chain.sh"; exit 1; }
rm -f "$O"/H/*.lean
mkdir -p "$O/H"
pat=$(echo $MODS | tr ' ' '|')
for m in $MODS; do
  sed -E "s/^import ($pat)\$/import ZInQKernel.OneProof.H.\\1/" "$S/$m.lean" > "$O/H/$m.lean"
done
grep -v -E '^#print' scratch/frontier/TopChain.lean > "$O/TopChain.lean"
wc -l "$O"/H/*.lean "$O/TopChain.lean" | tail -1
