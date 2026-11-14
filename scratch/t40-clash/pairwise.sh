#!/bin/bash
# For each top-level Contrib module M (list file $1), compile a two-import file `import T40; import M`
# with `lake env lean`, one after another; prints OK/FAIL per module.
tmp=scratch/t40-clash/_pair.lean
while read -r m; do
  [ "$m" = ZInQKernel.Contrib.RLeaf.T40 ] && continue
  printf 'import ZInQKernel.Contrib.RLeaf.T40\nimport %s\n' "$m" > $tmp
  out=$(lake env lean $tmp 2>&1)
  if [ -z "$out" ]; then echo "OK   $m"; else echo "FAIL $m :: $(echo "$out" | head -1 | sed "s|$HOME|~|g")"; fi
done < "$1"
rm -f $tmp
