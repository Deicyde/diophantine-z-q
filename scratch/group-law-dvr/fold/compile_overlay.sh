#!/bin/bash
# usage: compile_overlay.sh VARIANT_DIR [START]  (e.g. /tmp/gldfold/F1; patched sources in VARIANT_DIR/src;
#   START = first index of downstream-modules.txt to compile, default 1)
# Recompiles, in topological order, the modules of scratch/group-law-dvr/fold/downstream-modules.txt into the
# overlay VARIANT_DIR/lib (first on LEAN_PATH); unpatched modules are compiled from the worktree's sources.
V=$1
START=${2:-1}
cd ~/dzq-wt/group-law-dvr; export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
LP=$(lake env printenv LEAN_PATH)
export LEAN_PATH=$V/lib:$LP
mkdir -p $V/logs
# symlink tree of the worktree's build (Lean resolves a module inside the first LEAN_PATH entry that has its
# top-level package directory); rebuilt modules replace their symlinks
[ -d $V/lib/ZInQKernel ] || { mkdir -p $V/lib && cp -as $PWD/.lake/build/lib/lean/ZInQKernel $V/lib/ZInQKernel; }
i=0
while read m; do
  i=$((i+1))
  [ $i -lt $START ] && continue
  p=${m//.//}.lean
  if [ -f $V/src/$p ]; then src=$V/src/$p; root=$V/src; else src=$p; root=.; fi
  out=$V/lib/${m//.//}
  mkdir -p $(dirname $out)
  for x in olean ilean; do [ -L $out.$x ] && unlink $out.$x; done
  s=$(date +%s)
  lean -R $root -o $out.olean -i $out.ilean $src > $V/logs/$i.txt 2>&1
  rc=$?
  echo "$i $m rc=$rc $(( $(date +%s)-s ))s errors=$(grep -c 'error' $V/logs/$i.txt)"
  [ $rc -ne 0 ] && break
done < scratch/group-law-dvr/fold/downstream-modules.txt
