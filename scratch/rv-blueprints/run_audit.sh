#!/bin/bash
# Sequential compile of the blueprint Lean files with the appended axiom audit (one Lean process at a time).
cd ~/dzq-wt/rv-blueprints
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
out=scratch/rv-blueprints/audit_out
mkdir -p $out
for b in "$@"; do
  uptime; free -g | sed -n 2p
  s=$(date +%s)
  timeout 1800 lake env lean scratch/rv-blueprints/Audit_$b.lean > $out/$b.txt 2>&1
  echo "exit=$? secs=$(( $(date +%s)-s ))" >> $out/$b.txt
  echo "$b: $(tail -1 $out/$b.txt)"
done
echo ALLDONE
