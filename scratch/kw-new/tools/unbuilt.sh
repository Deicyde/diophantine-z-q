#!/bin/bash
# count oct16 modules of the KW closure unbuilt here / built in tc-port
cd ~/dzq-wt/kw-new
new=$(sed 's/^TauCeti/ZInQKernel.Contrib.TauCeti/' ~/dzq-runs/tc/kw-new-nov01.txt)
t=0; n=0
for m in $(cat ${1:-/tmp/kwloc.txt}); do
  echo "$new" | grep -qx "$m" && continue
  p=$(echo $m | tr . /).olean
  if [ ! -f .lake/build/lib/lean/$p ]; then t=$((t+1)); [ -f ~/dzq-wt/tc-port/.lake/build/lib/lean/$p ] && n=$((n+1)); fi
done
echo "oct16 unbuilt here: $t ; of which built in tc-port: $n"
