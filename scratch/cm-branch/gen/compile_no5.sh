#!/bin/bash
# compile No5 parts in order; stop at the first part with errors
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
cd ~/dzq-wt/cm-branch
for p in ${@:-A B C D E F}; do
  f=ZInQKernel/Contrib/OneProof/CMBranch/No5$p.lean
  [ -f $f ] || continue
  n=$(timeout 2400 lake env lean $f 2>&1 | tee /tmp/no5_$p.log | grep -c "error")
  echo "No5$p errors: $n"
  if [ "$n" != "0" ]; then grep -E "error" /tmp/no5_$p.log | head -15; exit 1; fi
  timeout 2400 lake build ZInQKernel.Contrib.OneProof.CMBranch.No5$p 2>&1 | grep -E "error|Build completed" | head -2
done
