#!/bin/bash
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
cd ~/dzq-wt/rv-wave17
for b in leaf-push_Push leaf-push_PushDR glue-c10_C10 glue-c10_Trace glue-a6-alg_A6 glue-a6-alg_Quat glue-a6-alg_Extend glue-d1-local_Local; do
  s=$(date +%s)
  timeout 1500 lake env lean scratch/rv-wave17/chk/$b.lean > scratch/rv-wave17/chk/$b.out 2>&1
  echo "$b exit=$? secs=$(( $(date +%s)-s ))" >> scratch/rv-wave17/chk/status.txt
done
echo ALLDONE >> scratch/rv-wave17/chk/status.txt
