#!/bin/bash
# usage: buildlist.sh LIST OUTDIR ; builds each module sequentially, logs to OUTDIR/<mod>.log
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
cd ~/dzq-wt/kw-new
mkdir -p $2
for m in $(cat $1); do
  timeout 3000 lake build $m > $2/$m.log 2>&1
  r=$?; e=$(grep -c 'error:' $2/$m.log)
  echo "$m rc=$r errors=$e" >> $2/summary.txt
done
echo DONE >> $2/summary.txt
