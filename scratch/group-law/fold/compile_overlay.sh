#!/bin/bash
# usage: compile.sh FROM TO  (1-based indices into /tmp/gl_down.txt)
cd ~/dzq-wt/group-law; export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
LP=$(lake env printenv LEAN_PATH)
export LEAN_PATH=/tmp/glfold/lib:$LP
i=0
while read m; do
  i=$((i+1))
  [ $i -lt $1 ] && continue
  [ $i -gt $2 ] && break
  p=${m//.//}.lean
  if [ -f /tmp/glfold/src/$p ]; then src=/tmp/glfold/src/$p; root=/tmp/glfold/src; else src=$p; root=.; fi
  out=/tmp/glfold/lib/${m//.//}
  mkdir -p $(dirname $out)
  s=$(date +%s)
  lean -R $root -o $out.olean -i $out.ilean $src > /tmp/glfold/log_$i.txt 2>&1
  rc=$?
  echo "$i $m rc=$rc $(( $(date +%s)-s ))s errors=$(grep -c 'error' /tmp/glfold/log_$i.txt)"
  [ $rc -ne 0 ] && break
done < /tmp/gl_down.txt
