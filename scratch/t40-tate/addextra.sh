#!/bin/bash
# usage: addextra.sh TauCeti.X  -- generate extras file for vendored module X and redirect Backport imports
cd ~/dzq-wt/t40-tate
m=$1; r=${m#TauCeti.}
echo $m >> scratch/t40-tate/extras-list.txt
python3 scratch/t40-tate/extras.py $m scratch/t40-tate/backport-main.txt
f=ZInQKernel/Contrib/TauCeti/Backport/$(echo $r | tr . /).lean
for g in $(grep -rl "import ZInQKernel.Contrib.$m\$" ZInQKernel/Contrib/TauCeti/Backport); do
  [ "$g" = "$f" ] && continue
  sed -i "s/import ZInQKernel\.Contrib\.TauCeti\.$r\$/import ZInQKernel.Contrib.TauCeti.Backport.$r/" $g; echo "  redirected $g"
done
