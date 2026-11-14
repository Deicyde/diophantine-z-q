#!/bin/bash
# compile the flat file AssemblePort.lean (one Lean process); output in flat_out.txt (host paths stripped)
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
F=scratch/assemble-port/AssemblePort.lean
uptime | sed 's/.*load/load/'; free -g | sed -n 2p; md5sum $F; wc -l < $F
start=$(date +%s)
lake env lean $F > /tmp/ap_flat_raw.txt 2>&1; rc=$?
sed "s#$PWD/##g" /tmp/ap_flat_raw.txt > scratch/assemble-port/flat_out.txt
echo "exit $rc in $(( $(date +%s) - start ))s"
echo "errors: $(grep -c ': error' scratch/assemble-port/flat_out.txt)  sorry: $(grep -c "declaration uses 'sorry'" scratch/assemble-port/flat_out.txt)"
