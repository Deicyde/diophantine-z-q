#!/bin/bash
# compile scratch/cpts-transport/$1 against g0-assemble3's olean chain (copied to ~/cpts-olean); output to ${1%.lean}_out.txt
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$HOME/cpts-olean
F=$1
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env bash -c "LEAN_PATH=$D:\$LEAN_PATH lean scratch/cpts-transport/$F" > scratch/cpts-transport/${F%.lean}_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
echo "errors: $(grep -c ': error' scratch/cpts-transport/${F%.lean}_out.txt)  sorry: $(grep -c "declaration uses 'sorry'" scratch/cpts-transport/${F%.lean}_out.txt)"
grep -A12 ": error" scratch/cpts-transport/${F%.lean}_out.txt | head -${2:-100}
echo "--- axioms:"
grep "depends on axioms\|does not depend" scratch/cpts-transport/${F%.lean}_out.txt | head -30
