#!/bin/bash
# Rerun el-k3's ns_lattice.py / ns_invariants.py / ns_h1.py for several beta (copies with BETA and
# the json path substituted; originals untouched). Usage: k1_rerun.sh BETA
B=$1; D=scratch/rv-elim3/k1_b$B; mkdir -p $D
for f in ns_lattice ns_invariants ns_h1; do
  sed -e "s/^BETA = 7.0/BETA = $B.0/" -e "s#scratch/el-k3/ns_data.json#$D/ns_data.json#" \
      -e "s#scratch/el-k3/ns_inv.json#$D/ns_inv.json#" scratch/el-k3/$f.py > $D/$f.py
done
for f in ns_lattice ns_invariants ns_h1; do ~/pyenv/bin/python $D/$f.py; done
