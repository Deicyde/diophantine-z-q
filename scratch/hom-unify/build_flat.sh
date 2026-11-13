#!/bin/bash
# Single-file check of scratch/hom-unify/HomUnifyFlat.lean (one Lean process).
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
python3 scratch/hom-unify/py/assemble.py
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env lean scratch/hom-unify/HomUnifyFlat.lean > scratch/hom-unify/flat_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
echo "errors: $(grep -c 'error' scratch/hom-unify/flat_out.txt)  sorry: $(grep -ci 'sorry' scratch/hom-unify/flat_out.txt)"
python3 - <<'PY'
import re
t = open('scratch/hom-unify/flat_out.txt').read()
reps = re.findall(r"depends on axioms: \[([^\]]*)\]", t)
bad = [r for r in reps if ' '.join(r.split()) != 'propext, Classical.choice, Quot.sound']
print('axiom reports:', len(reps), 'non-standard (line wraps joined):', len(bad))
PY
