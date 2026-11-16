#!/bin/bash
# build one module, show only diagnostics from the abhyankar files
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
cd ~/dzq-wt/abhyankar
lake build "$1" > /tmp/abh_build.log 2>&1
st=$?
python3 - <<'PY'
import re
lines=open('/tmp/abh_build.log').read().split('\n')
out=[];keep=False
for l in lines:
    if re.match(r'^(error|warning|info): ',l) or l.startswith('✔') or l.startswith('⚠') or l.startswith('✖'):
        keep = ('Abhyankar' in l) and not l.startswith('✔')
    if keep: out.append(l)
print('\n'.join(out[:150]))
PY
tail -2 /tmp/abh_build.log
exit $st
