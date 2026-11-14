"""Print the number of anonymous sections (`noncomputable section`, `section`) left open at the end of a
Lean file, so that the assembly can close them before the part's own `end` (leaf-fold3)."""
import re, sys
n = 0
inblock = 0
for l in open(sys.argv[1]).read().split('\n'):
    if re.match(r'^(noncomputable )?section\s*(--.*)?$', l): n += 1
    elif re.match(r'^end\s*(--.*)?$', l): n -= 1
print(max(n, 0))
