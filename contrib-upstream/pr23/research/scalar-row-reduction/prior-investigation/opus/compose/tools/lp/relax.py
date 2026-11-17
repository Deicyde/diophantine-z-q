import json, sys, copy
sys.path.insert(0, __file__.rsplit('/',1)[0])
from lp import solve
d=json.load(open(sys.argv[1]))
for drop in sys.argv[2:]:
    dd=copy.deepcopy(d); dd['residuals']=[r for r in dd['residuals'] if not any(r['name'].startswith(x) for x in drop.split(','))]
    print('== drop',drop); solve(dd)
