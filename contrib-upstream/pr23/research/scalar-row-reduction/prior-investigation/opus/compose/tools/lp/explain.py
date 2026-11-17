import json, sys
sys.path.insert(0, __file__.rsplit('/',1)[0])
from lp import solve
from fractions import Fraction as Fr
def explain(d, extra=()):
    v,w,rd=solve(d)
    names={c['id']:c['name'] for c in d['coordinates']}
    W={c['id']:w[c['name']] for c in d['coordinates']}
    for j in list(rd)+[i for i,r in enumerate(d['residuals']) if r['name'] in extra]:
        r=d['residuals'][j]
        print('ROW',r['name'])
        for t in r['terms']:
            e=Fr(t['sPower'])+sum(W[i] for i in t['monomial'])
            print('   %8s  %s*%s'%(e,t['coefficient'],'*'.join(names[i]+'['+str(W[i])+']' for i in t['monomial'])))
if __name__=='__main__':
    explain(json.load(open(sys.argv[1])), sys.argv[2:])
