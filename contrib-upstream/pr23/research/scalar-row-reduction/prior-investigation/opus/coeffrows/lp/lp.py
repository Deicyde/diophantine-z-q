"""Powers-of-S diagonal scaling LP on a hybrid IR (rows with symbolic sPower).
Usage: python lp.py IR.json  -> optimum spread, binding rows (nonzero duals)."""
import sys, json
from collections import Counter, defaultdict
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

def solve(data, fixed=('input',), verbose=True):
    coords, rows = data['coordinates'], data['residuals']
    ids = {c['id']: i for i, c in enumerate(coords)}
    n, m = len(coords), len(rows)
    nterm = sum(2*len(r['terms'])+1 for r in rows)
    A = lil_matrix((nterm, n+2*m+1)); b = np.zeros(nterm); owner=[]
    k = 0
    for j, row in enumerate(rows):
        lo, hi = n+2*j, n+2*j+1
        for t in row['terms']:
            for i, mult in Counter(t['monomial']).items():
                A[k, ids[i]] = mult; A[k+1, ids[i]] = -mult
            A[k, hi] = -1; A[k+1, lo] = 1
            b[k] = -float(Fraction(t['sPower'])); b[k+1] = float(Fraction(t['sPower']))
            owner += [j, j]; k += 2
        A[k, hi] = 1; A[k, lo] = -1; A[k, -1] = -1; owner.append(j); k += 1
    obj = np.zeros(A.shape[1]); obj[-1] = 1
    bounds = [(None, None)]*len(obj)
    for c in coords:
        if c['name'] in fixed: bounds[ids[c['id']]] = (0, 0)
    bounds[-1] = (0, None)
    res = linprog(obj, A_ub=A.tocsr(), b_ub=b, bounds=bounds, method='highs')
    assert res.success, res.message
    dual = res.ineqlin.marginals
    rowdual = defaultdict(float)
    for kk, y in enumerate(dual):
        if abs(y) > 1e-9: rowdual[owner[kk]] += -y
    weights = {c['name']: Fraction(res.x[ids[c['id']]]).limit_denominator(10000) for c in coords}
    if verbose:
        print('optimum spread', res.fun, Fraction(res.fun).limit_denominator(10000))
        for j, y in sorted(rowdual.items(), key=lambda t: -t[1]):
            print('  binding row %4d %-60s dual %.4f' % (j, rows[j]['name'], y))
    return res.fun, weights, rowdual

if __name__ == '__main__':
    d = json.load(open(sys.argv[1]))
    f, w, rd = solve(d)
    if len(sys.argv) > 2:
        json.dump({k: str(v) for k, v in w.items() if v}, open(sys.argv[2], 'w'), indent=1)
