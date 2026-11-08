"""Route K with Tian-Yuan-Zhang in place of Kriz: same search as descent_search.py ('first' driver),
but a curve C_d that needs the converse must also satisfy TYZ's criterion (Smith's determinant
form, tyz_smith.tyz), which gives analytic rank 1 hence rank 1 and finite Sha by
Gross-Zagier-Kolyvagin."""
import sys
import descent_search as ds
from sel2cong import selmer, vec_of, first_coord_contains
from tyz_smith import tyz


def good_tyz(d, beta):
    if ds.sqf_int(beta * d) == 1 or ds.sqf_int(-beta * d) == 1:
        return "torsion"
    basis, gens = selmer(d, ds.oddprimes(d))
    if len(basis) != 3 or not first_coord_contains(basis, vec_of(beta, gens)):
        return None
    return "tyz" if tyz(abs(d)) else None


ds.good = good_tyz
sys.argv = [sys.argv[0]] + sys.argv[1:]
ds.main()
