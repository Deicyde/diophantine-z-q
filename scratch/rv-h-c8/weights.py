# Exact enumeration: which (k, n) make HT(rho_g (x) psi) = {0,-1} (Tate convention: cyclotomic chi
# has HT weight -1; n = HT weight of the twisting character psi = eta*chi^(-n)).
# HOM: rho_g with arithmetic-Frobenius trace a_l, det = eps*chi^(k-1): HT {0, 1-k}  (k>=2)
# COH: rho_g^vee (geometric-Frobenius trace a_l, Pan's notation),  HT {0, k-1}
# k=1: finite image (Deligne-Serre), HT {0,0} in both.
from collections import Counter
target = Counter([0, -1])
def wts(norm, k):
    if k == 1: return [0, 0]
    return [0, 1 - k] if norm == "HOM" else [0, k - 1]
for norm in ("HOM", "COH"):
    sols = [(k, n) for k in range(1, 201) for n in range(-300, 301)
            if Counter(w + n for w in wts(norm, k)) == target]
    print(norm, "solutions (k,n) with 1<=k<=200, |n|<=300:", sols)
    # determinant consistency: det r5 = chi * finite has HT weight -1;
    # det(rho_g (x) psi) weight = sum(wts) + 2n
    for k, n in sols:
        assert sum(wts(norm, k)) + 2 * n == -1
    # what fails if k=1 is NOT known to have weights {0,0} (e.g. wrongly {0,1-k}={0,0} anyway)
# k=0 / negative weights: excluded since S_k = 0 for k <= 0
print("det check passed for all solutions")
