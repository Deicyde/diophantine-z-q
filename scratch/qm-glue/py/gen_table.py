# Emit the Lean table lemmas (tab_x4, tab_x6, tab_x4i, tab_x6i) from table.py's computation.
import subprocess, re, sys
from fractions import Fraction as F
exec(open(__file__.replace("gen_table.py","table.py")).read().split("print(\"inv x4")[0])
def lq(q):
    q = F(q)
    return f"({q.numerator})" if q.denominator == 1 else f"({q.numerator} / {q.denominator})"
def lB(x): return "⟨" + ", ".join(lq(t) for t in x) + "⟩"
for gname, g in gens.items():
    print(f"theorem tab_{gname} (i : Fin 4) : ∃ (k : Fin 4) (r : ℚ) (u : PkgI1.B), r ≠ 0 ∧ PkgI1.InO u ∧ nrd u = 1 ∧")
    print(f"    {gname} * rep i = ((r : ℚ) : PkgI1.B) * rep k * u := by")
    print(f"  fin_cases i")
    for i, r_i in enumerate(reps):
        y = mul(g, r_i); n = nrd(y)
        k = cls_of[sqfree_class(n)]
        r2 = n / nrd(reps[k]); r = F(math.isqrt(r2.numerator), math.isqrt(r2.denominator))
        u = sc(1/r, mul(inv(reps[k]), y)); c = [int(t) for t in coords(u)]
        print(f"  · refine ⟨{k}, {lq(r)}, {lB(u)}, by norm_num, (inO_iff _).2 ⟨{c[0]}, {c[1]}, {c[2]}, {c[3]}, by ext <;> norm_num⟩,")
        print(f"      by norm_num [nrd], ?_⟩")
        print(f"    ext <;> simp [rep, x4, x6, x4i, x6i, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,\n      QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num")
    print()
