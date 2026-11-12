import re
p='docs/research/h-decomposition.md'
s=open(p).read()
def sub_between(s, start, end, new):
    i=s.index(start); j=s.index(end, i)+len(end)
    assert s.count(start)==1
    return s[:i]+new+s[j:]
R2new = """**R2. Baba–Granath** (restated by loc-adopt, 2026-11-12, after the locator audit; the statement
replaced 2026-11-12 by loc-fix with the exact text of rv-nocm §3.2). `X₆/W ≅ P¹_j` over `ℚ`. The
orbifold `Γ*\\ℍ` (`Γ* = Γ_W`, the normalizer group) has exactly three elliptic points, at
`j = 0, ∞, −16/27`, of orders 4, 6, 2, the CM points of discriminants −4, −3, −24. Two QM surfaces
with principal polarization of the fixed type have the same polarized moduli point iff their
points of `X₆` are `W`-conjugate. Ref: Canad. J. Math. 60 (2008), Thm 2.1, Lemma 3.1, §3.1
elliptic-order table (p. 740 per locators.md); the numerical `j`-normalization of the labels needs
Prop. 3.6/3.9-Cor. 3.11 or R3 (locators.md). The ramification indices are glue, not part of the
leaf: `X₆ → X₆/W` has index 2 over each of the three values (stabilizers of order 4/2, 6/3, 2/1 in
`W`). The level-three cover `Y₃ → P¹_j` has indices 4, 6, 2 there and is unramified elsewhere,
because `Γ₃` is torsion-free and normal in `Γ*` (`RvNocm.ramification_eq_orbifold_order`).
(Audit details kept from loc-adopt: Thm 2.1 p. 737, Lemma 3.1 pp. 739-740, §3 p. 739, Prop. 3.9
and Thm 3.10 p. 744, Cor. 3.11 p. 745, all read by the audit in the journal text; the 2005
preprint was not located by the audit. Audit verdict: YES for the polarized quotient
identification, a geometric moduli identification, not an equality of arbitrary forms over their
fields of definition; NO for the former statement "branched with indices 4, 6, 2".) E (for the
restated form). Lean: **no** (via R1). Steps A2, A7, and A5, which uses the indices `4, 6, 2` of
`Y₃ → P¹_j` as glue: rv-nocm §2 checked that A5 holds with them (the argument is unchanged; only
the supplier's wording was wrong)."""
s = sub_between(s, "**R2. Baba–Granath** (restated by loc-adopt", "data of `Y₃ → P¹_j`: h-trust A5 note of 2026-11-12).", R2new)
R5new = """**R5. González–Rotger** (corrected by loc-adopt, 2026-11-12, after the locator audit; replaced
2026-11-12 by loc-fix with the exact text of rv-nocm §3.1). Let `R` be an order of conductor `f`,
`(f, 6) = 1`, in an imaginary quadratic field `k` in which neither 2 nor 3 splits. Let
`CM(R) ⊂ X₆(ℚ̄)` be the points of `X₆ = X₀(6,1)` with CM by `R`, let `D(R)` be the product of the
primes `p | 6` inert in `k`, and `b(R) = #{p | D(R)}`. Then (i) `#CM(R) = 2^{b(R)} h(R)`, and
`⟨w_p : p | D(R)⟩ × Gal(H_R/k)` acts simply transitively on `CM(R)`; (ii) for `x ∈ CM(R)`,
`ℚ(x) = H_R` if `D(R) ≠ 1`, and `[H_R : ℚ(x)] = 2` if `D(R) = 1`. Both parts concern points
of `X₆` itself, not their images in `X₆/W` or points of `Y₃`. For example, `R = ℤ[√−6]` maps
to the rational point `j = −16/27` of `X₆/W`, of index 4 in `H_R`. Ref: J. Math. Soc. Japan 58
(2006), Prop. 5.6, Thm 5.12 (arXiv:math/0612732 numbering VERIFIED by rv-h-cm; journal
pp. 943, 946 per locators.md). E (restricted to `(f,6) = 1`, `N = 1`). Lean: **no** (via R1).
Step A10 (NoCM), which uses (i) only when `D(R) = 1`, where it reads `#CM(R) = h(R)`.
(History: the statement before 2026-11-12 read "`#CM(R) = h(R)`", which is false: for `R`
maximal of discriminant −19, `h(R) = 1`, 2 and 3 are inert, and there are four CM points; 15 of
the 24 non-elliptic rows of Elkies' table contradict it, and so does `ℤ[i]`, with `h = 1` and two
points (rv-nocm §1.2). The audit read Prop. 5.6 (p. 943; arXiv v1/v2 p. 15), Thm 5.8
(pp. 943-944) and Thm 5.12 (p. 946) in v1, v2 and the journal. rv-nocm §1 checked that both
proofs of NoCM use only the corrected count, on `X₆`, so the argument is unchanged.)"""
s = sub_between(s, "**R5. González–Rotger** (corrected by loc-adopt", "E (in the corrected form). Lean: **no** (via R1).", R5new)
old2 = """   value; `4, 6, 2` are the elliptic (orbifold) orders of the uniformization, not indices of
   this cover."""
new2 = """   value; `4, 6, 2` are the elliptic (orbifold) orders of the uniformization, not indices of
   this cover. They are the indices of the level-three cover `Y₃ → P¹_j` (glue: `Γ₃` is
   torsion-free and normal in `Γ*`; rv-nocm §2.2, added 2026-11-12 by loc-fix)."""
assert s.count(old2)==1; s=s.replace(old2,new2)
old5 = "   Corrected 2026-11-12: Prop. 5.6 counts `2^{#{p | D(R)N(R)}}·h(R)` CM points, not `h(R)`."
new5 = old5 + "\n   At `N = 1` this is `2^{b(R)} h(R)`, `b(R) = #{p | 6 inert in k}` (rv-nocm §3.1; loc-fix 2026-11-12)."
assert s.count(old5)==1; s=s.replace(old5,new5)
open(p,'w').write(s)
