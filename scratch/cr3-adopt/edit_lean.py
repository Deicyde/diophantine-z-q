import re,sys
def edit(p, pairs):
    s=open(p).read()
    for a,b in pairs:
        assert s.count(a)==1, (p, a[:70])
        s=s.replace(a,b)
    open(p,'w').write(s)

# 1. Hypotheses/CertifiedRank.lean: replace the docstring by the cr3-trust §3 draft
p='ZInQKernel/Hypotheses/CertifiedRank.lean'
s=open(p).read()
i=s.index("/-- **Hypothesis CR₃** (certified rank).")
j=s.index("def CertifiedRank : Prop :=")
d=open('docs/research/cr3-trust.md').read()
k=d.index("```lean\n/-- **Hypothesis CR₃** (certified rank).")+len("```lean\n")
l=d.index("```", k)
draft=d[k:l]
assert draft.rstrip().endswith("-/")
s=s[:i]+draft+s[j:]
open(p,'w').write(s)

# 2. Statements.lean: trust paragraphs of CertifiedRankRk and CertifiedRankTYZClRk
def block(name):
    k=d.index("**`RouteK.Rank.%s`**"%name)
    k=d.index("```lean\n",k)+len("```lean\n")
    l=d.index("```",k)
    return d[k:l].rstrip("\n")
p='ZInQKernel/RouteK/Rank/Statements.lean'
s=open(p).read()
i=s.index("**Trust statement.** CR₃^Rk is not proved in Lean.")
j=s.index(" -/\ndef CertifiedRankRk")
s=s[:i]+block("CertifiedRankRk")+s[j:]
i=s.index("**Trust statement.** Not proved in Lean. It is Tian–Yuan–Zhang (arXiv:1411.4728, Theorem 3.5")
j=s.index(" -/\ndef CertifiedRankTYZClRk")
s=s[:i]+block("CertifiedRankTYZClRk")+s[j:]
open(p,'w').write(s)
edit(p,[("""Proposition N: `ord_{s=1} L(C_d, s) = 1`) and Gross–Zagier (`docs/research/pc-audit.md` RK7:
analytic rank one gives `rank C_d(ℚ) ≥ 1`); see `Rank5b.CertifiedRankTYZ` for the precise citations.""",
"""Proposition N: `ord_{s=1} L(C_d, s) = 1`) and Gross–Zagier with an auxiliary imaginary quadratic
field (`docs/research/pc-audit.md` RK7: analytic rank one gives `rank C_d(ℚ) ≥ 1`); see
`CertifiedRankTYZClRk` and `Rank5b.CertifiedRankTYZ` for the precise citations.""")])
