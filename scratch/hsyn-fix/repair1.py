import re,sys
p='docs/research/h-decomposition.md'
s=open(p).read()
def rep(old,new,count=1):
    global s
    n=s.count(old)
    if n!=count: print("MISMATCH",n,repr(old[:70])); return
    s=s.replace(old,new)
rep("""`TYZThm35ReadingA` is the intended reading of their Theorem 3.5(2), with
  the hypothesis weakened to `𝓛(n) = 0`;""","""`TYZThm35ReadingA` is the intended reading of their Theorem 3.5(2), used only in the case
  `𝓛(n) = 0`. That case is a special case of the printed hypothesis "`2^{−ρ(n)}𝓛(n)` even", and
  it does not depend on the unproved "i.e." of Theorem 3.5(2) (`docs/research/nt-tyz.md` §2.2, F6);""")
rep("both NEW and unreviewed (hdec-elementary §2.2);","both new (hdec-elementary §2.2), verified as arguments by one adversarial model review\n(rv-routek) with repairs 1-4 of §1 pending, and with no human review;")
rep("""Glazer's Brauer and
cochain steps B2-B3 from four textbook leaves, ending in `[L':ℚ] ≤ Q·M`;""","""Glazer's Brauer and
cochain steps B2-B3, ending in `[L':ℚ] ≤ Q·M`, from four textbook statements: T30, T31 and
glue-descent's cochain forms of T14-T15 (`LeafHasse`, `LeafLocalTwo`). Deriving those two forms
from the T14-T15 leaves as bundled is glue that is not yet proved (WP3);""")
rep("from T14-T15 (glue-descent forms), T30, T31","from glue-descent's cochain forms of T14-T15 (`LeafHasse`, `LeafLocalTwo`; their derivation from `PkgI6.BrauerHasse2`, `BrauerReciprocity2`, `LocalH2Card` is unproved, WP3), T30, T31")
rep("and **21\nglue steps**:","and **20\nglue steps** (G1-G20, composed in G0):")
rep("plus 21 glue steps;","plus 20 glue steps;")
rep("the whole arithmetic of the repository's Lemma PR(i) and NoCM;","the valuation case analysis and the identities of the repository's Lemma PR(i) (not Prop. TS or\nLemma NV), and the explicit part of NoCM (not the count from R5);")
rep("""Reasons. (i) A leaf must be a refereed published theorem; K2 (Ribet 1992) and the converse
direction of Pyle appeared in proceedings whose refereeing is UNVERIFIED, while every route-P
modularity leaf is a journal paper (Pan in JAMS).""","""Reasons. (i) A leaf must be a refereed published theorem. K2 (Ribet 1992) and the converse
direction of Pyle appeared in proceedings whose refereeing is UNVERIFIED. Route P's modularity
leaves are journal papers (Pan in JAMS) except R14 for `k ≥ 2`, which cites Deligne's Bourbaki
exposé (Sém. Bourbaki 355, 1971). Route P has the same question for R1 (Deligne, Sém. Bourbaki
389; Shimura 1967 in Ann. of Math. is the primary source), R21 (Bost, Sém. Bourbaki 795) and the
SGA citations (R6, R8, T1, T2). These are standard sources, but whether they count as refereed
should be stated, not assumed.""")
rep("""The other 12
research-level and 7 textbook leaves are named placeholders that carry no content until their
definitions exist.""","""The other 12
research-level and 7 textbook leaves are `opaque` placeholders with no content. Each needs new
definitions (cheap for T29 and T32, up to very large for R1-R3, R5, R16, R18-R22) before it can
be stated.""")
rep("and 25 textbook leaves, 35 of 54, are stated concretely","and 25 textbook leaves, 35 of 54 (33 stated individually, R11 and R12 only through their joint\nconsequence), are stated concretely")
rep("(with T18, T19 for \"every semisimple `ρ` with these\ntraces\")","(with T25 to pass from an eigenform to a newform, and T18, T19 for \"every semisimple `ρ`\nwith these traces\"; if the printed Thm 4.1 covers every eigenform of the `T_p`, `p ∤ N`, T25 is\nnot needed: UNVERIFIED)")
open(p,'w').write(s)
