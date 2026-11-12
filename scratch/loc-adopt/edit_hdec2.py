import sys
p = 'docs/research/h-decomposition.md'
s = open(p).read()
def rep(old, new):
    global s
    n = s.count(old)
    if n != 1:
        sys.exit(f'count {n} for: {old[:80]!r}')
    s = s.replace(old, new)
A = 'Locator audit (2026-11-12, `locators.md`)'

rep("""produces the fibre surface `A` as a Lean object (§6 R6). Formalized: none (Anthropic FLT has QM
fake elliptic curves for Čerednik–Drinfeld; use for `Y₃/ℚ` unchecked). Steps A3-A6, A10.""",
"""produces the fibre surface `A` as a Lean object (§6 R6). Formalized: none (Anthropic FLT has QM
fake elliptic curves for Čerednik–Drinfeld; use for `Y₃/ℚ` unchecked). Steps A3-A6, A10.
""" + A + """: Deligne's §§4.9-4.17, Thm 4.21, Cor. 5.7, Ex. 5.8 (and §1.8, §§3.7-3.13,
Thm 4.19 for the action and reciprocity) were read; printed page mapping not recovered. Verdict:
UNVERIFIED as the full literal leaf, a qualified consequence. Thm 4.21 is the Siegel canonical
model and Ex. 5.8 a PEL model over the reflex field `E(G,h)`; (a) still needs the lattice, the
polarization-compatible level structure, the PEL conditions, the component convention and
`E(G,h) = ℚ` checked (neatness alone does not give them). (c) holds on the tower: at fixed level
only the subgroup preserving the level and the datum acts. (d) keeps the reflex-field
qualifications. Shimura 1967 (Main Thms I-II) and Kottwitz 1992 (§5) were not read: UNVERIFIED.""")

rep("""**R2. Baba–Granath.** `X₆/W ≅ P¹_j`, branched at `0, ∞, −16/27` with indices 4, 6, 2 at CM
discriminants −4, −3, −24; equal polarized moduli points iff `W`-conjugate. Ref: Canad. J. Math.
60 (2008), Thm 2.1, Lemma 3.1 (2005 preprint read by a model). E. Lean: **no** (via R1). Steps
A2, A7.""",
"""**R2. Baba–Granath** (restated by loc-adopt, 2026-11-12, after the locator audit). For the
discriminant-6 curve `V = X₆` with the fixed principally polarized maximal-order datum and its
Atkin–Lehner group `W ≅ (ℤ/2)²`: the forgetful polarized moduli space is `V/W`, and `V/W ≅ P¹_ℚ`
with the three distinguished images rational; two points of `V` give the same polarized moduli
point iff they are `W`-conjugate. The three branch values of the degree-4 map `V → V/W` are
`0, ∞, −16/27` (CM discriminants −4, −3, −24), and the **ramification index of `V → V/W` is 2 at
each of them**. The numbers `4, 6, 2` are the elliptic orders of the orbifold uniformization
`Γ_W\\ℍ → V/W` (the normalizer group), not ramification indices of the degree-4 cover. Ref:
Canad. J. Math. 60 (2008), Thm 2.1 (p. 737), Lemma 3.1 (pp. 739-740), §3 (p. 739), the
elliptic-order table of §3.1 (p. 740), Prop. 3.9 and Thm 3.10 (p. 744), Cor. 3.11 (p. 745), all
read by the audit in the journal text; the 2005 preprint was not located by the audit (it had been
read by a model earlier). Audit verdict: YES for the polarized quotient identification (a
geometric moduli identification, not an equality of arbitrary forms over their fields of
definition); NO for the former statement "branched with indices 4, 6, 2". Thm 2.1 and Lemma 3.1
alone do not fix the numerical normalization of `j` (that comes from R3/R4 and the checks of F1).
E (for the restated form). Lean: **no** (via R1). Steps A2, A7 (and A5, which uses the branch
data of `Y₃ → P¹_j`: h-trust A5 note of 2026-11-12).""")

rep("""**R3. Lin–Yang.** On the finite nonzero `j`-locus, the QM surface over `j` is a genus-2 Jacobian
with `[J₂:J₄:J₆:J₁₀] = [12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]`. Ref: Math. Z. 295 (2020),
Example 30, eqs. (13)-(14) (VERIFIED in arXiv v1 by h-v14; journal numbering UNVERIFIED). E.""",
"""**R3. Lin–Yang.** On the finite nonzero `j`-locus, the QM surface over `j` is a genus-2 Jacobian
with `[J₂:J₄:J₆:J₁₀] = [12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]`. Ref: Math. Z. 295 (2020),
775-819; arXiv:1807.00466v1 **Example 29** (pp. 20-21, discriminant 6), eqs. (13)-(14).
Corrected 2026-11-12 (locator audit): the former locator "Example 30" is v1's example for
discriminant 14 (p. 21 onward); h-v14 had verified the content in arXiv v1 but not the number
(h-v14 row L719: "the published number 30 was not compared"). Journal numbering UNVERIFIED (the
audit did not read the journal body). Alternative supplier of the tuple and of the
finite-nonzero-`j` Jacobian assertion: Baba–Granath, Canad. J. Math. 60 (2008), Prop. 3.6, p. 742
(read by the audit; an alternative source, not a verification of the Lin–Yang citation). The
bracket is weighted-projective: fix the `J`/Igusa–Clebsch convention before using
ordinary-coordinate identities. E.""")

rep("""**R5. González–Rotger.** For orders `R` of conductor `f`, `(f,6)=1`, embeddable in `𝒪`:
`#CM(R) = h(R)` and `ℚ(x)` is `H_R` or of index 2 in it. Ref: J. Math. Soc. Japan 58 (2006),
Thm 5.12, Prop. 5.6 (VERIFIED in arXiv:math/0612732 by rv-h-cm). E (restricted to `(f,6)=1`).
Lean: **no** (via R1). Step A10 (NoCM).""",
"""**R5. González–Rotger** (corrected by loc-adopt, 2026-11-12, after the locator audit). On the
Shimura curve `X₀(D,N)` of the paper (here `D = 6`, `N = 1`), for orders `R` of conductor `f`,
`(f,6)=1`, embeddable in `𝒪`: `#CM(R) = 2^{#{p | D(R)N(R)}}·h(R)` (Prop. 5.6); a single
specified orientation branch has `h(R)` points, the whole CM set in general does not
(`(f,6) = 1` does not remove the factor: for `R` maximal of discriminant −19, `h(R) = 1`, 2 and 3
are inert, and there are four CM points). Fields: `ℚ(x) = H_R` if `D(R)N*(R) ≠ 1`, otherwise
the specified index-2 subfield of `H_R` (Thms 5.8, 5.12). Ref: J. Math. Soc. Japan 58 (2006),
Prop. 5.6 (p. 943; arXiv v1/v2 p. 15), Thm 5.8 (pp. 943-944; v1/v2 p. 16), Thm 5.12 (p. 946;
v1/v2 pp. 18-19), read by the audit in v1, v2 and the journal (rv-h-cm had read the arXiv text).
These statements concern `X₀(D,N)`; they do not apply automatically to `Y₃` or to the image in the
full Atkin–Lehner quotient (audit example: at discriminant −24 the quotient coordinate −16/27 is
rational while the ring class field has degree 4). The former statement "`#CM(R) = h(R)`" is
contradicted by Prop. 5.6 (audit verdict NO). E (in the corrected form). Lean: **no** (via R1).
Step A10 (NoCM), whose use of the count is under separate review (h-trust A10 note of
2026-11-12).""")

rep("""consequence). Lean: **yes**, `PkgI2.RaynaudCriterion`. Formalized: none. Steps D2 and A6 (Raynaud route, rv-a6-route: with SGA 7 IX 3.5).""",
"""consequence). Lean: **yes**, `PkgI2.RaynaudCriterion`. Formalized: none. Steps D2 and A6 (Raynaud route, rv-a6-route: with SGA 7 IX 3.5).
""" + A + """: Silverberg–Zarhin Thm 3.5 (p. 406, citing SGA 7 IX Prop. 4.7) and Thm 3.3
(p. 405) read; the threshold at the boundary `m = 3` (the case A6 uses) could not be confirmed
from the display, and SGA 7 was not read: UNVERIFIED at `m = 3`. The square-zero consequence is
conditional on it and must be quantified over every inertia element, every `ℓ ≠ p` and every `n`
(as stated here).""")

rep("""forms, equivalent to the Tate-module forms). Lean: **yes**, `PkgI2.NeronOggShafarevich`,
`PkgI2.SerreTatePotentialGood`. Formalized: elliptic curves only (Tau Ceti). Steps A6, A8, C6.""",
"""forms, equivalent to the Tate-module forms). Lean: **yes**, `PkgI2.NeronOggShafarevich`,
`PkgI2.SerreTatePotentialGood`. Formalized: elliptic curves only (Tau Ceti). Steps A6, A8, C6.
""" + A + """: the original was not read (UNVERIFIED). In (b) one common open subgroup of inertia
must fix all `ℓⁿ`-torsion; a subgroup depending on `n` is much weaker.""")

rep("""Thm 3.6. E. Objects: Néron models.""",
"""Thm 3.6 (UNVERIFIED; Silverberg–Zarhin Thm 3.4, pp. 405-406, cite it as **Prop.** 3.6: the
number needs the SGA text, locator audit 2026-11-12). E. Objects: Néron models.""")

rep("""`PkgI3.range_tateHomZl_subset`, so the leaf asserts exactly the published content). Steps C2, C10,
E1.""",
"""`PkgI3.range_tateHomZl_subset`, so the leaf asserts exactly the published content). Steps C2, C10,
E1. """ + A + """: the original was not opened (only the erratum, Invent. Math. 75 (1984), p. 381,
which corrects Satz 2): UNVERIFIED. The integral statement `Hom_F(A,B) ⊗ ℤ_ℓ` must not be replaced
by the rational one.""")

rep("""weights. Step C3.

**R11. Berger.**""",
"""weights. Step C3. """ + A + """: read in arXiv v2 (Thm 1.6, Cor. 1.8, p. 4; Thm 8.4, p. 48;
Thms 9.1, 9.3, pp. 53-54), the journal (Thm 1.6, p. 5; Cor. 1.8, pp. 5-6; Thm 8.4, pp. 67-69;
Thms 9.1, 9.3, pp. 74-75) and the corrigendum: YES for the filtered comparison (proper smooth
rigid spaces over a complete discretely valued extension of `ℚ_p` with perfect residue field; no
good-reduction or odd-`p` hypothesis); the Tate weights `0, −1` are a consequence (duality and
Hodge dimensions).

**R11. Berger.**""")

rep("""**R11. Berger.** de Rham ⇒ potentially semistable. Ref: Invent. Math. 148 (2002), Thm 0.7 (read
by a model; arXiv v3 Thm 0.6 VERIFIED by rv-h-a011). E.""",
"""**R11. Berger.** de Rham ⇒ potentially semistable. Ref: Invent. Math. 148 (2002), Thm 0.7
(p. 6) and Cor. 5.22 (p. 52) in the published version (read by the audit in an author-hosted copy;
Springer pagination unread); arXiv math/0102179v3 Thm **0.6** (p. 6) and Thm 5.19 (pp. 56-57)
(VERIFIED by rv-h-a011, read again by the audit). Theorem 0.7 of arXiv v3 is a different
statement: cite 0.6 for v3 and 0.7 for the published text. No dimension, oddness, residual or
odd-`p` hypothesis; the conclusion is potential semistability, not semistability over the
original field (locator audit, 2026-11-12). E.""")

rep("""(the trace reading; every reading in the literature implies it; §6 R2).""",
"""(the trace reading; every reading in the literature implies it; §6 R2). Locator audit
(2026-11-12): arXiv v2 Thm 1.0.4 (p. 5) with Conj. 1.0.1 (p. 2) and the conventions (pp. 6-7)
read; the JAMS number and page are UNVERIFIED. At `p = 3` the hypothesis must keep Pan's local
residual exception (the semisimplified local residual representation is not `η ⊕ ηω`); there is
no such proviso at `p = 5`, the prime C7 uses. Pan uses geometric Frobenius and cyclotomic HT
weight −1, so the arithmetic-Frobenius trace form stated here is a consequence after dualization
and an adjusted twist; the printed conclusion is a cuspidal eigenform up to twist, and the trace
form needs the attached representation (R14). CONSEQUENCE of v2, not a check of the journal
number.""")

rep("""**R13. Hodge–Tate weights of eigenforms, every level.** `ρ_{g,ι}` for a weight-`k ≥ 2` eigenform
of any level is HT at `ℓ` with weights `{0, 1−k}` (Tate normalization). Ref: Saito, Invent. Math.
129 (1997); or Kato, Astérisque 295 (2004), §9.4; or Faltings 1987. C (normalization; rv-h-c8 R1).""",
"""**R13. Hodge–Tate weights of eigenforms, every level.** `ρ_{g,ι}` for a weight-`k ≥ 2` eigenform
of any level is HT at `ℓ` with weights `{0, 1−k}` (Tate normalization). Ref: Kato, Astérisque 295
(2004), §§9.2-9.4, especially (9.2.2), pp. 187-188, with §§6.3, 8.3 (pp. 161-162, 181-182),
§§11.3-11.4 (pp. 205-207), §14.10.2-3 (p. 240), read by the audit: the **all-level supplier**
for cusp forms and newforms (no `p ∤ N` restriction; bad reduction through semistable models over
finite extensions, `p = 2` included), with the cohomological realization dualized to the Tate
weights `{0, 1−k}`. General cuspidal eigenforms need the reduction from old to new eigensystems;
Eisenstein series need their two-character construction or must be excluded; weight one is
outside R13. Saito, Invent. Math. 129 (1997): body unread, UNVERIFIED (locator audit,
2026-11-12); Faltings 1987 not audited. C (normalization; rv-h-c8 R1).""")

rep("""`HSyn.EigenformRepExists`. Formalized: none (Anthropic FLT has mod-p versions). Steps C8, C10.""",
"""`HSyn.EigenformRepExists`. Formalized: none (Anthropic FLT has mod-p versions). Steps C8, C10.
""" + A + """: Deligne exp. 355 §§3.9-3.12, Prop. 4.8, Thm 4.9 and Deligne–Serre Thm 4.1
(pp. 513-514) read; Shimura 1971 Thm 7.14 unread. CONSEQUENCE, citation chain partly UNVERIFIED:
the semisimple 2-dimensional form needs eigen-isotypic extraction, algebraicity, scalar extension
and semisimplification; geometric versus arithmetic Frobenius must be explicit; no `ℓ = 2`
exclusion was found. For Eisenstein series "every normalized eigenform" needs the reducible
construction, or the leaf must be restricted to cusp forms (a statement check, WP13; the Lean
statement is not changed here).""")

rep("""not needed: UNVERIFIED). C. Lean: **yes**, `HSyn.DeligneSerreConseq`. Step C8.""",
"""not needed: UNVERIFIED). C. Lean: **yes**, `HSyn.DeligneSerreConseq`. Step C8. """ + A + """:
Thm 4.1 (pp. 513-514), §3.1 with Lemma 3.2 and Remark 3.4 (p. 513), Remark 4.3 (p. 514) read.
Thm 4.1 starts from a nonzero weight-one eigenform with odd nebentypus (cuspidality not needed
for existence) and gives finite image with arithmetic Frobenius explicit; the transfer to every
semisimple `ℓ`-adic representation with these traces uses Lemma 3.2 (Chebotarev and
Brauer–Nesbitt). Semisimplicity cannot be dropped. CONSEQUENCE.""")

rep("""Lean Pool has Eichler–Shimura for `Γ₀(N)` (cohomological form). Step C9.""",
"""Lean Pool has Eichler–Shimura for `Γ₀(N)` (cohomological form). Step C9. """ + A + """:
Shimura 1973 Thm 1 (pp. 526-527), §0 and Thm 2 read; Shimura 1971 Thm 7.9 unread. Thm 1 gives the
`ℚ`-rational quotient `A_f`, its coefficient-field action and dimension for
`Γ₁(N) ⊂ Γ ⊂ Γ₀(N)`; its total Euler-factor clause has an extra `Γ₀`/Fricke-stability condition,
which must not be attached to the unconditional clauses nor dropped when that clause is used.
The rank-2 realization for an individual embedding and the Frobenius–Hecke relation must still be
supplied (divisibility of the total characteristic polynomial is not enough). CONSEQUENCE with an
incompletely sourced realization bridge.""")

rep("""`CarayolR17` in `scratch/def-ladic-cond/LadicCond.lean` (compiles; not yet in `Leaves.lean`, where
R17 is still a placeholder).""",
"""`CarayolR17` in `scratch/def-ladic-cond/LadicCond.lean` (compiles; not yet in `Leaves.lean`, where
R17 is still a placeholder). """ + A + """: §§0.3-0.8 and Théorème A (pp. 409-411) read. Coverage
YES for `p | N` and for coefficient characteristic `ℓ = 2` (every finite `p` and every
coefficient place of different residue characteristic); the extra discrete-series hypothesis is
only for totally real `F` of even degree, not `ℚ`. Combine with the newform conductor
`a(π_p) = v_p(N)` and identify the realization; contragredient and norm twists do not change the
conductor. Do not replace Théorème A by Théorème B or by the `Γ₀` elliptic corollary.
CONSEQUENCE.""")

rep("""degree `d`. Ref: Algebra Number Theory 8 (2014), Thm 1.1.1 (read by a model). E.""",
"""degree `d`. Ref: Algebra Number Theory 8 (2014), Thm 1.1.1 (p. 90; arXiv v1 p. 1) with the
height identification (p. 98; arXiv §2.3, p. 9), read by the audit: stable Jacobian height, no
field-degree factor, no semistability over the original field; any Belyi map of degree `d`
bounds the minimal Belyi degree. CONSEQUENCE (audit) of the printed bound; the inequality itself
is as printed.""")

rep("""Ref: Duke Math. J. 163 (2014), Thm 1.4 (read by a model). E. Lean: **no**. Step E3.""",
"""Ref: Duke Math. J. 163 (2014), Thm 1.4 (p. 2060), with `κ` and `α(g) = 1024g³` (p. 2058) and the
pair convention (p. 2059), read by the audit in a typeset author copy of the journal text: YES
with the number-field hypotheses. `κ(A) = ((14g)^{64g²}[k:ℚ]max(h_F(A), log[k:ℚ], 1)²)^{1024g³}`;
the theorem gives a `K`-isogeny in each direction, each of degree `≤ κ(A)` (for a pair, the
maximum, not the product); specialize `k = K`; stable original-Faltings normalization; no
principal polarization or simplicity hypothesis. E. Lean: **no**. Step E3.""")

rep("""Raynaud, Astérisque 127 (1985), VII Cor. 2.1.3. E. Lean: **no**. Step E4.""",
"""Raynaud, Astérisque 127 (1985), VII Cor. 2.1.3. E. Lean: **no**. Step E4. Locator audit
(2026-11-12): Lemma 5 unread (Pazuki's Remark 2.3 points to p. 358, a secondary locator):
UNVERIFIED, including the direction and the stable/semistable hypotheses.""")

rep("""2014 §9 (read by a model). C (weaker constant). Lean: **no**. Step E4.""",
"""2014 §9 (read by a model). C (weaker constant). Lean: **no**. Step E4. Locator audit
(2026-11-12): Bost's §2.1.3, Thm 2.1(i), Prop. C.2 identified but the decisive displays were
unreadable: UNVERIFIED from Bost. Gaudron–Rémond §9 (proof of Lemma 9.1, p. 2098) uses
`−(3/2)dim A` (read), which verifies their published use, not Bost's constant. Conditional on a
Deligne-normalized bound `h_D ≥ −(g/2)log(2π)`, one gets `h_F ≥ −(g/2)log(2π²) > −(3/2)g`.""")

rep("""SMF 140 (2012), Cor. 1.3(2) (read by a model). C (hardened). Lean:
**no** (Faltings height, theta constants). Step F3.""",
"""SMF 140 (2012), Cor. 1.3(2) (read by a model). C (hardened). Lean:
**no** (Faltings height, theta constants). Step F3. Locator audit (2026-11-12): read in arXiv v2
(Cor. 1.3(2), p. 3; metric, Def. 2.1, pp. 6-7; theta height, Def. 2.6, p. 9; Lemma 5.7, p. 20)
and in the journal (Cor. 1.3, pp. 21-22; metric p. 26; theta height p. 30; Lemma 5.7 p. 43).
CONSEQUENCE, not the literal corollary: the corollary bounds the truncated heights,
`|max(1,h_Θ) − max(1,h_D)/2| ≤ C₂ log(min(max(1,h_Θ), max(1,h_D)) + 2)`, with
`C₂(g,r) = 1000r^{2g}(log r^{2g})⁵` (`g = r = 2` gives the constant above), for the paper's
theta (Fubini–Study) height and **Deligne's metric**, for which `h_D = h_F + (g/2)log π`, i.e.
`h_D = h_F + log π` for surfaces. So `X_D` must satisfy `X_D ≥ max(1, h_D(A))`; an unshifted
bound on `h_F` cannot be substituted. The hardened `X_D = max(1, h_F(A) + 3)` satisfies this
(`log π < 1.15 < 3`), so the `+3` now covers a shift that the audit identified, not only a
hypothetical one. The theta height must be identified with the project's coordinate height
(glue).""")

open(p,'w').write(s)
print('ok part 2')
