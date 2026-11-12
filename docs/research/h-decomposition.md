# h-decomposition: hypothesis H as literature leaves plus glue (synthesis)

Status: research note (task hsyn, 2026-11-11), first version. Lean companion:
`scratch/h-decomposition/Leaves.lean` (compiles with `lake env lean`; results log
`scratch/hsyn/log.md`). No file under `ZInQKernel/`, `blueprint/` or another task's notes was
edited.

**Inputs folded in.** The three designs `hdec-faithful.md`, `hdec-elementary.md`, `hdec-alt.md`
(with their Lean drafts); the reports **pkg-I2** (reduction theory, `docs/research/pkg-I2.md`,
`scratch/pkg-I2/I2.lean`) and **glue-conductor** (Glazer's conductor bound,
`docs/research/glue-conductor.md`, `scratch/glue-conductor/`). **Not yet landed** at this version:
pkg-I1, pkg-I3, pkg-I4, pkg-I5, pkg-I6, glue-descent, glue-assembly, glue-repo, rv-routek.

Sources: the frozen manuscript `diophantine_zq.tex` ("N5"; proof of Theorem 4.1 at L404-964, the
appendix lemma at L10936-11005); `h-trust.md` (steps A1-F4); `h-b1.md`, `rv-h-cm.md`, `h-a011.md`,
`wk-h.md`, `rv-lit.md`, `prereq-survey.md`, `nt-tyz.md`, `README.md`;
`ZInQKernel/Hypotheses/{Height,HeightMin,JHeight,CR3Literature}.lean`; Mathlib v4.35.0.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published
theorem with its reference. **SPECULATIVE**: an assessment. There is no network on this host:
every theorem number below is **UNVERIFIED** unless marked otherwise; "read by a model" means a
repository note records an AI model's reading of the published text (h-trust's ASTRA-READ or
AUDIT-READ), which is not a human check.

---

## §0. Summary for the announcement

**Claim for H** (the six-contact height estimate, the one instance of Theorem 4.1 of Glazer's
manuscript that the proof uses). On the manuscript's own route, H follows from **22 research-level
theorems** of the literature, **25 textbook theorems** in six groups, and **21 glue steps** that
are the manuscript's new arguments, the repository's replacement arguments, and bookkeeping. The
glue is **not** formalized: it has been reviewed only by AI models, and only its last step and
some elementary pieces are proved in Lean. No research-level theorem has been merged with another
to shorten the list.

Research-level theorems (all locators UNVERIFIED in the journal versions unless noted):

1. Shimura 1967 / Deligne 1971 (Thm 4.21): canonical model and moduli interpretation of the
   level-3 Shimura curve of discriminant 6, with Shimura reciprocity.
2. Baba–Granath 2008 (Thm 2.1, Lemma 3.1): the Atkin–Lehner quotient and its branch points.
3. Lin–Yang 2020 (Example 30): Igusa invariants on the quaternionic locus.
4. Igusa 1967: the Siegel modular forms ψ₄, χ₁₀ in theta constants.
5. González–Rotger 2006 (Thm 5.12, Prop. 5.6): fields of definition of CM points.
6. Raynaud (SGA 7 IX, Prop. 4.7): semistable reduction when the m-torsion is rational, m ≥ 3.
7. Serre–Tate 1968 (Thms 1, 2): the Néron–Ogg–Shafarevich criterion and potential good reduction.
8. Grothendieck (SGA 7 IX, Thm 3.6): semistable reduction theorem.
9. Faltings 1983 (Satz 3, Satz 4): semisimplicity and the Tate conjecture for abelian varieties.
10. de Rham comparison (Scholze 2013 Cor. 1.8; or Faltings 1989, Tsuji 1999).
11. Berger 2002 (Thm 0.7): de Rham implies potentially semistable.
12. Pan 2022 (JAMS, Thm 1.0.4): the Fontaine–Mazur conjecture for GL₂ over ℚ, p odd.
13. Hodge–Tate weights of eigenform representations at every level (Saito 1997, or Kato 2004).
14. Galois representations of eigenforms (Eichler–Shimura, Deligne 1971).
15. Deligne–Serre 1974 (Thm 4.1): weight one gives finite image.
16. Eichler–Shimura in J₁(N) (Shimura 1971 Thm 7.9; Shimura 1973 Thm 1).
17. Carayol 1986 (Théorème A): local–global compatibility of the conductor.
18. Javanpeykar 2014 (Thm 1.1.1): Faltings height of Jacobians of Belyi curves.
19. Gaudron–Rémond 2014 (Duke, Thm 1.4): explicit isogeny theorem.
20. Faltings 1983 (Lemma 5): variation of the Faltings height under isogeny.
21. Bost 1996: lower bound for the Faltings height.
22. Pazuki 2012 (Cor. 1.3): theta height against Faltings height.

Textbook foundations: (a) purity of the branch locus and Abhyankar's lemma (SGA 1); (b) abelian
varieties (Mumford: torsion, rank of Hom, ℓ-independence, Poincaré reducibility, Weil pairing;
Néron mapping property for abelian schemes; reduction of torsion; Tate module and étale cohomology;
Riemann/GAGA and Artin comparison); (c) arithmetic of ℚ (Skolem–Noether, the Brauer group of ℚ,
local class field theory, Kronecker–Weber, Chebotarev, Brauer–Nesbitt); (d) ramification theory
(Hilbert's different formula, the different bound, upper numbering and conductors);
(e) Fontaine's closure properties of de Rham representations; (f) twists and newforms of modular
forms.

**What is in Lean today** (VERIFIED: `scratch/h-decomposition/Leaves.lean` compiles). Of the
leaves, **5 research-level statements (items 6, 7 twice, 14, 15) and 15 textbook statements** are
stated concretely over Mathlib with cheap, genuine definitions (abelian varieties as group objects
over `Spec K`, good reduction as an abelian scheme over the valuation ring, Galois
representations into `GL_n(ℚ̄_ℓ)`, eigenforms through their q-expansions). The rest are named
placeholders carrying no content. Proved in Lean: the last glue step (from the height of `J(u)`
back to `u`, in `ZInQKernel`), and elementary pieces of four other glue steps (the conductor
arithmetic, the level bound `N ≤ Q·M²`, the dyadic unit lemma, two reduction-theory consequences,
the weight arithmetic). The top-level theorem "leaves ⇒ H" is stated in Lean with its main glue
step as `sorry`.

**What cannot be stated in Lean today, and why.** Items 1-5, 8, 16, 18-22 need definitions that no
Lean library has: the Shimura curve as a moduli scheme with its canonical model (items 1-5), Néron
models (8), the modular curve X₁(N) and its Jacobian over ℚ (16, 18), the Faltings height (18-22),
Siegel modular forms and theta constants (4, 22). Items 9-13 and 17 need medium-to-large new
definitions: Tate modules with Galois action (9), de Rham, Hodge–Tate and potentially semistable
representations (10-13), conductors of ℓ-adic representations (17).

**Alternative modularity route.** Items 10-16 (p-adic Hodge theory, Pan, eigenform
representations) can be replaced by Ribet's theorem on building blocks and modularity of GL₂-type
abelian varieties over ℚ (Khare–Wintenberger with Ribet), with two new glue lemmas that no one has
reviewed yet (§1). That route has 17 research-level theorems.

**The CR3 side** (positive rank of congruent number curves). The implication from these
literature statements to the main theorem is kernel-checked (no `sorry`, axioms `propext`,
`Classical.choice`, `Quot.sound`):
- `Literature.GrossZagier`: a simple zero of L(E,s) at s=1 gives a point of infinite order.
  Not one printed sentence: Gross–Zagier 1986 with an auxiliary twist (Bump–Friedberg–Hoffstein
  1990) and modularity (Breuil–Conrad–Diamond–Taylor 2001).
- `Literature.FunctionalEquation5`: the functional equation of L(C_d, s), d ≡ 5 mod 8, with root
  number −1 (Deuring, Hecke; Birch–Stephens 1966), a textbook consequence.
- Tian–Yuan–Zhang, either as `Literature.TYZRow5b`, or as the pair
  `Literature.TYZThm35ReadingA` + `Literature.HeckeContinuation`, which `tyzRow5b_of_readingA`
  turns into `TYZRow5b`. **No refereed text that we have read states `TYZRow5b`.** Theorem 1.2 of
  TYZ (arXiv:1411.4728v1) read literally is false (d = 26565, 33117); `TYZThm35ReadingA` is the
  intended reading of their Theorem 3.5(2), whose proof passes through a proposition that is only
  sketched; the journal version (Asian J. Math. 21 (2017)) has not been checked. `TYZRow5b` is
  proved from unambiguous results of the arXiv version, with Hecke's continuation, by
  Proposition N (`docs/research/nt-tyz.md` §4), a new argument reviewed twice by AI models and
  never by a human. `HeckeContinuation` is textbook (Deuring, Hecke).

**The exact claim the project can make.** "The main theorem is proved in Lean from two
hypotheses. The CR3 hypothesis is reduced in Lean to three statements about L-functions (with
the TYZ caveat above). Hypothesis H is reduced *on paper* to the 22 research-level theorems and
the textbook results listed, plus 21 glue steps that still have to be formalized; 20 of the leaf
statements can already be written in Lean, the others need the definitions named above." It is
**not** yet true that formalizing the literature theorems alone would complete the proof: the glue
for H has to be formalized as well.

---

## §1. Route decision: route P against route K

**Route P** (the manuscript's): Glazer builds a 2-dimensional representation `r_ℓ` of `G_ℚ` from
the QM surface by scalar descent, proves it de Rham with Hodge–Tate weights `{0,−1}` (appendix
lemma, from a de Rham comparison and Fontaine's closure), potentially semistable (Berger), odd,
irreducible, then applies Pan's theorem, fixes the twist and weight (Hodge–Tate weights of
eigenforms, Deligne–Serre, Kronecker–Weber), passes to a newform and to `J₁(N)`
(Atkin–Lehner–Li, Eichler–Shimura, Faltings) and identifies `r₃` with `r₅` in one compatible
system. Evidence: N5 L719-795; audited step by step in h-trust (C1-C10); new passages (C3's
appendix lemma, C8's determinant argument, C9, C10) have two model reviews each (rv-h-c3, rv-h-c8,
rv-h-a9c9, rv-h-novel). Pan's statement read in arXiv v2 by a model (h-a011 §1.1).

**Route K** (hdec-elementary §2.2, hdec-alt §1.2, proposed independently by both): after the
descent (C1, C2), note that `A_ℚ̄` is a building block (End⁰ = B central over ℚ, Schur index 2);
Ribet's theorem (Ribet 1992/2004, Pyle 2004) places it in a GL₂-type abelian variety `B₀/ℚ`
(hdec-elementary does this explicitly through the Weil restriction of `A` and Faltings'
theorem: Lemma GL₂); Khare–Wintenberger 2009 with Ribet's reduction makes `B₀` a quotient of
`J₁(N₀)`; Carayol gives the conductor `N^{dim}`; Glazer's local bounds are transplanted to
`Res A` through Mackey's formula (Lemma Ind). Removes research items 10-16 and textbook (e) and
Kronecker–Weber, the appendix lemma (G9), oddness (G10), the twist-and-weight step (G12) and the
compatible system (G14). Adds: K1 Ribet (building blocks are factors of GL₂-type varieties over
ℚ), K2 modularity of GL₂-type abelian varieties over ℚ (Khare–Wintenberger, Invent. Math. 178
(2009), with Ribet 2004, Thm 4.4; UNVERIFIED), K3 Carayol in the form "a ℚ-simple quotient of
`J₁(N)` has conductor `M^{dim}`" (consequence of Carayol with Shimura 1973), Weil restriction and
the conductor of an abelian variety as definitions, and two new glue lemmas, GK1 (Lemma GL₂) and
GK2 (Lemma Ind). Research count: 22 − 7 (items 10-16) + 2 (K1, K2; K3 replaces item 17) = **17**.

**Evidence and review status.** Route K's two glue lemmas are NEW in hdec-elementary and hdec-alt
and have no review (rv-routek, the adversarial review commissioned for exactly this, has not
landed at this version). hdec-alt §1.2 flags that the printed form of Ribet's theorem must be
checked against the proceedings text. hdec-alt also notes a danger for any GL₂-type route: the
dimension of `B₀` is not bounded in `M` (§1.1 of hdec-alt, on von Känel); in route K the
dimension enters only through `J₁(N)` with `N ≤ QM²`, as in route P, so the final constant is
unchanged (claimed by both designs; SPECULATIVE until reviewed).

**Recommendation (first version).** Announce on **route P**: it is the manuscript's proof, every
step has a supplier in h-trust, and its new passages have model reviews. Keep **route K as the
fallback and as the formalization-cheaper alternative**: its definitions are a subset of route P's
(abelian varieties, `J₁(N)`, Faltings height) plus Weil restriction, and it avoids `B_dR`, `B_st`
and Hodge–Tate theory entirely, so a crowd should know it exists. Switch the recommendation only
if rv-routek confirms GK1 and GK2 and the statement of K1.

---

## §2. The leaves

Columns: **statement** (the form the proof uses); **reference** (UNVERIFIED unless marked);
**E/C** (exact, or a consequence never stronger than the published statement); **objects**;
**Lean** (yes = stated in `Leaves.lean` over genuine definitions, with its name; new defs = names
the missing definitions and their tier; no = needs a very large definition); **formalized**
(where the proof exists in a library). Step names A1-F4 are h-trust's.

### §2.1 Research-level leaves (route P)

**R1. Shimura–Deligne: the level-3 QM curve.** `B = (2,−3)/ℚ`, `𝒪` maximal, `μ = 2j + ij`,
`K₃` the level-3 principal congruence subgroup. (a) The moduli functor of `(A, ι, λ, η)` on
`ℚ`-schemes (abelian surface scheme, `𝒪`-action, principal polarization with Rosati `a ↦ μ⁻¹āμ`,
`𝒪`-linear level-3 structure) is represented by a smooth projective curve `Y₃/ℚ`; (b) complex
uniformization; (c) the adelic normalizer acts over `ℚ`; (d) Shimura reciprocity at CM points.
Ref: Shimura, Ann. of Math. 85 (1967), Main Thms I-II; Deligne, Sém. Bourbaki 389 (1971),
Thm 4.21, Cor. 5.7, Ex. 5.8, §§4.8-4.17; Kottwitz, JAMS 5 (1992), §5; neatness by Serre's lemma.
C (PEL theorem specialized; assembled from several statements, §6 R4). Objects: abelian schemes,
PEL moduli, CM points. Lean: **no** (very large). Formalized: none (Anthropic FLT has QM fake
elliptic curves for Čerednik–Drinfeld; use for `Y₃/ℚ` unchecked). Steps A3-A6, A10.

**R2. Baba–Granath.** `X₆/W ≅ P¹_j`, branched at `0, ∞, −16/27` with indices 4, 6, 2 at CM
discriminants −4, −3, −24; equal polarized moduli points iff `W`-conjugate. Ref: Canad. J. Math.
60 (2008), Thm 2.1, Lemma 3.1 (2005 preprint read by a model). E. Lean: **no** (via R1). Steps
A2, A7.

**R3. Lin–Yang.** On the finite nonzero `j`-locus, the QM surface over `j` is a genus-2 Jacobian
with `[J₂:J₄:J₆:J₁₀] = [12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]`. Ref: Math. Z. 295 (2020),
Example 30, eqs. (13)-(14) (VERIFIED in arXiv v1 by h-v14; journal numbering UNVERIFIED). E.
Lean: **no** (QM locus). Steps A7, F1. (The Igusa-invariant side is cheap; hdec-elementary
proves in Lean the algebraic identity `j = 3779136·I₁₀²/I₄⁵` on its Igusa–Clebsch form of the
locus, `HDec.j_eq_of_onQMLocus`.)

**R4. Igusa: theta constants.** `ψ₄ = 2⁻²Σθ_m⁸`, `χ₁₀ = −2⁻¹⁴Πθ_m²` (even `m`), with the
conversion to `J₂..J₁₀`. Ref: Amer. J. Math. 89 (1967), pp. 833-834, 848. E. Lean: **new defs**
(theta constants with characteristics on `𝔥₂`, Siegel modular forms; large). Step F1.
(hdec-elementary replaces it by Thomae's formula merged into R22; not adopted: it merges two
publications.)

**R5. González–Rotger.** For orders `R` of conductor `f`, `(f,6)=1`, embeddable in `𝒪`:
`#CM(R) = h(R)` and `ℚ(x)` is `H_R` or of index 2 in it. Ref: J. Math. Soc. Japan 58 (2006),
Thm 5.12, Prop. 5.6 (VERIFIED in arXiv:math/0612732 by rv-h-cm). E (restricted to `(f,6)=1`).
Lean: **no** (via R1). Step A10 (NoCM).

**R6. Raynaud's criterion, Galois form.** `K` with a DVR `O`, `A/K` abelian, `m ≥ 3` invertible
in `O`, `A[m]` rational over `K` ⇒ every inertia element satisfies `(σ−1)² = 0` on `A(K̄)[ℓⁿ]`
for every prime `ℓ` invertible in `O`. Ref: SGA 7 I, Exp. IX, Prop. 4.7 with Prop. 3.5;
Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), Thm 3.5 (read by a model). C (the Galois
consequence). Lean: **yes**, `PkgI2.RaynaudCriterion`. Formalized: none. Steps D2 (and A6 on the
Raynaud route).

**R7. Serre–Tate.** (a) Néron–Ogg–Shafarevich: good reduction ⟺ inertia fixes `A(K̄)[m]` for all
`m` invertible in `O` ⟺ for infinitely many such `m`. (b) Potential good reduction ⟺ an open
subgroup of inertia fixes all `A(K̄)[ℓⁿ]`. Ref: Ann. of Math. 88 (1968), Thms 1, 2. E (finite-level
forms, equivalent to the Tate-module forms). Lean: **yes**, `PkgI2.NeronOggShafarevich`,
`PkgI2.SerreTatePotentialGood`. Formalized: elliptic curves only (Tau Ceti). Steps A6, A8, C6.

**R8. Grothendieck's semistable reduction theorem.** Abelian varieties over the fraction field of a
henselian DVR acquire semistable reduction over a finite extension. Ref: SGA 7 I, Exp. IX,
Thm 3.6. E. Objects: Néron models. Lean: **new defs** (Néron models, large); its Galois
consequence is `PkgI2.GrothendieckMonodromy` (compiles). Needed only on h-b1's reviewed route for
A6; pkg-I2's Raynaud route avoids it (§3 G3).

**R9. Faltings 1983.** `V_ℓ(A)` semisimple; `Hom_F(A,B) ⊗ ℚ_ℓ ≅ Hom_{G_F}(V_ℓA, V_ℓB)`. Ref:
Invent. Math. 73 (1983), Satz 3, Satz 4, Korollar 1 (read by a model). E. Lean: **new defs**
(Tate modules with Galois action; medium). Steps C2, C10, E1.

**R10. de Rham comparison.** For `F/ℚ_ℓ` finite and `A/F`, `H¹_et(A_F̄, ℚ_ℓ)` is de Rham with
`D_dR ≅ H¹_dR(A/F)`; `V_ℓ(A)` has HT weights `0, −1`, each with multiplicity `dim A`. Ref: Scholze,
Forum Math. Pi 1 (2013), Cor. 1.8, Thms 9.1, 9.3 + corrigendum; or Faltings 1989, Tsuji 1999. E
(first clause). Lean: **new defs** (`B_dR` with action and filtration; large; Mathlib has bare
`BDeRham`). Step C3.

**R11. Berger.** de Rham ⇒ potentially semistable. Ref: Invent. Math. 148 (2002), Thm 0.7 (read
by a model; arXiv v3 Thm 0.6 VERIFIED by rv-h-a011). E. Lean: **new defs** (`B_st`; very large).
Step C4.

**R12. Pan.** `p` odd, `ρ : G_ℚ → GL₂(ℚ̄_p)` continuous irreducible, finitely ramified,
potentially semistable at `p`, odd, distinct HT weights (residual clause at `p = 3`) ⇒ there are a
normalized eigenform `g` and a continuous character `ψ` with `tr ρ(Frob_v) = ψ(Frob_v)·ι(a_v(g))`
for almost all `v`. Ref: JAMS 35 (2022), Thm 1.0.4 (arXiv v2 statement VERIFIED by h-a011). C
(the trace reading; every reading in the literature implies it; §6 R2). Lean: **new defs**
(potentially semistable, HT weights); the rest is expressible over `HSyn` §0. Step C7.

**R13. Hodge–Tate weights of eigenforms, every level.** `ρ_{g,ι}` for a weight-`k ≥ 2` eigenform
of any level is HT at `ℓ` with weights `{0, 1−k}` (Tate normalization). Ref: Saito, Invent. Math.
129 (1997); or Kato, Astérisque 295 (2004), §9.4. C (normalization; rv-h-c8 R1). Lean: **new
defs** (HT representations; large). Step C8.

**R14. Galois representations of eigenforms.** For every normalized eigenform of weight `k ≥ 1`,
every `ℓ` and embeddings, a continuous semisimple `ρ : G_ℚ → GL₂(ℚ̄_ℓ)` unramified outside `Nℓ`
with `tr ρ(Frob_p) = a_p` for `p ∤ Nℓ`. Ref: Shimura 1971, Thm 7.14 (`k=2`); Deligne, Sém.
Bourbaki 355 (1971) (`k ≥ 2`); Deligne–Serre 1974 (`k=1`). C. Lean: **yes**,
`HSyn.EigenformRepExists`. Formalized: none (Anthropic FLT has mod-p versions). Steps C8, C10.

**R15. Deligne–Serre, finite image.** A semisimple `ρ` attached to a weight-1 eigenform has finite
image. Ref: Ann. Sci. ÉNS 7 (1974), Thm 4.1 (with T18, T19 for "every semisimple `ρ` with these
traces"). C. Lean: **yes**, `HSyn.DeligneSerreConseq`. Step C8.

**R16. Eichler–Shimura in `J₁(N)`.** For a weight-2 newform `f` of level `N`, `V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ`
has a `G_ℚ`-stable 2-dimensional subquotient with `tr Frob_p = ι(a_p(f))`, `p ∤ Nℓ`. Ref: Shimura
1971, Thm 7.9, §7; Shimura 1973, Thm 1. C. Lean: **no** (`X₁(N)`, `J₁(N)` over `ℚ`). Formalized:
Lean Pool has Eichler–Shimura for `Γ₀(N)` (cohomological form). Step C9.

**R17. Carayol.** For a weight-2 newform of level `N` and `p ≠ ℓ`, the Artin conductor exponent
of `ρ_{f,λ}|G_{ℚ_p}` is `v_p(N)`. Ref: Ann. Sci. ÉNS 19 (1986), Théorème (A). C. Lean: **new
defs** (conductor of an ℓ-adic representation; newforms; medium). Step D5.

**R18. Javanpeykar.** `h_F(Jac X) ≤ 13·10⁶·g·d⁵` for `X/ℚ̄` of genus `g ≥ 1` with a Belyi map of
degree `d`. Ref: Algebra Number Theory 8 (2014), Thm 1.1.1 (read by a model). E. Lean: **no**
(Faltings height). Step E2.

**R19. Gaudron–Rémond.** Isogeny of degree `≤ ((14g)^{64g²}[K:ℚ]max(h_F(A), log[K:ℚ], 1)²)^{1024g³}`.
Ref: Duke Math. J. 163 (2014), Thm 1.4 (read by a model). E. Lean: **no**. Step E3.

**R20. Faltings' height lemma.** `|h_F(A) − h_F(B)| ≤ ½ log deg φ`. Ref: Faltings 1983, Lemma 5;
Raynaud, Astérisque 127 (1985), VII Cor. 2.1.3. E. Lean: **no**. Step E4. (Additivity and
invariance under base change of the stable height follow from the definition: glue.)

**R21. Bost.** `h_F(A) ≥ −(3/2)dim A`. Ref: Bost, Sém. Bourbaki 795 (1996), via Gaudron–Rémond
2014 §9 (read by a model). C (weaker constant). Lean: **no**. Step E4.

**R22. Pazuki.** `h_Θ(A) ≤ ½X_D + C₂ log(X_D+2)` for principally polarized abelian surfaces,
`C₂ = 1000·2⁴(log 2⁴)⁵`. Ref: Bull. SMF 140 (2012), Cor. 1.3(2) (read by a model). E. Lean:
**no** (Faltings height, theta constants). Step F3.

### §2.2 Textbook foundations (route P)

| # | Statement (form used) | Reference (UNVERIFIED) | E/C | Lean | Formalized |
| --- | --- | --- | --- | --- | --- |
| **(a) Étale covers** | | | | | |
| T1 | Zariski–Nagata purity, ring form | SGA 1 X 3.4; Stacks 0BMB | E | yes, `PkgI2.PurityBranchLocus` | Stacks formalization (unreviewed); Tau Ceti dim ≤ 2 |
| T2 | Abhyankar's lemma, DVR form | SGA 1 X 3.6; Stichtenoth 3.9.1 | E | yes, `PkgI2.AbhyankarDVR` | Stacks 0EYG (unreviewed); Tau Ceti (function fields) |
| **(b) Abelian varieties** | | | | | |
| T3 | Néron mapping property, abelian-scheme case | BLR §1.2 Prop. 8 | C | yes, `PkgI2.NeronMappingAbelianScheme` | Anthropic FLT (Néron models, special case) |
| T4 | Reduction of prime-to-`p` torsion is bijective | Serre–Tate 1968 §1 | C | yes, `PkgI2.ReductionTorsionBijective` | none |
| T5 | `A(K̄)[n] ≅ (ℤ/n)^{2g}` | Mumford §4, §6 | E | yes, `PkgI2.TorsionStructure` | none |
| T6 | `rank Hom(A,B) ≤ 4 dim A dim B` | Mumford §19 Thm 3 | E | yes, `PkgI2.HomRankBound` | none |
| T7 | Characteristic polynomials integral, independent of `ℓ` | Mumford §19 Thm 4 | E | yes, `PkgI2.CharpolyIndependentOfEll` | none |
| T8 | Poincaré reducibility | Mumford §19 Thm 1 | E | new defs (isogenies; medium) | none |
| T9 | Galois-equivariant Weil pairing, `GSp` with cyclotomic multiplier | Mumford §§20, 23 | E | new defs (polarizations, Tate modules) | none |
| T10 | `V_ℓ(A) ≅ H¹_et(A_K̄, ℚ_ℓ)^∨` | Milne 1986, Thm 15.1(a) | E | new defs (étale cohomology; large) | none |
| T11 | Riemann/GAGA/rigidity: `End⁰(A_ℂ)` = Hodge endomorphisms, `Hom_ℚ̄ = Hom_ℂ` | Mumford §§1-3; Serre 1956; Conrad 2006 | E | new defs (analytification; large) | Tau Ceti: Riemann forms |
| T12 | Artin comparison with complex conjugation | SGA 4 XI 4.4 | E | new defs (as T11) | none |
| **(c) Arithmetic of ℚ** | | | | | |
| T13 | Skolem–Noether | Reiner Thm 7.21 | E | yes, `HSyn.SkolemNoether` | Tau Ceti `TauCeti.skolemNoether` |
| T14 | Hasse principle for central simple ℚ-algebras | Milne ADT I | C | yes, `HSyn.HasseBrauerQ` | Tau Ceti (local–global sequence) |
| T15 | `H²(G_ℚ, ±1) ≅ Br(ℚ)[2]`, compatible with localization | Milne ADT I; Tate in C–F VII | E | new defs (crossed products; medium) | partly Tau Ceti |
| T16 | Local class field theory with norms and upper numbering | Serre, *Local fields* | E | new defs (local Artin map; medium) | Tau Ceti |
| T17 | Kronecker–Weber | Washington Thm 14.1 | E | yes, `HSyn.KroneckerWeber` | Tau Ceti `kroneckerWeber` |
| T18 | Frobenius elements are dense in `G_ℚ` (Chebotarev) | Neukirch VII.13.4 | C | yes, `HSyn.FrobeniusDense` | Tau Ceti (Chebotarev) |
| T19 | Brauer–Nesbitt (char 0, trace form) | Curtis–Reiner §30 | E | yes, `HSyn.BrauerNesbitt` | none found |
| **(d) Ramification** | | | | | |
| T20 | Hilbert's different formula | Serre, *Corps locaux* IV §1 | E | yes, `GlueConductor.HilbertDifferentFormula` | Tau Ceti |
| T21 | Different bound `δ ≤ e − 1 + e·v_p(e)` | Serre, *Corps locaux* III §6 | E | yes, `GlueConductor.SerreDifferentBound` | not located |
| T22 | Herbrand, subgroup formula for absolute groups, Artin/Swan conductors | Serre, *Corps locaux* IV, VI | E | new defs (upper numbering on `G_{ℚ_p}`, ℓ-adic conductors; medium) | Tau Ceti (finite levels) |
| **(e) p-adic Hodge theory** | | | | | |
| T23 | Fontaine: de Rham representations closed under duals, ⊗, ⊕, subquotients | Astérisque 223, Thm 3.8 | E | new defs (large) | none |
| **(f) Modular forms** | | | | | |
| T24 | Twisting an eigenform by a Dirichlet character | Shimura 1971 Prop. 3.64; Atkin–Li 1978 | C | yes, `HSyn.EigenformTwist` | none |
| T25 | Newforms: strong multiplicity one, conjugates | Li 1975 Thm 5; Miyake 4.6.19 | E | new defs (old space; medium) | Tau Ceti (newform bookkeeping) |

### §2.3 Counts (VERIFIED from the lists and the compiled file)

- Research-level: 22 leaves (R1-R22), 23 statements (R7 a, b). Textbook: 25
  (T1-T25).
- Stated in Lean over genuine definitions: research R6, R7a, R7b, R14, R15 (5 statements);
  textbook T1-T7, T13, T14, T17-T21, T24 (15). Total **20 statements**. All others are `opaque`
  placeholders.
- Needing medium definitions: R9, R17, T8, T9, T15, T16, T22, T25. Large: R4, R8, R10, R13, T10,
  T11, T12, T23. Very large: R11, R12 (through `B_st`), and the not-statable R1-R3, R5, R16,
  R18-R22.
- Route K: drop R10-R16, T23, T17; add K1, K2 (and K3 in place of R17): 17 research leaves.

---

## §3. The glue

Sizes (SPECULATIVE): small < 500 lines, medium 0.5-3k, large 3-10k. Origin: N5 (Glazer's
argument, with the line numbers), repository (the repository's replacement, with its note), or
new here. Every glue item has model reviews only, except those marked proved.

| # | Statement | Inputs | Origin | Lean provability | Size | Status |
| --- | --- | --- | --- | --- | --- | --- |
| G0 | The leaves imply `SixContactMin` | G1-G20 | N5 L404-964 | `HSyn.sixContactMin_of_leaves` | small | **stated**; proved from G1-G19 (`sorry`) and G20 |
| G1 | Fibre datum: Gram matrix det 1, Rosati, unique polarization, normalizer index 4, `deg(Y₃→P¹_j) ≤ 324` | R1, R2 | N5 L410-441; h-b1 M1-M3 | matrix and unit count now; rest needs R1's objects | medium | elementary parts unproved |
| G2 | Lemma PR(i): fibre field `K` Galois, `[K:ℚ] ≤ 324!`, unramified outside `T`; `J(u)` not a branch value | G1; R1(d), R2, T1, T2; polynomial identities | repository, h-b1 (rv-h-b1) | identities cheap now; rest needs normalization of covers | large | needs definitions |
| G3 | Lemma PR(ii): `A`, `σA` good reduction at `v ∤ 3` | R1(a); route h-b1: R8, R7b, T3; route Raynaud: R6, R7a, T4, T5 | repository, h-b1 §4(ii); Raynaud route new in pkg-I2 §4.2 | statement compiles (`PkgI2.goodReduction_of_QM_rational3`, body `sorry`) | medium | stated; Raynaud route unreviewed |
| G4 | Conjugates have one moduli point; Hom field `L`, `[L:ℚ] ≤ D`, unramified outside `T` | G2, G3; R2, R3, T6, R7a; Minkowski's lemma | N5 L532-563 | Minkowski and numerics now | medium | elementary parts unproved |
| G5 | `End⁰(A_ℚ̄) ∈ {B, M₂(k)}` | T11; centralizer computation | N5 L564-577 | centralizer now | medium | needs definitions |
| G6 | NoCM: no CM point over `J(u)`, so `End⁰ = B` | G5; R1(d), R2, R5 | repository, h-cm, rv-h-cm §7.2 | identities now; counting small given R5 | small | needs definitions |
| G7 | Scalar descent: `μ_σ`, `ε`, `χ` with `m ≤ 2R^R M`, `β`, `[L':ℚ] ≤ QM` | G4, G6; T13, T14, T15, T16 | N5 L632-716 (Glazer) | over Tau Ceti's Brauer group and local CFT | medium-large | needs definitions |
| G8 | `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`, Tate action on `G_{L'}`, `r_ℓ|G_{L'}` absolutely irreducible | G7; R9 | N5 L719-734 | over Tate modules | medium | needs definitions |
| G9 | Appendix lemma: `r_ℓ` de Rham, weights `{0,−1}` | G8; R10, T23, T10 | N5 L10939-11000 | over `B_dR` | medium | needs definitions |
| G10 | `r_ℓ` odd | G8; T11, T12 | N5 L742-751 | over T11-T12 | medium | needs definitions |
| G11 | `r_ℓ` unramified outside `T ∪ {ℓ}` | G2, G3, G4, G7; R7a | N5 L752-754 | core lemma **proved**: `PkgI2.inertiaTrivial_of_goodReduction` | small | partly proved |
| G12 | Twist finite, `k = 2` | G8-G11; R11, R12, R13, R14, R15, T9, T17, T18, T19 | N5 L757-768, V16 L660-667 | weight arithmetic **proved**: `HSyn.weight_match` | medium | partly proved |
| G13 | Newform `f` of weight 2, `r₅ ≅ ρ_{f,5}`, constituent of `V₅(J₁(N))` | G12; T24, T25, R16, R9, T18, T19 | N5 L768-774 | over `J₁(N)` | medium | needs definitions |
| G14 | `r₃`, `r₅` in one compatible system | G3, G7, G13; T7, T3, T4, T18, T19, R9 | N5 L776-795 | over Tate modules | medium | needs definitions |
| G15 | Conductor exponents `≤ E₀` (`p ≤ R`), `≤ 2` (`R < p ∈ T`), `0` outside `T` | G3, G7, G14; R6, T16, T20, T21, T22 | N5 L796-852 (Glazer) | D1 **proved** from T20-T21 over Mathlib (`GlueConductor.D1_genuine`); break, Herbrand, Swan/Artin arithmetic **proved**; `(U^{e+1})⁴ = U^{3e+1}` **proved** (`GlueConductor.fourth_pow_mem`, `exists_fourth_root`; removes Silverman IV.6.4); D2 core **proved** (`PkgI2.D2_fixed_of_raynaud`) | large | partly proved |
| G16 | `N ≤ ∏_{p≤R} p^{E₀}·M² ≤ Q_R·M²` | G13, G15; R17 | N5 L852-857 | **proved** over the repository's `heightQ`, `contactSupport`: `GlueConductor.level_le` (given the exponents) | small | proved (arithmetic) |
| G17 | `L'`-isogeny `A × Z → J₁(N)` | G6, G13; R9, T8 | N5 L861-867 | over abelian varieties | small-medium | needs definitions |
| G18 | `h_F(A) ≤ Q¹⁷M²⁴` | G16, G17; R18-R21 | N5 L868-905 | numerics **proved** (`transfer_numerics`, `scratch/wk-h/Arakelov.lean`, not copied) | small | numerics proved |
| G19 | `h(J(u)) ≤ 40h([z_m]) + 22`, `h([z_m]) ≤ 10⁴·2²⁴max(1,h_F(A))`; hence `JHeightBound` | G18; R3, R4, R22 | N5 L908-947 | height of a polynomial map over Mathlib's `NumberTheory/Height` | medium | needs definitions |
| G20 | `JHeightBound Mult.S_mul → SixContactMin` | — | N5 L949-964 | **proved**: `ZInQ.JHeight.sixContactMin_of_jHeightBound` | — | **proved** (ZInQKernel) |

Route K replaces G9, G10, G12, G14 by **GK1** (Lemma GL₂: `r_ℓ` is a constituent of `V_ℓ(B₀)` for a
GL₂-type `ℚ`-simple factor `B₀` of `Res_{L'/ℚ}A`, and `B₀,L' ∼ A^k`; inputs R9, T8, Weil
restriction) and **GK2** (Lemma Ind: Glazer's local bounds for `V_ℓ(Res A)` via Mackey; inputs as
G15), both NEW and unreviewed (hdec-elementary §2.2); G13 and G17 become "K2 gives
`J₁(N) → B₀`, Poincaré gives `J₁(N)_{L'} ∼ A × Z`".

---

## §4. Definitions

| Object | Needed by | Status (declaration) | Cost |
| --- | --- | --- | --- |
| `ℚ̄`, `G_ℚ` with Krull topology | all Galois leaves | Mathlib `AlgebraicClosure`, `AlgEquiv` topology | — |
| places of `ℚ̄`, decomposition/inertia groups, Frobenius | R12-R15, T18, G11 | `HSyn.LiesOver`, `IsArithFrob` over Mathlib `ValuationSubring.decompositionSubgroup`, `inertiaSubgroup` | cheap (done) |
| continuous `GL_n(ℚ̄_ℓ)`-representations, irreducible, semisimple, odd | R12, R14, R15, T19 | `HSyn.GaloisRep` over Mathlib `PadicAlgCl` | cheap (done) |
| cusp forms on `Γ₁(N)`, nebentypus, normalized eigenforms, attached representation | R12-R17, T24 | `HSyn.CF`, `IsNormalizedEigenform`, `AttachedTo` over Mathlib `CuspForm`, `qExpansion` | cheap (done; §6 R6) |
| abelian varieties over a field, points, Galois action, torsion | R6-R9, T3-T12 | `PkgI2.IsAbelianVariety`, `Pts`, `galAct`, `torsion` over Mathlib `Grp (Over (Spec K))` | cheap (done) |
| abelian schemes over a DVR, good reduction | R7, T3, T4, G3 | `PkgI2.IsAbelianScheme`, `HasGoodReduction` | cheap (done) |
| regular local rings, étale/unramified at a prime | T1, T2 | Mathlib `IsRegularLocalRing`, `Algebra.IsEtaleAt` | — |
| different ideal, lower ramification groups | T20, T21 | Mathlib `differentIdeal`, `Ideal.inertia` | — |
| central simple algebras, quaternion algebras | T13, T14 | Mathlib | — |
| Tate modules `T_ℓ`, `V_ℓ` as `ℤ_ℓ`-modules with continuous action; Hom groups; polarizations, Weil pairing | R9, T8, T9, G8-G17 | missing (finite-level substitutes in pkg-I2) | medium |
| Galois cohomology of `G_ℚ`, crossed products, local invariants | T15, G7 | Mathlib `BrauerGroup` (definition); Tau Ceti local–global | medium |
| local Artin map, upper numbering on `G_{ℚ_p}`, conductors of ℓ-adic representations | T16, T22, R17, G15 | Tau Ceti (finite extensions, characters) | medium |
| Hecke operators, old space, newforms | T25, R17 | Tau Ceti | medium |
| Néron models | R8 | Anthropic FLT (special case) | large |
| ℓ-adic étale cohomology | T10, R10 | missing | large |
| analytification, complex tori, Hodge structures | T11, T12, G5, G10 | Tau Ceti (Riemann forms); GAGA missing | large |
| `B_dR` with action and filtration; de Rham, Hodge–Tate representations | R10, R12, R13, T23, G9 | Mathlib `BDeRham` (bare ring) | large |
| `B_st`, potentially semistable | R11, R12 | missing | very large |
| theta constants with characteristics, Siegel modular forms of degree 2 | R4, R22, G19 | missing | large |
| QM abelian schemes, `Y₃`, canonical model, `X₆`, Atkin–Lehner, CM points | R1-R5, G1-G6 | missing | very large |
| `X₁(N)`, `J₁(N)` over `ℚ`, Belyi maps | R16, R18, G13, G17 | missing (Anthropic FLT: Jacobians) | very large |
| Faltings height (stable) | R18-R22, G18, G19 | missing | very large |
| Weil restriction of abelian varieties; conductor of an abelian variety | route K (GK1, K3) | missing | medium |
| Weil heights | G19, G20 | Mathlib `NumberTheory/Height` | — |

---

## §5. Work packages for crowdsourcing

| WP | Content | Depends on | Unlocks |
| --- | --- | --- | --- |
| WP1 | Review the cheap definitions of `Leaves.lean` and prove sanity lemmas (Frobenius trace independent of place and lift at unramified primes; eigenform recursion ⇔ Hecke eigenvector; abelian-variety API: torsion finite, group of points commutative) | none | trust in all 20 stated leaves |
| WP2 | Prove the statable textbook leaves from existing libraries: T13, T14, T17, T18 (port from Tau Ceti), T1, T2 (port from Stacks/Tau Ceti), T20 (Tau Ceti), T21, T19 (self-contained) | WP1 | 9 textbook leaves closed |
| WP3 | Glue elementary now: G1's matrix and unit count, G2's and G6's polynomial identities, G4's Minkowski lemma and numerics, G7's numerics, remaining D3-D4 lemmas of G15, porting `transfer_numerics` (G18) | none | glue skeleton |
| WP4 | Tate modules `V_ℓ` with Galois action, Hom groups, isogenies, polarizations (medium) | WP1 | statements of R9, T8, T9; glue G8, G11, G14, G17; route K's GK1 |
| WP5 | ℓ-adic conductors and upper numbering on `G_{ℚ_p}` (on Tau Ceti) | WP4 | R17, T22; **G15 in full** (Glazer's conductor bound, the new mathematics most worth checking early) |
| WP6 | Galois cohomology and local CFT layer (on Tau Ceti) | — | T15, T16; **G7** (Glazer's scalar descent) |
| WP7 | Newforms and Hecke operators | — | T25, R17 |
| WP8 | p-adic Hodge theory: `B_dR` with action, de Rham/HT representations; then `B_st` | WP4 | R10-R13, T23, G9, G12 (route P only) |
| WP9 | `X₁(N)`, `J₁(N)` over `ℚ` | WP4 | R16, R18; G13, G17; route K's K2 |
| WP10 | Faltings height | WP4, Néron models | R18-R22, G18, G19 |
| WP11 | Siegel modular forms, theta constants; Igusa invariants | — | R4, R22, G19 |
| WP12 | QM moduli scheme `Y₃`, canonical model, CM points | WP4 | R1-R5, G1-G6 |
| WP13 | Statement-checking: locators, the trace reading of Pan, the printed form of Ribet (route K) | none | §6 R1-R3 |

---

## §6. Risks

**Checks to do first.**
- **R1. Locators.** Almost every theorem number is UNVERIFIED in the published version. Most
  worth checking before the announcement: Pan (JAMS numbering of Thm 1.0.4), Baba–Granath and
  Lin–Yang (journal numbering), Carayol (Théorème A covers `p | N` for `F = ℚ`), Javanpeykar,
  Gaudron–Rémond, Pazuki (model readings only).
- **R2. Leaves at risk of being stronger than published.** Pan's conclusion "comes from a cuspidal
  eigenform up to twist" is undefined in his introduction; R12 uses the trace reading, which every
  reading implies. A reading fixing level, minimal twist or weight would be stronger. R13's
  normalization (Tate vs cohomological). R6 and R7 are Galois/finite-level consequences of the
  published statements (pkg-I2's derivations), to be recorded with their proofs. R1 is assembled
  from several statements of Shimura and Deligne and must be checked piece by piece.
- **R3. Unreviewed new lemmas.** In route P: pkg-I2's Raynaud route for G3 (drops R8, R7b, T3;
  SPECULATIVE until formalized). In route K: GK1, GK2 (no review; rv-routek pending). All of
  Glazer's glue (G7, G9, G12, G14, G15) and the repository's (G2, G3, G6) has model reviews only.
- **R4. Definitions in `Leaves.lean` are unreviewed** (hdec-faithful's §0, pkg-I2's §2). A wrong
  definition could make a leaf vacuous or false: `IsNormalizedEigenform` must match the Hecke
  definition; `GaloisRep.FrobTrace` is meaningful only at unramified primes; abelian varieties as
  `Grp (Over (Spec K))` need the commutativity and dimension conventions of pkg-I2.
- **R5. Placeholders.** 28 of the 48 leaf statements (47 leaves) are `opaque` placeholders; `sixContactMin_of_leaves`
  says nothing about them until they are replaced by genuine statements.

**Disagreements and resolutions.**
- *Leaf count.* hdec-faithful: 40 leaves (21 research + 19 textbook). hdec-elementary: 12
  research leaves + 5 textbook groups, route K, with Pazuki and Thomae merged and the Shimura-curve
  facts bundled (L2 = Baba–Granath + Lin–Yang). hdec-alt: 30 leaves (18 deep), route K.
  Resolution: no merging of distinct publications (the task's rule), so Baba–Granath, Lin–Yang,
  Igusa, Pazuki stay separate; route P is primary; 22 research leaves. The difference from
  hdec-faithful's 21 is that Eigenform representations (R14) and Deligne–Serre (R15) are counted
  separately, as distinct theorems.
- *Statability.* wk-h said the I2 package was not statable; pkg-I2 states it over Mathlib
  (VERIFIED: compiles). hdec-elementary and hdec-alt stated some leaves over invented placeholder
  structures (`Objects`, `opaque` types); those are not used here, since a leaf over an invented
  structure can be vacuous. Here unstatable leaves are uninterpreted Props with docstrings.
- *A6 (G3).* h-b1 (reviewed) uses R8 + Néron models; pkg-I2 proposes Raynaud + NOS, using that
  `B ⊗ ℚ₃` is a division algebra; hdec-elementary proposes a Galois-theoretic argument via
  Grothendieck's monodromy theorem. Resolution: keep h-b1's route in the count (R8 stays, marked
  droppable), record pkg-I2's as the leaner candidate.
- *D3's formal logarithm.* hdec-faithful lists Silverman IV.6.4 as an input; glue-conductor proves
  the needed unit identity in Lean (VERIFIED), so it is not a leaf.
- *Route.* hdec-faithful (route P) against hdec-elementary and hdec-alt (route K). Resolution in
  §1: P for the claim, K as fallback, pending rv-routek.
- *Name collision.* `docs/research/rv-route-k.md` is about a different "Route K" (pole
  completeness, `rs-pole.md`), not this one.
