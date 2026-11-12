# h-decomposition: hypothesis H as literature leaves plus glue (synthesis)

Status: research note (task hsyn, 2026-11-11). Lean companion:
`scratch/h-decomposition/Leaves.lean` (compiles with `lake env lean`; assembled from the reports'
compiled drafts by `scratch/hsyn/assemble.py`; results log `scratch/hsyn/log.md`). No file under
`ZInQKernel/`, `blueprint/` or another task's notes was edited.

**Inputs folded in.** The three designs `hdec-faithful.md`, `hdec-elementary.md`, `hdec-alt.md`
(with their Lean drafts) and **all eleven reports**: **pkg-I1** (the Shimura curve), **pkg-I2**
(reduction theory), **pkg-I3** (Faltings 1983 and Mumford), **pkg-I4** (modularity), **pkg-I5**
(Arakelov theory), **pkg-I6** (arithmetic of ℚ), **glue-descent** (Glazer's scalar descent),
**glue-conductor** (Glazer's conductor bound), **glue-assembly** (C8, C10, E1-E4, F2-F4),
**glue-repo** (the repository's Part A arguments) and **rv-routek** (adversarial review of route
K), each `docs/research/<task>.md` with `scratch/<task>/`.

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

**Claim for H** (the six-contact height estimate: the one instance of Theorem 4.1 of Glazer's
manuscript that the proof uses). On the manuscript's own route, H follows from **22
research-level theorems** of the literature, **32 textbook theorems** in six groups, and **21
glue steps**: the manuscript's new arguments, the repository's replacement arguments, and
bookkeeping. The glue is **not** formalized. It has been reviewed only by AI models; in Lean,
its last steps (from the level bound, the theta point and the height inequalities to H) and
Glazer's Brauer and cochain steps are proved, together with elementary pieces of most other
steps. No two research-level theorems have been merged to shorten
the list.

Research-level theorems ("read by a model": a repository note records an AI model's reading of
the published text; no human has checked it):

1. Shimura 1967 / Deligne 1971 (Thm 4.21): canonical model and moduli interpretation of the
   level-3 Shimura curve of discriminant 6, with Shimura reciprocity. UNVERIFIED.
2. Baba–Granath 2008 (Thm 2.1, Lemma 3.1): the Atkin–Lehner quotient and its branch points. Preprint read by
   a model; journal numbering UNVERIFIED.
3. Lin–Yang 2020 (Example 30): Igusa invariants on the quaternionic locus. arXiv v1 VERIFIED;
   journal numbering UNVERIFIED.
4. Igusa 1962/1967: the Siegel modular forms ψ₄, χ₁₀ in theta constants. UNVERIFIED (form
   checked numerically).
5. González–Rotger 2006 (Thm 5.12, Prop. 5.6): fields of definition of CM points. arXiv VERIFIED;
   journal numbering UNVERIFIED.
6. Raynaud (SGA 7 IX, Prop. 4.7): semistable reduction when the m-torsion is rational, m ≥ 3.
   UNVERIFIED (Silverberg–Zarhin's form read by a model).
7. Serre–Tate 1968 (Thms 1, 2): Néron–Ogg–Shafarevich and potential good reduction. UNVERIFIED.
8. Grothendieck (SGA 7 IX, Thm 3.6): semistable reduction theorem. UNVERIFIED.
9. Faltings 1983 (Satz 3, Satz 4): semisimplicity and the Tate conjecture for abelian varieties. Read
   by a model.
10. de Rham comparison (Scholze 2013 Cor. 1.8; or Faltings 1989, Tsuji 1999). UNVERIFIED.
11. Berger 2002 (Thm 0.7): de Rham implies potentially semistable. arXiv VERIFIED; journal
   read by a model.
12. Pan 2022 (JAMS, Thm 1.0.4): Fontaine–Mazur for GL₂ over ℚ, p odd. arXiv v2 statement
   VERIFIED; JAMS numbering UNVERIFIED.
13. Hodge–Tate weights of eigenform representations at every level (Saito 1997, or Kato 2004). UNVERIFIED.
14. Galois representations of eigenforms (Eichler–Shimura, Deligne 1971). UNVERIFIED.
15. Deligne–Serre 1974 (Thm 4.1): weight one gives finite image. UNVERIFIED.
16. Eichler–Shimura in J₁(N) (Shimura 1971 Thm 7.9; Shimura 1973 Thm 1). UNVERIFIED.
17. Carayol 1986 (Théorème A): local–global compatibility of the conductor. UNVERIFIED.
18. Javanpeykar 2014 (Thm 1.1.1): Faltings height of Jacobians of Belyi curves. Read by a model.
19. Gaudron–Rémond 2014 (Duke, Thm 1.4): explicit isogeny theorem. Read by a model.
20. Faltings 1983 (Lemma 5): variation of the Faltings height under isogeny. UNVERIFIED.
21. Bost 1996: lower bound for the Faltings height. Read by a model (as recorded by
    Gaudron–Rémond).
22. Pazuki 2012 (Cor. 1.3): theta height against Faltings height. Read by a model.

Textbook foundations: (a) purity of the branch locus and Abhyankar's lemma (SGA 1); (b) abelian
varieties: structure of torsion and of the Tate module, rank of Hom, ℓ-independence, Poincaré
reducibility, the QM dichotomy, the Weil pairing, the Néron mapping property for abelian schemes,
reduction of torsion, the Tate module against étale cohomology, Riemann/GAGA and Artin comparison;
(c) arithmetic of ℚ: Skolem–Noether, Hasse principle and reciprocity for H²(G_ℚ, ℤ/2), local H²,
local Kronecker–Weber and local class field theory with upper numbering, Kronecker–Weber,
Chebotarev, Brauer–Nesbitt, local normalizers of maximal quaternion orders, the local
square-root criterion, vanishing of unramified local classes, tame quadratic characters;
(d) ramification theory: Hilbert's different formula, the different bound, Herbrand's theorems; (e) Fontaine's
closure properties of de Rham representations; (f) modular forms and invariants: twists,
newforms, the Clebsch–Bolza–Igusa separation of binary sextics.

**What is in Lean today** (VERIFIED: `scratch/h-decomposition/Leaves.lean` compiles, no
`axiom`). 10 research-level leaves (items 4, 6, 7, 9, 10, 13, 14, 15, and 11 + 12 through their
joint consequence) and 25 textbook leaves, 35 of 54, are stated concretely over Mathlib, using
cheap genuine definitions built in the reports: abelian varieties as group objects over `Spec K`
with Tate modules and Galois action, good reduction as an abelian scheme over the valuation ring,
continuous Galois representations into `GL_n(ℚ̄_ℓ)`, Hodge–Tate weights and the de Rham
condition (on Mathlib's `ℂ_p` and `B_dR`), eigenforms and newforms through their q-expansions,
genus-2 theta constants as lattice sums, continuous Galois cohomology. The other 12
research-level and 7 textbook leaves are named placeholders that carry no content until their
definitions exist. Proved in Lean (axioms
`propext`, `Classical.choice`, `Quot.sound` only): the whole Arakelov end of the glue, from the
level bound, the theta point and the transfer inequalities to H (F2 on Mathlib's Weil heights,
E2-E4 and F3 arithmetic, the final constant, the return from `J(u)` to `u`); Glazer's Brauer and
cochain steps B2-B3 from four textbook leaves, ending in `[L':ℚ] ≤ Q·M`; the algebra of B1 and C1;
the whole arithmetic of the repository's Lemma PR(i) and NoCM; and elementary parts of most other
steps (quaternion order, weight and twist arithmetic, conductor arithmetic, the level bound,
consequences of Faltings' and of the reduction theorems). The top theorem "leaves ⇒ H" is
stated in Lean; its one `sorry` is the glue from the leaves to the numerical interface of the
Arakelov end.

**What cannot be stated in Lean today, and why.** Items 1-3, 5, 8, 16, 18-22 need definitions that
no Lean library has: the Shimura curve as a moduli scheme of QM abelian surfaces with its canonical
model (1-3, 5), Néron models (8), the modular curve X₁(N) and its Jacobian over ℚ (16, 18), the
stable Faltings height (18-22). Item 17 needs conductors of ℓ-adic representations (medium).
Items 11 and 12 separately need potentially semistable representations (very large), which the
proof does not need once they are combined. A further obstacle for the glue: Mathlib cannot yet
construct any nonzero abelian variety, so the surface `A` and `J₁(N)` must be produced by leaves
1 and 16.

**Alternative modularity route.** Items 10-15 (p-adic Hodge theory, Pan, eigenform
representations) can be replaced by Serre's conjecture (Khare–Wintenberger 2009) with Ribet's
theorem that it implies the modularity of GL₂-type abelian varieties over ℚ, plus two new glue
lemmas (§1). That route has 20 research-level theorems; one adversarial model review, and no
human, found it sound after five repairs; whether Ribet's 1992 proceedings paper was refereed is
unchecked.

**The CR3 side** (positive rank of congruent number curves). The implication from these
statements to the main theorem is kernel-checked (no `sorry`, axioms `propext`,
`Classical.choice`, `Quot.sound`):
- `Literature.GrossZagier`: a simple zero of L(E,s) at s=1 gives a point of infinite order.
  Not one printed sentence: Gross–Zagier 1986 with an auxiliary twist (Bump–Friedberg–Hoffstein
  1990) and modularity (Breuil–Conrad–Diamond–Taylor 2001).
- `Literature.FunctionalEquation5`: the functional equation of L(C_d, s), d ≡ 5 mod 8, with root
  number −1 (Deuring, Hecke; Birch–Stephens 1966); a textbook consequence, not one printed
  sentence.
- Tian–Yuan–Zhang, either as `Literature.TYZRow5b`, or as the pair
  `Literature.TYZThm35ReadingA` + `Literature.HeckeContinuation`, which `tyzRow5b_of_readingA`
  turns into `TYZRow5b`. **Neither TYZ form is a printed statement.** No refereed text that we
  have read states `TYZRow5b`. Theorem 1.2 of TYZ (arXiv:1411.4728v1), read literally, is false
  (d = 26565, 33117). `TYZThm35ReadingA` is the intended reading of their Theorem 3.5(2), with
  the hypothesis weakened to `𝓛(n) = 0`; its proof in the paper passes through a proposition
  whose proof is only sketched, and the journal version (Asian J. Math. 21 (2017)) has not been
  checked. `TYZRow5b` is proved from unambiguous results of the arXiv version, with Hecke's
  continuation, by Proposition N (`docs/research/nt-tyz.md` §4), a new argument reviewed twice by
  AI models and never by a human. `HeckeContinuation` is textbook (Deuring, Hecke).

**The exact claim the project can make.** "The main theorem is proved in Lean from two
hypotheses. The CR3 hypothesis is reduced in Lean to three statements about L-functions, with the
caveats above on Tian–Yuan–Zhang. Hypothesis H is reduced on paper to the 22 research-level
theorems and 32 textbook results listed, plus 21 glue steps; in Lean, 35 of these 54 leaves can
already be stated, and the last part of the glue is proved." It is **not** yet true that
formalizing the literature theorems alone would complete the proof: most of the glue for H
(Glazer's descent, modularity and conductor arguments, the repository's Lemma PR and NoCM) still
has to be formalized, and it has only model reviews.

---

## §1. Route decision: route P against route K

**Route P** (the manuscript's): Glazer builds a 2-dimensional representation `r_ℓ` of `G_ℚ` from
the QM surface by scalar descent, proves it de Rham with Hodge–Tate weights `{0,−1}` (appendix
lemma, from a de Rham comparison and Fontaine's closure), potentially semistable (Berger), odd,
irreducible, then applies Pan's theorem, fixes the twist and weight (Hodge–Tate weights of
eigenforms, Deligne–Serre, Kronecker–Weber), passes to a newform and to `J₁(N)`
(Atkin–Lehner–Li, Eichler–Shimura, Faltings) and identifies `r₃` with `r₅` in one compatible
system. Evidence: N5 L719-795; audited step by step in h-trust (C1-C10); the passages new in N5
(C3's appendix lemma, C8's determinant argument, C9, C10) have two model reviews each (rv-h-c3,
rv-h-c8, rv-h-a9c9, rv-h-novel). Pan's statement read in arXiv v2 by a model (h-a011 §1.1).
Statability (pkg-I4, VERIFIED: compiles): Hodge–Tate weights and the de Rham predicate are now
defined over Mathlib (`PkgI4.HasHTWeights`, `PkgI4.IsDeRham`, on `ℂ_p` and Mathlib's `BDeRham`), so
every route-P modularity leaf is stated except Shimura's `A_f` / Eichler–Shimura in `J₁(N)` (R16)
and general Carayol (R17); Pan and Berger are stated through their joint consequence
`PkgI4.PanBerger`, which avoids `B_st`.

**Route K** (hdec-elementary §2.2, hdec-alt §1.2): after the descent (C1, C2), the `ℚ`-simple
factor `B₀` of `Res_{L'/ℚ}A` carrying `r_ℓ` is of GL₂-type with `B₀,L' ∼ A^k` (Lemma GL₂, from
Faltings' theorem and Weil restriction); Serre's conjecture (Khare–Wintenberger) with Ribet's
theorem makes `B₀` a quotient of `J₁(N₀)`; Shimura's `A_f`, the newform decomposition, the
`ℚ`-simplicity of `A_f` and Carayol give a quotient map `J₁(N) → B₀` with `cond(B₀) = N^{dim B₀}`;
Glazer's local bounds pass to `Res A` by Mackey's formula (Lemma Ind).

**Review status (rv-routek, landed; VERIFIED as read).** Verdict **sound after repairs** for both
variants; constants unchanged (`[L':ℚ] ≤ QM`, `N ≤ QM²`, `h_F(A) ≤ Q¹⁷M²⁴`); Lemma GL₂ and Lemma
Ind verified as arguments; hdec-alt's claim that the dimension of `B₀` is unbounded is retracted
(`dim B₀ ≤ 2QM`). Repairs: (1) the citation must add Khare–Wintenberger II and Kisin 2009 (the level
may be even); (2) hdec-elementary's L7 is a bundle of four results, and its use at `p = 3` with
`ℓ = 2` needs Grothendieck's ℓ-independence of the conductor or Carayol at `ℓ = 2`; (3) Lemma
Ind's two facts (`G^u ⊂ G_{L'}` for `u > U₀`; normality and Mackey) must be written out; (4)
"for an embedding τ" must read "for some τ"; (5) prefer Lemma GL₂ to Ribet–Pyle's converse.
Unchecked: every theorem number of Ribet 1992, Pyle 2004, Khare–Wintenberger, Kisin, Carayol;
whether Ribet 1992 and Pyle 2004 (proceedings volumes, reprinted in Progr. Math. 224) were refereed.

**Route K's leaves** (replacing R10-R15 and T9, T17, T23; R16 and R17 stay, inside the bundle):
- K1. Serre's modularity conjecture: Khare–Wintenberger, Invent. Math. 178 (2009) (I) and (II)
  (main theorems UNVERIFIED), whose proof uses Kisin, Invent. Math. 178 (2009) at `p = 2`.
- K2. Ribet: Serre's conjecture implies that every abelian variety of GL₂-type over `ℚ` is a
  quotient of some `J₁(N)` (Ribet 1992, Thm 4.4, UNVERIFIED; reprinted Progr. Math. 224 (2004)).
- K3. Ribet: the abelian variety `A_f` is `ℚ`-simple (Ribet 1975/1980, UNVERIFIED).
- K4. Grothendieck: the conductor exponent of an abelian variety at `p` is independent of
  `ℓ ≠ p` (SGA 7 I, Exp. IX, UNVERIFIED), unless Carayol's Théorème (A) is checked at `ℓ = 2`.
- Textbook: Milne, Invent. Math. 17 (1972) §1 (`V_ℓ(Res A) ≅ Ind V_ℓ(A)`), Mackey's formula.
- Count: 22 − 6 (R10-R15) + 4 = **20 research leaves** (19 if Carayol covers `ℓ = 2`). Glue:
  G9, G10, G12, G14 replaced by GK1 (Lemma GL₂) and GK2 (Lemma Ind), with repairs 1-4.

**Recommendation: route P** for the announced decomposition, **route K as the fallback.**
Reasons. (i) A leaf must be a refereed published theorem; K2 (Ribet 1992) and the converse
direction of Pyle appeared in proceedings whose refereeing is UNVERIFIED, while every route-P
modularity leaf is a journal paper (Pan in JAMS). (ii) Route K is not shorter: 20 research
leaves against 22, and its deep core (Khare–Wintenberger with Kisin) is not shallower than Pan's
(rv-routek §1: more mature, not less deep). (iii) After pkg-I4, route P is at least as statable as
route K: its p-adic Hodge theory no longer blocks any statement, and both routes need `J₁(N)` and
conductors. (iv) Route P is the manuscript's proof, with every step audited in h-trust and its new
passages reviewed twice; route K's glue has one adversarial review and five pending repairs.
Switch to route K if Ribet 1992's refereed status and the printed statements of K1-K2 are
confirmed and repairs 1-4 are written: it then removes the appendix lemma, oddness, the
twist-and-weight argument and the compatible system from the trust base.

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
C (PEL theorem specialized; assembled from several statements, §6 R2). Objects: abelian schemes,
PEL moduli, CM points. Lean: **no** (very large; pkg-I1's I1-a). It must be stated so that it
produces the fibre surface `A` as a Lean object (§6 R6). Formalized: none (Anthropic FLT has QM
fake elliptic curves for Čerednik–Drinfeld; use for `Y₃/ℚ` unchecked). Steps A3-A6, A10.

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
conversion to `J₂..J₁₀`. Ref: Amer. J. Math. 89 (1967), pp. 833-834, 848; Amer. J. Math. 84
(1962). C in the form stated: `Σθ_m⁸` and `Πθ_m²` transform under `Sp₄(ℤ)` with weights 4 and 10
(signs and weights VERIFIED numerically by pkg-I1, `theta_modular.py`). Objects: genus-2 theta
constants as `tsum`s over `ℤ²`, `𝔥₂`, the `Sp₄(ℤ)` action (cheap, pkg-I1). Lean: **yes**,
`PkgI1.ThetaModularity`. The conventions linking `ψ₄, χ₁₀` to `J₂, J₄, J₁₀` enter through the proved
glue `PkgI1.f1_algebra`. Step F1. (hdec-elementary replaces R4 by Thomae's formula merged into R22;
not adopted: it merges two publications.)

*Statable consequence of R2 + R3 + R4 together* (pkg-I1's I1-b, not counted as a leaf because it
combines three publications): `PkgI1.QMHauptmodul`, "`3779136·Πθ⁴/(Σθ⁸)⁵ ∘ Ω(τ)` is a Hauptmodul of
`Γ*\ℍ` with values `0, ∞, −16/27` at the CM points of discriminants −4, −3, −24", for pkg-I1's
explicit period matrix `Ω(τ)` (numerically VERIFIED to 20-30 digits by pkg-I1). It says nothing
about the `ℚ`-structure, which is R1.

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

**R9. Faltings 1983.** (a) `V_ℓ(A)` is a semisimple `G_F`-representation; (b)
`Hom_F(A,B) ⊗ ℤ_ℓ → Hom(T_ℓA, T_ℓB)` is injective with image the `G_F`-equivariant maps. Ref:
Invent. Math. 73 (1983), Satz 3, Satz 4, Korollar 1, pp. 360-361 (read by a model); erratum 75
(1984). E. Objects: abelian varieties, `Hom`, `T_ℓ`, `V_ℓ` with Galois action, all defined by
pkg-I3 on Mathlib's group schemes (`PkgI3.AbVar`, `AbVar.T`, `AbVar.galRep`). Lean: **yes**,
`PkgI3.FaltingsSemisimple`, `PkgI3.FaltingsTate` (the easy inclusion of (b) is proved,
`PkgI3.range_tateHomZl_subset`, so the leaf asserts exactly the published content). Steps C2, C10,
E1.

**R10. de Rham comparison.** For `F/ℚ_ℓ` finite and `A/F`, `H¹_et(A_F̄, ℚ_ℓ)` is de Rham with
`D_dR ≅ H¹_dR(A/F)`; `V_ℓ(A)` has HT weights `0, −1`, each with multiplicity `dim A`. Ref: Scholze,
Forum Math. Pi 1 (2013), Cor. 1.8, Thms 9.1, 9.3 + corrigendum; or Faltings 1989, Tsuji 1999. E
(first clause); the Tate-module form stated in Lean is a consequence with T10. Lean: **yes**,
`PkgI4.DeRhamComparison`, over pkg-I3's Tate modules (copied as `PkgI4.I3`) and pkg-I4's de Rham
predicate (`G_F`-action on Mathlib's `BDeRham 𝓞_ℂ_p`, `D_dR`, `IsDeRhamOver`) and Hodge–Tate
weights. Step C3.

**R11. Berger.** de Rham ⇒ potentially semistable. Ref: Invent. Math. 148 (2002), Thm 0.7 (read
by a model; arXiv v3 Thm 0.6 VERIFIED by rv-h-a011). E. Lean: alone, **new defs** (`B_st`;
very large; template `PkgI4.BergerDR IsPst`); jointly with R12, **yes** (below). Step C4.

**R12. Pan.** `p` odd, `ρ : G_ℚ → GL₂(ℚ̄_p)` continuous irreducible, finitely ramified,
potentially semistable at `p`, odd, distinct HT weights (residual clause at `p = 3`) ⇒ there are a
normalized eigenform `g` and a continuous character `ψ` with `tr ρ(Frob_v) = ψ(Frob_v)·ι(a_v(g))`
for almost all `v`. Ref: JAMS 35 (2022), Thm 1.0.4 (arXiv v2 statement VERIFIED by h-a011). C
(the trace reading; every reading in the literature implies it; §6 R2). Lean: alone, template
`PkgI4.PanFor IsPst` (missing only `IsPst`); jointly with R11, **yes**: `PkgI4.PanBerger`, Pan's
theorem with "de Rham at `p`" in place of "potentially semistable at `p`", the form N5 uses
(a consequence of R11 + R12, not a merged leaf: both are counted). Step C7.

**R13. Hodge–Tate weights of eigenforms, every level.** `ρ_{g,ι}` for a weight-`k ≥ 2` eigenform
of any level is HT at `ℓ` with weights `{0, 1−k}` (Tate normalization). Ref: Saito, Invent. Math.
129 (1997); or Kato, Astérisque 295 (2004), §9.4; or Faltings 1987. C (normalization; rv-h-c8 R1).
Lean: **yes**, `PkgI4.EigenformHT` (Hodge–Tate multiplicities by Tate–Sen, `PkgI4.HasHTWeights`,
cyclotomic weight −1). Step C8.

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
defs** (conductor of an ℓ-adic representation; medium; template `PkgI4.CarayolFor a`); the
unramified case is stated, `PkgI4.CarayolUnramified`, but D5 needs `p | N`. Step D5.

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
| T1 | Zariski–Nagata purity, ring form | SGA 1 X 3.4; Stacks 0BMB | E | yes, `PkgI2.PurityBranchLocus` | Stacks formalization `etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne` (unreviewed); Tau Ceti dim ≤ 2 |
| T2 | Abhyankar's lemma, DVR form | SGA 1 X 3.6; Stichtenoth 3.9.1 | E | yes, `PkgI2.AbhyankarDVR` | Stacks 0EYG (unreviewed); Tau Ceti `Place.ramificationIdx_restrict_sup` (function fields) |
| **(b) Abelian varieties** | | | | | |
| T3 | Néron mapping property, abelian-scheme case | BLR §1.2 Prop. 8 | C | yes, `PkgI2.NeronMappingAbelianScheme` | Anthropic FLT (Néron models, special case) |
| T4 | Reduction of prime-to-`p` torsion is bijective | Serre–Tate 1968 §1 | C | yes, `PkgI2.ReductionTorsionBijective` | none |
| T5 | `A(K̄)[n] ≅ (ℤ/n)^{2g}`, `n` invertible | Mumford §4, §6 | E | yes, `PkgI2.TorsionStructure` | none |
| T6 | `Hom(A,B)` free of rank `≤ 4 dim A dim B`, injective into `Hom(T_ℓA, T_ℓB)` | Mumford §19 Thm 3 | E | yes, `PkgI3.HomFreeFinite` (also `PkgI2.HomRankBound`) | none |
| T7 | Characteristic polynomials integral, independent of `ℓ` | Mumford §19 Thm 4 | E | yes, `PkgI3.CharPolyIndepOfEll` (also `PkgI2.CharpolyIndependentOfEll`) | none |
| T8 | Poincaré reducibility, form used at E1 | Mumford §19 Thm 1 | C | yes, `PkgI3.PoincareReducibility` | none |
| T9 | Galois-equivariant Weil pairing, `GSp` with cyclotomic multiplier | Mumford §§20, 23 | E | new defs (polarizations; medium) | none |
| T10 | `V_ℓ(A) ≅ H¹_et(A_K̄, ℚ_ℓ)^∨` | Milne 1986, Thm 15.1(a) | E | new defs (étale cohomology; large) | none |
| T11 | Riemann/GAGA/rigidity: `End⁰(A_ℂ)` = Hodge endomorphisms, `Hom_ℚ̄ = Hom_ℂ` | Mumford §§1-3; Serre 1956; Conrad 2006 | E | new defs (analytification; large) | Tau Ceti: Riemann forms |
| T12 | Artin comparison with complex conjugation | SGA 4 XI 4.4 | E | new defs (as T11) | none |
| T26 | `T_ℓ(A)` free of rank `2 dim A` over `ℤ_ℓ`, `ℓ ≠ char` | Mumford §§4, 18-19 | E | yes, `PkgI3.TateModuleFree` | none |
| T27 | QM dichotomy: a quaternion division algebra in `End⁰` of an abelian surface over `k = k̄`, char 0, forces `End⁰ ≅ B` or `M₂(ℚ(√d))`, `d < 0` | Mumford §§19, 21-22 (Albert); Shimura 1963 | C | yes, `PkgI3.QMDichotomy` | none |
| **(c) Arithmetic of ℚ** | | | | | |
| T13 | Skolem–Noether | Reiner Thm 7.21 | E | yes, `HSyn.SkolemNoether` (also `PkgI6.SkolemNoether`) | Tau Ceti `skolemNoether` |
| T14 | ABHN and reciprocity for `H²(G_ℚ, ℤ/2)`: injective into `∏_v H²(G_{ℚ_v}, ℤ/2)`, finite even support | Milne ADT I; Tate in C–F VII §11 | C | yes, `PkgI6.BrauerHasse2`, `PkgI6.BrauerReciprocity2`; the finite-places cochain form used by glue-descent, `GlueDescent.B2Q.LeafHasse`, is a consequence (with T15 at `∞`); algebra form `HSyn.HasseBrauerQ` also compiles | Tau Ceti (Br forms `brLocalization_injective`, `sumLocalInv_brLocalization_eq_zero`); the `H²` bridge not located |
| T15 | Local `H²(G_{ℚ_v}, ℤ/2) ≅ ℤ/2` | Serre, *Corps locaux* XIII §3, X §5 | E | yes, `PkgI6.LocalH2Card` | Tau Ceti `h2MuEquivZMod` (compatibility unknown) |
| T16 | Local Kronecker–Weber for `ℚ_p`; local reciprocity at a finite abelian level with the upper numbering theorem | Neukirch V (1.10); Serre XIII §4, XV §2 | E | yes, `PkgI6.LocalKroneckerWeber`, `PkgI6.LocalReciprocityUpper` | not located |
| T17 | Kronecker–Weber | Washington Thm 14.1 | E | yes, `HSyn.KroneckerWeber` | Tau Ceti `kroneckerWeber` |
| T18 | Frobenius elements are dense in `G_ℚ` (Chebotarev) | Neukirch VII.13.4 | C | yes, `HSyn.FrobeniusDense` (finite form `PkgI6.ChebotarevExists`) | Tau Ceti `hasNaturalDensity_frobeniusPrimeSet` |
| T19 | Brauer–Nesbitt (char 0, trace form) | Curtis–Reiner §30; Lang XVII 3.8 | E | yes, `HSyn.BrauerNesbitt` (also `PkgI6.BrauerNesbittChar0`) | none found |
| T29 | Local normalizers of maximal quaternion orders (index 2 at ramified `p`, 1 at split `p`) | Vignéras LNM 800 Ch. II | E | statable (pkg-I1 I1-f; glue-repo calls it elementary), not drafted: placeholder `HSyn.T29_LocalNormalizers` | none found |
| T30 | Local square-root criterion: `χ|G_{ℚ_p}` has a continuous square root iff `χ(u) = 1` for `u ≡ −1 mod p^k`, `≡ 1` prime to `p` | consequence of local CFT for `ℚ_p` (Serre, *Local fields*) | C | yes, `GlueDescent.B2Q.LeafSqrtCrit` | none |
| T31 | Unramified classes of `H²(G_{ℚ_p}, ±1)` vanish (`cd ℤ̂ = 1`) | Serre, *Galois cohomology* II §3 | C | yes, `GlueDescent.B2Q.LeafUnramified` | none |
| T32 | Tame inertia of `ℚ_p` has a unique quadratic character; a quadratic Dirichlet character ramifies exactly at its conductor | Serre, *Local fields* IV §2 | E | new defs (inertia subgroups of `G_ℚ`; cheap): placeholder `HSyn.T32_TameQuadratic` | none |
| **(d) Ramification** | | | | | |
| T20 | Hilbert's different formula | Serre, *Corps locaux* IV §1 Prop. 4 | E | yes, `GlueConductor.HilbertDifferentFormula` (also `PkgI6.HilbertDifferentFormula`) | Tau Ceti |
| T21 | Different bound `v(𝔇) ≤ e − 1 + v(e)` | Serre III §6 | E | yes, `GlueConductor.SerreDifferentBound` (also `PkgI6.DifferentBound`) | not located |
| T22 | Herbrand: quotients `(G/H)^v = G^vH/H`, transitivity of `φ` | Serre IV §3 Props. 14, 15 | E | yes, `PkgI6.HerbrandQuotient`, `PkgI6.HerbrandTransitivity` | Tau Ceti `map_restrictNormalHom_upperRamificationGroup` |
| **(e) p-adic Hodge theory** | | | | | |
| T23 | Fontaine: de Rham representations closed under duals, ⊗, ⊕, subquotients | Astérisque 223, Thm 3.8 | E | new defs (large) | none |
| **(f) Modular forms, invariants** | | | | | |
| T24 | Twisting an eigenform by a Dirichlet character | Shimura 1971 Prop. 3.64; Atkin–Li 1978 | C | yes, `HSyn.EigenformTwist` | none |
| T25 | Newforms: each eigensystem away from the level is that of a newform of level dividing it | Li 1975 Thm 5; Miyake 4.6.19 | C | yes, `PkgI4.NewformOfEigenform` (newforms through the old space) | Tau Ceti (newform bookkeeping) |
| T28 | Clebsch–Bolza–Igusa: Igusa invariants separate `GL₂`-orbits of binary sextics with nonzero discriminant | Igusa, Ann. of Math. 72 (1960) | E | yes, `PkgI1.IgusaClebschSeparation` | none |

### §2.3 Counts (VERIFIED from the lists and the compiled file)

- Research-level: 22 leaves (R1-R22), 24 statements (R7 and R9 have parts a, b). Textbook: 32
  leaves (T1-T32), 35 statements (T14, T16, T22 have two parts). In all 54 leaves.
- Stated in Lean over genuine definitions: research R4, R6, R7, R9, R10, R13, R14, R15, and R11 +
  R12 jointly (`PkgI4.PanBerger`): 10 leaves, 11 Props; textbook T1-T8, T13-T22, T24-T28, T30,
  T31: 25 leaves, 28 Props. Total **35 of 54 leaves, 39 Props**. The other 19 leaves (R1-R3, R5,
  R8, R16-R22; T9-T12, T23, T29, T32) are `opaque` placeholders.
- New definitions needed: cheap for T29, T32; medium for R17, T9; large for R8, T10, T11, T12,
  T23; very large for R1-R3, R5 (QM moduli), R16, R18 (`J₁(N)`), R18-R22 (Faltings height).
- Route K (§1): 20 research leaves.

---

## §3. The glue

Sizes (SPECULATIVE): small < 500 lines, medium 0.5-3k, large 3-10k. Origin: N5 (Glazer's
argument, with line numbers), repository (with its note), or a report of this round. Every glue
item has model reviews only, except what is marked proved.

| # | Statement | Inputs | Origin | Lean status | Size |
| --- | --- | --- | --- | --- | --- |
| G0 | The leaves imply `SixContactMin` | G1-G20 | N5 L404-964 | **stated**: `HSyn.sixContactMin_of_leaves` = (G1-G17, G19 non-Arakelov part: `HSyn.glueOutputs_of_leaves`, `sorry`) then (G18-G20: **proved**) | small |
| G1 | Fibre datum: Gram matrix det 1, Rosati, unique polarization, normalizer index 4, `deg(Y₃→P¹_j) ≤ 324` | R1, R2, T29 | N5 L410-441; h-b1 M1-M3 | **proved**: `𝒪` an order of discriminant 6, Gram determinant 1, the Rosati identity and positivity, `|(𝒪/3𝒪)^*| = 72`, `4·72 ≤ 324` (glue-repo `A1Quaternion.lean`; `PkgI1.gram_det`); CM elements of `𝒪` (`PkgI1.cm4`, `cm3`, `cm24`); the quotient `Y₃/Γ' = P¹_j` needs R1's objects | medium |
| G2 | Lemma PR(i): fibre field `K` Galois, `[K:ℚ] ≤ 324!`, unramified outside `T`; `J(u)` not a branch value | G1; R1(d), R2, T1, T2 | repository, h-b1 (rv-h-b1) | **proved**: the whole valuation case analysis of PR(i) (for `p ≥ 17`, the three inertia orders are 1 iff `p ∤ M_S(u)`, `GlueRepo.PR.inertia_orders_eq_one_iff`), `[K:ℚ] ≤ 324!`, `G⁶ − 97200F² = H²`, `J(u)` finite, nonzero, not a branch value (`PkgI1.G6_sub_F2`, `Ju_ne_branch`); unproved: Prop. TS itself (from T1-T2 or Beckmann 1991 Prop. 4.2) and Lemma NV | large |
| G3 | Lemma PR(ii): `A`, `σA` good reduction at `v ∤ 3` | R1(a); h-b1 route: R8, R7b, T3; Raynaud route: R6, R7a, T4, T5 | repository, h-b1 §4(ii); Raynaud route new in pkg-I2 §4.2 | statement compiles (`PkgI2.goodReduction_of_QM_rational3`, body `sorry`); `1 + 3M_r(ℤ₃)` torsion-free and `B` a division algebra **proved** (glue-repo `TorsionFree.lean`) | medium |
| G4 | Conjugates have one moduli point; Hom field `L`, `[L:ℚ] ≤ D`, unramified outside `T` | G2, G3; R2, R3, T6, R7a, T28; Minkowski's lemma | N5 L532-563 | A7's algebraic step **proved** (`PkgI1.equiv_of_lyVec`, from T28); Minkowski's bound and `[EK:ℚ] ≤ F₀·3^{r²} ≤ D` **proved** (glue-repo); Weil restriction, the Hom field unproved | medium |
| G5 | `End⁰(A_ℚ̄) ∈ {B, M₂(k)}` | T27 (or T11 + centralizer) | N5 L564-577; pkg-I3 | immediate from T27 once `A` exists | small |
| G6 | NoCM: no CM point over `J(u)`, so `End⁰ = B` | G5; R1(d), R2, R5 | repository, h-cm, rv-h-cm §7.2 | **proved**: Elkies identities (`PkgI1.elkies_t`, `elkies_t_sub_one`), the fibre over `t(u)` is a free `W`-orbit with no real point and complex conjugation acts as `w₃` (`GlueRepo.PR.fibre_free`), `ℚ(√−2) ⊄ B`; the counting with R5 unproved | small |
| G7 | Scalar descent: `μ_σ`, `ε`, `χ` with `m ≤ 2R^R M`, `β`, `[L':ℚ] ≤ QM` | G4, G6; T13-T16 | N5 L632-716 (Glazer); pkg-I6 (B2 via local Kronecker–Weber, SPECULATIVE) | **B2-B3 proved** over Mathlib's `G_ℚ`, Dirichlet characters and intermediate fields from T14-T15 (glue-descent forms), T30, T31: `GlueDescent.B3Q.b3_degree_le_QM` gives `χ`, `β` with `β² = χ`, `∂β = ε`, `L'` Galois with `[L':ℚ] ≤ Q·M` against the repository's `heightQ`, `contactSupport`; B1's algebra (cocycle, sign normalization, centralizer `c ∈ ℚ^×`, `B` central simple) **proved** (glue-descent `B1Quat`, `Cochain`); B2's Brauer step also from pkg-I6's forms (`PkgI6.eq_of_same_finite_support`); unproved: unramifiedness of `L'` (needs T32), instantiation on the actual `A` | medium-large |
| G8 | `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`, Tate action on `G_{L'}`, `r_ℓ|G_{L'}` absolutely irreducible | G7; R9, T26, T6 | N5 L719-734 | C1's algebra **proved** (`ρ` a representation commuting with `B ⊗ E`, the Tate action on `G_{L'}`, `ρ ≅ r ⊕ r` by matrix units: glue-descent `ProjRep`); C2's Faltings part **proved** (`PkgI3.finrank_equivEnd`); instantiation on `A` unproved | medium |
| G9 | Appendix lemma: `r_ℓ` de Rham, weights `{0,−1}` | G8; R10, T23, T10 | N5 L10939-11000 | needs `B_dR` | medium |
| G10 | `r_ℓ` odd | G8; T11, T12 | N5 L742-751 | needs T11-T12 | medium |
| G11 | `r_ℓ` unramified outside `T ∪ {ℓ}` | G2, G3, G4, G7; R7a | N5 L752-754 | core **proved** (`PkgI2.inertiaTrivial_of_goodReduction`) | small |
| G12 | Twist finite, `k = 2` | G8-G11; R11-R15 (R11-R12 as `PanBerger`), T9, T17-T19 | N5 L757-768, V16 L660-667 | weight arithmetic in both normalizations and the determinant argument **proved** (`HSyn.weight_match`, `GlueAssembly.weight_match_coh`, `GlueAssembly.twist_finite`) | medium |
| G13 | Newform `f` of weight 2, `r₅ ≅ ρ_{f,5}`, constituent of `V₅(J₁(N))` | G12; T24, T25, R16, R9, T18, T19 | N5 L768-774 | needs `J₁(N)` | medium |
| G14 | `r₃`, `r₅` in one compatible system | G3, G7, G13; T7, T3, T4, T18, T19, R9 | N5 L776-795 | needs Galois representations of abelian varieties with Frobenius | medium |
| G15 | Conductor exponents `≤ E₀` (`p ≤ R`), `≤ 2` (`R < p ∈ T`), `0` outside `T` | G3, G7, G14; R6, T16, T20-T22 | N5 L796-852 (Glazer); glue-conductor | D1 **proved** from T20-T21 over Mathlib (`GlueConductor.D1_genuine`); break, Herbrand, Swan/Artin arithmetic **proved**; `(U^{e+1})⁴ = U^{3e+1}` **proved** (`GlueConductor.fourth_pow_mem`; removes Silverman IV.6.4; pkg-I6's form `HSyn.sq_principalUnits_proved`); D2 core **proved** (`PkgI2.D2_fixed_of_raynaud`); D4's `f(V) ≤ dim V·(1+U)` stated (`PkgI6.artinConductor_le_of_upper`, `sorry`) | large |
| G16 | `N ≤ ∏_{p≤R} p^{E₀}·M² ≤ Q_R·M²` | G13, G15; R17 | N5 L852-857 | **proved** from the exponents over the repository's `heightQ`, `contactSupport` (`GlueConductor.level_le`) | small |
| G17 | `L'`-isogeny `A × Z → J₁(N)` | G6, G13; R9, T8, T26 | N5 L861-867 | **proved**: nonzero equivariant map ⇒ nonzero homomorphism (`PkgI3.exists_hom_ne_zero_of_equivariant`) and invariants under coefficient extension (`GlueAssembly.invariants_ne_bot_of_baseChange`); the assembly with T8 unproved | small-medium |
| G18 | `h_F(A) ≤ Q¹⁷M²⁴` | G16, G17; R18-R21 | N5 L868-905 | **proved** as arithmetic from the inequalities (`GlueAssembly.transfer_of_level`), with `[SL₂(ℤ):Γ₁(N)] ≤ N²` (`GlueAssembly.index_Gamma1_le`) | small |
| G19 | `h(J(u)) ≤ 40h([z_m]) + 22`, `h([z_m]) ≤ 10⁴·2²⁴max(1,h_F(A))` | G18; R3, R4, R22 | N5 L908-947 | **proved**: F2 on Mathlib's Weil heights (`GlueAssembly.logHeight_Phi_le`), heights of rationals in number fields, F3 normalizations and arithmetic, F1's algebra (`PkgI1.f1_algebra`) and theta-structure independence (`PkgI1.thetaRatio_invariant`); unproved: that the theta point of the actual `A` satisfies F1 (from R1-R4) | medium |
| G20 | `JHeightBound Mult.S_mul → SixContactMin` | — | N5 L949-964 | **proved** (`ZInQ.JHeight.sixContactMin_of_jHeightBound`) | — |

**The proved end of the glue** (glue-assembly, VERIFIED here: `HSyn.sixContactMin_of_glueOutputs :
GlueAssembly.GlueOutputs Mult.S_mul → ZInQ.SixContactMin`, axioms `propext`, `Classical.choice`,
`Quot.sound`, checked against the repository's own `ZInQ.SixContactMin`). `GlueOutputs` asks, for
each `u ∉ 𝒞`, for a number field `K`, a point `z ∈ K¹⁰` with `3779136(∏z)⁴/(Σz⁸)⁵ = J(u)`, a real
`h_A` with Pazuki's bound for `h(z)`, and the numerical outputs of the non-CM transfer (the level
`N ≤ QM²`, `h_F(J₁(N)) ≤ 1.3·10⁷N¹²`, `[L':ℚ] ≤ QM`, the Gaudron–Rémond degree bound, Faltings'
variation with additivity, Bost). **As a Prop it is a height bound in disguise, not a leaf**
(glue-assembly §0.2): it is the contract between the leaves and the proved end. Each conjunct is
what one leaf, applied to the actual varieties, must deliver.

Route K replaces G9, G10, G12, G14 by **GK1** (Lemma GL₂: `r_ℓ` is a constituent of `V_ℓ(B₀)` for a
GL₂-type `ℚ`-simple factor `B₀` of `Res_{L'/ℚ}A`, and `B₀,L' ∼ A^k`; inputs R9, T8, Weil
restriction) and **GK2** (Lemma Ind: Glazer's local bounds for `V_ℓ(Res A)` via Mackey; inputs as
G15), both NEW and unreviewed (hdec-elementary §2.2); G13 and G17 become "K2 gives
`J₁(N) → B₀`, T8 gives `J₁(N)_{L'} ∼ A × Z`".

---

## §4. Definitions

| Object | Needed by | Status (declaration) | Cost |
| --- | --- | --- | --- |
| `ℚ̄`, `G_ℚ` with Krull topology | all Galois leaves | Mathlib `AlgebraicClosure`, `AlgEquiv` topology, `Field.absoluteGaloisGroup` | — |
| places of `ℚ̄`, decomposition/inertia groups, Frobenius | R12-R15, T18, G11 | `HSyn.LiesOver`, `IsArithFrob` on Mathlib `ValuationSubring.decompositionSubgroup`, `inertiaSubgroup`; Mathlib `IsArithFrobAt` | cheap (done) |
| continuous `GL_n(ℚ̄_ℓ)`-representations, irreducible, semisimple, odd | R12, R14, R15, T19 | `HSyn.GaloisRep` on Mathlib `PadicAlgCl` | cheap (done) |
| cusp forms on `Γ₁(N)`, nebentypus, normalized eigenforms, attached representation | R12-R17, T24 | `HSyn.CF`, `IsNormalizedEigenform`, `AttachedTo` on Mathlib `CuspForm`, `qExpansion` | cheap (done; §6) |
| abelian varieties over a field, points, Galois action, torsion | R6-R9, T3-T8, T26, T27 | two versions: `PkgI2.IsAbelianVariety` (predicate on `Grp (Over (Spec K))`) and `PkgI3.AbVar` (bundled, with `Hom`, `End⁰`, base change) | cheap (done; to be unified) |
| Tate modules `T_ℓ`, `V_ℓ` with continuous Galois action | R9, T6-T8, T26, G8-G17 | `PkgI3.AbVar.T`, `AbVar.V`, `AbVar.galRep` (a Mathlib `Representation`) | cheap (done) |
| abelian schemes over a DVR, good reduction, reduction map | R7, T3, T4, G3 | `PkgI2.IsAbelianScheme`, `HasGoodReduction`, `IsReductionOf` | cheap (done) |
| regular local rings, étale/unramified at a prime | T1, T2 | Mathlib `IsRegularLocalRing`, `Algebra.IsEtaleAt` | — |
| different ideal, lower ramification groups, upper numbering at finite level, Artin conductor of a finite-level representation | T20-T22, G15 | Mathlib `differentIdeal`, `Ideal.inertia`; `PkgI6.lowerRam`, `upperRam`, `artinConductor` | cheap (done) |
| continuous Galois cohomology `H²(G_ℚ, ℤ/2)` | T14, T15, G7 | Mathlib `continuousCohomology` | — |
| genus-2 theta constants, `𝔥₂`, `Sp₄(ℤ)` action; Igusa invariants of sextics | R4, T28, G19 | `PkgI1.thetaConst`, `SiegelH2`, `spAct`, `J2`..`J10` | cheap (done) |
| central simple algebras, quaternion algebras | T13, T14, G1 | Mathlib | — |
| polarizations, Weil pairing | T9, G12 | missing | medium |
| conductors of ℓ-adic representations of `G_{ℚ_p}` (infinite level) | R17, G15 | missing (finite level in `PkgI6`) | medium |
| old space, newforms | T25, R17 | `PkgI4` (through the old space, no Petersson product); Tau Ceti | cheap (done) |
| Néron models | R8 | Anthropic FLT (special case) | large |
| ℓ-adic étale cohomology | T10 (to derive R10's Tate-module form) | missing | large |
| analytification, complex tori, Hodge structures | T11, T12, G10 | Tau Ceti (Riemann forms); GAGA missing | large |
| `G_{ℚ_p}` acting on `ℂ_p` and on `B_dR`; de Rham predicate, `D_dR`; Hodge–Tate multiplicities | R10-R13, T23, G9, G12 | `PkgI4.IsDeRham`, `IsDeRhamOver`, `HasHTWeights` on Mathlib `ℂ_[p]`, `BDeRham` (pkg-I4, about 500 lines, no `sorry`) | cheap (done) |
| filtration on `B_dR`, closure properties | T23 | missing | medium |
| `B_st`, potentially semistable | R11, R12 separately (not needed: `PanBerger`) | missing | very large |
| a nonzero abelian variety at all (projective group schemes) | applying every abelian-variety leaf | missing (pkg-I3 §7: Mathlib cannot construct one) | large |
| QM abelian schemes with PEL structure, `Y₃`, canonical model, `X₆`, Atkin–Lehner, CM points | R1-R3, R5, G1-G6 | missing | very large |
| `X₁(N)`, `J₁(N)` over `ℚ`, Belyi maps | R16, R18, G13, G17 | missing (Anthropic FLT: Jacobians) | very large |
| stable Faltings height | R18-R22, G18, G19 | missing; pkg-I5 gives acceptance tests (closed formula for elliptic curves, genus-2 good-model formula) | very large |
| Weil restriction of abelian varieties; conductor of an abelian variety | route K (GK1, K3) | missing | medium |
| Weil heights | G19, G20 | Mathlib `NumberTheory/Height` | — |

---

## §5. Work packages for crowdsourcing

| WP | Content | Depends on | Unlocks |
| --- | --- | --- | --- |
| WP1 | Review the cheap definitions of `Leaves.lean`; unify `PkgI2.IsAbelianVariety` with `PkgI3.AbVar`; prove sanity lemmas (Frobenius trace independent of place and lift at unramified primes; eigenform recursion ⇔ Hecke eigenvector; torsion finite; `T_ℓ` of `ℤ/ℓⁿ`-points) | none | trust in all 39 stated Props (35 leaves) |
| WP2 | Prove statable textbook leaves from existing libraries: T13, T17, T18 (port Tau Ceti), T14-T15 (bridge Tau Ceti's Br forms to `H²`), T1, T2 (port Stacks/Tau Ceti), T20, T22 (Tau Ceti), and self-contained T19, T21, T29 | WP1 | 12 textbook leaves |
| WP3 | Glue provable now: pkg-I6's forms of T14-T15 ⇒ glue-descent's `LeafHasse`, `LeafLocalTwo`; D4's `artinConductor_le_of_upper`; glue-assembly's "finite-image character is Dirichlet"; T29 (elementary); Prop. TS over `RatFunc ℚ` from T1-T2 | none | glue skeleton |
| WP4 | Abelian-variety layer: polarizations, isogenies, products, Weil restriction; and at least one nonzero abelian variety (Jacobians or projective group schemes) | WP1 | T9; G8, G11, G14, G17 applied to actual varieties; route K's GK1 |
| WP5 | ℓ-adic conductors at infinite level (on `PkgI6` and Tau Ceti) | WP4 | R17; **G15 in full** (Glazer's conductor bound, the new mathematics most worth checking early) |
| WP6 | Instantiate G7-G8 (B1, C1 algebra and B2-B3 already proved by glue-descent) on the actual abelian surface; unramifiedness of `L'` with T32 | WP4 | G7, G8 |
| WP7 | Fontaine's closure (T23) and N5's appendix lemma (G9) as statements over pkg-I4's de Rham layer; principality of `ker θ` | — | T23, G9 |
| WP8 | Prove the p-adic Hodge theory leaves (R10, R11+R12 via `PanBerger`, R13) — the deepest route-P leaves; long term | WP7 | route P's modularity block |
| WP9 | `X₁(N)`, `J₁(N)` over `ℚ` | WP4 | R16, R18; G13, G17; route K's K2 |
| WP10 | Stable Faltings height, with pkg-I5's acceptance tests | WP4, Néron models | R18-R22; instantiating `GlueOutputs` |
| WP11 | Classical analysis and invariant theory: prove T28 (first fundamental theorem for sextics) and R4 (theta transformation formula in genus 2) | — | 2 leaves closed |
| WP12 | QM moduli scheme `Y₃`, canonical model, CM points | WP4 | R1-R3, R5, G1-G6 |
| WP13 | Statement checks: locators, Pan's trace reading, QM dichotomy's locator, Ribet's printed form (route K) | none | §6 |

---

## §6. Risks

**Checks to do first.**
- **R1. Locators.** Almost every theorem number is UNVERIFIED in the published version. Most
  worth checking before the announcement: Pan (JAMS numbering of Thm 1.0.4), Baba–Granath and
  Lin–Yang (journal numbering), Carayol (Théorème A covers `p | N` for `F = ℚ`), Javanpeykar
  (field and `g ≥ 1`), Gaudron–Rémond, Pazuki (`max(1, ·)` in `X_D`, the constant `C₂`), Faltings
  Lemma 5 in inequality form (all model readings only), and a refereed locator for T27, the QM
  dichotomy (pkg-I3 §7).
- **R2. Leaves at risk of being stronger than published.** Pan's conclusion "comes from a cuspidal
  eigenform up to twist" is undefined in his introduction; R12 uses the trace reading, which every
  reading implies; a reading fixing level, minimal twist or weight would be stronger. R13's
  normalization (Tate vs cohomological). R6, R7, T3, T4 are Galois/finite-level consequences of
  published statements (pkg-I2's derivations), T27 is a consequence assembled from Mumford §§19,
  21-22, and R4 is stated as the transformation law, not as Igusa's identity; each derivation must
  be recorded with its proof. R1 is assembled from several statements of Shimura and Deligne.
- **R3. Unreviewed new lemmas.** In route P: pkg-I2's Raynaud route for G3 (drops R8, R7b, T3);
  pkg-I6's B2 through local Kronecker–Weber and D3 without norm functoriality (both SPECULATIVE
  until written). In route K: GK1, GK2, verified as arguments by one adversarial model review
  (rv-routek) with five repairs pending. All of Glazer's glue (G7, G9, G12,
  G14, G15) and the repository's (G2, G3, G6) has model reviews only.
- **R4. Definitions are unreviewed.** A wrong definition could make a leaf vacuous or false:
  `IsNormalizedEigenform` must match the Hecke definition; `GaloisRep.FrobTrace` is meaningful only
  at unramified primes; the two abelian-variety definitions must agree; pkg-I1's period matrix
  `Ω(τ)` and characteristic conventions were checked numerically only; pkg-I4's `B_dR` action and
  Hodge–Tate multiplicities need non-vacuity checks (pkg-I4 §3.4: `ℚ_p(1)` has weight −1,
  `ℚ_p` is de Rham). `Leaves.lean` contains three copies of the abelian-variety layer
  (`PkgI2`, `PkgI3`, and `PkgI4.I3`, a renamed copy of `PkgI3`) and two of the Galois-representation
  layer (`HSyn`, `PkgI4`); they must be merged before the leaves are offered.
- **R5. Placeholders and the numerical interface.** 19 of the 54 leaves are `opaque`
  placeholders; `sixContactMin_of_leaves` says nothing about them until they are replaced by
  genuine statements. `GlueAssembly.GlueOutputs` is a numerical contract, not a leaf; it must not
  be offered to contributors as a statement to prove from the literature.
- **R6. Objects, not only statements.** Even with every leaf proved, the glue needs the actual QM
  surface and `J₁(N)` as Lean objects; Mathlib cannot construct a nonzero abelian variety today
  (pkg-I3 §7). R1 and R16 must therefore be stated so that they produce these objects.

**Disagreements and resolutions.**
- *Leaf count.* hdec-faithful: 40 leaves (21 research + 19 textbook). hdec-elementary: 12
  research leaves + 5 textbook groups (route K, Pazuki with Thomae merged, Baba–Granath with
  Lin–Yang bundled). hdec-alt: 30 leaves (18 deep), route K. The package reports add textbook
  leaves that the designs had hidden in glue (T26 Tate module free, T27 QM dichotomy, T28
  Igusa–Clebsch separation, T29 local normalizers, T15 local `H²`, T16 local Kronecker–Weber).
  Resolution: no merging of distinct publications, route P primary: 22 research leaves; the
  difference from hdec-faithful's 21 is that R14 (eigenform representations) and R15
  (Deligne–Serre) are counted separately.
- *Statability.* wk-h judged packages I2, I3 and I6 not statable; pkg-I2, pkg-I3 and pkg-I6 state
  them over Mathlib (VERIFIED: compile here). hdec-faithful's placeholders for L15b, L16, L20 are
  replaced by pkg-I6's leaves, and for L4, L21, L11c by pkg-I1's and pkg-I3's. hdec-elementary and
  hdec-alt stated some leaves over invented placeholder structures (`Objects`, `opaque` types);
  those are not used, since a leaf over an invented structure can be vacuous. pkg-I5 shows the
  Faltings height cannot be avoided (heights of `J₁(N)` of dimension up to `N²`), so R18-R22 wait
  for that definition; its special-case leaves (Bost and Pazuki for good genus-2 Jacobians) are
  faithful but not sufficient for H and are not included.
- *Route K's merits.* pkg-I4 (§4, §6): route K needs no period rings but is now no better for
  statability, since `PanBerger` compiles; rv-routek: sound after repairs, deep core more mature
  (2009) but not less deep. hdec-elementary and hdec-alt recommended route K. Resolution (§1):
  route P, because K2's refereed status is unverified and route K is not shorter (20 vs 22).
- *B2's two formalizations.* pkg-I6 proves the Brauer step from the printed-form leaves
  (injectivity, reciprocity, local `H²`); glue-descent proves all of B2-B3 from finite-place
  cochain forms. Resolution: pkg-I6's forms are the leaves (T14, T15), glue-descent's forms are
  derived from them (WP3), and glue-descent's theorem carries the glue.
- *Leaf count, glue-repo.* glue-repo lists 14 Part-A leaves, including Beckmann's Prop. 4.2 (an
  alternative to T1-T2 for Prop. TS), Morita 1981 (an alternative to R8) and Elkies 1998 (a
  cross-check of the model used in NoCM, derived from R1(d) and R5). Resolution: alternatives and
  cross-checks are not counted; T29 (local normalizers) is counted as a textbook leaf although
  glue-repo calls it elementary.
- *A6 (G3).* h-b1 (reviewed) uses R8 + Néron models; pkg-I2 proposes Raynaud + NOS (using that
  `B ⊗ ℚ₃` is a division algebra); hdec-elementary a Galois-theoretic argument via Grothendieck's
  monodromy theorem. Resolution: keep h-b1's route in the count (R8 marked droppable), record
  pkg-I2's as the leaner candidate.
- *A9 (G5).* hdec-faithful: Riemann's theorem (T11) and a centralizer computation; pkg-I3: the QM
  dichotomy T27 as a textbook consequence. Resolution: T27, with its locator as a first check;
  T11 remains for oddness (G10).
- *B2's local input.* N5 and hdec-faithful: local reciprocity (T16 in full); pkg-I6: local
  Kronecker–Weber suffices. Both are in T16; the weaker route is SPECULATIVE until written.
- *D3's formal logarithm.* hdec-faithful lists Silverman IV.6.4; glue-conductor proves the unit
  identity in Lean, so it is not a leaf. pkg-I6 states the same lemma with `sorry` (it had not
  seen the proof); `Leaves.lean` proves pkg-I6's statement from glue-conductor's
  (`HSyn.sq_principalUnits_proved`).
- *Route.* hdec-faithful (route P) against hdec-elementary and hdec-alt (route K). Resolution in
  §1: P for the claim, K as fallback (rv-routek: sound after repairs; K2's refereed status unchecked).
- *Scratch imports.* glue-assembly reports that scratch files cannot import `JHeight` in a fresh
  worktree; here `lake build ZInQKernel.Hypotheses.JHeight` (two upstream helper modules, seconds)
  fixes it, and `Leaves.lean` checks glue-assembly's `SixContactMinAt Mult.S_mul` against the real
  `ZInQ.SixContactMin` by definitional unfolding (VERIFIED).
- *Name collision.* `docs/research/rv-route-k.md` is about a different "Route K" (pole
  completeness, `rs-pole.md`), not this one.
