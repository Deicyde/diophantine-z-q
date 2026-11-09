# The reduced trust base of the six-contact estimate H

Status labels.

- **VERIFIED**: checked here against the text: the manuscript `diophantine_zq.tex` (line numbers
  refer to the frozen 11/5 source, SHA256 `cb1148cd…d792b`), the audit records in
  `docs/theorem-application-audit/`, the Lean files, or the text of a paper that was read here.
- **STANDARD**: a well-known published theorem whose statement was checked to apply. The
  reference is given.
- **SPECULATIVE**: an idea or assessment that is not proved.
- **UNCHECKED**: the source could not be read here. The step is recorded with the attribution
  that could be verified (for instance in a survey that was read), but the exact statement and
  numbering in the primary source were not checked.

Notation as in `docs/research/rs-height.md` and `docs/research/h-cm.md`: `A/K` is the fibre
surface of the proof of Theorem 4.1, `L` its Hom field (`[L:ℚ] ≤ D`), `L'` the field of the
scalar descent (`[L':ℚ] ≤ QM`), `r_ℓ` the two-dimensional representation of `G_ℚ` with
`ρ_ℓ ≅ r_ℓ ⊕ r_ℓ` (line 730), `f` the weight-two newform of level `N`, `J = J₁(N)`.
`NoCM` is the lemma of h-cm, in the corrected form of `docs/research/rv-h-cm.md` §7.2.

Sources read for this note (besides the repository):

- E. Gaudron and G. Rémond, *Théorème des périodes et degrés minimaux d'isogénies*,
  arXiv:1105.1230 (Comment. Math. Helv. 89 (2014)); cited as GR11. Its introduction restates the
  period theorem of Masser–Wüstholz.
- L. Pan, arXiv:1901.07166v2, Conjecture 1.0.1 and Theorem 1.0.4 (the version pinned by the
  audit, A011).
- P. Scholze, arXiv:1205.3463, introduction and the de Rham corollary.
- L. Berger, *An introduction to the theory of p-adic representations*, arXiv:math/0210184
  (in *Geometric aspects of Dwork theory*, de Gruyter 2004), §I.3, "Comparison theorems";
  cited as Berger04.
- D. Zywina, *An effective open image theorem for abelian varieties*, arXiv:1910.14171,
  Theorem 2.4 (attributed to Masser–Wüstholz) and its proof; cited as Zywina.
- R. von Känel, *Modularity and integral points on moduli schemes*, arXiv:1310.7263,
  §§1, 4; cited as vK.

Sources that could **not** be read here (no access): D. Masser and G. Wüstholz, *Periods and
minimal abelian subvarieties* and *Isogeny estimates for abelian varieties, and finiteness
theorems*, Ann. of Math. 137 (1993), 407–458 and 459–472 (MW93a, MW93b); their *Factorization
estimates for abelian varieties*, Publ. Math. IHÉS 81 (1995), 5–24, and *Refinements of the Tate
conjecture for abelian varieties*, in *Abelian varieties* (Egloffstein 1993), de Gruyter 1995,
211–223 (MW95); J.-B. Bost, Séminaire Bourbaki exposé 795, Astérisque 237 (1996); Gaudron–Rémond,
Duke 163 (2014) (GR14; known here only through audit records A005, A015, A016); Faltings 1983
(known here through A006, A008, A063); Faltings 1989; Tsuji 1999; Fontaine 1982/1983;
Coleman–Iovita 1999; Breuil 2000; Tate 1966 and 1967; SGA 7; Carayol 1986.

## Summary

- **Inventory (§1).** The proof of Theorem 4.1 (lines 404-966, with the appendix lemma at lines
  10936-11005) consumes 26 audit records: A001-A018, A061-A065, A071, A078, A079 (VERIFIED from
  `applications.json` anchors and a scan of every `\cite` in those lines). Two further external
  inputs are used without a citation or an audit record: Carayol's local–global compatibility
  (lines 852-857, "Local–global compatibility … bounds the primitive level") and the extension of
  homomorphisms of good-reduction abelian varieties (lines 781-784). Both should be recorded.
- **CM branch (§1.3).** NoCM removes A003, A004 and A005 from the proof entirely, and removes the
  H-use of A065 (its other uses, lines 1009-1016 and 1759-1769, are outside H). It removes the CM
  use of A006 and of Faltings 1983 at line 621, but A006 stays for lines 894-900. It adds
  González–Rotger §5, Vignéras (Emb) and, through González–Rotger, Shimura's reciprocity law.
- **R5.1, Masser–Wüstholz (§2).** Both uses of Faltings' finiteness theorems can switch. What the
  proof needs is qualitative: semisimplicity and the endomorphism theorem for `A/L'` at `ℓ = 3, 5`
  (A008), and the Hom theorem for `(A, J)` over `L'` (A063). These follow by Tate's 1966 argument
  from the finiteness of the `L'`-isogeny class up to isomorphism, which follows at once from the
  isogeny theorem of Gaudron–Rémond (GR14, Theorem 1.4, already a leaf as A015). This is the
  Masser–Wüstholz proof of the Tate conjecture, with GR14 in place of MW93b. The proof of the
  derivation is written out in §2.3 (VERIFIED as an argument). The large-`ℓ` mod-`ℓ` statements
  of MW95 do **not** apply at `ℓ = 3, 5`. One check is left open: that the proof of GR14
  Theorem 1.4 does not itself use Faltings' Tate theorem (§2.5).
- **R5.2, p-adic comparison (§3).** Pan's Theorem 1.0.4 needs `r₅|G_{ℚ₅}` *potentially
  semistable* with distinct Hodge–Tate weights (VERIFIED in arXiv v2). Two replacements:
  (a) the de Rham comparison for abelian varieties from Fontaine (1983), Faltings (1989) or Tsuji
  (1999) in place of Scholze; (b) better, `A` has potentially good reduction at 5 (Lemma PG,
  VERIFIED from inputs already in the base: Silverberg–Zarhin A013, Néron–Ogg–Shafarevich A061, and
  `B ⊗ ℚ₃` a division algebra), so `r₅` is potentially crystalline by the classical crystalline
  comparison for abelian varieties with good reduction. Route (b) removes Scholze (A009's main
  source) **and** Berger (A010). The primary sources of the crystalline comparison were not
  readable here (UNCHECKED; attribution VERIFIED in Berger04).
- **Further leaves (§4).** Raynaud's criterion is older than Silverberg–Zarhin (SGA 7 I, IX,
  Prop. 4.7, UNCHECKED). Several leaves cite unrefereed notes (Milne's course notes,
  Brinon–Conrad, Conrad's preprint, the Stacks project) or preprint versions of published papers
  (Baba–Granath, Buzzard, Lin–Yang); §4.4 lists published replacements. No older replacement was
  found for Pan, Javanpeykar, Pazuki, Gaudron–Rémond or the Lin–Yang/Lauter–Naehrig–Yang theta
  formula.
- **Constants (§5).** None of the changes alters a constant. `H₆(S;R)` is unchanged, and
  `SixContactEstimate` (`Hypotheses/Height.lean`, lines 89-98) and `SixContactMin`
  (`Hypotheses/HeightMin.lean`, line 36) hold as stated, with the same numerals (VERIFIED by
  reading both files).

## 1. The external theorems imported by the proof of Theorem 4.1

### 1.1 Method (VERIFIED)

The list below was obtained in two ways, which agree.

- Every `\cite` in lines 377-966 and 10936-11010 was extracted (32 occurrences, at lines 419,
  422, 444, 564, 588, 605, 615, 621, 692, 733, 737, 739, 756, 761, 769, 771, 812, 816, 830, 870,
  878, 895, 911, 916, 934 and 10955-11003).
- Every application record whose `manuscript_anchors` meet these lines was listed from
  `applications.json`. This gives A001-A018, A061-A065, A071, A078, A079, and A066 with a context
  anchor at lines 770-774 only.

A066 (BCDT and Milne's modular-forms notes) is not imported by the proof of H. Its anchor at
lines 770-774 records the Tate-versus-cohomological convention for `A_f`, and the `A_f` of the
proof of H is constructed by Shimura's Theorem 1, which is part of A011. A071 enters only
through its citation of Silverman IV.6.4 at line 830 (the `2`-adic logarithm in the conductor
bound).

### 1.2 Inventory

"Step" refers to the outline in rs-height §3.1. The last column gives the effect of NoCM.

| Step | Statement as used | Lines | Audit | Source | Under NoCM |
| --- | --- | --- | --- | --- | --- |
| 1 | Polarization datum, normalizer quotient `P¹_j`, branch values `0, ∞, -16/27`, indices `4, 6, 2` | 409-442 | A001 | Baba–Granath 2005 preprint; Lin–Yang arXiv v1 | kept |
| 1 | Smooth integral model of the level-3 curve via `V₁(5)` | 443-478 | A002 | Buzzard 1996/2002; Stacks 07S7 | kept |
| 1-2 | Stable-model extension of automorphisms, free quotients, tame Kummer local form | 480-534 | A078 | Stacks 0E97, 07S7, 0EYG | kept |
| 3 | Restriction of scalars, endomorphism rank, Néron–Ogg–Shafarevich, Hom field `L` | 544-562 | A061 | Milne AV notes | kept |
| 3 | Polarizable tori are abelian varieties; Hodge endomorphisms are algebraic; `End⁰ ∈ {B, M₂(k)}` | 564-577 | A079 | Milne AV notes I.2.8-2.9 | kept (NoCM needs the dichotomy) |
| 4 | `h(Δ) ≤ k ⇒ √(-Δ) ≤ 2k²e^{21000k²}` at `k = D` | 581-593 | A003 | Fowler, Prop. 2.7 | **removed** |
| 4 | Degree of `j(E)` is the order class number; `j(E)` integral | 583-598 | A065 | Fowler §2.1 | **removed from H** (kept at 1009-1016, 1759-1769) |
| 4 | Faltings height of a CM elliptic curve (discriminant formula) | 595-613 | A004 | Barquero-Sanchez et al., Eq. (6.2) | **removed** |
| 4 | Isogeny estimate with source `E²`, target `A` | 614-619 | A005 | Gaudron–Rémond 2014, Thm 1.4 | **removed** (theorem kept via A015) |
| 4, 8 | `h_F(target) ≤ h_F(source) + ½ log deg`, additivity | 620-628, 894-900 | A006 | Faltings 1983, Lemma 5 | CM use removed; kept for 894-900 |
| 5 | Skolem–Noether; sign cocycle | 632-663 | A062 | Milne CFT notes IV.2.10 | kept |
| 5 | `Br(ℚ)[2]`, local square roots, reciprocity, injectivity of `Br(ℚ) → ⊕ Br(ℚ_v)` | 665-708 | A007 | Milne ADT I; Milne CFT notes | kept |
| 6 | Semisimplicity of `V_ℓ(A)` over `G_{L'}` and `End_{G_{L'}} V_ℓ(A) = B ⊗ ℚ_ℓ`, hence `r_ℓ` absolutely irreducible | 732-734 | A008 | Faltings 1983, Satz 3, Satz 4 | kept; §2 |
| 6 | `H¹_et(A_{F̄}, ℚ_ℓ)` de Rham; duality; summands; finite descent; weights `0, -1` | 735-738, 10939-11005 | A009 | Scholze 2013 + corrigendum; Brinon–Conrad; Milne AV I.12.1 | kept; §3 |
| 6 | de Rham ⇒ potentially semistable | 739-741 | A010 | Berger 2002 | kept; §3 |
| 6 | Fontaine–Mazur for `GL₂` at `p = 5`; local algebraicity of the twist; Li's Fricke formula; Shimura's `A_f` | 755-774 | A011 | Pan, Thm 1.0.4; Conrad preprint; Li 1975; Shimura 1973 | kept |
| 6 | Independence of `ℓ` of characteristic polynomials; Chebotarev; Brauer–Nesbitt | 776-794 | A064 | Milne AV notes I.10.20, IV.3.9; Milne CFT notes VIII.7.4 | kept |
| 7 | Different and upper ramification breaks; conductor bound `2 + 2U₀` | 796-846 | A012 | Serre, *Local class field theory* (Cassels–Fröhlich), VI.4.1-4.3 | kept |
| 7 | Semistable reduction over `F(A[3])` (`F(A[5])` if `p = 3`); unipotent inertia | 814-818 | A013 | Silverberg–Zarhin, Thms 3.3, 3.5 | kept |
| 7 | Logarithm of `Ĝ_m` at `p = 2` | 828-831 | A071 | Silverman IV.6.4 | kept |
| 8 | Faltings Hom theorem for `(A, J)` over `L'`; Poincaré complement | 861-867 | A063 | Faltings 1983, §5 Cor. 1; Milne AV notes I.10.1 | kept; §2 |
| 8 | `h_F(J₁(N)) ≤ 1.3·10⁷ N^{12}` | 868-876 | A014 | Javanpeykar, Thm 1.1.1 | kept |
| 8 | Isogeny estimate with source `J`, target `A × Z` | 878-892 | A015 | Gaudron–Rémond 2014, Thm 1.4 | kept |
| 8 | `h_F(Z) ≥ -(3/2) dim Z` | 894-895 | A016 | Gaudron–Rémond 2014, §9 (Bost) | kept |
| 9 | Theta formula for `j` on the quaternionic locus | 908-932 | A017 | Lin–Yang (2), (14); Lauter–Naehrig–Yang §2.2 | kept |
| 9 | Theta height versus Faltings height, `r = 2`, `g = 2` | 934-947 | A018 | Pazuki, Cor. 1.3(2) | kept |

Two inputs are used **without a citation and without an audit record** (VERIFIED by reading the
lines and by checking the anchors of every record):

- **I1. Local–global compatibility for weight-two newforms** (lines 852-857). The level `N` of
  `f` is bounded by the Artin conductor of `r₅` (of `r₃` at the prime 5). This needs: for a
  newform of weight 2, level `N` and character, and a place `λ ∤ p`, the exponent of `p` in `N`
  equals the conductor exponent of `ρ_{f,λ}|G_{ℚ_p}`. That is Carayol, Ann. Sci. ÉNS 19 (1986),
  Théorème (A) (STANDARD; the paper is already pinned in the audit for A032). No audit record of
  the proof of H contains it: A012 bounds the conductor of `r_ℓ`, not the level of `f`. The
  existing evidence files mention Carayol only for A032 (lines 9761-9880).
- **I2. Extension of homomorphisms to good reduction** (lines 781-784). The reduction of
  `μ_σ : {}^σA → A` to an isogeny of reductions uses the Néron mapping property (Bosch–Lütkebohmert–
  Raynaud, *Néron models*, §1.2; STANDARD, section number not rechecked here). The descent review
  (`evidence/descent.md`, line 137) already notes that the sentence names no theorem.

Two further standard facts are inside recorded applications and need no separate entry:
Poincaré reducibility (A063, Milne I.10.1) and Chebotarev (A064).

### 1.3 What the CM-branch removal changes

NoCM (h-cm Theorem NoCM; rv-h-cm §7.2) says: for `u ∈ ℚ \ 𝒞`, no point of `X⁶` over
`j = J(u)` is a CM point, so `End⁰(A_ℚ̄) = B` for every fibre surface `A`. The paragraph "CM
fibers" (lines 581-631) is replaced by this lemma. The proof keeps the dichotomy of A079
(`End⁰(A_ℚ̄)` is `B` or `M₂(k)`) and excludes the second case.

**Removed from the proof of H** (VERIFIED against INVENTORY.md and the anchors):

- A003 (Fowler, Prop. 2.7 at `k = D`), A004 (the CM Faltings height formula) and A005 (the
  `E² → A` application of Gaudron–Rémond Theorem 1.4) entirely;
- the H-use of A065 (Fowler §2.1, class polynomials). Its uses at lines 1009-1016 and 1759-1769
  are in other parts of the manuscript and stay;
- the CM use of A006 (lines 619-628). A006 stays for lines 894-900;
- the sources Fowler and Barquero-Sanchez et al. leave the trust base of H; Gaudron–Rémond and
  Faltings 1983 stay through A015, A016 and A006.

**Added** (statements as checked by rv-h-cm; the numbering of González–Rotger was rechecked
here in the arXiv text):

- J. González and V. Rotger, *Non-elliptic Shimura curves of genus one*, J. Math. Soc. Japan 58
  (2006), 927-948 (journal reference VERIFIED from the arXiv record of math/0612732), §5:
  Theorem 5.8 (Shimura reciprocity, which they attribute to Shimura 1967, Main Theorem II),
  Proposition 5.6 (structure and count of `CM(R)`, to be used only under `(f, 6) = 1`), Lemma 5.9
  (ramified Atkin–Lehner rule), and Theorem 5.12 if the short proof of rv-h-cm §7.2 is used;
- Vignéras, LNM 800, Ch. II §1 and Ch. III §5, for the local embedding condition (Emb);
- ring class fields are unramified outside the conductor (Cox, §9), for Case A of h-cm;
- the labelling of `j` by Baba–Granath, which the manuscript already uses (A001, A017).

With repair R3 of rv-h-cm (the twist constants from Shimura reciprocity at the elliptic
points), Elkies' paper is a cross-check and not a premise. rv-h-cm lists five repairs of
citations and wording (R1-R5); none affects the argument, and none affects the list above,
except that Saia's restatements must not be cited (R1).

**Jordan's thesis is not a hidden leaf** (VERIFIED against the arXiv text of González–Rotger,
math/0612732). Their introduction says that Jordan's thesis (Ch. III) is unpublished and treats
only maximal orders and trivial level, and that they therefore prove the needed statements "in
full generality" in their appendix (§5). In that appendix:

- Theorem 5.12 (field of moduli) is proved there from Theorem 5.8 (Shimura reciprocity, cited
  to Shimura 1967, Main Theorem II), Lemma 5.10 (complex conjugation on `CM(R)`) and
  Proposition 5.6;
- Proposition 5.6 is stated with citations to Ogg, Jordan and Bertolini–Darmon, and is derived
  from the bijection between `CM(R)` and `𝒪¹`-classes of normalized optimal embeddings together
  with Eichler's theory of optimal embeddings (Vignéras). Jordan is cited, not used.

So the published inputs of NoCM are González–Rotger §5, Shimura's reciprocity law (Shimura 1967,
through their Theorem 5.8), Eichler's theory of optimal embeddings (Vignéras) and Ogg's
description of the fixed points of Atkin–Lehner involutions. The misprint in the non-emptiness
criterion of Proposition 5.6 (rv-h-cm R1(a)) is visible in the arXiv text as well: the printed
criterion "`DN/(D(R)N*(R))` divides `disc R`" carries no hypothesis `(f, D) = 1`. NoCM uses
only the count and the free transitive action, under `(f, 6) = 1`, which (Emb) supplies.

**Count.** Before NoCM the proof of H consumed 26 records. After NoCM it consumes 22 (A003,
A004, A005 and A065 leave), plus the new NoCM inputs above, plus the unrecorded inputs I1 and
I2 of §1.2. Fowler's effective class-number bound at `k = D`, the CM height formula and one
application of the isogeny estimate are gone; they are replaced by classical facts about CM
points on `X⁶` (Shimura 1967, Vignéras 1980, González–Rotger 2006).

## 2. Route R5.1: Faltings' finiteness theorems replaced by isogeny estimates

### 2.1 The two uses, stated exactly (VERIFIED by reading lines 718-734 and 860-867, A008, A063)

Let `k = L'`, a number field with `[k:ℚ] ≤ QM`, Galois over `ℚ` (line 711). Every geometric
endomorphism and every conjugacy homomorphism of `A` is defined over `L ⊆ k` (line 561), and
`End⁰(A_k) = B` by NoCM.

- **U1 (A008, line 732).** For `ℓ ∈ {3, 5}`: `V_ℓ(A)` is a semisimple `ℚ_ℓ[G_k]`-module and
  `End_{G_k}(V_ℓ(A)) = End_k(A) ⊗ ℚ_ℓ = B ⊗ ℚ_ℓ`. The manuscript says "for each coefficient prime
  `ℓ`", but only `ℓ = 5` (Pan's irreducibility hypothesis, line 756) and `ℓ = 3` (the
  identification of `r₃` with the modular representation by traces, line 792) are consumed.
  The audit's derivation of absolute irreducibility of `r_ℓ|G_k` from these two facts (A008,
  "Source inspection") is elementary and stays as it is.
- **U2 (A063, lines 861-864).** For `J = J₁(N)` over `k`: if `V₅(A)` and `V₅(J)` have a common
  `G_k`-constituent after extending coefficients, then `Hom_k(A, J) ≠ 0`. The audit's derivation
  uses two Faltings facts: semisimplicity of `V₅(J)` (so that a common constituent gives a
  nonzero equivariant map, after the finite-intersection argument for coefficient extension), and
  the Hom theorem `Hom_k(A, J) ⊗ ℚ₅ = Hom_{G_k}(V₅A, V₅J)`.

In both uses the statement is **qualitative** (no bound is consumed), over the **given number
field `k`**, for **arbitrary** abelian varieties `A` and `J` (no polarization hypothesis is
used), and at the **fixed** primes `ℓ = 3, 5`. The only explicit bound in this part of the proof
comes afterwards, from GR14 Theorem 1.4 applied to the isogeny that U2 produces (A015).

### 2.2 What Masser and Wüstholz prove, and what could be checked

- **The period theorem** (MW93a). GR11 (VERIFIED, read in the arXiv text, introduction) restate
  it as: for a polarized `(A, L)` of dimension `g` over `k`, a complex embedding `σ` and a period
  `ω ≠ 0` of `A_σ`, the smallest abelian subvariety `A_ω` whose tangent space contains `ω`
  satisfies `deg_L A_ω ≤ c·max(1, h_F(A), ‖ω‖²)^κ`, with `κ = (g-1)4^g g!` and
  `c = c₀[k:ℚ]^κ (deg_L A)^{1+gκ}`. This is the transcendence input of every isogeny estimate.
- **The isogeny theorem and the Tate conjecture** (MW93b). The paper was not readable here
  (UNCHECKED). vK (§4, the paragraph after the proof of Lemma 4.1; VERIFIED as a statement of vK)
  records that "Masser–Wüstholz gave a new proof of the Tate conjecture on using their isogeny
  estimates which rely on transcendence theory", that Bost and David made the estimates effective
  (Bost's Bourbaki exposé, p. 121), and that GR14 gives completely explicit constants. vK also
  states the GR14 bound in the form used here: for `A'` that is `K`-isogenous to `A`, GR14 Theorem
  1.4 gives isogenies of degree at most `κ(A)` (vK, equation for `|h(A) - h(A')|`).
- **The refinements** (MW95). Not readable here (UNCHECKED). Zywina, Theorem 2.4 (VERIFIED as
  Zywina's restatement, with his proof citing MW95, §1, Corollaries 1 and 2, Lemmas 2.3 and 5.2
  and the final remark): there are `c, γ` depending only on `dim A` such that for
  `ℓ ≥ c·max([L:ℚ], h(A))^γ`, `A[ℓ]` is a semisimple `𝔽_ℓ[G_L]`-module and
  `End(A_L) ⊗ 𝔽_ℓ = End_{G_L}(A[ℓ])`.
- **GR14, Theorem 1.4** (audited as A015 against the published page images; not reread here).
  For abelian varieties over `k` that are isogenous, there are isogenies in both directions of
  degree at most `κ(A) = ((14g)^{64g²}[k:ℚ]·max(h_F(A), log[k:ℚ], 1)²)^{1024g³}`, where `A` is the
  first of the two and `g = dim A`. No polarization is assumed. The manuscript applies it with
  `k = K = L'` (line 878); the same specialization is used below.

**The mod-`ℓ` refinements do not cover U1.** They need `ℓ ≥ c·max([L':ℚ], h(A))^γ`. Here
`h_F(A)` can be as large as `Q^{17}M^{24}` and `[L':ℚ]` as large as `QM`, so the threshold is
astronomically larger than 5, and the proof cannot move to a large `ℓ`: Pan's theorem is applied
at `p = 5`, and the identification of `r₃` is needed at `ℓ = 3` to compute the conductor at 5.
So the uses at `ℓ = 3, 5` need the `ℓ`-adic theorem, valid for every `ℓ`, which comes from the
isogeny theorem through Tate's argument.

### 2.3 From the isogeny theorem to U1 and U2 (VERIFIED as an argument)

Fix a number field `k`, a prime `ℓ`, and an abelian variety `X/k`. Write `T = T_ℓ(X)`,
`V = T ⊗ ℚ_ℓ`, `G = G_k`, `E = End_k(X)`, `R = E ⊗ ℚ_ℓ`. Two standard facts are used: `E ⊗ ℤ_ℓ →
End(T)` is injective with torsion-free cokernel (Mumford, *Abelian varieties*, §19, Theorem 3;
Milne AV I.10.15, already used in A061), and `E ⊗ ℚ` is a semisimple algebra by Poincaré
reducibility (Milne AV I.10.1, already used in A063). Since `ℚ` has characteristic zero, `R` is
then semisimple as well.

**(F_X)** *There are only finitely many `k`-isomorphism classes of abelian varieties over `k`
that are `k`-isogenous to `X`.*

*(F_X) from GR14 Theorem 1.4.* If `Y` is `k`-isogenous to `X`, there is a `k`-isogeny `φ: X → Y`
of degree at most `κ(X)`. Then `Y ≅ X/ker φ` over `k`, and `ker φ` is a `G`-stable subgroup of
`X(k̄)` of order at most `κ(X)`, hence contained in `X[n]` with `n = ⌊κ(X)⌋!`. The finite group
`X[n](k̄)` has finitely many subgroups, and each `G`-stable one determines `X/G` up to
`k`-isomorphism. ∎

**Claim 1 (Tate).** *Assume (F_X). For every `G`-stable subspace `W ⊆ V` there is `u ∈ R` with
`u(V) = W`.*

*Proof.* Put `U_n = (W ∩ T) + ℓⁿT`, a `G`-stable lattice with `ℓⁿT ⊆ U_n ⊆ T`. Its image
`G_n = U_n/ℓⁿT ⊂ T/ℓⁿT = X[ℓⁿ]` is a finite `k`-subgroup. Let `π_n : X → Y_n = X/G_n`, and let
`ρ_n : Y_n → X` be the isogeny with `ρ_n ∘ π_n = ℓⁿ`. Identifying `V_ℓ(Y_n)` with `V` through
`π_n`, one has `T_ℓ(Y_n) = ℓ^{-n}U_n`, so `T_ℓ(ρ_n)` maps `T_ℓ(Y_n)` onto `U_n`. By (F_X) there
are `m` and an infinite set `I` of indices `n > m` with `Y_n ≅ Y_m` over `k`; fix such
isomorphisms `α_n : Y_m → Y_n`. Then `u_n = ρ_n α_n ρ_m^{-1} ∈ E ⊗ ℚ` maps `U_m` onto `U_n`.
Since `ℓ^mT ⊆ U_m`, `v_n = ℓ^m u_n` maps `T` into `U_n ⊆ T`, so `v_n ∈ E ⊗ ℤ_ℓ` by the
torsion-freeness of the cokernel. As `E ⊗ ℤ_ℓ` is compact, a subsequence converges to some
`v ∈ E ⊗ ℤ_ℓ`.

- `v(T) ⊆ W ∩ T`: for `n ≥ n'` in `I`, `v_n(T) ⊆ U_n ⊆ U_{n'}`, and `⋂_{n'} U_{n'} = W ∩ T`.
- `v(U_m) ⊇ ℓ^m(W ∩ T)`: if `y ∈ ℓ^m(W ∩ T) ⊆ ℓ^mU_n = v_n(U_m)`, write `y = v_n(x_n)` with
  `x_n ∈ U_m`; a limit point `x` of the `x_n` satisfies `v(x) = y`.

Hence `v(V) = W`. ∎

**Claim 2 (semisimplicity).** *Assume (F_X). Then `V` is a semisimple `ℚ_ℓ[G]`-module.*

*Proof.* Let `W ⊆ V` be `G`-stable and `𝔞 = {x ∈ R : x(V) ⊆ W}`. It is a right ideal of `R`, so
`𝔞 = eR` for an idempotent `e`, because `R` is semisimple. Then `eV ⊆ W`, and `W = u(V) = eu(V) ⊆
eV` for the `u ∈ 𝔞` of Claim 1. So `W = eV`, and `(1 - e)V` is a `G`-stable complement, since
`e` commutes with `G`. ∎

**Claim 3 (Tate conjecture).** *Assume (F_{X×X}). Then `End_G(V) = R`. If `X = A × A'`, then
`Hom_G(V_ℓA, V_ℓA') = Hom_k(A, A') ⊗ ℚ_ℓ`.*

*Proof.* Let `f ∈ End_G(V)`. Its graph `Γ_f ⊆ V ⊕ V = V_ℓ(X × X)` is `G`-stable, so by Claims 1
and 2 for `X × X` it equals `e(V ⊕ V)` for an idempotent `e ∈ End_k(X × X) ⊗ ℚ_ℓ = M₂(R)`. Let `C`
be the commutant of `R` in `End(V)`. For `c ∈ C`, `diag(c, c)` commutes with `M₂(R)`, hence with
`e`, and preserves `Γ_f`, so `cf = fc`. Thus `f` lies in the bicommutant of `R`, which is `R`
because `V` is a faithful module over the semisimple algebra `R` (double centralizer theorem).
For `X = A × A'`, `End_k(X)` and `End_G(V_ℓX)` both decompose into the four blocks
`Hom(A, A)`, `Hom(A', A)`, `Hom(A, A')`, `Hom(A', A')` (respectively their `G`-equivariant Tate
versions); equality of the wholes gives equality of the `(A, A')` blocks. ∎

These are Tate's arguments (Invent. Math. 2 (1966); section number not rechecked), written out
because his paper treats finite fields; the proofs above use nothing about `k` except (F). The
only arithmetic input is (F), which GR14 Theorem 1.4 supplies for every abelian variety over a
number field.

**Application.**

- **U1.** Apply GR14 Theorem 1.4 over `k = L'` to `X = A` and to `X = A × A`. Claims 2 and 3 give
  the semisimplicity of `V_ℓ(A)` and `End_{G_k}(V_ℓA) = B ⊗ ℚ_ℓ` for **every** `ℓ`, in
  particular `ℓ = 3, 5`.
- **U2.** Apply it to `X = A × J` and `X = (A × J)²`. Claim 2 gives the semisimplicity of
  `V₅(A × J) = V₅(A) ⊕ V₅(J)`, hence of `V₅(J)`, and Claim 3 gives
  `Hom_{G_k}(V₅A, V₅J) = Hom_k(A, J) ⊗ ℚ₅`. The rest of A063 (coefficient extension, absolute
  simplicity, Poincaré complement over `L'`) is unchanged.

### 2.4 Use-by-use comparison

| | U1 (A008) | U2 (A063) |
| --- | --- | --- |
| Field of definition needed | `L'` (all endomorphisms already over `L ⊆ L'`) | `L'` (both `A` and `J` over `L'`; the isogeny `A × Z → J` must be over `L'` for A015) |
| Abelian varieties | `A` (dim 2) | `A` and `J₁(N)` (dim `≥ 2`, `≤ Q³M⁴`) |
| Polarization | none used | none used |
| Primes `ℓ` | `3` and `5` | `5` |
| Effective? | no; qualitative | no; qualitative (the bound comes later from A015) |
| Faltings 1983 gives | Satz 3, Satz 4 (all `k`, all `ℓ`) | §5 Cor. 1 and Satz 3 |
| Replacement gives | Claims 2-3 for `X = A`, `A × A` over `L'`, all `ℓ` | Claims 2-3 for `X = A × J`, `(A × J)²` over `L'`, all `ℓ` |
| Input of the replacement | GR14 Thm 1.4 over `k = K = L'` | the same |
| Can switch? | **yes** | **yes** |

The fields match exactly: GR14 Theorem 1.4 is applied over the same field `L'` and with `k = K`,
as A015 already does. The statements match exactly: Claims 2-3 are Faltings' Satz 3 and Satz 4
(rational form) and Corollary 1 of §5, for every number field and every `ℓ`. Nothing effective is
needed, so nothing about the size of `κ(X)` matters, and in particular the large dimension of
`(A × J)²` is harmless.

If one prefers to cite Masser–Wüstholz directly, the same derivation works with MW93b's isogeny
theorem in place of GR14, provided MW93b gives (F_X) for every abelian variety over a number field
without a polarization hypothesis. That could not be checked (MW93b not readable here; UNCHECKED).
The route through GR14 has the advantage that GR14 Theorem 1.4 is already a leaf (A015), with its
statement checked against the published page images, so the change adds no new source at all.

### 2.5 The one open check: non-circularity

The replacement is only a reduction if the proof of GR14 Theorem 1.4 (or of MW93b) does not
itself use Faltings' Tate theorem or semisimplicity. Masser and Wüstholz's purpose was a proof
independent of Faltings (vK §4, quoted in §2.2; GR11's introduction describes the period theorem
and its isogeny consequences as resting on transcendence and the slope method). It is plausible
that GR14 follows the same scheme: the period theorem applied to the graph of a given isogeny,
Zarhin's trick, and Faltings' height-variation lemma (A006), which belongs to the Arakelov part of
Faltings 1983, not its finiteness part. But GR14 was not readable here, so this is **UNCHECKED**.
It is the first item to verify when the pinned GR14 file is available: search its proof of
Theorem 1.4 for any use of the Tate conjecture, of semisimplicity of Tate modules, or of
Faltings' finiteness theorem.

### 2.6 Verdict on R5.1

- U1 and U2 both switch. The new trust base for these steps is GR14 Theorem 1.4 (already A015)
  plus the elementary arguments of §2.3 and two standard facts already in the base (Mumford §19
  Theorem 3 / Milne I.10.15; Poincaré reducibility).
- Faltings 1983 then remains in the trust base of H only through A006 (Lemma 5, the
  height-variation inequality `h_F(target) ≤ h_F(source) + ½ log deg`, with additivity). That is
  part of the Arakelov theory of the Faltings height, which GR14 needs anyway.
- No constant changes: U1 and U2 are qualitative, and the degree bound at lines 878-892 is
  computed from A015 as before.
- The audit records A008 and A063 would change their source fields from Faltings 1983 to
  "GR14 Theorem 1.4 + Tate's argument", with this note as the translation.

## 3. Route R5.2: the p-adic comparison

### 3.1 What is needed (VERIFIED)

Pan's theorem is applied to `r₅` at `p = 5` (line 756). In arXiv:1901.07166v2, Conjecture 1.0.1
requires `ρ : G_ℚ → GL₂(ℚ̄_p)` continuous, irreducible, ramified at finitely many places, odd, and
"the restriction of `ρ` at the decomposition group at `p` is **potentially semi-stable** in the
sense of Fontaine". Theorem 1.0.4 adds, for odd `p`: `ρ|G_{ℚ_p}` has **distinct Hodge–Tate
weights**, and a residual condition only when `p = 3`. So at `p = 5` the `p`-adic input is:

> **(P)** `r₅|G_{ℚ₅}` is potentially semistable, with Hodge–Tate weights `0, -1` at every
> coefficient embedding.

The manuscript obtains (P) in three steps: the de Rham comparison for the rigid analytification
of `A/F`, `F = L'_v` with `v | 5` (Scholze, Cor. 1.8 and Thms 9.1, 9.3, with the corrigendum;
A009); duality, summands and finite descent to `G_{ℚ₅}` (Milne AV I.12.1(a), Brinon–Conrad 5.2.1,
6.3.3, 6.3.8; A009); then Berger's theorem "de Rham ⇒ potentially semistable" (A010). The de Rham
property of `r₅` over `ℚ₅` is used once more at line 759: the twisting character in Pan's
conclusion is a de Rham subrepresentation of the Hom representation, which feeds Conrad's local
algebraicity statement.

Scholze's corollary is a statement about proper smooth *rigid-analytic* varieties (VERIFIED in
arXiv:1205.3463: "For any proper smooth rigid-analytic variety `X` over `k` … `H^i(X_et, ℚ_p)` is
de Rham, with associated filtered `k`-vector space `H^i_dR(X)`"). Only the algebraic case, for an
abelian surface, is needed here; that is why the manuscript needs the extra GAGA-type step through
Scholze's Theorems 9.1 and 9.3.

### 3.2 Option (a): the same statement from the algebraic comparison theorems

Replace the first paragraph of the proof of Lemma `lem:de-rham-descent` (lines 10953-10965) by:
`H¹_et(A_{F̄}, ℚ₅)` is de Rham, with `D_dR` equal to `H¹_dR(A/F)` and its Hodge filtration.
Published sources for exactly this statement:

- Fontaine, *Cohomologie de de Rham, cohomologie cristalline et représentations p-adiques*,
  LNM 1016 (1983), 86-108, for abelian varieties;
- Fontaine–Messing, *p-adic periods and p-adic étale cohomology*, Contemp. Math. 67 (1987), for
  abelian varieties, by an explicit pairing;
- Faltings, *Crystalline cohomology and p-adic Galois representations*, in *Algebraic analysis,
  geometry and number theory* (Johns Hopkins, 1989), 25-80, for proper smooth varieties;
- Tsuji, *p-adic étale cohomology and crystalline cohomology in the semi-stable reduction case*,
  Invent. Math. 137 (1999), 233-411, which gives `C_st`; with de Jong's alterations it gives
  `C_pst` and hence `C_dR`.

Status: the attributions are VERIFIED against Berger04, §I.3 ("It was shown early on by Fontaine
that the Tate modules … of all abelian varieties `A` are de Rham … and that `D_dR(V)` is
isomorphic to the dual of the de Rham cohomology of `A`"; "Faltings (who proved that `V` is
crystalline if `X` has good reduction and that `V` is de Rham otherwise)"; Tsuji for `C_st`). The
primary statements and their numbering are **UNCHECKED** (sources not readable here).

What option (a) changes: Scholze 2013, its corrigendum and the analytic comparison (Theorems 9.1,
9.3) leave the trust base. Everything after the first paragraph of the lemma stays, and Berger's
theorem (A010) stays. The statement consumed is the same, so no constant changes.

### 3.3 Option (b): potential good reduction and the crystalline comparison

Option (b) uses the special nature of `A`: a QM surface has potentially good reduction
everywhere. The following lemma needs no input outside the present trust base.

**Lemma PG.** *Let `v` be a place of `L'` above 5, `F = L'_v`, `F' = F(A[3])`. Then `A_{F'}` has
good reduction.*

*Proof* (VERIFIED as an argument).

1. `A_{F'}` has semistable reduction, by Silverberg–Zarhin Theorem 3.5 with `n = 3`, which is
   prime to 5 (A013, exactly the application at lines 814-818). By their Theorem 3.3 (as recorded
   in A013), the inertia group `I` of `F'` acts unipotently on `V₃(A)`. So `V₃(A)^I ≠ 0`.
2. Every geometric endomorphism of `A` is defined over `L ⊆ F'` (line 561), and
   `End⁰(A_{F'}) = B` by NoCM. The action of `B` on `V₃(A)` commutes with `G_{F'}`, so
   `V₃(A)^I` is a `B ⊗ ℚ₃`-submodule.
3. `B ⊗ ℚ₃` is a division algebra (`B = (2, -3)` has discriminant 6; the manuscript uses this at
   line 454). A module over it has `ℚ₃`-dimension divisible by 4, and `dim V₃(A) = 4`. So
   `V₃(A)^I = V₃(A)`.
4. By the criterion of Néron–Ogg–Shafarevich (Serre–Tate, Ann. of Math. 88 (1968), Theorem 1;
   already used in A061), `A_{F'}` has good reduction. ∎

The same argument works at every prime `p`, with `n = 3` and `V₃` if `p ≠ 3`, and with `n = 5`
and `V₂` if `p = 3` (`B ⊗ ℚ₂` is also a division algebra). This is the classical fact that QM
abelian surfaces have potentially good reduction everywhere.

**Consequence for (P).** Assume:

> **(Cris)** *If an abelian variety `A'` over a finite extension `F'` of `ℚ_p` has good reduction,
> then `V_p(A')` is crystalline, and `D_cris(V_p(A')^∨) ⊗ F' = H¹_dR(A'/F')` with its Hodge
> filtration.*

Then:

- `V₅(A)|G_{F'}` is crystalline with Hodge numbers `2, 2`, hence Hodge–Tate weights `0, 0, -1, -1`
  in the Tate convention;
- by the lemma's hypothesis, restricted to `G_{F'}`, `V₅(A) ⊗ C₅ ≅ r|G_{F'} ⊕ r|G_{F'}`. As a
  `ℚ₅`-representation, `r|G_{F'}` is a direct summand of a finite direct sum of copies of
  `V₅(A)|G_{F'}`, hence crystalline. Brinon–Conrad Theorem 5.2.1, already cited in A009, is the
  closure statement for any regular period ring, `B_cris` included (STANDARD);
- the weight bookkeeping of the lemma's last paragraph is unchanged and gives weights `0, -1` for
  `r` at each coefficient embedding;
- `F'/ℚ₅` is finite, so `r₅|G_{ℚ₅}` is potentially crystalline, in particular potentially
  semistable. This is (P), without Berger's theorem.

The de Rham property over `ℚ₅` used at line 759 still follows: crystalline implies de Rham over
`F'`, and the finite descent paragraph of the lemma (lines 10980-10994, which is proved in the
text) carries it down to `ℚ₅`.

**Sources for (Cris).** Faltings 1989 (crystalline if good reduction, for proper smooth
varieties); Coleman–Iovita, *The Frobenius and monodromy operators for curves and abelian
varieties*, Duke Math. J. 97 (1999), 171-215, and Breuil, *Groupes p-divisibles, groupes finis et
modules filtrés*, Ann. of Math. 152 (2000), 489-549 (good reduction if and only if crystalline,
for abelian varieties); Tsuji 1999 (the case of trivial monodromy of `C_st`). The attributions are
VERIFIED against Berger04, §I.3. The primary statements are **UNCHECKED**. For abelian varieties
with good reduction the statement goes back to Fontaine's theory of Barsotti–Tate groups
(Ann. of Math. 115 (1982)); that attribution is from memory and is **UNCHECKED**.

### 3.4 Comparison and verdict on R5.2

| | Manuscript (A009 + A010) | Option (a) | Option (b) |
| --- | --- | --- | --- |
| Variety | rigid analytification of `A/F` | `A/F` algebraic | `A/F'`, `F' = F(A[3])`, good reduction |
| Comparison used | de Rham, rigid-analytic (Scholze) | de Rham, algebraic | crystalline, good reduction |
| GAGA step (Scholze 9.1, 9.3) | needed | not needed | not needed |
| dR ⇒ pst (Berger) | needed | needed | **not needed** |
| Finite descent (lemma, lines 10980-10994) | needed | needed | needed only for line 759 |
| New inputs | — | Fontaine 1983 / Faltings 1989 / Tsuji 1999 | (Cris); Lemma PG (no new source) |
| Status of the new input | — | UNCHECKED (attribution VERIFIED) | UNCHECKED (attribution VERIFIED) |
| Effect on constants | — | none | none |

Both options consume a statement that the proof needs in exactly the form stated: Pan's
hypothesis (P) is qualitative, and the conductor bounds (lines 796-857) do not use the
`p`-adic comparison at all (the conductor at 5 is computed from `r₃`, line 794). So **both
switches are possible and neither changes a constant.**

Recommendation: option (b). It removes two leaves (Scholze with corrigendum, Berger) instead of
one, it replaces them by a theorem that is older and narrower than Scholze's (crystalline
comparison for abelian varieties with good reduction), and the extra geometric input, Lemma PG,
is proved from leaves already in the base (A013, A061) and NoCM. The final remark of the
appendix (lines 11001-11005: Hodge–Tate alone would not prove de Rham) is respected: (Cris) gives
crystalline, which is stronger than de Rham.

## 4. Further leaves

### 4.1 Berger (A010)

Removed by option (b) of §3.3.

### 4.2 Raynaud's criterion (A013)

The manuscript cites Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), Theorem 3.5 (semistable
reduction over a field where all `n`-torsion is rational, `n ≥ 3` prime to the residue
characteristic) and Theorem 3.3 (unipotent inertia). The same criterion is Raynaud's, in
Grothendieck's exposé IX of SGA 7 I (LNM 288, 1972), Proposition 4.7, and the unipotence is in the
same exposé. vK (Lemma 4.1, proof of (i); VERIFIED as vK's citation) cites "[Grothendieck–Raynaud,
Proposition 4.7]" for exactly the statement "`A_L` is semistable for `L = K(A[15])`". The SGA
statement and numbering are **UNCHECKED** here. Payoff: an older and canonical source with the
same statement; no constant changes.

### 4.3 Unrecorded leaves: Carayol and the Néron mapping property

These are not replacements but additions (§1.2, I1 and I2). They are standard and published, but
they are part of the trust base and should have audit records.

- **I1.** Carayol 1986, Théorème (A), at `F = ℚ`, weight 2, places `λ | 5` (for `p ≠ 5`) and
  `λ | 3` (for `p = 5`): `v_p(N)` equals the conductor exponent of `ρ_{f,λ}|G_{ℚ_p}`. Only the
  inequality "`v_p(N)` is at most the conductor exponent" is consumed (line 856), together with
  "`p ∤ N` if `ρ_{f,λ}` is unramified at `p`". Both are contained in Théorème (A). The older
  converse direction ("`p ∤ N` implies unramified", from the good reduction of `X₁(N)` at `p`)
  is **not** the one consumed; the consumed direction bounds the level by the conductor and
  needs Carayol's theorem (for weight 2 perhaps also Langlands' Antwerp II paper, LNM 349
  (1973); its coverage was not checked, SPECULATIVE).
- **I2.** Néron mapping property (Bosch–Lütkebohmert–Raynaud, *Néron models*, Springer 1990,
  §1.2): a homomorphism between abelian varieties with good reduction at `v` extends to their
  Néron models, hence reduces. Used for `μ_σ` at lines 781-784.

### 4.4 Unrefereed or preprint sources, and published replacements

Several leaves of H are cited from course notes, a preprint, an online project, or a preprint
version of a paper that was later published (VERIFIED from SOURCES.md, which records the version
used). In each case the statement used is classical and a published source with the same
statement exists. The numbering in the published sources listed below was **not** rechecked
here (UNCHECKED); the replacements change no statement and no constant.

| Leaf | Cited version | Statement used | Published source |
| --- | --- | --- | --- |
| A061, A063 (I.10.1), A064 (I.10.20), A079 (I.2.8-2.9), A009 (I.12.1) | Milne, *Abelian varieties*, course notes v2.00 (2008) | analytic and algebraic basics of abelian varieties | Mumford, *Abelian varieties* (1970), §§1-3, 19-21; Milne, *Abelian varieties*, in Cornell–Silverman (eds.), *Arithmetic geometry*, Springer 1986 |
| A062 (IV.2.10), A007, A064 (VIII.7.4) | Milne, *Class field theory*, course notes v4.03 (2020) | Skolem–Noether; Brauer group of `ℚ`; Chebotarev | Reiner, *Maximal orders* (Skolem–Noether); Cassels–Fröhlich (eds.), *Algebraic number theory* (1967), Ch. VII (Tate) |
| A007 | Milne, *Arithmetic duality theorems*, 2nd ed. (2006), Ch. I | local and global duality | published book (Academic Press 1986; 2nd ed. 2006) |
| A009 | Brinon–Conrad, CMI notes (2009) | closure of admissible representations; finite descent | Fontaine, *Le corps des périodes p-adiques* and *Représentations p-adiques semi-stables*, Astérisque 223 (1994) |
| A011 | Conrad, *Lifting global representations with local properties*, preprint (2011), App. B | a de Rham character of `G_{ℚ₅}` is finite times an integral power of the cyclotomic character | Serre, *Abelian ℓ-adic representations and elliptic curves* (1968), Ch. III (locally algebraic characters); Fontaine, Astérisque 223 |
| A002, A078 | Stacks project, tags 07S7, 0E97, 0EYG | free finite quotients; uniqueness of stable models; tame Kummer form | SGA 1, Exp. V and XIII (Abhyankar's lemma); Deligne–Mumford, Publ. IHÉS 36 (1969) |
| A001, A017 | Baba–Granath, MPI preprint (2005) | polarization datum, branch data, labelling of `j` | Baba–Granath, *Genus 2 curves with quaternionic multiplication*, Canad. J. Math. 60 (2008) (from memory; equivalence of numbering UNCHECKED) |
| A001, A017 | Lin–Yang, arXiv:1807.00466v1 | Riemann form convention; Igusa invariants on the locus | publication not determined (the arXiv record has no journal reference, VERIFIED) |
| A002 | Buzzard, author version corrected in 2002 | integral model of `V₁(5)` | Buzzard, Duke Math. J. 87 (1997) (from memory). The audit deliberately uses the corrected author version; the corrections should be compared with the published text before switching |
| A011 | Pan, arXiv:1901.07166v2 | Theorem 1.0.4 | J. Amer. Math. Soc. 35 (2022), 1031-1169 (recorded in SOURCES.md; publisher text not compared) |

### 4.5 Leaves for which no older replacement was found

- **Pan, Theorem 1.0.4 (A011).** The older route is Khare–Wintenberger (Serre's conjecture) plus
  Kisin's Fontaine–Mazur theorem (J. Amer. Math. Soc. 22 (2009)), as in the earlier von
  Känel–Kret-type argument (rs-height R5.4). It needs `r̄_ℓ|G_{ℚ(ζ_ℓ)}` absolutely irreducible
  for the chosen `ℓ`, hence a move to a large `ℓ`. Large-`ℓ` irreducibility is available from
  MW95 (Zywina, Theorem 2.4) and Lemma PG gives potential crystallinity at every `ℓ`, so the route
  is not obstructed. But it trades one modularity theorem for two of the same depth, plus an
  irreducibility argument over `ℚ(ζ_ℓ)` that was not worked out (SPECULATIVE). Not recommended
  as a reduction.
- **Javanpeykar (A014).** No other published bound polynomial in `N` for `h_F(J₁(N))` was found;
  bounds of Ullmo type cover `J₀(N)` for squarefree `N` only. vK uses the same input
  (introduction, item (iii); VERIFIED as vK's statement), which suggests it is the standard one.
- **Pazuki (A018).** The published explicit comparison between theta height and Faltings height
  in genus 2. Older comparisons (Bost–David) are not explicit or not published.
- **Gaudron–Rémond (A015, A016).** The explicit isogeny estimate is needed for the bound at lines
  878-892, so the non-explicit MW93b cannot replace A015. After §2 the same theorem also carries
  U1 and U2, so this single leaf now supplies all three isogeny-theoretic inputs.
- **Faltings 1983, Lemma 5 (A006).** It is the origin of the height-variation inequality. Raynaud,
  *Hauteurs et isogénies*, exposé VII of *Séminaire sur les pinceaux arithmétiques : la
  conjecture de Mordell*, Astérisque 127 (1985) (reference VERIFIED from the bibliography of
  GR11), gives the exact formula and the additivity `h(A₁ × A₂) = h(A₁) + h(A₂)` (GR11 cites its
  Corollary 2.1.3 for additivity and duality). It is an alternative with a stronger statement,
  not an older one.
- **Lin–Yang and Lauter–Naehrig–Yang (A017), Buzzard (A002), Serre's local class field theory
  (A012), Silverman (A071), Li (1975), Shimura (1973).** Published or classical; no change
  proposed beyond §4.4.

## 5. The reduced trust base

### 5.1 Final table

The table assumes the three recommended changes: NoCM in place of the CM paragraph (§1.3),
R5.1 through GR14 and Tate's argument (§2), and R5.2 option (b) (§3.3). It includes the two
unrecorded inputs I1 and I2. "Refereed" refers to the best source listed; "book" means a
published monograph or textbook. The last column says whether the change of source alters a
constant in `H₆(S;R)`.

| # | Leaf | Statement as used | Lines | Best source (status) | Constant |
| --- | --- | --- | --- | --- | --- |
| 1 | A001 | QM polarization datum; quotient `P¹_j` with branch values `0, ∞, -16/27`, indices `4, 6, 2`; labelling of `j` at discriminants `-4, -3, -24` | 409-442, 532-542 | Baba–Granath, Canad. J. Math. 2008 (refereed; audit uses the 2005 preprint); Lin–Yang arXiv:1807.00466 (refereed status not determined) | none |
| 2 | A002 | smooth projective model of the full level-3 curve through Buzzard's `V₁(5)` | 443-478 | Buzzard, Duke 1997 (refereed; audit uses the corrected 2002 author version) | none |
| 3 | A078 | extension of automorphisms to stable models; free finite quotients; tame local form `u - c = z²` | 480-534 | SGA 1; Deligne–Mumford 1969 (refereed); currently Stacks project | none |
| 4 | A061 | endomorphism rank of `Res_{K/ℚ} A`; Néron–Ogg–Shafarevich; Hom field `L` unramified outside `T` | 544-562 | Mumford 1970 (book); Serre–Tate, Ann. of Math. 1968 (refereed) | none |
| 5 | A079 | polarizable tori are abelian varieties; Hodge endomorphisms algebraic; `End⁰ ∈ {B, M₂(k)}` | 564-577 | Mumford 1970 (book) | none |
| 6 | NoCM | Shimura reciprocity for `X⁶`; structure and count of `CM(R)` under `(f, 6) = 1`; ramified Atkin–Lehner rule; local embeddings; ring class fields | replaces 581-631 | González–Rotger, J. Math. Soc. Japan 2006, §5 (refereed); Shimura, Ann. of Math. 1967 (refereed); Vignéras, LNM 800 (book); Cox (book) | none (`C_cm` kept in the formula) |
| 7 | A062 | Skolem–Noether | 632-647 | Reiner, *Maximal orders* (book) | none |
| 8 | A007 | `Br(ℚ)[2]`, local square-root obstruction, reciprocity, injectivity of the local–global map | 665-708 | Cassels–Fröhlich 1967 (book); Milne, *Arithmetic duality theorems* (book) | none |
| 9 | A008, A063 | semisimplicity and `End_{G_{L'}} V_ℓ A = B ⊗ ℚ_ℓ` (`ℓ = 3, 5`); `Hom_{L'}(A, J) ⊗ ℚ₅ = Hom_{G_{L'}}(V₅A, V₅J)`; Poincaré complement | 732-734, 861-867 | GR14, Duke 2014, Thm 1.4 (refereed; already A015) + Tate's argument (§2.3) + Mumford §19 | none |
| 10 | A009 (new form) | `A_{F'}` has good reduction (Lemma PG); `V₅(A)` crystalline over `G_{F'}` with Hodge numbers `2, 2`; duality; summands; finite descent | 735-741, 10939-11005 | (Cris): Faltings 1989 (proceedings), Coleman–Iovita, Duke 1999 (refereed), Breuil, Ann. of Math. 2000 (refereed), all UNCHECKED; Lemma PG from rows 4 and 15; descent proved in the text | none |
| 11 | A011 | Fontaine–Mazur for `GL₂` at `p = 5`; local algebraicity of the twist; Fricke stability; `A_f` and its Euler factors | 755-774 | Pan, J. Amer. Math. Soc. 2022 (refereed); Serre 1968 (book) for local algebraicity; Li, Math. Ann. 1975 (refereed); Shimura, J. Math. Soc. Japan 1973 (refereed) | none |
| 12 | A064 | independence of `ℓ` of characteristic polynomials; Chebotarev; Brauer–Nesbitt | 776-794 | Mumford 1970 §19 (book); Cassels–Fröhlich (book) | none |
| 13 | I2 | homomorphisms of good-reduction abelian varieties reduce | 781-784 | Bosch–Lütkebohmert–Raynaud, *Néron models* (book) | none |
| 14 | A012 | different and upper breaks; conductor exponent `≤ 2 + 2U₀` | 796-846 | Serre, in Cassels–Fröhlich 1967 (book) | none |
| 15 | A013 | semistable reduction over `F(A[3])` (`F(A[5])` at `p = 3`); unipotent inertia | 814-818 | Silverberg–Zarhin, Ann. Inst. Fourier 1995 (refereed); SGA 7 I, IX, Prop. 4.7 (UNCHECKED) | none |
| 16 | A071 | logarithm of `Ĝ_m` on `U^{e+1}` | 828-831 | Silverman (book) | none |
| 17 | I1 | level of `f` bounded by the conductor of `ρ_{f,λ}` | 852-857 | Carayol, Ann. Sci. ÉNS 1986, Théorème (A) (refereed) | none |
| 18 | A014 | `h_F(J₁(N)) ≤ 1.3·10⁷ N^{12}` | 868-876 | Javanpeykar, Algebra Number Theory 2014 (refereed) | none |
| 19 | A015 | isogeny `J → A × Z` over `L'` of degree `≤ κ(J)` | 878-892 | GR14, Duke 2014, Thm 1.4 (refereed) | none |
| 20 | A006 | `h_F(target) ≤ h_F(source) + ½ log deg`; additivity | 894-900 | Faltings, Invent. Math. 1983, Lemma 5 (refereed); Raynaud, Astérisque 127 (1985) | none |
| 21 | A016 | `h_F(Z) ≥ -(3/2) dim Z` | 894-895 | GR14 §9, quoting Bost (refereed; Bost's own text not read) | none |
| 22 | A017 | `j = 3779136 (∏ z_m)⁴ / (∑ z_m⁸)⁵` on the quaternionic locus | 908-932 | Lauter–Naehrig–Yang, J. Number Theory (refereed); Lin–Yang (status not determined) | none |
| 23 | A018 | theta height versus Faltings height, `r = 2`, `g = 2` | 934-947 | Pazuki, Bull. Soc. Math. France 2012 (refereed) | none |

Leaves that leave the base: A003 (Fowler), A004 (CM Faltings height), A005 (CM isogeny), the
H-use of A065, Faltings 1983 Satz 3, Satz 4 and §5 Corollary 1, Scholze 2013 with its
corrigendum, and Berger 2002 (A010).

The deep inputs that remain are: one modularity theorem (Pan), one transcendence theorem
(GR14 Theorem 1.4, used for the explicit isogeny at lines 878-892 and, through Tate's argument,
for the Hom and semisimplicity statements), the crystalline comparison for abelian varieties with
good reduction, Shimura's reciprocity law for CM points, Carayol's local–global compatibility, and
the explicit Arakelov estimates (Faltings' Lemma 5, Bost's lower bound, Javanpeykar, Pazuki).

### 5.2 Constants and the Lean statements (VERIFIED)

No change in §§1-4 alters a numerical bound:

- NoCM deletes the CM paragraph, but the definitions of `B_cm`, `C_cm` and `H₆(S;R)` (lines
  390-397) are kept, as rv-h-cm §5 recommends. Since `max(1, C_cm, Q_R^{17}) = Q_R^{17}` for every
  admissible `R` (rv-h-cm §5, and line 6353), `H₆(S;R)` has the same value and the same formula.
- R5.1 and R5.2 replace qualitative statements (existence of homomorphisms, semisimplicity,
  potential semistability). The bounds at lines 868-900 use A014, A015, A016 and A006, whose
  statements do not change.
- §4 changes only citations, except for I1 and I2, which make explicit inputs that were already
  used.

The Lean statements are unaffected. `heightH6 R = 2·10¹³·max 1 (max heightCcm (heightQ R ^ 17))`
with `heightCcm = 2·heightBcm + 4096·(1028 + 5·heightD + 84000·heightD²)` and
`heightBcm = heightD²·3^(21000·heightD²) + 1` (`ZInQKernel/Hypotheses/Height.lean`, lines 70-90)
match lines 390-395. `SixContactEstimate` (lines 95-98) and `SixContactMin`
(`ZInQKernel/Hypotheses/HeightMin.lean`, lines 36-38: `ratHeight u ≤ heightH6 heightD *
contactSupport Mult.S_mul u ^ 24`) state Theorem 4.1 and its instance `S = S_mul`, `R = D`.
Since Theorem 4.1 is proved with the same constant, both statements hold as stated, with the
same numerals.

## 6. Open checks

In order of importance:

1. **Non-circularity of GR14 Theorem 1.4** (§2.5). Read the proof of Theorem 1.4 in the pinned
   published GR14 file and confirm that it uses neither the Tate conjecture nor the
   semisimplicity of Tate modules nor Faltings' finiteness theorem. If it does, cite MW93b for
   (F) instead, after checking that MW93b gives (F) for every abelian variety over a number field
   without a polarization hypothesis.
2. **(Cris)** (§3.3). Pin a primary source for the crystalline comparison for abelian varieties
   with good reduction over an arbitrary finite extension of `ℚ₅` (Faltings 1989, Coleman–Iovita
   1999, Breuil 2000 or Tsuji 1999) and record the exact theorem number. If none can be pinned,
   option (a) with Fontaine 1983 or Faltings 1989 is the fallback, and A010 stays.
3. **New audit records for I1 and I2** (§1.2): Carayol 1986, Théorème (A) at weight 2, in the
   direction "level ≤ conductor"; the Néron mapping property for the reduction of `μ_σ`.
4. **Numbering in the published replacements of §4.4** (Mumford, Reiner, Cassels–Fröhlich,
   Fontaine's Astérisque 223, Serre 1968, SGA 1, SGA 7, Deligne–Mumford, Baba–Granath 2008,
   Buzzard 1997). None changes a statement, but each must be read before it is cited.
5. **NoCM** is used here as checked by rv-h-cm. Its repairs R1-R5 must be applied when the CM
   paragraph is replaced; in particular González–Rotger's Proposition 5.6 must be cited only
   under `(f, 6) = 1`, and Saia's restatements must not be cited.
