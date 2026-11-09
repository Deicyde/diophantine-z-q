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
  use of A006 and of Faltings 1983 at line 621, but A006 stays for lines 894-903. It adds
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
| 4 | `h(Δ) ≤ k ⇒ √|Δ| ≤ 2k²e^{21000k²}` at `k = D` | 581-593 | A003 | Fowler, Prop. 2.7 | **removed** |
| 4 | Degree of `j(E)` is the order class number; `j(E)` integral | 583-598 | A065 | Fowler §2.1 | **removed from H** (kept at 1009-1016, 1759-1769) |
| 4 | Faltings height of a CM elliptic curve (discriminant formula) | 595-613 | A004 | Barquero-Sanchez et al., Eq. (6.2) | **removed** |
| 4 | Isogeny estimate with source `E²`, target `A` | 614-619 | A005 | Gaudron–Rémond 2014, Thm 1.4 | **removed** (theorem kept via A015) |
| 4, 8 | `h_F(target) ≤ h_F(source) + ½ log deg`, additivity | 620-628, 894-900 | A006 | Faltings 1983, Lemma 5 | CM use removed; kept for 894-900 |
| 5 | Skolem–Noether; sign cocycle | 632-663 | A062 | Milne CFT notes IV.2.10 | kept |
| 5 | `Br(ℚ)[2]`, local square roots, reciprocity, injectivity of `Br(ℚ) → ⊕ Br(ℚ_v)` | 665-708 | A007 | Milne ADT I; Milne CFT notes | kept |
| 6 | Semisimplicity of `V_ℓ(A)|G_{L'}` and `End_{G_{L'}} V_ℓ(A) = B ⊗ ℚ_ℓ`, hence `r_ℓ` absolutely irreducible | 732-734 | A008 | Faltings 1983, Satz 3, Satz 4 | kept; §2 |
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

**Added** (as checked by rv-h-cm; not rechecked here):

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
  (UNCHECKED). vK (§4, the paragraph after the proof of Lemma 4.1; VERIFIED as a statement of vK) records that
  "Masser–Wüstholz gave a new proof of the Tate conjecture on using their isogeny estimates which
  rely on transcendence theory", that Bost and David made the estimates effective (Bost's
  Bourbaki exposé, p. 121), and that GR14 gives completely explicit constants. vK also states the
  GR14 bound in the form used here: for `A'` that is `K`-isogenous to `A`, GR14 Theorem 1.4 gives
  isogenies of degree at most `κ(A)` (vK, equation for `|h(A) - h(A')|`).
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

