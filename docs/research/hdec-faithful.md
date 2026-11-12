# hdec-faithful: Theorem 4.1 (instance `SixContactMin`) decomposed along Glazer's proof

Status: research note (task hdec-faithful, 2026-11-11). Lean draft:
`scratch/hdec-faithful/Leaves.lean` (compiles with `lake env lean`; log
`scratch/hdec-faithful/log.md`). No file under `ZInQKernel/`, `blueprint/` or other notes was
edited.

Sources: the frozen 11/5 manuscript `diophantine_zq.tex` ("N5 Lxxx"; proof of Theorem 4.1 at
L404-964, appendix lemma at L10936-11005, both read for this note); `docs/research/h-trust.md`
(the 36 steps A1-F4, their suppliers and locators); `h-b1.md` (Lemma PR), `rv-h-cm.md` §7.2
(NoCM), `h-a011.md` §1.1 (Pan's Theorem 1.0.4 as printed in arXiv v2), `wk-h.md`, `rv-lit.md`,
`prereq-survey.md`; `ZInQKernel/Hypotheses/{Height,HeightMin,JHeight}.lean`; Mathlib v4.35.0 in
`.lake/packages/mathlib` (grep and compilation).

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a
published theorem with its reference. **SPECULATIVE**: an assessment. Theorem numbers are those
of h-trust; h-trust marks almost all of them UNVERIFIED in the journal versions (some
ASTRA-READ or AUDIT-READ), and I could not read any journal here (no network): every locator
below is **UNVERIFIED** unless h-trust records it as read. I added no locator from memory without
marking it UNVERIFIED.

## 1. Verdict

1. **The proof of Theorem 4.1 decomposes cleanly, but not into about ten theorems (VERIFIED as a
   reading of N5 and h-trust).** Following N5 with the repository's adopted replacements (Lemma
   PR for N5 L443-530, NoCM for the CM paragraph, the determinant argument in C8), the
   literature inputs that carry weight are **40 leaves: 21 research-level theorems (from 18
   sources) and 19 textbook theorems** (§3). Merging them into ten would merge distinct
   theorems (for instance Pan with Berger, or Faltings' isogeny theorem with his height lemma).
   They fall into **eight packages**, which is the natural unit for crowdsourcing:
   P1 the discriminant-6 Shimura curve (L1-L5), P2 reduction theory (L6-L10), P3 classical
   abelian varieties (L11-L13), P4 arithmetic of `ℚ` (L14-L20), P5 Faltings (L21), P6 p-adic Hodge
   theory and modularity (L22-L27), P7 modular curves (L28-L30), P8 Arakelov heights (L31-L35).
2. **The glue is 21 items G0-G20 (§4).** Glazer's new arguments are G7 (scalar descent), G8-G10
   and G12 (the representation `r_ℓ`, its de Rham property and oddness, the twist), G14 (one
   compatible system) and G15 (the uniform conductor bound). The repository's replacements are G2,
   G3 (Lemma PR) and G6 (NoCM). G20, the return from `J(u)` to `u`, is already a Lean proof
   (`ZInQ.JHeight.sixContactMin_of_jHeightBound`). No glue step hides a deep theorem: each one
   cites its leaves.
3. **Statability today (VERIFIED by compiling `Leaves.lean`).** Eight statements are stated in Lean
   now, as concrete `def … : Prop` over Mathlib plus cheap new definitions (absolute Galois group
   of `ℚ`, inertia and Frobenius through valuation subrings of `ℚ̄`, continuous
   representations into `GL_n(ℚ̄_ℓ)`, cusp forms on `Γ₁(N)` with nebentypus, normalized
   eigenforms through the Hecke recursion of their q-expansion coefficients):
   Skolem–Noether (L14), the Hasse principle for central simple `ℚ`-algebras (L15),
   Kronecker–Weber (L17), Chebotarev in the density form used (L18), Brauer–Nesbitt (L19),
   existence of eigenform representations (Eichler–Shimura–Deligne–Serre, L27a), Deligne–Serre's
   finiteness for weight one (L27b), and twisting of eigenforms (L28a). They cover five leaves
   fully (L14, L17, L18, L19, L27) and two in part (L15, L28). The other 35 statements (43 in all
   when L15, L27 and L28 are split into parts) need new definitions: medium (abelian varieties
   with Tate modules, models with good reduction, conductors of ℓ-adic representations, upper
   ramification groups), large (de Rham and Hodge–Tate representations; Siegel modular forms
   and theta constants) or very large (the Faltings height; the moduli scheme of QM abelian
   surfaces of discriminant 6; `J₁(N)` as an abelian variety over `ℚ`). For them `Leaves.lean`
   has a named placeholder `def L… : Prop := sorry` whose docstring is the statement, so that
   the top-level glue theorem `sixContactMin_of_leaves` has every leaf as a named hypothesis.
   It is proved from `jHeightBound_of_leaves` (the glue G1-G19, `sorry`) by the existing Lean
   proof of G20. Those placeholders carry no content until their definitions exist; the theorem
   must not be cited as a reduction before then. Two small glue facts are proved (the weight
   arithmetic of G12 and the prime-product bound of G16).
4. **What this changes against wk-h (SPECULATIVE as an assessment).** wk-h concluded that no
   interface package could be stated faithfully and proposed abstract signatures. Here no leaf
   is stated over an abstract structure: the statable ones are over genuine definitions, the rest
   are explicit gaps with named missing definitions. The Galois-representation side (P4, half of
   P6, part of P7) is closer than wk-h judged, because "attached to an eigenform" can be phrased
   through Frobenius traces and q-expansion coefficients with cheap definitions. The geometric
   side (P1, P8, `J₁(N)`) is as far as wk-h said.
5. **Biggest missing definitions:** the Faltings height (five leaves L31-L35 and glue G18-G19),
   then the moduli scheme `Y₃` of the discriminant-6 QM curve with its canonical model
   (L1-L5 and G1-G6). **Most serious risk:** the leaves must be stated never stronger than
   published, and three of them have a delicate published form: Pan's conclusion "comes from a
   cuspidal eigenform up to twist" is undefined in his introduction (§6 R2), several leaves are
   used in a consequence form that needs Chebotarev and Brauer–Nesbitt to derive (§6 R3), and
   L1 is assembled from several statements of Deligne 1971 (§6 R4).

## 2. The proof graph

Kinds: **LITERATURE** (the node is an application of a published theorem, with at most a
hypothesis check), **NEW** (an argument of N5 or of the repository, reviewed by models only),
**BOOKKEEPING** (exact computation, numerics, or routine assembly). A node with literature inputs
and a new argument is NEW, and its inputs are listed. Arrows "⇐" give the nodes and leaves used.
The step names are h-trust's; "L" and "G" refer to §§3-4.

### 2.0 The spine

For `u ∈ ℚ \ 𝒞`, with `M = M_S(u)`, `T = S ∪ supp M`, `Q = Q_R`, the proof produces in order
(VERIFIED by reading N5 L404-964):

1. a number field `K`, Galois over `ℚ`, `[K:ℚ] ≤ 324!`, unramified outside `T`, and a principally
   polarized abelian surface `A/K` with QM by `𝒪` over `j = J(u)`, with good reduction at all
   places not above 3 (Part A);
2. `End⁰(A_ℚ̄) = B` (A9 + A10);
3. a Galois number field `L'` with `[L':ℚ] ≤ QM` and a two-dimensional `r_ℓ : G_ℚ → GL₂`, with
   `V_ℓ(A) ⊗ E ≅ r_ℓ ⊕ r_ℓ` on `G_{L'}` (Part B, C1);
4. a weight-two newform `f` of level `N ≤ QM²` with `r₅ ≅ ρ_{f,5}` (Parts C, D);
5. an `L'`-isogeny `A × Z → J₁(N)` (E1);
6. `h_F(A) ≤ Q¹⁷M²⁴` (E2-E4);
7. `h(J(u)) ≤ (40·10⁴·2²⁴ + 22) · max(1, C_cm, Q¹⁷) · M²⁴`, which is `ZInQ.JHeight.JHeightBound`
   (F1-F3);
8. `h(u) ≤ H₆ M²⁴`, i.e. `SixContactMin` (F4; Lean, `sixContactMin_of_jHeightBound`).

### 2.1 Nodes

| Node | N5 lines | Content | Kind | ⇐ (nodes; leaves) |
| --- | --- | --- | --- | --- |
| A1 | L410-420 | QM datum `B=(2,−3)`, `𝒪`, `μ = 2j+ij`, Gram matrix of `Trd(μ⁻¹xȳ)` with det 1 | BOOKKEEPING | script `form_check.py`; LY eq. (3) as a convention |
| A2 | L420-422, L908-909 | `X₆/W ≅ P¹_j`, branch values `0, ∞, −16/27`, indices 4, 6, 2, at CM discriminants −4, −3, −24 | LITERATURE | L2, L3 |
| A3 | L423-441 | normalizer index 4, central ideles act trivially, `Γ'` acts on `Y₃` over `ℚ` with quotient `P¹_j`, `deg(Y₃ → P¹_j) ≤ 324` | NEW | A1, A4; L1 (Hecke action over `ℚ`); local normalizers (Vignéras; elementary, glue G1) |
| A4 | used at L528 | `Y₃` is the fine moduli scheme over `ℚ` of `(A, ι, λ, η)`, `K₃` neat | LITERATURE | L1 (with polarization uniqueness, an elementary argument in G1) |
| A5 | replaces L443-528 | Lemma PR(i): the fibre field `K` is Galois, `[K:ℚ] ≤ 324!`, unramified outside `T`; `J(u)` is not a branch value | NEW (repository, h-b1) | A2, A3, A4; L1 (reciprocity at CM points, Lemma NV), L6, L7; polynomial identities `G⁶ − 97200F² = H²` and supports (scripts) |
| A6 | replaces L529-530 | Lemma PR(ii): `A` and its conjugates have good reduction at every `v ∤ 3` | NEW (repository, h-b1) | A4; L8, L10; torsion-freeness of `1 + 3M₄(ℤ₃)` |
| A7 | L532-543 | the conjugates `σA` have the same geometric polarized moduli point | NEW | A2; L2 (`V_ℤ = V/W`), L3 (Igusa vector); `F(u) ≠ 0`, `disc G < 0` |
| A8 | L544-563 | Hom field `L`: `[L:ℚ] ≤ D`, `L/ℚ` normal, unramified outside `T` | NEW | A5, A6, A7; L11a (rank of Hom), L10; Minkowski's lemma (elementary) |
| A9 | L564-577 | `End⁰(A_ℚ̄) ∈ {B, M₂(k)}` | NEW | L12; centralizer computation |
| A10 | replaces L578-631 | NoCM: `End⁰(A_ℚ̄) = B` for every `u ∈ ℚ \ 𝒞` | NEW (repository, h-cm + rv-h-cm §7.2) | A2, A4, A9; L1 (reciprocity), L5; Vignéras' embedding criterion (textbook, in L5's use); script `rv-h-cm/check.py` |
| B1 | L632-664 | `B`-linear isogenies `μ_σ`, scalar cocycle `c`, sign cocycle `ε` on `Gal(L/ℚ)` | NEW | A8, A10; L14 |
| B2 | L665-693 | `[ε] ∈ Br(ℚ)[2]` is trivial outside `T`; Dirichlet character `χ` with the same invariants, `m ≤ 2R^R M` | NEW | B1; L15, L16 (square-root criterion via local reciprocity) |
| B3 | L693-716 | cochain `β`, `β² = χ`, `∂β = ε`; `L'` Galois, `[L':ℚ] ≤ QM` | NEW | B2; numerics |
| C1 | L719-731 | `ρ_ℓ(σ) = β(σ)⁻¹a_σμ_σ∘σ`, `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`, Tate action on `G_{L'}` | NEW | B1-B3 |
| C2 | L731-734 | `r_ℓ|G_{L'}` absolutely irreducible | NEW (one-line commutant argument on a LITERATURE input) | C1, A10; L21 |
| C3 | L734-737, L10939-11000 | `r_ℓ` de Rham at `ℓ`, HT weights `{0, −1}` (lemma `lem:de-rham-descent`) | NEW (appendix lemma, two model reviews) | C1; L22, L23, L11e |
| C4 | L739-741 | de Rham ⇒ potentially semistable | LITERATURE | C3; L24 |
| C5 | L742-751 | `r_ℓ` odd | NEW | C1; L13, L12 |
| C6 | L752-754 | `r_ℓ` unramified outside `T ∪ {ℓ}` | BOOKKEEPING | A5, A6, A8, B3; L10 |
| C7 | L755-757 | Pan at `ℓ = 5`: `r₅` comes from a cuspidal eigenform up to twist | LITERATURE | C2-C6; L25 |
| C8 | L757-768 | the twist is a finite character, `k = 2` (determinant argument of V16 L660-667) | NEW | C7, C3; L26, L27b (`k = 1`), L11d (Weil pairing), L17 |
| C9 | L768-774 | newform `f`; `r₅` is a constituent of `V₅` of the modular abelian variety (here: of `J₁(N)`) | NEW (assembly of LITERATURE inputs) | C8; L28, L29, L18, L19 |
| C10 | L776-795 | `r₃` and `r₅` lie in one compatible system with `f` | NEW | A6, B1, C9; L11b, L11f, L18, L19, L21 |
| D1 | L796-812 | break bound `u_last ≤ 2δ/e ≤ 4a²` | NEW | L20 |
| D2 | L813-823 | semistability over `F(A[3])`; wild inertia trivial on `V_ℓ`, odd `p` | NEW | L9, L20 |
| D3 | L823-846 | the `p = 2` paragraph: relative upper break of `β` at most `3e` | NEW | L16, L20; formal logarithm (Silverman IV.6.4, elementary) |
| D4 | L846-852 | conductor exponents `a_p(r_ℓ) ≤ E₀` (`p ≤ R`), `≤ 2` (`R < p ∈ T`), `0` (outside `T`) | NEW | D1-D3, A6, C10 |
| D5 | L852-857 | `N ≤ ∏_{p≤R} p^{E₀} · M² ≤ QM²` | LITERATURE (+ numerics) | D4, C9; L30 |
| E1 | L861-867 | `L'`-isogeny `A × Z → J₁(N)`, `g = dim J ≥ 2` | NEW (assembly) | C9, A10; L21, L11c |
| E2 | L868-876 | `h_F(J₁(N)) ≤ 1.3·10⁷ N¹²` | LITERATURE | L31 (with genus and Belyi degree `≤ N²`, elementary) |
| E3 | L878-892 | `log deg φ ≤ Q¹⁷M²⁴` | LITERATURE (+ numerics) | E1, E2; L32 |
| E4 | L893-905 | `h_F(A) ≤ Q¹⁷M²⁴` | LITERATURE (+ numerics) | E3; L33, L34 |
| F1 | L908-927 | `j = 3779136 (∏ z_m)⁴/(∑ z_m⁸)⁵` in even theta nulls | LITERATURE (+ script) | A2; L3, L4 |
| F2 | L928-932 | `h(j) ≤ 40 h([z_m]) + 22` | BOOKKEEPING | F1; Mathlib `logHeight_eval_le`-type bound |
| F3 | L934-947 | `h([z_m]) ≤ 10⁴·2²⁴ max(1, h_F(A))` | LITERATURE (+ normalization) | L35 |
| F4 | L949-964 | `h(u) < h(j) + 74`, final constant | BOOKKEEPING | proved in Lean (`JHeight.lean`, in the stronger form `12h(u) ≤ h(J(u)) + 450`) |

The N5 CM paragraph (L581-631: Fowler, the CM height formula, the CM use of GR14) is not a node:
A10 makes the branch empty (rv-h-cm §7.2), so Fowler and the CM Faltings-height formula are not
leaves. N5's integral-model route (Buzzard) is replaced by A5-A6 and is not a leaf either.

Counts (VERIFIED from the table): LITERATURE 10 nodes (A2, A4, C4, C7, D5, E2, E3, E4, F1, F3,
counted with their numerics; F3 has a normalization check), NEW 22, BOOKKEEPING 4 (A1, C6, F2,
F4). The difference from wk-h's counts (15 W) is that wk-h classed C2, C3, C9, A9 and E1 as W;
here they are NEW because each contains an argument beyond the hypothesis check (rv-lit N3 made
the same correction for A9, C3, C9).

## 3. The leaves

Format of each leaf: **statement** (the form the proof uses); **reference**; **exact or
consequence** (a consequence is never stronger than the published statement; when it needs other
leaves to derive, they are named); **objects**; **Lean now**: yes (stated in `Leaves.lean` over
genuine definitions), with new definitions (tier of the missing definition), or no (needs a very
large definition first). "Research" or "textbook" says whether the leaf is a specific published
research theorem or a standard result of a monograph.

### P1. The discriminant-6 Shimura curve

**L1. Canonical model and moduli interpretation of the level-3 QM curve** (research).
- *Statement.* Let `B = (2,−3)/ℚ`, `𝒪` the maximal order of A1, `μ` as in A1, and `K₃ ⊂ 𝒪̂^*` the
  principal congruence subgroup of level 3. (a) The functor on `ℚ`-schemes of quadruples
  `(A, ι, λ, η)`, with `A` an abelian scheme of relative dimension 2, `ι : 𝒪 → End A`, `λ` a
  principal polarization with Rosati involution `a ↦ μ⁻¹āμ`, and `η : 𝒪/3𝒪 ≅ A[3]` an
  `𝒪`-linear isomorphism, is represented by a smooth projective curve `Y₃/ℚ` (`K₃` is neat).
  (b) `Y₃(ℂ)` is `⊔ Γ_i\ℍ` for the arithmetic groups of `K₃`, compatibly with the universal
  family. (c) The finite-adelic normalizer of `𝒪̂` acts on `Y₃` over `ℚ` (Hecke action).
  (d) Shimura's reciprocity law at CM points: for a CM point `x` with CM by an order `R` of an
  imaginary quadratic `k`, `Gal(ℚ̄/k)` acts on `x` through the Artin map of `k` composed with the
  action of `k̂^*` through the embedding of `R`.
- *Reference.* Shimura, Ann. of Math. 85 (1967), Main Theorems I-II; Deligne, Sém. Bourbaki
  389 (1971), Thm 4.21, Cor. 5.7, Ex. 5.8, §§4.8-4.17 (moduli and markings), §3 (reciprocity);
  Kottwitz, JAMS 5 (1992), §5; neatness by Serre's lemma (Mumford, *Abelian varieties*, §21
  Thm 5). Locators per h-trust A4 and h-b1 §4A, UNVERIFIED.
- *Exact or consequence.* Exact, but assembled from several statements of Deligne 1971 and
  Shimura 1967 (§6 R4). (d) is part of the definition of the canonical model in Deligne's
  sense, so (a) + "canonical model" gives (d).
- *Objects.* Abelian schemes over `ℚ`-schemes, QM structures, polarizations, level structures,
  representability; CM points; Artin map of an imaginary quadratic field.
- *Lean now.* **No.** Needs abelian schemes and moduli functors (very large). Anthropic FLT has
  QM fake elliptic curves and fine moduli for its Čerednik–Drinfeld step (prereq-survey §1, row
  A4); whether they give `Y₃` over `ℚ` is unchecked.

**L2. Baba–Granath: the Atkin–Lehner quotient and the polarized relation** (research).
- *Statement.* For discriminant 6, the quotient `X₆/W` (`W ≅ (ℤ/2)²` the Atkin–Lehner group) is
  `P¹_j` with branch points `j = 0, ∞, −16/27`, of indices 4, 6, 2, at the CM points of
  discriminants −4, −3, −24; and two QM surfaces with principal polarizations of the fixed type
  have the same polarized moduli point iff their points of `X₆` are in one `W`-orbit
  (`V_ℤ = V/W`).
- *Reference.* Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1, Lemma 3.1, §3 datum (p. 739)
  (journal numbering UNVERIFIED; the 2005 preprint's Thm 1 and §3.2 are ASTRA-READ). The −24
  label is confirmed by `scratch/rv-up/endo24.py` (h-trust A2).
- *Exact or consequence.* Exact.
- *Objects.* `X₆` (from L1), the Atkin–Lehner involutions, CM points.
- *Lean now.* **No** (needs L1's objects).

**L3. Lin–Yang: Igusa invariants on the quaternionic locus** (research).
- *Statement.* On the finite nonzero `j`-locus, the principally polarized QM surface over `j` is
  the Jacobian of a genus-2 curve with Igusa invariants
  `[J₂ : J₄ : J₆ : J₁₀] = [12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]` in weighted projective
  space; the Siegel modular forms `ψ₄` and `χ₁₀` restricted to the locus `X ≅ P¹` have divisors
  making `χ₁₀²/ψ₄⁵` a degree-one function with zero at `P₋₄` and pole at `P₋₃`.
- *Reference.* Lin–Yang, Math. Z. 295 (2020), Example 30 and eqs. (13)-(14) (VERIFIED in arXiv
  v1 by h-v14; journal numbering UNVERIFIED); derived without eq. (2) by
  `scratch/h-v14/igusa_check.py` (h-trust F1).
- *Exact or consequence.* Exact (Example 30 with eqs. (13)-(14)); eq. (2) is not used.
- *Objects.* Igusa invariants of genus-2 curves (cheap: polynomials in the sextic's
  coefficients); Siegel modular forms of degree 2 (large); the QM locus and its coordinate `j`
  (L1, L2).
- *Lean now.* **No** (needs the QM locus).

**L4. Igusa: `ψ₄` and `χ₁₀` in theta constants** (research, classical).
- *Statement.* `ψ₄ = 2⁻² Σ_{m even} θ_m⁸` and `χ₁₀ = −2⁻¹⁴ Π_{m even} θ_m²` as Siegel modular forms
  of degree 2, with Igusa's conversion between `ψ₄, ψ₆, χ₁₀, χ₁₂` and `J₂, …, J₁₀`.
- *Reference.* Igusa, Amer. J. Math. 89 (1967), pp. 833-834 and 848; Lauter–Naehrig–Yang,
  J. Number Theory (2015), §2.2 (conventions). UNVERIFIED.
- *Exact or consequence.* Exact.
- *Objects.* Theta constants with characteristics on the Siegel upper half space `𝔥₂`; Siegel
  modular forms of degree 2.
- *Lean now.* **With new definitions (large).** Mathlib has the genus-1 Jacobi theta function
  only.

**L5. González–Rotger: CM points on `X₆`** (research).
- *Statement.* For an order `R` of conductor `f` in an imaginary quadratic `k` with `(f, 6) = 1`
  and `R` embeddable in `𝒪` (Vignéras' criterion: neither 2 nor 3 splits in `k`), the set
  `CM(R)` of points of `X₆` with CM by `R` has `h(R)` elements (Prop. 5.6), and the field `ℚ(x)`
  of `x ∈ CM(R)` is the ring class field `H_R` if some prime dividing 6 is inert in `k`, and has
  index 2 in `H_R` otherwise (Thm 5.12).
- *Reference.* González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, Prop. 5.6 (VERIFIED in
  arXiv:math/0612732 by rv-h-cm; journal numbering UNVERIFIED); Prop. 5.6 only under
  `(f, 6) = 1` (rv-h-cm repair 1). Vignéras, LNM 800 (1980), for the embedding criterion.
- *Exact or consequence.* Exact, restricted to `(f, 6) = 1`.
- *Objects.* `X₆`, CM points, ring class fields (Tau Ceti has ring class fields).
- *Lean now.* **No** (needs L1's objects).

### P2. Reduction theory and étale covers

**L6. Zariski–Nagata purity of the branch locus** (textbook).
- *Statement.* A finite surjective morphism from a normal scheme to a regular scheme that is
  étale outside a closed subset of codimension ≥ 2 is étale.
- *Reference.* SGA 1, Exp. X, Thm 3.1 (UNVERIFIED). Stacks Tag 0BMB, formalized in Axiom's
  Stacks (proved, unreviewed; prereq-survey row A5).
- *Exact or consequence.* Exact.
- *Objects.* Regular and normal schemes, finite étale morphisms (Mathlib has étale morphisms and
  regular local rings; codimension of closed subsets is available).
- *Lean now.* **With new definitions (medium):** a statement-level port of Stacks 0BMB.

**L7. Abhyankar's lemma** (textbook).
- *Statement.* For a regular scheme with a normal crossings divisor, a finite cover tamely
  ramified along the divisor is, étale locally, a Kummer cover `z^e = t`.
- *Reference.* SGA 1, Exp. XIII, 5.3; Grothendieck–Murre, LNM 208 (1971) (UNVERIFIED). Stacks
  Tag 0EYG (proved, unreviewed).
- *Exact or consequence.* Exact (h-b1's Prop. TS uses it for a regular divisor on a surface).
- *Objects.* As L6, plus tame ramification along a divisor.
- *Lean now.* **With new definitions (medium).**

**L8. Grothendieck's semistable reduction theorem** (research, classical).
- *Statement.* An abelian variety over the fraction field of a henselian DVR acquires semistable
  reduction (the identity component of the special fibre of the Néron model is an extension of
  an abelian variety by a torus) over a finite extension.
- *Reference.* SGA 7 I (LNM 288), Exp. IX, Thm 3.6 (UNVERIFIED).
- *Exact or consequence.* Exact (used in h-b1 §4(ii) step 2 with the toric-part argument).
- *Objects.* Néron models (Anthropic FLT has them in a special case), tori.
- *Lean now.* **With new definitions (large: Néron models).** A Galois-side form
  (Grothendieck's monodromy theorem: inertia acts quasi-unipotently on `V_ℓ(A)`) needs only Tate
  modules (medium), but h-b1's toric-part argument uses the Néron model, so that form is not a
  drop-in replacement (SPECULATIVE).

**L9. Raynaud's criterion** (research, classical).
- *Statement (Galois form used).* Let `F/ℚ_p` be finite, `A/F` an abelian variety, `n ≥ 3` with
  `p ∤ n`, and `A[n] ⊂ A(F)`. Then `A` has semistable reduction over `F`; consequently the
  inertia group `I_F` acts unipotently on `V_ℓ(A)` for every `ℓ ≠ p`, so the wild inertia acts
  trivially.
- *Reference.* SGA 7 I, Exp. IX, Prop. 4.7; Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995),
  Thm 3.5, p. 406, `n ≥ 3` (ASTRA-READ). "Consequently": Grothendieck's criterion, SGA 7 IX,
  Prop. 3.5 (UNVERIFIED).
- *Exact or consequence.* The first sentence is exact; the Galois form is a consequence of it and
  SGA 7 IX 3.5. D2 uses only the Galois form.
- *Objects.* Abelian varieties over local fields, Tate modules, inertia groups.
- *Lean now.* **With new definitions (medium: Tate modules).**

**L10. Néron–Ogg–Shafarevich (Serre–Tate)** (research, classical).
- *Statement.* For `A` over the fraction field `F` of a DVR with residue characteristic `p` and
  `ℓ ≠ p`: (a) `A` has good reduction iff `I_F` acts trivially on `V_ℓ(A)` (equivalently on
  `A[ℓ^∞]`); (b) `A` has potentially good reduction iff `I_F` acts on `V_ℓ(A)` through a finite
  quotient.
- *Reference.* Serre–Tate, Ann. of Math. 88 (1968), Thms 1-2 (UNVERIFIED).
- *Exact or consequence.* Exact.
- *Objects.* Good reduction (an abelian scheme over the DVR with generic fibre `A`), Tate
  modules, inertia. Tau Ceti proves the elliptic-curve case only.
- *Lean now.* **With new definitions (medium).**

### P3. Abelian varieties, classical

**L11. Mumford's theorems** (textbook; six statements, counted as six leaves).
- (a) `Hom(A, B)` is free of rank `≤ 4 dim A dim B` (Mumford, *Abelian varieties*, §19 Thm 3).
- (b) The characteristic polynomial of an endomorphism on `V_ℓ(A)` has integer coefficients
  independent of `ℓ ≠ char` (§19 Thm 4).
- (c) Poincaré reducibility: every abelian subvariety has a complement up to isogeny (§19 Thm 1).
- (d) The Weil pairing of a polarization is Galois-equivariant with values in `ℤ_ℓ(1)`; hence
  `G_K` acts on `V_ℓ(A)` through `GSp` with multiplier the cyclotomic character (§§20, 23).
- (e) `V_ℓ(A) ≅ H¹_et(A_K̄, ℚ_ℓ)^∨`, Galois-equivariantly (§§19-20; Milne in Cornell–Silverman
  1986, Thm 15.1(a), p. 129).
- (f) Homomorphisms between abelian varieties with good reduction extend to their abelian-scheme
  models (Néron mapping property: Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2 Prop. 8).
- *Exact or consequence.* Exact. Locators per h-trust, UNVERIFIED.
- *Objects.* Abelian varieties, Tate modules, étale cohomology (e), abelian schemes (f).
- *Lean now.* **With new definitions:** (a)-(d) medium (abelian varieties are cheap on Mathlib's
  group schemes, `AlgebraicGeometry/Group/Abelian.lean`; Tate modules with Galois action are
  medium); (e) large (ℓ-adic étale cohomology); (f) medium.

**L12. Riemann's theorem, GAGA and rigidity** (textbook).
- *Statement.* For a complex abelian variety `A`, `End⁰(A)` is the algebra of endomorphisms of the
  rational Hodge structure `H₁(A(ℂ), ℚ)`; for abelian varieties over `ℚ̄`,
  `Hom(A, B) = Hom(A_ℂ, B_ℂ)`.
- *Reference.* Mumford §§1-3 with Serre, GAGA, Ann. Inst. Fourier 6 (1956); Conrad, Enseign.
  Math. 52 (2006), §3 (rigidity) (UNVERIFIED; replaces N5's citation of Milne's notes, h-trust
  §2.4).
- *Exact or consequence.* Exact.
- *Objects.* Complex tori, Hodge structures (Tau Ceti has Riemann forms), analytification.
- *Lean now.* **With new definitions (large: analytification of abelian varieties).**

**L13. Artin's comparison theorem** (textbook).
- *Statement.* For `A` over a subfield of `ℂ`, `V_ℓ(A) ≅ H₁(A(ℂ), ℚ) ⊗ ℚ_ℓ`, compatibly with
  complex conjugation acting on both sides.
- *Reference.* SGA 4, Exp. XI, 4.4 (UNVERIFIED); for abelian varieties also elementary from the
  uniformization `A(ℂ) = ℂ²/Λ` (torsion points).
- *Exact or consequence.* Exact (for abelian varieties the elementary form suffices).
- *Objects.* As L12.
- *Lean now.* **With new definitions (large).**

### P4. Arithmetic of `ℚ` and of local fields

**L14. Skolem–Noether** (textbook). *Statement:* for `A` central simple over `K` and `B` simple,
any two `K`-algebra maps `B → A` are conjugate by a unit of `A`. *Reference:* Reiner, *Maximal
orders*, Thm 7.21 (UNVERIFIED). *Exact.* *Lean now:* **yes** (`SkolemNoether`); Tau Ceti proves
it (`TauCeti.skolemNoether`).

**L15. The Brauer group of `ℚ`** (textbook).
- *Statement.* (a) Albert–Brauer–Hasse–Noether with reciprocity, in the form used: a central
  simple `ℚ`-algebra that splits over every `ℚ_p` splits over `ℚ`. (b) The identification
  `H²(G_ℚ, {±1}) ≅ Br(ℚ)[2]` (Kummer sequence and Hilbert 90), compatible with restriction to
  `G_{ℚ_v}`.
- *Reference.* Milne, *Arithmetic duality theorems*, Ch. I (ASTRA-READ); Tate in
  Cassels–Fröhlich, Ch. VII (UNVERIFIED).
- *Exact or consequence.* (a) is a consequence of ABHN (injectivity) and the sum formula
  (`inv_∞ ∈ {0, ½}` is forced to 0); (b) exact.
- *Objects.* Central simple algebras (Mathlib), base change to `ℚ_p` (Mathlib); for (b), Galois
  cohomology of `G_ℚ` with crossed products (medium).
- *Lean now.* (a) **yes** (`HasseBrauerQ`); (b) **with new definitions (medium)**. Tau Ceti proves
  the local–global sequence for `Br` (prereq-survey row B2).

**L16. Local class field theory for `ℚ_p` and its finite extensions** (textbook).
- *Statement.* The local Artin map `F^× → G_F^{ab}` (dense image, kernel trivial on the profinite
  completion), its compatibility with norms, and the upper numbering theorem (it maps `U_F^n`
  onto `G_F^{n,ab}`).
- *Reference.* Serre, *Local fields*, and Serre in Cassels–Fröhlich (UNVERIFIED).
- *Exact or consequence.* Exact. B2 uses it for the square-root criterion, D3 for `β⁴ = 1` on
  `U_F` and the break of `β`.
- *Lean now.* **With new definitions (medium).** Tau Ceti has local class field theory.

**L17. Kronecker–Weber** (textbook). *Statement:* a finite abelian extension of `ℚ` embeds in a
cyclotomic field. *Reference:* Washington, *Cyclotomic fields*, Thm 14.1 (UNVERIFIED). *Exact.*
*Lean now:* **yes** (`KroneckerWeber`); Tau Ceti proves it.

**L18. Chebotarev density** (textbook).
- *Statement (form used).* Frobenius elements are dense in `G_ℚ`: for every open subgroup `U`,
  every `σ` and every finite set `S` of primes, there are a prime `p ∉ S`, a place of `ℚ̄` above
  `p` and an arithmetic Frobenius `τ` at it with `τ⁻¹σ ∈ U`.
- *Reference.* Neukirch, *Algebraic number theory*, VII.13.4 (UNVERIFIED).
- *Exact or consequence.* Consequence of Chebotarev (applied to the finite Galois quotient cut out
  by the normal core of `U`).
- *Lean now.* **Yes** (`FrobeniusDense`). Tau Ceti proves Chebotarev
  (`NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet`).

**L19. Brauer–Nesbitt** (textbook). *Statement:* two semisimple finite-dimensional
representations of a group over a field of characteristic 0 with equal traces are isomorphic.
*Reference:* Curtis–Reiner (30.16) (UNVERIFIED; that numbering is the characteristic-polynomial
form, the trace form in characteristic 0 is the same section). *Exact.* *Lean now:* **yes**
(`BrauerNesbitt`).

**L20. Ramification groups of local fields** (textbook).
- *Statement.* For a finite Galois extension of `p`-adic fields: Hilbert's formula
  `δ = Σ_{i≥0}(|G_i| − 1)` for the different; Herbrand's theorem (upper numbering passes to
  quotients); the subgroup formula `G^u ∩ H = H^{ψ_{F'/F}(u)}` for the absolute groups; the
  different bound `δ ≤ e − 1 + e·v_p(e)`; the Artin and Swan conductors of a representation with
  finite wild image.
- *Reference.* Serre, *Corps locaux*, III §6, IV §§1-3, VI §2 (UNVERIFIED). The different bound is
  also proved in N5 L801-806.
- *Exact or consequence.* Exact.
- *Lean now.* **With new definitions (medium).** Tau Ceti proves Herbrand, Hilbert's formula and
  Artin conductor exponents (prereq-survey row D1); the different bound was not located.

### P5. Faltings

**L21. Faltings' finiteness theorems** (research).
- *Statement.* For abelian varieties `A, B` over a number field `F` and a prime `ℓ`: `V_ℓ(A)` is a
  semisimple `G_F`-module (Satz 3), and `Hom_F(A, B) ⊗ ℚ_ℓ → Hom_{G_F}(V_ℓA, V_ℓB)` is an
  isomorphism (Satz 4, Korollar 1).
- *Reference.* Faltings, Invent. Math. 73 (1983), Satz 3, Satz 4, Korollar 1, pp. 360-361
  (ASTRA-READ), with the erratum, Invent. Math. 75 (1984) (that it does not touch these is
  UNVERIFIED).
- *Exact or consequence.* Exact.
- *Lean now.* **With new definitions (medium: Tate modules with Galois action).**

### P6. p-adic Hodge theory and modularity

**L22. de Rham comparison** (research).
- *Statement (form used).* For `F/ℚ_ℓ` finite and an abelian variety `A/F` of dimension `g`,
  `H¹_et(A_F̄, ℚ_ℓ)` is de Rham, with `D_dR ≅ H¹_dR(A/F)` as filtered `F`-spaces; hence `V_ℓ(A)`
  is de Rham with Hodge–Tate weights `0` and `−1`, each with multiplicity `g` (`ℚ_ℓ(1)` of weight
  `−1`).
- *Reference.* Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 with Thms 9.1 and 9.3, and the
  corrigendum, Forum Math. Pi 4 (2016); alternatively Faltings 1989 or Tsuji 1999 (h-trust C3;
  UNVERIFIED in the journals).
- *Exact or consequence.* The first clause is exact (Scholze's statement is for proper smooth
  rigid spaces, applied to the analytification; Faltings/Tsuji state it for proper smooth
  schemes directly). The second is a consequence with L11e and L23.
- *Objects.* `B_dR` with its `G_F`-action and filtration, de Rham representations, Hodge–Tate
  weights, algebraic de Rham cohomology with its Hodge filtration.
- *Lean now.* **With new definitions (large).** Mathlib has `BDeRham R p` for perfectoid `R`
  (VERIFIED), with no Galois action, filtration or admissibility.

**L23. Fontaine's closure properties** (textbook). *Statement:* de Rham representations are
closed under duals, tensor products, direct sums and subquotients; Hodge–Tate weights are additive
in the evident way. *Reference:* Fontaine, Astérisque 223 (1994), 113-184, Thm 3.8, p. 142
(content UNVERIFIED; h-trust C3). *Exact.* *Lean now:* **with new definitions (large, as L22).**

**L24. Berger's p-adic monodromy theorem** (research). *Statement:* a de Rham representation of
`G_K`, `K/ℚ_p` finite, is potentially semistable. *Reference:* Berger, Invent. Math. 148 (2002),
Théorème 0.7 = Cor. 5.22 (published numbering ASTRA-READ; Thm 0.6 = 5.19 in arXiv v3, VERIFIED by
rv-h-a011). *Exact.* *Objects:* `B_st` with `φ`, `N`, filtration; potentially semistable
representations. *Lean now:* **with new definitions (very large: `B_st`).**

**L25. Pan's Fontaine–Mazur theorem** (research).
- *Statement.* Let `p` be an odd prime and `ρ : G_ℚ → GL₂(ℚ̄_p)` continuous and irreducible,
  ramified at finitely many places, potentially semistable at `p`, odd (`det ρ(c) = −1`), with
  distinct Hodge–Tate weights at `p`; if `p = 3`, assume the residual condition (vacuous at
  `p = 5`). Then `ρ` comes from a cuspidal eigenform up to twist.
- *Reference.* Pan, J. Amer. Math. Soc. 35 (2022), 1031-1169, Theorem 1.0.4 (arXiv:1901.07166v2
  statement VERIFIED by h-a011 §1.1; JAMS numbering UNVERIFIED).
- *Exact or consequence.* Exact once "comes from a cuspidal eigenform up to twist" is given a
  reading. Reading proposed for Lean (§6 R2): there are a normalized eigenform `g` of some
  weight `k ≥ 1`, level and nebentypus, and a continuous character `ψ : G_ℚ → ℚ̄_p^×`, such that
  `tr ρ(Frob_v) = ψ(Frob_v) · ι(a_v(g))` for almost all `v` (Frobenius traces; with L18-L19 this is
  `ρ ≅ ρ_g ⊗ ψ`). This reading is implied by every reading in the literature (an isomorphism with
  `ρ_g ⊗ ψ`, or with the representation of a regular algebraic cuspidal automorphic
  representation of `GL₂(𝔸_ℚ)` up to twist, which is `ρ_g ⊗ ψ` for a holomorphic eigenform `g` of
  weight `≥ 2`), so it is a consequence, not stronger.
- *Objects.* As L24; eigenforms and their Frobenius traces (cheap, in `Leaves.lean`).
- *Lean now.* **With new definitions (very large: potentially semistable, as L24; Hodge–Tate
  weights, large).** The rest of the statement (continuity, irreducibility, finite ramification,
  oddness, the conclusion) is expressible now with the definitions of `Leaves.lean` (VERIFIED by
  compiling those definitions).

**L26. Hodge–Tate weights of eigenform representations at every level** (research).
- *Statement (form used).* For a normalized eigenform `g` of weight `k ≥ 2`, any level `N`
  (including `ℓ | N`) and any nebentypus, the representation `ρ_{g,ι}` (Tate-module normalization:
  `tr ρ(Frob_p^arith) = a_p`) is Hodge–Tate at `ℓ` with weights `{0, 1 − k}`; normalization-free:
  its two weights differ by `k − 1`.
- *Reference.* Saito, Invent. Math. 129 (1997) (pst at `p` for every level); or Kato, Astérisque
  295 (2004), §9.4 p. 188 with §§5.4, 6.3, 8.3 and (14.10.2)-(14.10.3); or Scholl, Invent. Math. 100
  (1990) with L22 and L23 (h-trust C8; UNVERIFIED).
- *Exact or consequence.* Consequence (normalization conversion; rv-h-c8 R1).
- *Lean now.* **With new definitions (large: Hodge–Tate representations).**

**L27. Existence of the Galois representation of an eigenform, and Deligne–Serre** (research).
- *Statement.* (a) For every normalized eigenform `g` of weight `k ≥ 1`, level `N`, nebentypus `χ`,
  every prime `ℓ` and embeddings `ι_∞ : ℚ̄ → ℂ`, `ι_ℓ : ℚ̄ → ℚ̄_ℓ`, there is a continuous
  semisimple `ρ : G_ℚ → GL₂(ℚ̄_ℓ)`, unramified outside `Nℓ`, with
  `tr ρ(Frob_p) = ι_ℓ(α)` where `ι_∞(α) = a_p(g)`, for `p ∤ Nℓ`. (b) If `k = 1`, every continuous
  semisimple `ρ` with these traces has finite image.
- *Reference.* Eichler–Shimura (`k = 2`: Shimura 1971, Thm 7.14), Deligne, Sém. Bourbaki 355 (1971)
  (`k ≥ 2`), Deligne–Serre, Ann. Sci. ÉNS 7 (1974), Thm 4.1 (`k = 1`, finite image) (UNVERIFIED).
- *Exact or consequence.* (a) is a consequence of the published statements (which also give
  `det ρ`); (b) is a consequence of Deligne–Serre Thm 4.1 with L18 and L19 (the published
  `ρ_g` has finite image, and any semisimple `ρ` with its traces is isomorphic to it).
- *Lean now.* **Yes**, both (`EigenformRepExists`, `DeligneSerreConseq`).
- *Remark.* N5 uses (a) only implicitly (Pan's conclusion and C8-C10 presuppose `ρ_g`). In the
  trace reading of L25 the existence is needed by C8 (to apply L26) and C10.

### P7. Modular forms and modular curves

**L28. Twists and newforms** (textbook).
- *Statement.* (a) For a normalized eigenform `g` of weight `k`, level `N`, nebentypus `χ`, and a
  Dirichlet character `ψ` mod `m`, there is a normalized eigenform `g'` of level `Nm²` with
  `a_p(g') = ψ(p)a_p(g)` for `p ∤ Nm`. (b) Every system of Hecke eigenvalues `(a_p)_{p ∤ N}` of a
  normalized eigenform of level `N` is that of a unique newform, of level dividing `N`
  (strong multiplicity one), and Galois conjugates of newforms are newforms.
- *Reference.* Shimura 1971, Prop. 3.64; Atkin–Li, Invent. Math. 48 (1978); Li, Math. Ann. 212
  (1975), Thm 5; Miyake, *Modular forms*, Thm 4.6.19 (UNVERIFIED). Tau Ceti proves the newform
  bookkeeping (prereq-survey row C9).
- *Exact or consequence.* (a) is a consequence of the twisting proposition (which gives the
  coefficients `ψ(n)a_n`); (b) exact.
- *Lean now.* (a) **yes** (`EigenformTwist`); (b) **with new definitions (medium: newforms via the
  old space)**.

**L29. Eichler–Shimura: `ρ_f` inside `V_ℓ(J₁(N))`** (research).
- *Statement.* For a weight-2 newform `f` of level `N`, `J₁(N)` is an abelian variety over `ℚ`, and
  `V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` has a `G_ℚ`-stable two-dimensional subquotient on which
  `tr(Frob_p) = ι_ℓ(a_p(f))` for `p ∤ Nℓ` (the `K_f`-linear Eichler–Shimura relation for
  `A_f`; `V_ℓ(A_f)` free of rank 2 over `K_f ⊗ ℚ_ℓ`).
- *Reference.* Shimura 1971, Thm 7.9 and §7; Shimura, J. Math. Soc. Japan 25 (1973), Thm 1;
  Ribet 1977; Diamond–Im 1995, §12.5 (h-trust C9, rv-h-a9c9 R-C9-1; UNVERIFIED).
- *Exact or consequence.* Consequence (the subquotient is `V_λ(A_f)` for the place `λ` given by
  `ι_ℓ`).
- *Objects.* The modular curve `X₁(N)` over `ℚ` and its Jacobian; Tate modules.
- *Lean now.* **No** (needs `X₁(N)` as a scheme over `ℚ` and Jacobians: very large).
  Lean Pool proves the Eichler–Shimura isomorphism for `Γ₀(N)` and Anthropic FLT a mod-`𝔪`
  version (prereq-survey row C9).

**L30. Carayol's local–global compatibility** (research).
- *Statement (form used).* For a newform `f` of weight 2 and level `N`, a prime `λ` of residue
  characteristic `ℓ` and `p ≠ ℓ`, the Artin conductor exponent of `ρ_{f,λ}|G_{ℚ_p}` equals
  `v_p(N)`.
- *Reference.* Carayol, Ann. Sci. ÉNS 19 (1986), 409-468, Théorème (A) (N5 cites it at L9778 with
  §§0.3-0.7, pp. 409-411; UNVERIFIED; that Théorème (A) covers `F = ℚ` at `p | N` is h-trust D5's
  open check).
- *Exact or consequence.* Consequence (the Weil–Deligne conductor equals the Artin conductor of the
  `ℓ`-adic representation, which is what D4 bounds).
- *Objects.* Conductor of an `ℓ`-adic representation of `G_{ℚ_p}` (`dim V − dim V^{I_p}` plus the
  Swan conductor of the finite wild image), newforms.
- *Lean now.* **With new definitions (medium).**

### P8. Arakelov heights

**L31. Javanpeykar's bound for Jacobians of Belyi curves** (research).
- *Statement.* For a smooth projective connected curve `X` of genus `g ≥ 1` over `ℚ̄` with a Belyi
  map of degree `deg_B`, `h_F(Jac X) ≤ 13·10⁶ · g · deg_B⁵` (stable Faltings height, original
  normalization).
- *Reference.* Javanpeykar, Algebra Number Theory 8 (2014), Thm 1.1.1 (p. 90) and §2.3 (p. 98)
  (ASTRA-READ).
- *Exact or consequence.* Exact; applied to `X₁(N)` with `g, deg_B ≤ N²`.
- *Objects.* Faltings height (very large), Belyi maps, `X₁(N)`.
- *Lean now.* **No.**

**L32. Gaudron–Rémond's isogeny theorem** (research).
- *Statement.* For isogenous abelian varieties `A, B` of dimension `g` over a number field `K`,
  there is an isogeny `A → B` of degree at most
  `κ(A) = ((14g)^{64g²} [K:ℚ] max(h_F(A), log[K:ℚ], 1)²)^{1024g³}`.
- *Reference.* Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4 (exact `κ(A)`, original stable
  normalization, both directions: ASTRA-READ).
- *Exact or consequence.* Exact.
- *Lean now.* **No** (Faltings height).

**L33. Faltings' height lemma** (research).
- *Statement.* For an isogeny `φ : A → B` over a number field, `|h_F(A) − h_F(B)| ≤ ½ log deg φ`;
  `h_F(A × B) = h_F(A) + h_F(B)`; the stable height is invariant under finite extension.
- *Reference.* Faltings 1983, Lemma 5; Raynaud, Astérisque 127 (1985), Exp. VII, Cor. 2.1.3
  (UNVERIFIED). Additivity and invariance follow from the definition (glue once `h_F` exists).
- *Exact or consequence.* Exact (first clause).
- *Lean now.* **No** (Faltings height).

**L34. Bost's lower bound** (research). *Statement:* `h_F(A) ≥ −(3/2)·dim A` (N5's form; Bost's
is `≥ −log(π√2)·dim A`, and `log(π√2) < 3/2`). *Reference:* Bost, Sém. Bourbaki 795 (1996), as
recorded in Gaudron–Rémond, Duke 163 (2014), §9 (ASTRA-READ), and Comment. Math. Helv. 89 (2014)
§2.3 (h-trust E4). *Consequence* (weaker constant). *Lean now:* **no** (Faltings height).

**L35. Pazuki: theta height against Faltings height** (research).
- *Statement (g = 2, level r = 2).* For a principally polarized abelian surface `A` over a number
  field, with `X_D = max(1, h_F(A) + log π)` (Deligne metric),
  `h_Θ(A) ≤ ½ X_D + C₂ log(X_D + 2)` with `C₂ = 1000·2⁴(log 2⁴)⁵`, where `h_Θ` is the projective
  height of the sixteen level-2 theta constants.
- *Reference.* Pazuki, Bull. Soc. Math. France 140 (2012), Cor. 1.3(2) and §§2.2-2.3, with the
  `log π` shift for `g = 2` (ASTRA-READ).
- *Exact or consequence.* Exact.
- *Lean now.* **No** (Faltings height, theta constants).

### 3.1 Count and statability (VERIFIED from the list above)

- 40 leaves: L1-L10, L11a-f, L12-L35; 43 statements when L15, L27 and L28 are split into their
  parts (a), (b).
- Research-level, 21: L1, L2, L3, L4, L5, L8, L9, L10, L21, L22, L24, L25, L26, L27 (a and b
  counted once), L29, L30, L31, L32, L33, L34, L35. Sources, 18: Shimura 1967 with Deligne 1971
  (L1), Baba–Granath (L2), Lin–Yang (L3), Igusa (L4), González–Rotger (L5), SGA 7 IX (L8, L9),
  Serre–Tate (L10), Faltings 1983 (L21, L33), Scholze (L22), Berger (L24), Pan (L25), Saito or
  Kato (L26), Deligne 1971 with Deligne–Serre (L27), Shimura 1971/1973 (L29), Carayol (L30),
  Javanpeykar (L31), Gaudron–Rémond 2014 with Bost (L32, L34), Pazuki (L35).
- Textbook, 19: L6, L7, L11a-f, L12, L13, L14, L15, L16, L17, L18, L19, L20, L23, L28.
- Stated in Lean now, 8 statements (5 leaves fully, 2 in part): L14, L15(a), L17, L18, L19, L27(a), L27(b),
  L28(a).
- With new definitions of medium cost: L6, L7, L9, L10, L11a-d, L11f, L15(b), L16, L20, L21,
  L28(b), L30. Large: L4, L8, L11e, L12, L13, L22, L23, L26. Very large: L24, L25 (through `B_st`).
- Not statable until a very large definition exists: L1, L2, L3, L5 (QM moduli), L29 (`J₁(N)`),
  L31-L35 (Faltings height).

## 4. The glue

Format: **statement**; **inputs** (leaves and earlier glue); **origin** (N5 lines, or the
repository note, with its model review); **Lean** (provable from the leaves over the definitions
once those exist; what it needs beyond them); **size** (small < 500 lines, medium 0.5-3k, large
3-10k, very large > 10k; all sizes SPECULATIVE). Every glue item is model-reviewed only (h-trust
§2.1), except G18's numerics and G20, which are Lean proofs.

**G0. Top-level assembly.** *Statement:* the leaves imply `ZInQ.SixContactMin`. *Inputs:* G1-G20.
*Origin:* N5 L404-964 (spine §2.0). *Lean:* `sixContactMin_of_leaves` in `Leaves.lean`, stated
with `sorry`. Through G20 it reduces to `ZInQ.JHeight.JHeightBound Mult.S_mul`. Note that the
proof is uniform in admissible `S, R`, so the same glue gives `SixContactEstimate`. *Size:* small
once G1-G19 exist.

**G1. The fibre datum and the degree** (A1, A3, A4 input 2). *Statement:* N5's Gram matrix has
determinant 1 and Rosati involution `a ↦ μ⁻¹āμ`; the principal polarization with that Rosati
involution is unique; `|N/(𝔸_f^*K₀)| = 4`; central ideles act trivially on `Y₃`; `Γ'` acts with
quotient `P¹_j`; `deg(Y₃ → P¹_j) ≤ 4·72 ≤ 324`. *Inputs:* L1(a, c), L2; local normalizers of
maximal orders (Vignéras Ch. II; elementary over `ℚ_p`); `|(𝒪/3𝒪)^*| = 72`. *Origin:* N5
L410-441; h-b1 M1-M3; rv-h-trust §1.2 item 5. *Lean:* the matrix and the unit count are `decide`
or `norm_num` computations over Mathlib's `ℍ[ℚ, 2, −3]` (cheap, possible now); the rest needs
L1's objects. *Size:* medium.

**G2. Lemma PR(i): the fibre field** (A5). *Statement:* the splitting field `K` of the fibre of
`Y₃ → P¹_j` over `J(u)` is Galois over `ℚ`, `[K:ℚ] ≤ 324!`, unramified at every `p ≥ 17` (so at
every `p ∉ T`) unless some `v_p(u − c)` is positive and odd; `J(u)` is not a branch value.
*Inputs:* G1; L1(d) (Lemma NV), L2, L6, L7; the identities `G⁶ − 97200F² = H²`,
`J + 16/27 = 16H²/(27G⁶)` and the resultant supports (scripts `b1_checks.py`, `branch_check.py`;
Lean `ring`/`decide`). *Origin:* repository, `h-b1.md` (Prop. TS, Lemma NV, M1-M10), model review
`rv-h-b1.md`. *Lean:* needs normalization of finite covers of `P¹_ℤ[1/6]` and the leaves; the
polynomial facts are cheap now. *Size:* large.

**G3. Lemma PR(ii): good reduction away from 3** (A6). *Statement:* `A` and every conjugate
`σA` have good reduction at every place `v ∤ 3` of `K`. *Inputs:* L1(a) (`A[3] ⊂ A(K)`), L8, L10;
`1 + 3M₄(ℤ₃)` torsion-free (elementary). *Origin:* `h-b1.md` §4(ii); `rv-h-b1.md` §5. *Lean:* the
torsion-freeness is provable now (cheap); the rest over Néron models. *Size:* medium.

**G4. Conjugates and the Hom field** (A7, A8). *Statement:* the conjugates of `A` have one
geometric polarized moduli point; `W₀ = Res_{K/ℚ}A` has geometric endomorphism rank
`r ≤ 16F₀²`; `L = EK` is normal over `ℚ`, `[L:ℚ] ≤ F₀·3^{r²} ≤ D`, unramified outside `T`, and
defines all geometric endomorphisms and conjugacy homomorphisms. *Inputs:* G2, G3; L2, L3,
L11a, L10; Minkowski's lemma (finite subgroups of `GL_r(ℤ)` inject mod 3; elementary). *Origin:*
N5 L532-563 (Astra "whole"). *Lean:* Minkowski's lemma and the numerics are cheap now; the rest
over abelian varieties. *Size:* medium. Remark (h-trust A7): an isogeny between conjugates
suffices, which would remove L3 from G4 (it stays in G19).

**G5. The dichotomy** (A9). *Statement:* `End⁰(A_ℚ̄)` is `B` or `M₂(k)`, `k` imaginary quadratic.
*Inputs:* L12; the centralizer of `J ∈ B ⊗ ℝ` in `B ⊗ B^op` (exact computation,
`scratch/rv-h-a9c9/a9_centralizer.py`). *Origin:* N5 L564-577 (Milne paragraph new in N5; two
model reviews, rv-h-trust §2.1 and rv-h-a9c9 §1). *Lean:* the centralizer is linear algebra over
Mathlib's quaternion algebras (cheap); the identification with endomorphisms needs L12. *Size:*
medium.

**G6. NoCM** (A10). *Statement:* for `u ∈ ℚ \ 𝒞`, no point of `X₆` over `J(u)` is a CM point; hence
`End⁰(A_ℚ̄) = B`. *Inputs:* G5; L1(d), L2, L5; the coordinate `t = 1 + 27j/16`, the model
`ℚ(t)(√(−t), √(3(t−1)))`, `t(u) = H²/G⁶`, `t(u) − 1 = −3(180F/G³)²` (script
`rv-h-cm/check.py`; Lean `ring`). *Origin:* repository, `h-cm.md`, `rv-h-cm.md` §7.2 (shorter
proof), repairs R1-R5. *Lean:* the identities are cheap now; the counting argument is small once
L5 is stated. *Size:* small (given L5).

**G7. Scalar descent** (B1-B3). *Statement:* there are `B`-linear isogenies `μ_σ : σA → A` over
`L`, a sign cocycle `ε` inflated from `Gal(L/ℚ)`, a Dirichlet character `χ` of order
`m ≤ 2R^R M` unramified outside `T`, and a continuous cochain `β : G_ℚ → μ_{2m}` with `β² = χ`,
`∂β = ε`, wild inertia restrictions killed; `L'`, the kernel field of `β|G_L`, is Galois over `ℚ`
with `[L':ℚ] ≤ 2md ≤ 4DR^R M ≤ QM`. *Inputs:* G4, G6; L14, L15, L16; the square-root criterion
(`c2_sqrt_criterion.py`), constants (`c1_constants.py`). *Origin:* N5 L632-716 (Glazer, NEW);
rv-h-novel steps 1-3 with repair R1; Astra "descent". *Lean:* over Tau Ceti's Brauer group and
local class field theory; the numerics are cheap now. *Size:* medium-large (wk-h §4.3: 2-3k).

**G8. The representation `r_ℓ` and its irreducibility** (C1, C2). *Statement:*
`ρ_ℓ(σ) = β(σ)⁻¹a_σμ_σ∘σ` is a representation of `G_ℚ` commuting with `B`, `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`, equal
to the Tate action on `G_{L'}`, and `r_ℓ|G_{L'}` is absolutely irreducible. *Inputs:* G7; L21.
*Origin:* N5 L719-734 (NEW); rv-h-novel step 4; rv-h-a011 §3.1 H2. *Lean:* medium over Tate
modules. *Size:* medium.

**G9. The de Rham descent lemma** (C3). *Statement:* N5's Lemma `lem:de-rham-descent`: if
`V_ℓ(A) ⊗ C_ℓ ≅ r|G_F ⊕ r|G_F` for `A/F`, `F/K/ℚ_ℓ` finite, then `r` is de Rham with weights
`{0, −1}` at every coefficient embedding. *Inputs:* L22, L23, L11e; Hilbert 90 for the finite
Galois descent (h-trust C3: with `F` chosen Galois over `ℚ_ℓ`). *Origin:* N5 L10939-11000 (new
in N5; two model reviews rv-h-trust §2.1, rv-h-c3). *Lean:* medium once de Rham representations
exist. *Size:* medium.

**G10. Oddness** (C5). *Statement:* `det r_ℓ(c) = −1` for complex conjugation `c`. *Inputs:* G8;
L13, L12 (the Hodge decomposition of `H₁(A(ℂ), ℂ)` and `B ⊗ ℂ = M₂(ℂ)`). *Origin:* N5 L742-751
(Astra "descent"; rv-h-a011 §3.1 H5). *Lean:* medium. *Size:* medium.

**G11. Finite ramification** (C6). *Statement:* `r_ℓ` is unramified outside `T ∪ {ℓ}`. *Inputs:*
G2, G3, G4, G7; L10. *Origin:* N5 L752-754. *Size:* small.

**G12. Twist and weight** (C8). *Statement:* in the conclusion of L25 for `r₅`, the character `ψ`
has finite image and `k = 2`; hence `r₅` has the Frobenius traces of a weight-2 normalized
eigenform with finite nebentypus. *Inputs:* G8, G9, G10, G11; L25, L26, L27(a, b), L11d, L17
(Kronecker–Weber makes `ψ` a Dirichlet character), L18, L19. *Origin:* N5 L757-768 with the
determinant argument of V16 L660-667 (h-trust C8; rv-h-c8, rv-up §2.3). *Lean:* medium over
Hodge–Tate weights; the weight arithmetic (`{n, n+1−k} = {0, −1}` with `k ≥ 1` forces `n = 0`,
`k = 2`) is cheap now. *Size:* medium.

**G13. The newform and its place in `J₁(N)`** (C9, first half of E1). *Statement:* there is a
newform `f` of weight 2 and level `N` with `r₅ ≅ ρ_{f,5}`, and `r₅` is a constituent of
`V₅(J₁(N)) ⊗ ℚ̄₅`. *Inputs:* G12; L28 (twist into the eigenform, then the newform), L29, L18,
L19; Faltings' semisimplicity L21 for `J₁(N)`. *Origin:* N5 L768-774 (Li–Shimura sentence new in
N5; rv-h-trust §2.1, rv-h-a9c9 §2 with R-C9-1: the `K_f`-linear Eichler–Shimura relation replaces
the Euler-factor inference). The remark at L774 that duality preserves conductors is not needed
in this form (Tate normalization throughout). *Size:* medium.

**G14. One compatible system** (C10). *Statement:* for `p ∉ T ∪ {3, 5}` and a lift `σ` of
Frobenius, `tr r₃(σ)` and `tr r₅(σ)` are the images of one algebraic number; hence `r₃` is the
representation of `f` at 3. *Inputs:* G3, G7, G13; L11b, L11f, L18, L19, L21. *Origin:* N5
L776-795 (rv-h-novel step 4). *Size:* medium.

**G15. The uniform conductor bound** (D1-D4). *Statement:* the Artin conductor exponent of
`r_ℓ` (with `ℓ = 5` at `p ≠ 5` and `ℓ = 3` at `p = 5`) is `≤ 2 + 2U₀ ≤ E₀` at `p ≤ R`, `≤ 2` at
`R < p ∈ T`, and `0` outside `T`, where `U₀ = 4(DG₀)²`. *Inputs:* G3, G7, G14; L9, L16, L20; the
formal logarithm on `U_F^{e+1}` (Silverman IV.6.4; elementary); `c3_breaks.py`. *Origin:* N5
L796-852 (Glazer, NEW); rv-h-novel steps 5-8 with repairs R2-R3; Astra "conductor". *Lean:*
over Tau Ceti's upper ramification groups. *Size:* large. This is the most important new
argument to machine-check: its statement is entirely about local Galois theory, which Tau Ceti
already has.

**G16. The level bound** (D5). *Statement:* `N ≤ ∏_{p≤R} p^{E₀} · M² ≤ R^{RE₀}M² = QM²`.
*Inputs:* G13, G15; L30. *Origin:* N5 L852-857. *Lean:* the inequality `∏_{p ≤ R} p ≤ R^R` and
the product are cheap now. *Size:* small.

**G17. The isogeny to `J₁(N)`** (E1). *Statement:* there are an abelian variety `Z/L'` and an
`L'`-isogeny `A × Z → J₁(N)_{L'}`; `g = dim J₁(N) ≥ 2`. *Inputs:* G6 (absolute simplicity),
G13; L21 (Hom theorem over `L'`, with invariants commuting with coefficient extension), L11c.
*Origin:* N5 L861-867 (rv-h-novel step 9). *Size:* small-medium.

**G18. The transfer arithmetic** (E2-E4). *Statement:* `h_F(A) ≤ Q¹⁷M²⁴`. *Inputs:* G16, G17;
L31 (with `g, deg_B ≤ [SL₂(ℤ):Γ₁(N)] ≤ N²`), L32, L33, L34. *Origin:* N5 L868-905. *Lean:* the
real-number arithmetic is proved (`transfer_numerics`, `scratch/wk-h/Arakelov.lean`, wk-h §4.2,
compiled by wk-h); what remains is the bookkeeping over the Faltings height. *Size:* small once
`h_F` exists.

**G19. The theta step** (F1-F3). *Statement:* `h(J(u)) ≤ 40·h([z_m]) + 22` and
`h([z_m]) ≤ 10⁴·2²⁴·max(1, h_F(A))`, so with G18, `JHeightBound Mult.S_mul`. *Inputs:* G18; L3,
L4, L35; Weil height of a degree-40 map (Mathlib `NumberTheory/Height/MvPolynomial`), invariance
of the absolute height under field extension, the normalization `X_D ≤ 3X` and
`log(X_D + 2) ≤ 2X_D`; script `igusa_check.py`. *Origin:* N5 L908-947 (Astra "height"). *Lean:*
the height-of-polynomial-map step is medium now; the rest over L35. *Size:* medium.

**G20. Return to `u`** (F4). *Statement:* `JHeightBound Mult.S_mul → SixContactMin`. *Origin:* N5
L949-964. *Lean:* **proved**, `ZInQ.JHeight.sixContactMin_of_jHeightBound`
(`ZInQKernel/Hypotheses/JHeight.lean`), axioms `propext`, `Classical.choice`, `Quot.sound` (wk-h
§4.1). `Leaves.lean` uses it to prove G0 from `jHeightBound_of_leaves`.

## 5. Definitions

Status: **Mathlib** (in Mathlib v4.35.0, VERIFIED by grep or compilation), **Leaves.lean** (built
in the draft, compiled), **other library** (prereq-survey), **missing**. Cost tiers as in §4.

| Definition | Needed by | Status | Cost |
| --- | --- | --- | --- |
| `ℚ̄`, `G_ℚ` with the Krull topology | everything Galois | Mathlib (`AlgebraicClosure`, `AlgEquiv` Krull topology) | — |
| places of `ℚ̄` above `p`, decomposition and inertia groups | L18, L25-L28, G11 | Leaves.lean (`LiesOver` over Mathlib's `ValuationSubring.decompositionSubgroup`/`inertiaSubgroup`) | cheap |
| arithmetic Frobenius, Frobenius traces | L18, L25-L29 | Leaves.lean (`IsArithFrob`, `FrobTrace`) | cheap |
| complex conjugations, odd representations | L25, G10 | Leaves.lean (`IsComplexConj`, `IsOdd`) | cheap |
| `ℚ̄_ℓ` with its norm; continuous `GL_n(ℚ̄_ℓ)`-representations of `G_ℚ` | L25-L29 | Mathlib `PadicAlgCl ℓ`; Leaves.lean (`GaloisRep`; norm-continuity equals the usual notion by a Baire argument, SPECULATIVE as stated, standard) | cheap |
| irreducible, semisimple representations | L19, L25, L27 | Leaves.lean (`IsIrreducible` in Burnside form over the algebraically closed `ℚ̄_ℓ`; `IsSemisimple` by invariant complements) | cheap |
| cusp forms on `Γ₁(N)`, q-expansion coefficients | L27, L28 | Mathlib (`CuspForm`, `UpperHalfPlane.qExpansion`) | — |
| nebentypus, normalized eigenforms | L25-L30 | Leaves.lean (`HasNebentypus`, `IsNormalizedEigenform` via `a_m a_n = Σ_{d∣(m,n)} χ(d)d^{k−1}a_{mn/d²}`, equivalent to the Hecke definition by Diamond–Shurman Prop. 5.3.1, UNVERIFIED locator) | cheap |
| a representation attached to an eigenform (trace form) | L25-L28 | Leaves.lean (`AttachedTo`) | cheap |
| central simple algebras, base change, matrix algebras | L14, L15 | Mathlib | — |
| Hecke operators, old space, newforms | L28(b), L30 | missing in Mathlib; Tau Ceti has them | medium |
| Galois cohomology of `G_ℚ`, crossed products, local invariants | L15(b), G7 | Mathlib has continuous cohomology and `BrauerGroup` (definition); Tau Ceti has the local–global sequence | medium |
| local Artin map | L16, G7, G15 | Tau Ceti | medium |
| upper ramification groups, Herbrand function, Artin and Swan conductors of `ℓ`-adic representations | L20, L30, G15 | Tau Ceti (finite extensions, characters); `ℓ`-adic conductor missing | medium |
| regular schemes, purity, tame covers | L6, L7, G2 | Mathlib (schemes, étale morphisms); Axiom Stacks (0BMB, 0EYG) | medium |
| abelian varieties over a field | L8-L13, L21, G3-G17 | Mathlib has group schemes over a field and commutativity of proper geometrically integral ones; Tau Ceti has `AbelianVariety` | cheap |
| Tate modules `V_ℓ(A)` with `G_K`-action; Weil pairing; polarizations | L9-L11, L21, G8-G17 | missing (Anthropic FLT: Jacobians only) | medium |
| abelian schemes over a DVR (good reduction); Néron models | L8, L10, L11f, G3 | missing (Anthropic FLT: Néron models, special case) | medium (good reduction) / large (Néron models) |
| ℓ-adic étale cohomology of abelian varieties | L11e, L22 | missing (Stacks has étale cohomology foundations) | large |
| analytification, complex tori, rational Hodge structures | L12, L13, G5, G10 | Tau Ceti has Riemann forms; GAGA missing | large |
| `B_dR` with `G_K`-action and filtration; de Rham and Hodge–Tate representations; HT weights | L22, L23, L25, L26, G9, G12 | Mathlib has `BDeRhamPlus`, `BDeRham` (no action, no filtration) | large |
| `B_st`, potentially semistable representations | L24, L25 | missing | very large |
| Igusa invariants of genus-2 curves | L3 | missing; polynomials in the sextic | cheap |
| Siegel modular forms of degree 2, theta constants with characteristics | L4, L35, G19 | missing | large |
| QM abelian schemes, level structures, the moduli scheme `Y₃` and its canonical model; `X₆`, Atkin–Lehner action, CM points | L1-L5, G1-G6 | missing (Anthropic FLT: QM fake elliptic curves for Čerednik–Drinfeld; unchecked for `Y₃/ℚ`) | very large |
| modular curve `X₁(N)` over `ℚ`, `J₁(N)`, Belyi maps | L29, L31, G13, G17 | missing (Anthropic FLT has Jacobians of curves) | very large |
| Faltings height (Néron model or semistable model, metrized Hodge bundle), stable height | L31-L35, G18, G19 | missing | very large |
| Weil heights on `ℚ̄` and `P^n` | G19, G20 | Mathlib (`NumberTheory/Height`) | — |

## 6. Risks

- **R1. The count.** The owner's target of about ten literature theorems is not reachable
  faithfully: 21 research-level theorems from 18 sources, plus 19 textbook theorems. The eight
  packages P1-P8 are the honest unit of about ten. Merging leaves to hit ten would hide distinct
  theorems inside one statement (VERIFIED as a reading; SPECULATIVE as advice).
- **R2. Pan's conclusion is undefined in his introduction** (h-a011 §1.1, VERIFIED there). A Lean
  statement must fix a reading. The trace reading of L25 is implied by every reading in the
  literature, so it is a consequence of the published theorem; a reading that fixes the level,
  the minimal twist or the weight would be stronger than printed and must be avoided. The same
  care applies to L26 (normalization: Tate module versus cohomological, rv-h-c8 R1).
- **R3. Consequence forms need Chebotarev and Brauer–Nesbitt to derive.** L18, L25 (trace
  reading), L27, L28(a), L29 and L30 are stated through Frobenius traces. Each is implied by the
  published statement together with L18 and L19, which are themselves leaves; that derivation is
  part of the work of whoever proves the leaf from the literature, and should be recorded with
  it.
- **R4. L1 is assembled.** The moduli interpretation of `Y₃` over `ℚ`, its canonical model and
  Shimura reciprocity come from several statements of Shimura 1967 and Deligne 1971 (h-b1 §4A
  writes out four inputs). A single Lean statement of L1 would bundle them; it must be checked
  piece by piece against those sources. The Lean statement is far off (very large definitions).
- **R5. The new arguments have only model reviews.** G7, G9, G12, G14, G15 (Glazer) and G2, G3, G6
  (repository) have never had a human referee (h-trust §2.1). Formalizing them may find gaps; the
  leaves would not change, but the glue might need other leaves.
- **R6. Definitions in `Leaves.lean`.** The cheap definitions are mine and unreviewed. Specific
  checks: `IsNormalizedEigenform` must match the Hecke definition (the recursion with `χ(d) = 0`
  for `(d, N) > 1`, and `HasNebentypus` uses the lower-right entry `d`); `GaloisRep.IsIrreducible`
  is absolute irreducibility only because `ℚ̄_ℓ` is algebraically closed (Burnside);
  `GaloisRep.FrobTrace` quantifies over all places and all Frobenius lifts, which is right only at
  unramified primes, where `AttachedTo` uses it. A wrong definition could make a leaf vacuous or
  false; each needs a sanity lemma (§7).
- **R7. Placeholders.** 35 statements appear in `Leaves.lean` as `def L… : Prop := sorry`. As Lean
  terms they are `sorryAx Prop`, so `sixContactMin_of_leaves` says nothing until they are
  written. They are there to fix names and docstrings, not as hypotheses anyone should accept.
- **R8. Faithfulness alternatives that would change the count** (SPECULATIVE). rv-h-c3 §3.2:
  potentially semistable at 5 directly from L8 and Tsuji's `C_st`, which removes L22-L24 and G9
  for one comparison theorem; Raynaud (L9) may make L8 unnecessary in G3; an isogeny between
  conjugates (h-trust A7 remark) removes L3 from G4. None is N5's route; adopting one is a
  decision for the owner.
- **R9. Locators.** Almost every theorem number is UNVERIFIED in the published version (h-trust
  §2.5); a few are ASTRA-READ or AUDIT-READ (a model's reading). Before the announcement, the
  numbers of L25 (JAMS), L2 and L3 (journal versions) and L30 (`F = ℚ`, `p | N`) are the ones most
  worth checking.

## 7. First steps for a Lean team

1. **Adopt the cheap layer** (`Leaves.lean` §0): prove sanity lemmas for each definition (Frobenius
   traces independent of the place and the lift at unramified primes; `IsNormalizedEigenform`
   equivalent to being an eigenvector of Hecke operators once those exist; `UnramifiedAt` via one
   place iff all places). Small.
2. **Prove the textbook leaves that other libraries have**: L14, L15(a), L17, L18 from Tau Ceti
   (Skolem–Noether, the Brauer local–global sequence, Kronecker–Weber, Chebotarev), and L19
   (Brauer–Nesbitt, self-contained, medium). These close five of the eight statable leaves.
3. **Build abelian varieties with Tate modules** (medium) on Mathlib's group schemes or Tau
   Ceti's `AbelianVariety`, then state L9, L10, L11a-d, L21 concretely. This is the definition with
   the best ratio of leaves unlocked to cost.
4. **Conductors of `ℓ`-adic representations** (medium, on Tau Ceti's ramification groups), then
   state L30 and **formalize G15**, Glazer's uniform conductor bound, whose statement is local
   Galois theory. With G7 (scalar descent, on Tau Ceti's Brauer group), it is the new mathematics
   most worth machine-checking early.
5. **Hodge–Tate and de Rham representations** (large, on Mathlib's `BDeRham`), then state L22,
   L23, L26 and the statable core of L25.
6. **Long term (very large):** the Faltings height (P8), `X₁(N)` and `J₁(N)` over `ℚ` (L29, L31),
   and the QM moduli scheme `Y₃` (P1). Until those exist, G18-G19 can be developed against the
   wk-h numerics (`transfer_numerics`) and G1, G2, G6 against their polynomial identities, which
   are provable now.
