# wk-h: a plan for reducing H to well-known theorems

Status: research note (task wk-h, 2026-11-11). The goal of the wave is to replace each hypothesis
by Lean Props that are faithful statements of well-known published theorems, and to prove the
current hypothesis from them in Lean. This note does that planning for H = `ZInQ.SixContactMin`.
It classifies the 36 steps of `docs/research/h-trust.md` §1, groups the well-known inputs into
interface statements, checks what Mathlib v4.35.0 can state, and drafts the statable parts in
`scratch/wk-h/` (log: `scratch/wk-h/log.md`). No file under `ZInQKernel/`, `blueprint/` or other
notes was edited.

Marks: **VERIFIED** means checked against a source quoted in the repository, by exact computation,
or by Lean. **STANDARD** means a published theorem with a reference (locators as in h-trust, where
most are UNVERIFIED or ASTRA-READ). **SPECULATIVE** means an assessment or a proposal.

## Summary

1. **The proof factors through one quantity (VERIFIED, N5 L858-964).** Parts A-D produce, for
   `u ∉ 𝒞`, a number field `L'` with `[L':ℚ] ≤ QM`, the QM surface `A/L'` over `j = J(u)`, and an
   `L'`-isogeny `J₁(N) → A × Z` with `N ≤ QM²`. Part E turns this into `h_F(A) ≤ Q¹⁷M²⁴`, and
   Part F turns that into `h(u) ≤ 10¹³ max(1, h_F(A))`. So H splits into a **modularity half**
   (A-D and E1: geometry, scalar descent, Pan, conductor) and an **Arakelov half** (E2-E4,
   F1-F4: Javanpeykar, Gaudron–Rémond, Faltings, Bost, Pazuki, Lin–Yang/Igusa).
2. **Classification (§1).** Of the 36 steps: 15 are applications of well-known theorems, 8 are
   Glazer's new argument, 3 are repository replacements (Lemma PR, NoCM), and 10 are bookkeeping
   or computation. All the new arguments are in the modularity half, apart from E's arithmetic,
   which is bookkeeping. The well-known inputs form **six interface packages** (§2): I1 Shimura
   curve, I2 reduction theory, I3 Faltings, I4 modularity (Pan, eigenform p-adic Hodge theory,
   newforms, Carayol), I5 Arakelov (Javanpeykar, GR14, Faltings Lemma 5, Bost, Pazuki), and I6
   arithmetic of `ℚ` (Skolem–Noether, Brauer group, local fields).
3. **Statability (§3, VERIFIED by grep of Mathlib).** None of I1-I5 can be stated faithfully
   with concrete Mathlib objects today. Mathlib has Weil heights on number fields and projective
   space, congruence subgroups and cusp forms with q-expansions, group schemes over a field,
   absolute Galois groups, continuous cohomology, Brauer groups of CSAs and `B_dR`. It has no
   ℓ-adic Tate modules, Galois representations attached to abelian varieties or modular forms,
   de Rham or Hodge–Tate representations, Néron models, Faltings height, Hecke operators or
   newforms, Artin conductors or upper ramification groups, Shimura curves, Skolem–Noether or
   Chebotarev. I6 is partly statable (Hasse principle for quaternion algebras over `ℚ`), but it is
   used only inside the scalar descent, which cannot be stated without Galois representations.
   No "elementary consequence" form (as Proposition 0 did for CR3) exists for the deep
   inputs: the theorems are about Faltings heights and Galois representations, and their content
   is not expressible in rationals (§3.3).
4. **Drafts (§4; all compile with `lake env lean`, VERIFIED).**
   - **Tier 1, complete**, `scratch/wk-h/BackToU.lean` (no `sorry`). It has the residual
     `JHeightBound` (the `j`-form of H: `h(J(u)) ≤ (40·10⁴·2²⁴+22)·max(1,C_cm,Q¹⁷)·M²⁴`) and the
     theorem `sixContactMin_of_jHeightBound`, whose axioms are `propext`, `Classical.choice` and
     `Quot.sound` (`#print axioms`). It includes F4 in the form `12h(u) ≤ h(J(u)) + 450`, which is
     stronger than N5's `h(u) < h(j) + 74` for large `h(u)`, proved from two Nullstellensatz
     certificates.
   - **Tier 2**, `scratch/wk-h/Arakelov.lean`: a signature `ArakelovSig` with one Prop field per
     published theorem of the Arakelov half, the residual `ModularLevelBound`, and the reduction
     `jHeightBound_of_sig` (`sorry`, with an outline). Glazer's transfer arithmetic (E3-E4,
     N5 L868-905) is **proved** as `transfer_numerics`.
5. **Verdict (§6).** **A faithful reduction of H to well-known theorems is not within reach.**
   Two families of objects block it: ℓ-adic Galois representations of abelian varieties and
   modular forms, with their p-adic Hodge theory and conductors (for I3 and I4, and needed even to
   *state* Glazer's descent and conductor bound), and the Faltings height (for all of I5).
   Recommended partial reduction, in tiers:
   - **cheap win:** Tier 1, now complete in scratch (F4 proved). Adopting it removes F4 and the
     final numerics from the trust base. It does not change what kind of statement is assumed (`JHeightBound` is still a
     project statement).
   - **medium:** Tier 2. It machine-checks Glazer's E and F bookkeeping and makes each Arakelov
     theorem a separately readable field. Its weakness is decisive for this wave's goal: over
     abstract types the Lean kernel cannot enforce the intended interpretation. The packaged
     hypothesis `∃ W, W.Literature ∧ W.ModularLevelBound` implies `JHeightBound`, and it follows
     from a sharper bound of the same kind, `h(J(u)) ≤ c·Q¹²M²⁴`, through a model with no abelian
     varieties in it (§4.3; SPECULATIVE, argument sketched). As a Lean Prop it therefore says no
     more than a height bound for `J(u)`, and its faithfulness rests on reading, as it does
     today.
   - **bigger investment (years, SPECULATIVE):** concrete definitions of abelian varieties over
     number fields with Tate modules, Galois representations of newforms, p-adic Hodge theory
     and the Faltings height. Only this tier gives a genuine reduction.

   What remains assumed after the cheap and medium tiers: `ModularLevelBound` (Glazer's new
   argument with Pan, Carayol, Faltings and the Shimura-curve geometry: h-trust A1-E1), plus the
   six Arakelov-half theorem fields, read through the signature.

## 1. Classification of the 36 steps

Classes:

- **W**: an application of a well-known published theorem (refereed, standard). The exact
  statement used is given.
- **G**: Glazer's new argument (N5 text).
- **R**: a repository replacement of N5 text (model-reviewed).
- **B**: bookkeeping or exact computation.

A step with a W input whose own argument is new is classed G or B, and its W inputs are listed.
The supplier locators are h-trust's and are not repeated.

| Step | Class | Statement used from the literature, or the nature of the argument | Interface |
| --- | --- | --- | --- |
| A1 | B | quaternion datum and Riemann form (script `form_check.py`); LY 2020 eq. (3) is a convention | — |
| A2 | W | Baba–Granath 2008 Thm 2.1, §3; LY 2020 Ex. 30: `X₆/W ≅ P¹_j`, elliptic points `j = 0, ∞, −16/27` of orders 4, 6, 2 at CM discriminants −4, −3, −24 | I1 |
| A3 | B | the degree `≤ 324`; inputs Vignéras LNM 800 Ch. II (local normalizers), Deligne 1979 §2.7 (Hecke action over `ℚ`) | I1 |
| A4 | W | Shimura 1967, Deligne 1971, Kottwitz 1992: the canonical model of the level-3 curve is the fine moduli scheme of `(A, ι, λ, η)`; Mumford §21 (neatness) | I1 |
| A5 | R | Lemma PR(i) (h-b1): `K` unramified outside `T`; inputs SGA 1 X 3.1 (purity), XIII 5.3 (Abhyankar), Shimura reciprocity | I1, I2 |
| A6 | R | Lemma PR(ii): good reduction away from 3; inputs SGA 7 IX 3.6 (semistable reduction), Serre–Tate 1968 Thms 1-2 (NOS) | I2 |
| A7 | B | conjugates geometrically isomorphic; inputs BG 2008 Thm 2.1, LY Igusa vector (`igusa_check.py`) | I1 |
| A8 | B | Hom field bound; inputs Mumford §19 Thm 3 (`rank Hom ≤ 4 dim A dim A'`), Minkowski, NOS | I2 |
| A9 | W | `End⁰(A_ℚ̄) ∈ {B, M₂(k)}`: Mumford §§1-3 with GAGA, rigidity (Conrad 2006 §3); centralizer by computation | I3 |
| A10 | R | NoCM (h-cm): González–Rotger 2006 Thm 5.12, Prop. 5.6; Vignéras | I1 |
| B1 | G | sign cocycle `ε`; input Skolem–Noether (Reiner Thm 7.21) | I6 |
| B2 | G | the Brauer step; inputs `H²(G_ℚ, ±1) = Br(ℚ)[2]`, Albert–Brauer–Hasse–Noether, reciprocity (Milne ADT Ch. I) | I6 |
| B3 | G | the cochain `β`, `[L':ℚ] ≤ QM` (constants `c1_constants.py`) | — |
| C1 | G | `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ` on `G_{L'}` | — |
| C2 | W | Faltings 1983 Satz 3 (semisimplicity), Satz 4, Kor. 1 (Tate conjecture): `End(A) ⊗ ℚ_ℓ = End_{G_K}(V_ℓA)` | I3 |
| C3 | W | Scholze 2013 Cor. 1.8 (or Faltings 1989 / Tsuji 1999): `V_ℓ(A)` is de Rham with HT weights `{0, −1}`; Fontaine (closure under subquotients) | I4 |
| C4 | W | Berger 2002 Thm 0.7 (published numbering): de Rham ⇒ potentially semistable | I4 |
| C5 | B | oddness via the Betti–étale comparison (SGA 4 XI) | I4 |
| C6 | B | `r_ℓ` unramified outside `T ∪ {ℓ}` (NOS) | I2 |
| C7 | W | Pan 2022 Thm 1.0.4: an irreducible, odd, finitely ramified, de Rham `ρ: G_ℚ → GL₂(\bar ℚ₅)` with distinct HT weights comes from a cuspidal eigenform up to twist | I4 |
| C8 | B | twist and weight; inputs Saito 1997 / Scholl 1990 (eigenform reps are HT with weights `{0, 1−k}`), Deligne–Serre 1974 (`k = 1`), Tate/Serre 1968 III (HT characters) | I4 |
| C9 | W | Shimura 1973 Thm 1 (`A_f`), Li 1975 Thm 5 (newforms), Eichler–Shimura (Shimura 1971 Thm 7.9): `r₅` is a constituent of `V₅(A_f)` | I4 |
| C10 | B | one compatible system at 3 and 5; inputs BLR §1.2 (Néron property), Mumford §19 Thm 4, Chebotarev, Brauer–Nesbitt | I2, I6 |
| D1 | G | break bound `u_last ≤ 2δ/e ≤ 4a²`; inputs Serre, *Corps locaux* III §6, IV §§1-3 (`c3_breaks.py`) | I6 |
| D2 | G | semistability and wild inertia at odd `p`; inputs Raynaud's criterion (SGA 7 IX 4.7), SGA 7 IX §3 | I2 |
| D3 | G | the `p = 2` paragraph; inputs Silverman AEC IV.6.4, Serre IV §1 Prop. 2 | I6 |
| D4 | G | conductor exponents `a_p ≤ E₀`, `≤ 2`, `0`; input the Artin–Swan conductor (Serre VI §2) | I6 |
| D5 | W | Carayol 1986 Thm A: for a newform `f` of level `N`, `v_p(N)` = the conductor exponent of `ρ_{f,λ}` at `p ≠ ℓ` | I4 |
| E1 | W | Faltings 1983 Kor. 1 (Hom theorem) and Poincaré reducibility: an `L'`-isogeny `A × Z → J₁(N)` | I3 |
| E2 | W | Javanpeykar 2014 Thm 1.1.1: `h_F(Jac X) ≤ 13·10⁶ g deg_B(X)⁵`, at `X₁(N)` (`g, deg_B ≤ N²`) | I5 |
| E3 | W | Gaudron–Rémond 2014 Thm 1.4: isogenous `A, B/K` have an isogeny `A → B` of degree `≤ κ(A) = ((14g)^{64g²}[K:ℚ] max(h_F(A), log[K:ℚ], 1)²)^{1024g³}`; arithmetic B | I5 |
| E4 | W | Faltings 1983 Lemma 5: `|h_F(A) − h_F(B)| ≤ ½ log deg φ`; additivity; Bost: `h_F ≥ −(3/2) dim` (GR14 §9); arithmetic B | I5 |
| F1 | W | LY 2020 eqs. (2), (13), (14); LNY 2015 §2.2; Igusa 1967: `j = 3779136 (∏ z_m)⁴/(∑ z_m⁸)⁵` on the QM locus (`igusa_check.py`) | I1 |
| F2 | B | `h(Φ(z)) ≤ 40 h(z) + 22` (Weil height of a degree-40 map) | — |
| F3 | W | Pazuki 2012 Cor. 1.3(2), `g = r = 2`: `h_Θ(A) ≤ ½X_D + C₂ log(X_D + 2)`; normalization B | I5 |
| F4 | B | `h(u) < h(J(u)) + 74` (rational-root theorem) and the final constant | — |

Counts (VERIFIED from the table): W 15 (A2, A4, A9, C2, C3, C4, C7, C9, D5, E1, E2, E3, E4,
F1, F3), G 8 (B1-B3, C1, D1-D4), R 3 (A5, A6, A10), B 10 (A1, A3, A7, A8, C5, C6, C8, C10, F2,
F4). E3 and E4 also carry Glazer's arithmetic, and C8 and C10 carry new assembly; the counts
depend on how such mixed steps are split, and the grouping in §2 does not.

**Glazer's new arguments** are the scalar descent (B1-B3, C1), the uniform conductor bound
(D1-D4) and the assembly of the twist (C8) and of the compatible system (C10). They all live in
the modularity half. Their *statements* are about Galois representations (cocycles valued in
`ℚ^×` on `G_ℚ`, ramification breaks of `L'/ℚ`, conductor exponents of `r_ℓ`), and so cannot be
isolated as elementary lemmas. The exceptions are the numerics: B3's constants, D1's
inequality `δ ≤ e − 1 + e v_p(e) ⇒ u_last ≤ 4a²`, D4-D5's product `N ≤ QM²`, and E's arithmetic.

## 2. Interface statements

The smallest grouping from which the rest follows by Glazer's arguments and bookkeeping. Each is
a conjunction of published theorems; "statement" means the form N5 uses.

- **I1, the discriminant-6 Shimura curve** (A2-A5, A7, A10, F1). (a) The canonical model of the
  level-3 curve is the fine moduli scheme of principally polarized QM surfaces with level-3
  structure (Shimura 1967; Deligne 1971; Kottwitz 1992). (b) `X₆/W ≅ P¹_j` with N5's branch data
  (BG 2008; LY 2020). (c) Igusa invariants on the QM locus, `[J₂ : J₄ : J₆ : J₁₀] =
  [12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]`, and the theta form of F1 (LY 2020; LNY 2015; Igusa
  1967). (d) CM points (González–Rotger 2006).
- **I2, reduction theory** (A5, A6, A8, C6, C10, D2). Zariski–Nagata purity and Abhyankar (SGA 1);
  semistable reduction and Raynaud's criterion (SGA 7 IX); Néron–Ogg–Shafarevich (Serre–Tate
  1968); the Néron mapping property (BLR).
- **I3, Faltings 1983** (A9, C2, E1, C10). Semisimplicity of `V_ℓ(A)`, and
  `Hom(A, B) ⊗ ℚ_ℓ ≅ Hom_{G_K}(V_ℓA, V_ℓB)`.
- **I4, modularity** (C3-C5, C7-C9, D5). Pan 2022 Thm 1.0.4; the de Rham comparison and Berger
  (the hypotheses of Pan for `V_ℓ(A)`); eigenform Galois representations with their Hodge–Tate
  weights at every level (Saito 1997) and Deligne–Serre; newform theory and `A_f` (Li 1975;
  Shimura 1971, 1973); Carayol 1986 Thm A.
- **I5, Arakelov** (E2-E4, F3). Javanpeykar 2014 Thm 1.1.1; Gaudron–Rémond 2014 Thm 1.4;
  Faltings 1983 Lemma 5 with additivity; Bost's lower bound; Pazuki 2012 Cor. 1.3(2).
- **I6, arithmetic of `ℚ` and local fields** (B1, B2, C10, D1, D3, D4). Skolem–Noether; the exact
  sequence `0 → Br ℚ → ⊕_v Br ℚ_v → ℚ/ℤ → 0` (2-torsion part); local class field theory and
  the ramification filtration (Serre, *Corps locaux*); Chebotarev; Brauer–Nesbitt.

**A coarser alternative for I4 (SPECULATIVE).** The QM surface `A` with its `B`-linear isogenies
`μ_σ` to its conjugates (B1) is a *building block* in the sense of Ribet and Pyle. By Ribet 2004
and Pyle 2004 together with Khare–Wintenberger 2009 (Serre's conjecture), every building block
is a `\bar ℚ`-factor of some `A_f`. That would replace Pan and the p-adic Hodge inputs C3-C5, C8
by one classical theorem. It would not give the level bound `N ≤ QM²`, which needs the conductor
of Ribet's `GL₂`-type variety over `ℚ`, i.e. an effective version of B2 and D. This is worth a
separate look as a *trust* simplification. It does not help statability, since it needs the same
objects.

## 3. Can the interfaces be stated faithfully in Lean today?

### 3.1 What Mathlib v4.35.0 has (VERIFIED by grep; log Step 2)

| Object | In Mathlib | Where |
| --- | --- | --- |
| Weil height on number fields, `Pⁿ(K)`, absolute height of algebraic numbers | yes | `NumberTheory/Height/{Basic,NumberField,Projectivization}` |
| height of images of homogeneous polynomial maps, upper and lower bounds | yes | `NumberTheory/Height/MvPolynomial` (`logHeight_eval_le`, `logHeight_eval_ge`) |
| Néron–Tate machinery for elliptic curves (naive height, parallelogram law) | partial | `NumberTheory/Height/EllipticCurve` |
| congruence subgroups `Γ₁(N)`, cusp forms, q-expansions, modular-form L-functions | yes | `NumberTheory/ModularForms/*` |
| Hecke operators on modular forms, newforms | no | (`HeckeRing/Defs` is abstract) |
| group schemes over a field; proper geometrically integral ones are commutative | yes | `AlgebraicGeometry/Group/Abelian` |
| ℓ-adic Tate modules, Galois action on torsion of abelian varieties | no | — |
| absolute Galois group, continuous group cohomology, Tate–Shafarevich subgroup | yes | `FieldTheory/AbsoluteGaloisGroup`, `RepresentationTheory/Homological/ContCohomology` |
| inertia groups (finite Galois extensions of Dedekind domains) | yes | `NumberTheory/RamificationInertia/Galois` |
| upper ramification groups, Herbrand function, Artin/Swan conductors | no | — |
| `B_dR` (from perfectoid rings) | yes | `RingTheory/Perfectoid/BDeRham` |
| de Rham, Hodge–Tate, potentially semistable representations | no | — |
| Brauer group (as CSA classes), quaternion algebras | yes | `Algebra/BrauerGroup/Defs`, `Algebra/Quaternion` |
| Skolem–Noether, Hilbert symbol, Chebotarev | no | — |
| Néron models, Faltings height, theta constants of abelian varieties | no | — |
| Shimura curves, canonical models, modular curves as schemes, `J₁(N)` | no | — |

### 3.2 Per interface

| Interface | Objects needed | Statable today? | Cost to make statable (SPECULATIVE) |
| --- | --- | --- | --- |
| I1 | Shimura curves over `ℚ`, moduli of QM surfaces, Igusa invariants of genus-2 curves | (c) yes for genus-2 *curves* (Igusa–Clebsch invariants are polynomials in the sextic's coefficients); (a), (b), (d) no | very large: canonical models |
| I2 | abelian varieties over number fields, Néron models, Tate modules, inertia in `G_K` | no | large |
| I3 | Tate modules with Galois action, `Hom` of abelian varieties | no | large (abelian varieties with torsion points: 5-10k lines) |
| I4 | Galois representations of `G_ℚ`, de Rham/HT/pst, eigenforms and their Galois representations, conductors | no (`B_dR` exists, but no `G_{ℚ_p}`-action API or admissibility) | very large: modular curves, Eichler–Shimura, p-adic Hodge theory |
| I5 | Faltings height (Néron model plus metrized invariant differentials), isogeny degrees, theta nulls | no | very large: Arakelov theory |
| I6 | quaternion algebras over `ℚ` and `ℚ_p`; Galois cohomology of `G_ℚ` | the Hasse principle for quaternion algebras over `ℚ` (equivalently Hasse–Minkowski for ternary forms) yes; local CFT and ramification filtrations no | medium for the statable part; but B2 uses it on a cocycle built from Galois representations |

### 3.3 Why there is no Proposition-0-style elementary form

For CR3, Proposition 0 turned Selmer groups into Legendre symbols: the deep theorem's
*conclusion* (positive rank) and its *hypothesis* (a Selmer condition) had elementary avatars.
For H the deep theorems are inequalities between Faltings heights (I5) and isomorphisms of Galois
representations (I3, I4). Their elementary shadows are not faithful:

- **The theta step is vacuous as a statement about rationals (VERIFIED as an argument).** "There
  is `z ∈ P⁹(\bar ℚ)` with `Φ(z) = J(u)` and `h(z) ≤ X`" carries no information beyond a bound on
  `h(J(u))`. For any `j ≠ 0`, `z = (1, …, 1, t)` with `3779136 t⁴ = j(9 + t⁸)⁵` has
  `h(z) ≤ h(j)/40 + O(1)`. So F1 and F3 cannot be stated as elementary facts without the abelian
  surface. The same holds for any "∃ an algebraic point with small height" reformulation of I5.
- **Point counts.** Faltings' isogeny theorem makes "Jac(C) is a factor of `J₁(N)` over `L'`" an
  equality of Frobenius traces, which are point counts of an explicit genus-2 curve (if the QM
  family is given by Baba–Granath's explicit curves; SPECULATIVE) against Hecke eigenvalues of
  newforms. That is an elementary statement only once newforms and Hecke eigenvalues are defined
  (absent), and its height consequence (I5) still needs the Faltings height.

### 3.4 Signatures (abstract types with theorem-shaped fields)

When objects are missing, one can state the theorems over a signature: abstract types and
functions, one Prop per theorem, interpreted by the real objects. This is what Tier 2 does for
I5. Its limits must be stated plainly:

- the Lean kernel checks the deductions from the fields, and nothing about whether the real
  objects satisfy them. Faithfulness is a reading of each field against its paper, exactly as for
  `SixContactMin` today;
- packaged as one hypothesis `∃ W, W.Literature ∧ W.ModularLevelBound S`, it implies
  `JHeightBound S`, and it is implied by a sharper `j`-height bound of the same shape through a
  fake model (§4.3). As a Lean Prop it is a height bound in disguise. The gain is attribution
  (which theorem is used where) and the machine-checked bookkeeping between them.

## 4. Lean drafts (`scratch/wk-h/`)

Both files import `ZInQKernel.Hypotheses.Height` only (Mathlib-only). The upstream package
`lean/` is not built in this worktree, so `Hypotheses/HeightMin.lean` (which needs
`Multiplication/Certificate/Constants`) cannot be imported. Therefore `SixContactMin` appears as
`SixContactMinAt S`, which is `SixContactMin` at `S = Mult.S_mul` by `rfl`. Checked with
`lake env lean <file>`, one file at a time (log Steps 4-5).

### 4.1 Tier 1: `BackToU.lean` (compiles; no `sorry`; standard axioms)

- `Jmap u = −57600 F(u)²/G(u)⁶`; `Fh`, `Gh` as binary forms over `ℤ`.
- `cert_x`, `cert_y`: `3a⁷ = A₁F_h + B₁G_h` and `2¹⁰3⁸5⁶ b⁷ = A₂F_h + B₂G_h` with integer
  forms (from `scratch/wk-h/f4_cert.py`, output saved; `Res(F, G) = 2¹⁸3¹³5¹⁰`). **Proved**
  (`ring`).
- `dvd_C0`: for coprime `a, b`, every common divisor of `57600F_h²` and `G_h⁶` divides
  `C₀ = 57600²·3⁷·(2¹⁰3⁸5⁶)⁷`. **Proved**: raise the certificates to the 7th power and split
  `57600(x + y)⁷ = 57600x²(…) + y⁶(…)`.
- `lower_bound`: `max(|a|,|b|)¹² ≤ 10⁴⁸·max(57600F_h², G_h⁶)`. **Proved** (triangle
  inequality on the certificates).
- `twelve_mul_ratHeight_le`: `12 h(u) ≤ h(J(u)) + 450`. **Proved**, using
  `Rat.exists_eq_mul_div_num_and_eq_mul_div_den` and `log(10¹³⁹) < 450`. The hypothesis
  `u ∉ 𝒞` is not needed. The whole file is 263 lines.
- `JHeightBound S`, the residual, and `sixContactMin_of_jHeightBound`. **Proved** (`nlinarith`
  from F4, `X ≥ 1`, `M ≥ 1`).

### 4.2 Tier 2: `Arakelov.lean` (compiles; one `sorry`)

- `ArakelovSig`: abelian varieties over bundled number fields, `dim`, `hF`, isogenies with
  degrees, products, `J₁(N)`, the QM Hauptmodul coordinate `jQM`, and theta nulls in `P⁹`.
- Fields:
  - `Javanpeykar`: `h_F(J₁(N)) ≤ 1.3·10⁷N¹²`, `dim J₁(N) ≤ N²` (Thm 1.1.1 with `g, deg_B ≤ N²`;
    the shape `13·10⁶ g deg_B⁵` is ASTRA-READ, `docs/reviews/height-replacement/height/AUDIT.md`
    item 3);
  - `GaudronRemond`: Thm 1.4 with `κ(A)` as in that AUDIT item 4;
  - `FaltingsVariation`: Lemma 5, additivity, dimension under isogeny;
  - `BostLower`: `h_F ≥ −(3/2) dim` (GR14 §9, ASTRA-READ);
  - `Pazuki`: Cor. 1.3(2) for `g = r = 2` in N5's normalization;
  - `IgusaLY`: `Φ(theta nulls) = j` on the QM locus.
- `ModularLevelBound S`: the residual (A1-E1).
- `transfer_numerics`: **proved**. Given `Q ≥ 10¹²`, `M ≥ 1`, `2 ≤ g ≤ Q³M⁴`, `1 ≤ d ≤ QM`,
  `h_F(J) ≤ Q¹³M²⁴`, the GR14 bound on `L = log deg φ`, `h_F(A) + h_F(Z) ≤ h_F(J) + L/2` and
  `h_F(Z) ≥ −2g`, it concludes `h_F(A) ≤ Q¹⁷M²⁴`. This is N5's E3-E4 arithmetic, about 130
  lines. The logarithm bounds are `4P`, `P`, `13P` with `P = QM⁴`, slightly sharper than N5's
  `5QM⁴`, `2QM⁴`, `19QM⁴`.
- `jHeightBound_of_sig`: **`sorry`**, with outline. It is the remaining assembly: about 300-500
  lines (SPECULATIVE). The new ingredients are F2 via `logHeight_eval_le` (coefficient `ℓ¹`
  bound for `Φ`'s numerator and denominator in `mulHeightBound`), and the invariance of the
  absolute height of a rational number under a finite extension. The second is not in Mathlib in
  the needed form, as far as the grep shows: `absLogHeight₁` is defined through `ℚ⟮x⟯`.

### 4.3 What the residual contains, and the size of the new arguments

`ModularLevelBound` is h-trust A1-E1. To reduce it further one must state Galois
representations. Sizes for Glazer's arguments **once the Tier-3 objects exist** (all
SPECULATIVE):

| Argument | Lean statement needs | Proof size |
| --- | --- | --- |
| B1-B3 scalar descent | `H²(G_ℚ, ±1)`, Brauer group of `ℚ` with local invariants, Dirichlet characters | 2-3k lines; the square-root criterion and constants: a few hundred, elementary |
| C1, C5, C6, C8, C10 | Tate modules, Frobenius, HT characters, compatible systems | 2-4k lines |
| D1-D4 conductor bound | upper numbering, Herbrand function, Artin–Swan conductor | 3-5k lines of theory; Glazer's own inequalities about 300 lines |
| D4-D5 product `N ≤ QM²` | factorization only | about 100 lines, possible today |
| A3, A7, A8 geometric bookkeeping | Shimura curves; A8 needs only finite subgroups of `GL_r(ℤ)` | A8's group theory about 300 lines, possible today |
| E, F arithmetic | heights (Mathlib) | E done (`transfer_numerics`); F4 done (`twelve_mul_ratHeight_le`); F2, F3 about 200 lines |

**What the Tier-2 hypothesis says as a Lean Prop (SPECULATIVE: argument sketched, not in
Lean).** (⇒) `jHeightBound_of_sig` gives `JHeightBound`. (⇐, partial) A model can be built from a
sharper bound alone. Suppose that for every `u ∉ 𝒞` there is `z ∈ P⁹(\bar ℚ)` with
`Φ(z) = J(u)` and `h(z) ≤ 6.5·10⁶ N_u¹²`, where `N_u = ⌊QM²⌋`. Since
`t ↦ [3779136 t⁴ : (9 + t⁸)⁵]` is a degree-40 morphism of `P¹`, `z = (1, …, 1, t)` gives
`h(z) ≤ h(J(u))/40 + O(1)`, so `h(J(u)) ≤ 2.6·10⁸·Q¹²M²⁴ − O(1)` suffices. The model:

- `AV K` is the set of triples (dimension, height, `j`-value) in `ℕ × ℝ≥0 × Option K` whose
  height is large enough for Pazuki's field to hold with the chosen theta point of the `j`-value.
  `prod` adds the first two coordinates and keeps the third, which preserves this condition;
- `J1 N K := (N², 1.3·10⁷N¹², none)`;
- `Isog A B` is inhabited exactly when the dimensions agree and `2|hF A − hF B| + 1` is at most
  GR14's bound for `A`, with `deg := ⌈exp(2|hF A − hF B|)⌉`;
- the residual's witnesses: `A := (2, 1.3·10⁷N¹², some J(u))`, `Z := (N² − 2, 0, none)`, `K := ℚ`;
- the theta nulls of `A` are `z`.

Then every field holds, and the isogeny `J₁(N) → A × Z` has height difference 0. So the kernel
cannot tell the intended model from this one. The hypothesis is, as a Lean Prop, a height bound
for `J(u)` of the same shape as `JHeightBound` (exponent 12 in `Q` instead of 17). Its value is
attribution and checked bookkeeping, not a reduction of trust.

## 5. The obstacle, and the cheapest partial reduction

**What blocks a faithful reduction.**

1. **ℓ-adic Galois representations of abelian varieties and modular forms** (I2, I3, I4): Tate
   modules, Frobenius and inertia in `G_K`, de Rham/Hodge–Tate/pst conditions, conductors,
   eigenform representations. Without them neither Pan nor Carayol nor Faltings' Hom theorem can
   be stated, and *Glazer's own new argument cannot be stated either* (its objects are `r_ℓ`, a
   cocycle on `G_ℚ` and conductor exponents). This is the most serious obstacle: it is what keeps
   the novel part, the part the owner most wants isolated, outside Lean.
2. **The Faltings height** (I5): every published theorem of the Arakelov half is an inequality in
   `h_F`. Defining it needs Néron models and metrized invariant differentials.
3. **Shimura curves** (I1): the canonical model and moduli interpretation.

**Cheapest partial reduction.** Tier 1 (F4 proved; `JHeightBound` becomes the hypothesis), then
Tier 2's checked bookkeeping as a second layer of documentation. Additionally, the numerics of
Glazer's new arguments can be checked today as standalone lemmas whose hypotheses are the numeric
outputs of the deep theorems: D4-D5's product, B3's constants and D1's inequality. They do not
change the hypothesis, but they move model-reviewed arithmetic into Lean.

## 6. Verdict

**Recommended reduction:**

```
SixContactMin  ⇐(Lean, Tier 1)  JHeightBound
JHeightBound   ⇐(Lean, Tier 2)  ∃ W : ArakelovSig, W.Literature ∧ W.ModularLevelBound S_mul
```

`W.Literature` is Javanpeykar, GR14, Faltings Lemma 5 with additivity, Bost, Pazuki and
Lin–Yang/Igusa (six fields).

| Tier | Work | Lean cost (SPECULATIVE) | Effect on what is assumed |
| --- | --- | --- | --- |
| cheap win (**done in scratch**) | `JHeightBound` with `sixContactMin_of_jHeightBound`, F4 proved; to adopt, move it under `ZInQKernel/Hypotheses/` | 263 lines, written | F4 and the final numerics leave the trust base; the hypothesis is still a project statement |
| cheap win | D4-D5 product, B3 constants, D1 inequality as standalone lemmas | 300-500 lines | Glazer's arithmetic is checked; the hypothesis is unchanged |
| medium | finish `jHeightBound_of_sig` (F2 via Mathlib, height invariance under extension, assembly) | 300-500 lines, 1-2 weeks | the Arakelov half becomes six readable theorem fields plus checked bookkeeping; as a Lean Prop the hypothesis is still a `j`-height bound in disguise (§4.3) |
| bigger | concrete abelian varieties over number fields with Tate modules; Galois representations of newforms; p-adic Hodge conditions; Faltings height; Shimura curves | tens of thousands of lines, years | only this makes the interface statements faithful and lets Glazer's descent and conductor bound be stated and proved |

**What would remain assumed** after the cheap and medium tiers:
`ModularLevelBound S_mul`, i.e. Glazer's new argument (scalar descent, conductor bound) together
with Pan, Carayol, Faltings, eigenform p-adic Hodge theory, reduction theory and the
Shimura-curve geometry (h-trust A1-E1), and the six Arakelov-half theorem fields, read through
the signature. Compared with today, F4, E's arithmetic and F's arithmetic would be machine-checked.
The modularity half, which holds every new argument, would be unchanged.

**Single next step:** a task allowed to edit `ZInQKernel/` adopts Tier 1. It moves
`scratch/wk-h/BackToU.lean` to `ZInQKernel/Hypotheses/`, imports `HeightMin` so that
`SixContactMinAt Mult.S_mul` is `SixContactMin`, and makes the main theorems take
`JHeightBound Mult.S_mul`, with H's docstring and trust statement moved to it. Then it runs a
full build and `print_axioms`. That task should first ask the owner whether the `j`-form, a
statement about the Hauptmodul value rather than about `u`, is the preferred hypothesis.

## Note (2026-11-11, after rv-lit)

- §1: A9, C3 and C9 each contain a passage that is new in N5, so about 12 of the 36 steps are
  applications of well-known theorems, not 15 (rv-lit N3). The verdict is unchanged.
