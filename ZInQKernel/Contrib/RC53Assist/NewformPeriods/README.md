# `NewformPeriodsRational`: initial conditional package


## Update (2026-11-18)

G1 `ParametrizationPeriodsGlue` is now proved outright, with no hypotheses and no printed input: `ZInQ.Contrib.RC53Assist.NewformPeriodsG1.parametrizationPeriodsGlue_holds` in `NewformPeriodsG1/ParametrizationPeriods.lean`. The reduction without G1 as a hypothesis is `newformPeriodsRational_of_prints_G0_G2`. The proof uses only Mathlib facts about the Weierstrass function (it takes every value off the lattice; a local period is a lattice vector), a local inverse, the identity theorem on the upper half-plane, q-expansion calculus proved there, and j built from the Eisenstein series E4 and E6. G2 `IsogenyLatticeGlue` is proved as well (`ZInQ.Contrib.RC53Assist.NewformGlues.isogenyLatticeGlue_proved` in `NewformGlues/G1G2.lean`), and `newformPeriodsRational_of_prints_G0` there needs only the two printed leaves and G0. The statements below that list G1 or G2 as unproved glue are superseded by this note.

This directory reduces the period statement `NewformPeriodsRational`
(`ZInQ.Contrib.CloudB3RC53.ModularWeil.NewformPeriodsRational`, module
`ZInQKernel.Contrib.CloudB3RC53.ModularWeil.WeakWeil`) to two printed leaves and three named
translation steps. The target is not changed and is not relabelled as a print.

## Main theorem (PROVED, standard axioms only)

```lean
theorem newformPeriodsRational_of_prints
    (hS : Shimura1973Thm1RationalGamma0) (hF : Faltings1983Kor2EllipticQ)
    (h0 : NewformOfModularCurveGlue) (h1 : ParametrizationPeriodsGlue)
    (h2 : IsogenyLatticeGlue) : NewformPeriodsRational
```

and its corollary `modularToWeakWeil_of_prints : … → ModularToWeakWeil` (through the proved
assembly `modularToWeakWeil_of_newformPeriodsRational`). Namespace
`ZInQ.Contrib.RC53Assist.NewformPeriods`. `#print axioms` gives `[propext, Classical.choice,
Quot.sound]` for every theorem in these files.

## Files

| File | Content | Status |
|---|---|---|
| `Transport.lean` | weight-two period law, uniform finite-index exponent, `q`-expansion identity across levels, level `0`, `SomeLevelPeriodsRational → NewformPeriodsRational` | PROVED |
| `RationalParametrization.lean` | `E₄`, `E₆`, `j` over `ℚ`, `ℚ(j, j_M) ⊆ ℚ((q))`, `θ = q d/dq`, modular points, pull-back identity; rationality and nonvanishing of the pull-back scalar; `j` nonconstant | definitions, PROVED |
| `Leaves.lean` | the two printed leaves, with locators and quotes as read | PRINT (special cases, consequence form) |
| `Glue.lean` | the three named translation steps | GLUE (not proved) |
| `Reduction.lean` | the main theorem | PROVED |

Dependency order for single-file checking: `RationalParametrization`, `Transport`, `Leaves`,
`Glue`, `Reduction`.

## Printed leaves

Both sources are in the manuscript's bibliography; readings are page-image readings (not
human-certified).

1. **`Shimura1973Thm1RationalGamma0`** — G. Shimura, *On the factors of the jacobian variety of a
   modular function field*, J. Math. Soc. Japan 25 (1973), 523–544, **Theorem 1, p. 526**
   (definitions of `μ`, `T_n` on p. 525); bibitem `shimura-factors`, cited at tex L770–771. Kept:
   `Γ = Γ₀(M)`, `K = ℚ`; for a normalized full Hecke eigenform `g` with rational coefficients `b`,
   an elliptic curve `A/ℚ` and a nonconstant point `(x, y)` of `A` over `ℚ(j, j_M)` (the composite
   of the canonical map with `ν`, clauses (i), (iii)) such that `θx = c · ĝ · (2y + a₁x + a₃)` for
   some `c ∈ ℂ` (clause (iv)), and `A.LFunction p = b p` off a finite set of primes (the
   Euler-factor clause for `Γ = Γ₀(M)`). Dropped: clause (ii), `θ`, uniqueness.
2. **`Faltings1983Kor2EllipticQ`** — G. Faltings, *Endlichkeitssätze für abelsche Varietäten über
   Zahlkörpern*, Invent. Math. 73 (1983), 349–366, **§5, Korollar 2, p. 361**, implication
   iii) ⇒ i); bibitem `faltings1983` (with the erratum, Invent. Math. 75 (1984), 381, which only
   replaces Satz 2 and does not affect Korollar 2), cited at tex L621 and L732–733. Kept: `K = ℚ`,
   `A₁, A₂` elliptic curves; equal `L`-coefficients at almost all primes imply an isogeny
   `E₁ → E₂` over `ℚ` (`TauCeti.Isogeny`).

Existing rows considered: `PkgI3.FaltingsTate` (Satz 4 / Korollar 1, `Hom` form) is the related
existing interface; deriving an isogeny from it would add Satz 3, Čebotarev and a Tate-module
dictionary for Weierstrass curves, so Korollar 2 is stated. The Shimura rows `R16Thm1b.ShimuraThm1Af`
and `R16Thm1.ShimuraThm1Printed` of later editions (Theorem 1 at `Γ = Γ₁(N)`) are not in this
source edition and drop clause (iv), which this reduction needs; they are not reused.

Source copies read (SHA-256 of the downloaded PDF bytes):

| Copy | SHA-256 |
|---|---|
| Shimura 1973, Project Euclid open-access PDF (22 pp.; p. 526 is PDF page 4) | `0899e62a3c96b52e2d189458674b8c415c25016c14b1ac7f120088011d5a9ca2` |
| Faltings 1983, GDZ Göttingen PDF (19 pp.; p. 361 is PDF page 14) | `f72a869f4a050e6e4a435cc790f4ac2e47b61fcac35d564041b5f43d89c2f87a` |
| Faltings 1984 erratum, GDZ Göttingen PDF (p. 381) | `c3a71300e1806f71a71b006e0b1d68d126c62af38c0fbf1e325b5aefc857d455` |

Manuscript edition: `diophantine_zq.tex`, SHA-256
`cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`.

## Named translation steps (GLUE, not proved)

* **G0 `NewformOfModularCurveGlue`**: if `E/ℚ` is modular (`IsModular E`), then at some level
  `M > 0` there is a normalized eigenform of every `T_n` (bad indices included), trivial
  character, with `a_n = E.LFunction n` for all `n ≥ 1`. Classical: the newform of level the
  conductor (Li 1975; Carayol 1986 for the bad primes).
* **G1 `ParametrizationPeriodsGlue`**: a nonconstant point `(x, y)` of `A` over `ℚ(j, j_M)` with
  `θx = c · ĝ · (2y + a₁x + a₃)`, `c ≠ 0`, gives `c (F_g(γτ) − F_g(τ)) ∈ Lat` for every period
  lattice `Lat` of `A` (`IsLatticeOf`), all `γ ∈ Γ₀(M)`, `τ ∈ ℍ`. Classical: `Γ₀(M)`-invariance of
  `ℚ(j(τ), j(Mτ))`, normalized Weierstrass uniformization, lift of the map `ℍ → ℂ/Λ`; the period
  model is Shimura 1973, §3, Proposition 3 and Remark (p. 530).
* **G2 `IsogenyLatticeGlue`**: an isogeny `E₁ → E₂` over `ℚ` gives `r Lat₁ ⊆ Lat₂` with
  `r ∈ ℚ^×` for all period lattices: `β^* ω_{E₂} = r ω_{E₁}`, `r` rational, and `β` is
  `z ↦ r z` over `ℂ`.

Translations inside the leaves (CONSEQUENCE GLUE, part of reading the prints in this form):

* S1. The standard model of `X₀(M)` over `ℚ`, its rational cusp `∞`, and its function field
  `ℚ(j, j(Mz))` embedded in `ℚ((q))` by the `q`-expansion at `∞` (`modularFunctionFieldQ`).
* S2. One-dimensional abelian varieties over `ℚ` are elliptic curves with Weierstrass equations,
  and `D_A = C ω_A`, `ω_A = dx/(2y + a₁x + a₃)`.
* S3. The canonical map at `∞` and `ν` are defined over `ℚ`; with `δφ(μ(g)) = g(z)dz` and
  `dz = dq/(2πi q)`, clause (iv) is `θx = c · ĝ · (2y + a₁x + a₃)`.
* S4. Shimura's Euler factor of `A` at a good prime `p` is `(1 − a_p p^{-s} + p^{1−2s})^{-1}` with
  `a_p = p + 1 − #Ã(𝔽_p) = A.LFunction p`.
* S5. Tau Ceti's `T_n` on the trivial-character space of `Γ₁(M)` is Shimura's `T_n` on `S₂(Γ₀(M))`.
* F1. Faltings's `L_v(s, E)` at a good prime is `(1 − a_p p^{-s} + p^{1−2s})^{-1}` with
  `a_p = tr(F_p | T_l E) = E.LFunction p`.
* F2. An isogeny of elliptic curves over `ℚ` yields a `TauCeti.Isogeny`.

## Proved steps

* `eichlerPotential_period_indep`: for `f` on `Γ₀(N)` and `γ ∈ Γ₀(N)`, `F_f(γτ) − F_f(τ)` is
  independent of `τ` (derivative zero on `ℍ`).
* `eichlerPotential_pow_smul_sub`, `pow_natCard_mem_Gamma0`, `isParamScale_transport`: with
  `d = #SL(2, ℤ/Mℤ)`, `γ^d ∈ Γ₀(M)` and `c₀ Π_M(g) ⊆ Λ ⇒ (d c₀) Π_N(f) ⊆ Λ`.
* `coe_eq_of_qExpansion_coeff_eq`: forms on `Γ₀(N)`, `Γ₀(M)` with equal positive coefficients
  are equal on `ℍ`.
* `isParamScale_of_level_zero`: at level `0` all periods vanish.
* `newformPeriodsRational_of_someLevel`: `SomeLevelPeriodsRational → NewformPeriodsRational` (no
  conductor equality, no newform theory).
* `ne_zero_of_pullbackIsMultiple`, `exists_rat_eq_of_pullbackIsMultiple`: the pull-back scalar is
  nonzero and **rational** (from rational `q`-expansions; no Néron model, no Manin constant).
* `jInvariantQ_not_const`: `j` is not constant (`E₄³ − E₆² = 1728 q + O(q²)`), so `ℚ(j, j_M)` is not
  degenerate.
* `someLevelPeriodsRational_of_prints`, `newformPeriodsRational_of_prints`,
  `modularToWeakWeil_of_prints`.

## Remaining formalization obligations

1. The prints themselves: `Shimura1973Thm1RationalGamma0` and `Faltings1983Kor2EllipticQ` stay
   hypotheses.
2. The consequence translations S1–S4 and F2 (a scheme-level `X₀(M)`, `J₀(M)` and Shimura's
   quotient, the `q`-expansion principle at `∞`, pull-backs of differentials, Euler factors of
   abelian varieties against `WeierstrassCurve.LFunction`, isogenies of abelian varieties against
   `TauCeti.Isogeny`). S5 and F1 are proved (`NewformPeriodsDictionary/README.md`;
   `FrobeniusTraceDictionary/Proved.lean`, `goodReductionFrobeniusTraceDictionaryQ_proved`).
3. Proofs of G0, G1, G2.
4. Outside this target: conductor equality for `newformLevel` and the passage from the analytic
   stand-in `HasWeakWeilParametrization` to Kolyvagin's algebraic premise (documented with
   `ModularToWeakWeil`).
