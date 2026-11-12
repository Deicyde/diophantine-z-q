# bp-modcurves: formalization blueprint for `X₁(N)`, `J₁(N)`, the Hecke algebra, `A_f` and the Belyi degree

Task bp-modcurves, 2026-11-12. Written for the crowdsourced Lean team. Scope: the modular-curve
objects that block leaves **R16** (Eichler–Shimura in `J₁(N)`) and **R18** (Javanpeykar) and the
glue steps **G13**, **G17**, **G18/E2** of `docs/research/h-decomposition.md` (§2.1, §3, §4 row
"`X₁(N)`, `J₁(N)` over `ℚ`, Belyi maps", work package WP9). Lean layer 0 is in
`scratch/bp-modcurves/` (compiled, no `sorry`). The results log is `scratch/bp-modcurves/log.md`.

Markers: **VERIFIED** = read in a source, computed, or compiled here. **STANDARD** = published,
with a reference. **SPECULATIVE** = my judgement, not checked. Theorem numbers from memory are
marked **UNVERIFIED** (this host has no network). Mathlib facts are VERIFIED by `grep` in
`.lake/packages/mathlib` (v4.35.0) unless marked otherwise. Facts about other libraries come from
`docs/research/prereq-survey.md`, which read most of them only by file name.

---

## §0. Main result

1. **The project uses `X₁(N)`, `J₁(N)`, `A_f` in exactly three ways.** (a) `V_ℓ(J₁(N))` has
   the newform representation `ρ_{f,ℓ}` as a constituent (R16 → G13, G17). (b) `dim J₁(N) = g(X₁(N)) ≤ N²`.
   (c) `X₁(N)` has a Belyi map of degree `≤ N²`, so R18 gives `h_F(J₁(N)) ≤ 13·10⁶·N¹²` (E2,
   manuscript L868-871, VERIFIED read). Nothing else about modular curves is used. In particular
   the glue needs no Hecke operators on `J₁(N)`, no cusp-count formula and no exact genus formula.
   Hecke operators enter only inside the statement of R16, and an existential form avoids them
   (§6).

2. **Recommended route: algebraic, through the `j`-line. Not the Picard scheme, not complex
   tori.** (SPECULATIVE as a cost judgement; the mathematics is STANDARD.)
   - `X₁(N)` := Mathlib's **relative normalization** (`Scheme.Hom.normalization`, VERIFIED present)
     of `ℙ¹_ℚ` (the `j`-line) in the field `K_N = ℚ(j)(x(P))`. Here `P` is a point of exact order `N`
     on the universal curve `E_j/ℚ(j)` (Mathlib `ModelsWithJ`, VERIFIED present), with `N ≥ 3`.
     This gives `j : X₁(N) → ℙ¹` for free, as a finite morphism of degree `[K_N : ℚ(j)]`.
   - The moduli interpretation at the level of points is **Tate normal form**. This is Lean
     layer 0, done: `BPModCurves.exists_tateNF`, `tateNF_unique`.
   - `J₁(N)` := an abelian variety with the **Albanese property** for `(X₁(N), cusp)`. This is a
     predicate over Mathlib schemes and the repository's `PkgI3.AbVar`. Existence is a **leaf**
     (Weil; Chow; Milne 1986, Thm 1.1, UNVERIFIED). Uniqueness is glue (small).
   - `A_f` and the Hecke algebra: R16 is stated **existentially**, as an abelian variety `A`
     with a surjection `J₁(N) ↠ A`, `K_f ↪ End⁰(A)`, `dim A = [K_f:ℚ]`, and Frobenius traces
     `a_p(f)` on a rank-2 piece. This is a consequence of Shimura 1973, Thm 1 plus the realization
     bridge of `locators.md`. Hecke correspondences on `X₁(N)` become optional (tier large) (§6).
   - The Belyi degree and genus bound come from `deg j = [K_N:ℚ(j)] ≤ #E[N]/2 ≤ N²/2` and
     Riemann–Hurwitz for a Belyi map: `2g − 2 = d − #j⁻¹{0,1728,∞} ≤ d − 3`, so `g ≤ (d−1)/2`.
     The group-theoretic version is Lean layer 0, done: `belyiDeg_Gamma1_le`, `genus_Gamma1_le`.

3. **Size.** The full dependency graph (§3, §4) has 17 nodes. Proved in layer 0: MC0a, MC0b,
   MC2a, MC2b, MC2d. Definition compiled: MC6 (`IsJacobian`, with its uniqueness glue proved), MC1
   and MC4 (`fieldX1`, `Y1j`, open degree statements). That is 1 130 Lean lines in 5 files. Small or
   medium: 5 nodes. Large: 4. Very large: 3: the Jacobian's existence (MC6', a leaf, so not
   built), the Faltings height (WP10, out of scope) and, if wanted, Hecke correspondences on
   `J₁(N)` (MC8, avoidable). Without MC8 and with MC6' a leaf, the critical path is
   MC3a → MC1 → MC4 → MC5. It is large: properness and smoothness of the normalization of `ℙ¹` in
   `K_N`, geometric connectedness, and the Belyi property. It is the same order of work as
   Mathlib's existing curve infrastructure and needs no new cohomology theory.

4. **Lean layer 0** (VERIFIED: `lake env lean` on each file gives exit 0 with no errors, no
   warnings and no `sorry`; `#print axioms` gives `propext`, `Classical.choice`, `Quot.sound`):
   - `scratch/bp-modcurves/Gamma1Genus.lean`. Over Mathlib's `SL(2,ℤ)`, `Gamma1`, `ModularGroup.S/T`:
     `pmSubgroup`, `belyiDeg Γ = [SL₂(ℤ):±Γ]`, `nu2`, `nu3` (fixed points of `S`, `ST` on cosets),
     `nuInf` (`⟨T⟩`-orbits), `genus Γ = 1 + μ/12 − ν₂/4 − ν₃/3 − ν∞/2`. Theorems: `nu2_Gamma1`
     (`N ≥ 3`), `nu3_Gamma1` (`N ≥ 4`), `genus_Gamma1` (`g = 1 + μ/12 − ν∞/2` for `N ≥ 4`),
     `belyiDeg_Gamma1_le` (`μ ≤ N²`), `genus_Gamma1_le` (`g ≤ N²`), `index_Gamma1_le`.
     Also `cosetEquivPrimVec : SL(2,ℤ) ⧸ Gamma1 N ≃ PrimVec N` (primitive vectors of `(ℤ/N)²`),
     via the lifting lemma `exists_SL2_firstColMod`; `index_Gamma1_eq_card`; and
     `two_mul_belyiDeg_Gamma1` (`2μ = #PrimVec N` for `N ≥ 3`). A `decide` test checks
     `[SL₂(ℤ):Γ₁(5)] = 24`.
   - `scratch/bp-modcurves/TateNormalForm.lean`. Over Mathlib's `WeierstrassCurve`,
     `VariableChange` and `Affine.Point`: `tateNF b c`; `exists_tateNF` (a point `P` with `2P ≠ 0`,
     `3P ≠ 0` is moved to `(0,0)` on some `E(b,c)`); `tateNF_unique`, `tateNF_unique'` (the
     normalization is unique); `tateNF_Δ` (`Δ(b,c) = b³(16b² − 8bc² − 20bc + b + c(c−1)³)`).
   - `scratch/bp-modcurves/Jacobian.lean`: `IsCurve`; `IsJacobian X P₀ J aj` (the Albanese property
     over the repository's `AbVar`); `JacobianExists` (leaf statement); `IsJacobian.unique`
     (proved); `jacobian` (a chosen Jacobian, given the leaf).
   - `scratch/bp-modcurves/ModularCurveDefs.lean`: `Ej` (Mathlib `ofJNe0Or1728 X` over `ℚ(j)`,
     with `Ej_j : Ej.j = X` proved); `fieldX1 P = ℚ(j)⟮x(P)⟯`; `Y1j P` (Mathlib's relative
     normalization of `Spec ℚ[j]` in `fieldX1 P`, i.e. `X₁(N)` minus its cusps); `jMap`. The open
     statements `TorsionCardLe`, `FieldX1DegreeLe` and `FieldX1Degree` (leaf MC1') are `Prop`s.
   - `scratch/bp-modcurves/AnalyticModuli.lean`. The moduli interpretation of `Γ₁(N)\ℍ` at the
     level of points, over Mathlib's `ℍ`, `SL(2,ℤ)`-action and `Gamma1`, with `Λ_τ = ℤτ + ℤ`:
     `lattice_homothety` (`j(γ,τ)·Λ_{γτ} = Λ_τ`); `exists_SL2_of_homothety` (every homothety
     `Λ_{τ'} → Λ_τ` is `j(γ,τ)` with `τ' = γτ`); `pair_iso_iff`
     (`(ℂ/Λ_{τ'}, 1/N) ≅ (ℂ/Λ_τ, 1/N)` iff `τ' ∈ Γ₁(N)·τ`); `exactOrder` (`1/N` has exact
     order `N`); `exists_normalize` (every point `(cτ+d)/N` with `(c,d)` primitive mod `N` is
     equivalent to `1/N`).
   - Ground truth (VERIFIED, computed): `genus_check.py` (`N = 1..30`). The genus from the
     `S, ST, T` action equals the closed forms `μ = J₂(N)/2` and `ν∞ = ½Σ_{d|N}φ(d)φ(N/d)`, and
     the reference genus table (all 30 agree). `tate_check.py`: on Kubert's families for
     `N = 4..10`, `(0,0)` has exact order `N`.

---

## §1. What the leaves and glue need (the interface)

| Consumer | What it needs from this blueprint | Where used |
| --- | --- | --- |
| **R16** (Shimura 1973, Thm 1; Shimura 1971, Thm 7.9, UNVERIFIED there) | `J₁(N)` as a `PkgI3.AbVar ℚ`; for a weight-2 newform `f` (`HSyn.CF`, `IsNormalizedEigenform` on Mathlib `CuspForm`), a `ℚ`-quotient `A_f` with `K_f ↪ End⁰(A_f)`, `dim A_f = [K_f:ℚ]`, and the rank-2 realization with `tr Frob_p = ι(a_p)` for `p ∤ Nℓ` | G13, route K's K2 |
| **R18** (Javanpeykar, Thm 1.1.1) | a smooth projective geometrically connected curve `X/ℚ̄` of genus `g ≥ 1`, a Belyi map `X → ℙ¹` of degree `d`, and `Jac X` (with its stable Faltings height, WP10) | E2 / G18 |
| **G13** | `r₅ ≅ ρ_{f,5}` is a constituent of `V₅(J₁(N))`, from R16's surjection `V_ℓ(J₁(N)) ↠ V_ℓ(A_f)` | C9 |
| **G17** | `J₁(N)` over `L'` as an abelian variety, for Faltings' Hom theorem (T8) and Poincaré reducibility | E1 |
| **E2** (`GlueAssembly.transfer_of_level`) | `g(X₁(N)) ≤ N²`, `d ≤ N²`, `dim J₁(N) = g` | G18 |

The glue does not use the equality `g = genus formula`, the cusp count, `ν₂`, `ν₃`,
`dim S₂(Γ₁(N)) = g`, the Hecke algebra `𝕋` acting on `J₁(N)`, or the Eichler–Shimura
congruence relation `T_p = Frob + Ver` (that is inside R16). VERIFIED by reading the manuscript's
E2 paragraph (L860-880) and h-decomposition §3 rows G13, G17, G18.

---

## §2. What exists

### §2.1 Mathlib v4.35.0 (VERIFIED by grep in `.lake/packages/mathlib`)

| Topic | Declarations / files | Use here |
| --- | --- | --- |
| Congruence subgroups | `CongruenceSubgroup.Gamma`, `Gamma0`, `Gamma1`, `Gamma1_mem`, `IsCongruenceSubgroup`, `instFiniteIndexGamma1` (`NumberTheory/ModularForms/CongruenceSubgroups.lean`); `Subgroup.adjoinNegOne`, `IsArithmetic` (`ArithmeticSubgroups.lean`) | MC0 (used) |
| `S`, `T` | `ModularGroup.S`, `T`, `coe_S`, `coe_T`, `S_mul_S_eq` (`LinearAlgebra/Matrix/SpecialLinearGroup.lean`) | MC0 (used) |
| Cusps | `IsCusp`, `CuspOrbits`, `cosetToCuspOrbit`, `surjective_cosetToCuspOrbit`, `Finite (CuspOrbits 𝒢)` (`Cusps.lean`) | MC0c bridge (not used yet) |
| Modular / cusp forms | `ModularForm Γ k`, `CuspForm Γ k` for `Γ ≤ GL₂(ℝ)`, `qExpansion`, slash actions, level-one dimension formula (`DimensionFormulas/LevelOne.lean`), Petersson product file, `LFunction.lean` | inside R16's statement (`HSyn.CF`) |
| Hecke rings | `NumberTheory/HeckeRing/Defs.lean`: `IsHeckeTriple`, `HeckeCoset`, `HeckeCosetModule`, `HeckeRing` (abstract double cosets; product "in later files", which are absent from v4.35) | MC8 (abstract only); **no Hecke operators on modular forms** (grep `heckeOperator`, `heckeT`: none) |
| Diamond operators, nebentypus | none (grep) | `HSyn.CF` supplies a nebentypus |
| Elliptic curves | `WeierstrassCurve`, `VariableChange` (group, `•`), `Affine.Point` with the group law, `NormalForms.lean` (char-≠-2 and short forms; **no Tate normal form**), `ModelsWithJ.lean` (`ofJ0`, `ofJ1728`, curves with given `j`), `IsomOfJ.lean`, `DivisionPolynomial/{Basic,Degree}.lean` (`ψ`, `Φ`, degree bounds) | MC2 (used), MC3 |
| Analytic elliptic curves | `PeriodPair.weierstrassP`, `derivWeierstrassP`, `derivWeierstrassP_sq : ℘'² = 4℘³ − g₂℘ − g₃`, `g₂`, `g₃` (`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`); `ZLattice`; `UpperHalfPlane` as a manifold (`UpperHalfPlane/Manifold.lean`) | analytic moduli at the level of points (MC2d, done; the `℘` model not yet used) |
| Schemes | `Scheme`, `Over`, `IsProper`, `Smooth`, `SmoothOfRelativeDimension`, `GeometricallyIntegral`, `GeometricallyConnected`, `Scheme.functionField`, `Birational/*`, **relative normalization** `Scheme.Hom.normalization` with its universal property (`Normalization.lean`), `ProjectiveSpectrum` (Proj) | MC1, MC4 |
| Divisors | `AlgebraicCycle`, `IsWeilDivisor`, `weilDivisors`, `degree` (`AlgebraicCycle/Basic.lean`); order of vanishing `Scheme.ord` on the function field (`OrderOfVanishing.lean`) | MC6b (`Pic⁰` of a curve as a Galois module) |
| Group schemes | `GrpObj`, `isCommMonObj_of_isProper_of_geometricallyIntegral` (rigidity: a proper geometrically integral group scheme is commutative; `Group/Abelian.lean`) | `PkgI3.AbVar` uses it |
| Cohomology | `ℓ`-adic pro-étale cohomology `Scheme.EllAdicCohomology` (`Sites/ElladicCohomology.lean`); sheaf cohomology on sites (`CategoryTheory/Sites/SheafCohomology/*`); `Pic` of a commutative **ring** (`RingTheory/PicardGroup.lean`) | genus via `H¹(𝒪)` would need coherent cohomology of schemes (absent) |
| Not present | Picard group/scheme of a scheme, Jacobians, Albanese, Riemann–Hurwitz, genus of a curve, Riemann–Roch, the sheaf `Ω¹_{X/k}` of a scheme (Kähler differentials exist for rings only; grep in `AlgebraicGeometry`: no hit outside `FormallyUnramified.lean`), regular-implies-smooth for schemes, compact Riemann surfaces `Γ\ℍ*`, `X₀(N)`/`X₁(N)` as schemes, Hecke operators, the transport of points under `VariableChange` | — |

### §2.2 Other libraries (from `prereq-survey.md`, which read them mostly by file name; UNVERIFIED beyond that)

- **Tau Ceti**: `TauCeti.AlgebraicGeometry.AbelianVariety` (definition, `Hom`, `End`, `IsIsogeny`,
  **`IsAlbanese`**, 288 declarations). Newform theory: Hecke operators `CuspForm.heckeTCuspNat`,
  strong multiplicity one, Atkin–Lehner, `cuspFormsNew`, L-functions of newforms. Elliptic-curve Tate
  modules. Its `IsAlbanese` is the natural home for MC6's predicate.
- **Anthropic FLT**: Jacobians of algebraic curves via function fields: `genusFF`,
  `Pic0`, `Thm_AlgebraicCurve_Pic0_finrank_rationalTateModule_eq_two_mul_genusFF_of_charZero`
  (rank `2g` Tate module), Weil pairing, `GoodReductionJacobian.*` (about 560 files),
  `ModularCurve.mTorsionGaloisRep` (mod-`𝔪` Galois action on Hecke torsion of a Jacobian). This
  is the nearest existing supplier of MC4 (genus), MC6b (`Pic⁰` as a Galois module) and the rank
  `2g` statement. Which of these are proved or only stated was not checked.
- **Lean Pool** `flt-eichler-shimura`: the Eichler–Shimura **isomorphism** with group cohomology
  for `Γ₀(N)` (`HeckeEis.exists_eichlerShimura_heckeEquivariant`);
  `ModularCurve.x0_modularPolynomialPresentation` (the function field of `X₀(N)` by the modular
  polynomial). The latter is the `Γ₀` analogue of MC3's `K_N`.
- **openai/math**: `AbelianScheme/`, `PELModuli/` (not examined).

---

## §3. Dependency graph

Nodes `MCk`. `→` means "is used by". `[done]` = Lean layer 0, `[leaf]` = a published theorem to
be stated, not proved.

```
                        Mathlib: SL(2,ℤ), Gamma1, S, T          Mathlib: WeierstrassCurve, VariableChange,
                                   │                                     Affine.Point, ModelsWithJ, ψ_N
                                   ▼                                              │
 MC0a [done] belyiDeg, ν₂, ν₃, ν∞, genus of Γ₁(N); μ ≤ N², g ≤ N²                  ▼
 MC0b [done] cosets SL₂(ℤ)/Γ₁(N) ≅ primitive vectors of (ℤ/N)²; 2μ = #         MC2a [done] Tate normal form ∃!
 MC0c  ν∞ = #Γ₁(N)\ℙ¹(ℚ) (Mathlib CuspOrbits)                        MC2b [done] point hypotheses (2P,3P ≠ 0)
 MC2d [done] over ℂ: (ℂ/Λ_τ, 1/N) pairs up to homothety = Γ₁(N)\ℍ  (links MC0 to MC2)
          │                                                                       │
          │                    MC3a  #E[N](K̄) ≤ N² (char 0)  ◄──── Tau Ceti / FLT (E[n] ≅ (ℤ/n)²) or ψ_N
          │                       │                                               │
          │                       ▼                                               ▼
          │            MC1  K_N = ℚ(j)(x(P)) [def done], [K_N:ℚ(j)] ≤ N²/2 ◄──────── MC2c  Y₁(N)(K) ≅ {(b,c): Δ≠0, ord(0,0)=N}
          │                       │   (MC1' [leaf] Igusa/Shimura: Φ_N abs. irreducible ⇒ ℚ̄∩K_N = ℚ, = μ)
          │                       ▼
          │            MC4  X₁(N) := normalization of ℙ¹_j in K_N [affine chart def done]: proper, smooth, geom. connected curve /ℚ
          │                       │
          │                       ▼
          ├──────────► MC5  j : X₁(N) → ℙ¹ Belyi (étale over ℙ¹∖{0,1728,∞}), deg j = [K_N:ℚ(j)] ≤ N²
          │            MC5' [leaf] Riemann–Hurwitz (Hartshorne IV.2.4, UNVERIFIED) ⇒ g ≤ (d−1)/2 ≤ N²
          │                       │
          │                       ▼
          │            MC6  IsJacobian X P₀ J [done + uniqueness] (Albanese predicate)   MC6' [leaf] existence
          │            MC6b Pic⁰(X_ℚ̄) as a G_ℚ-module (Weil divisors, Scheme.ord)       MC6'' dim J = g [leaf/glue]
          │                       │
          │                       ▼
          │            MC7  R16 existential: ∃ A, J₁(N) ↠ A, K_f ↪ End⁰A, dim A = [K_f:ℚ], traces a_p  [leaf]
          │            MC8  (optional) Hecke correspondences T_n, ⟨d⟩ on X₁(N), 𝕋 ⊂ End J₁(N), I_f, A_f = J/I_f J
          │                       │
          ▼                       ▼
   E2 / G18 (g, d ≤ N²; R18)   G13 (constituent), G17 (J₁(N)_{L'} as AbVar)          WP10: Faltings height (R18)
```

---

## §4. The nodes: statement, tier, cheapest faithful route

Tiers: **small** (< 300 Lean lines), **medium** (300-2 000), **large** (2 000-10 000),
**very large** (> 10 000 or new theory). These are SPECULATIVE estimates. Layer-0 line counts are
VERIFIED.

| Node | Statement | Inputs | Tier | Cheapest faithful route | Status |
| --- | --- | --- | --- | --- | --- |
| **MC0a** | `belyiDeg (Γ₁ N) ≤ N²`; `ν₂ = 0` (`N ≥ 3`), `ν₃ = 0` (`N ≥ 4`); `genus (Γ₁ N) ≤ N²`; `g = 1 + μ/12 − ν∞/2` (`N ≥ 4`) | Mathlib `Gamma1`, `S`, `T` | small | trace argument: a conjugate of `S` (trace 0) or `ST` (trace 1) is never `≡ ±1 mod N` | **done** (`Gamma1Genus.lean`) |
| **MC0b** | `SL₂(ℤ) ⧸ Γ₁(N) ≃ {v ∈ (ℤ/N)² primitive}`, and `2μ = #` primitive vectors for `N ≥ 3` | `firstColMod_eq_iff`; lifting a primitive vector mod `N` to a coprime pair (Shimura Lemma 1.38, UNVERIFIED number) | small | first column; lift `a ↦ a + tN` with `t` = product of the primes of `c` not dividing `a` | **done** (`cosetEquivPrimVec`, `two_mul_belyiDeg_Gamma1`); `#PrimVec N = J₂(N)` (Jordan totient) open, small |
| MC0c | `nuInf Γ = #CuspOrbits Γ` (Mathlib's `Γ\ℙ¹(ℚ)`); `ν∞(Γ₁(N)) = ½Σ_{d|N}φ(d)φ(N/d)` for `N ≥ 5` | Mathlib `cosetToCuspOrbit` | medium | the stabilizer of `∞` is `±⟨T⟩`; double cosets | open (formula VERIFIED numerically, `N ≤ 30`) |
| **MC2a** | Tate normal form: `(E,P)` with `2P, 3P ≠ 0` ⇒ `∃ C, C•E = E(b,c)`, `C` sends `P ↦ (0,0)`; uniqueness; `Δ(b,c)` | Mathlib `VariableChange` | small | explicit `u = d/A₂`, `r = x₀`, `s = ℓ`, `t = y₀` | **done** (`TateNormalForm.lean`) |
| **MC2b** | the hypotheses of MC2a from `P+P ≠ 0`, `P+P+P ≠ 0` in `Affine.Point` | Mathlib `add_self_of_Y_eq`, `X_eq_iff` | small | — | **done** |
| MC2c | for `N ≥ 4`: `Y₁(N)(K) := {(E,P), ord P = N}/≅ ≃ {(b,c) : Δ(b,c) ≠ 0, ord_{E(b,c)}(0,0) = N}` | MC2a, MC2b, `addOrderOf`; **a change of variables acts on `Affine.Point` as a group isomorphism**, which is absent from Mathlib (only `equation_iff_variableChange`, `nonsingular_iff_variableChange` for translations, in `Affine/Basic.lean`) | medium | first the point transport `(x,y) ↦ ((x−r)/u², (y−s(x−r)−t)/u³)` and its additivity (slope identities), then package MC2a/b as an `Equiv` of quotients | open |
| **MC2d** | over `ℂ`: `(ℂ/Λ_{τ'}, 1/N) ≅ (ℂ/Λ_τ, 1/N)` by a homothety iff `τ' ∈ Γ₁(N)τ`; every primitive level-`N` point is equivalent to `1/N` (so pairs `(ℂ/Λ_τ, P)` up to homothety are `Γ₁(N)\ℍ`) | Mathlib `UpperHalfPlane`, `coe_specialLinearGroup_apply`, `Gamma1_mem`; Weierstrass model via `PeriodPair.derivWeierstrassP_sq` | small | lattices `ℤτ + ℤ` as sets, automorphy factor `cτ + d`, orientation from imaginary parts | **done** (`AnalyticModuli.lean`); "every lattice is some `αΛ_τ`" and "`(cτ+d)/N` has exact order `N` iff primitive" open, small |
| MC3a | `E[N](K̄)` has at most `N²` points for `E/K`, `char K = 0` (and exactly `N²`) | Silverman III.6.4 (UNVERIFIED) | medium-large | via Tau Ceti/FLT `E[n] ≅ (ℤ/n)²` if proved there; else `x(E[N]) ⊆ roots of ψ_N` (multiplication formula, absent from Mathlib) | open |
| MC1 | `K_N := ℚ(j)⟮x(P)⟯ ⊆ \overline{ℚ(j)}` for `P ∈ E_j(\overline{ℚ(j)})` of exact order `N`; `[K_N:ℚ(j)] ≤ N²/2` | MC3a; `E_j` from `ModelsWithJ`; `minpoly` | medium | `x(P)` is a root of `∏_{Q of order N}(X − x(Q))`, which has `≤ J₂(N)/2` distinct roots, and that polynomial has coefficients in `ℚ(j)` (Galois-stable) | **definition done** (`fieldX1`, `Ej_j`); bound open (`FieldX1DegreeLe`) |
| MC1' | `Φ_N` absolutely irreducible over `ℚ̄(j)`, so `ℚ` is algebraically closed in `K_N` and `[K_N:ℚ(j)] = J₂(N)/2` | Igusa 1959 or Shimura 1971 Thm 6.6 / Lang, *Elliptic Functions* Ch. 6 (all UNVERIFIED) | (leaf) | state as a leaf: `Gal(ℚ̄(j)(E[N])/ℚ̄(j)) ≅ SL₂(ℤ/N)/(±1 ∩ …)` acting transitively on order-`N` points mod `±` | leaf; or glue from monodromy (large) |
| MC4 | `X₁(N) := (Spec K_N → ℙ¹_ℚ).normalization` (**affine chart compiled**: `Y1j P`, `jMap`); it is proper, smooth of relative dimension 1, geometrically connected over `ℚ`, with function field `K_N` | Mathlib relative normalization; finiteness of integral closure (Noether, in Mathlib for f.g. algebras over a field, UNVERIFIED name); normal + dim 1 + char 0 ⇒ smooth (regular ⇒ smooth over a perfect field, absent?); MC1' for geometric connectedness | large | relative normalization (universal property in Mathlib) instead of gluing affine charts by hand | open |
| MC5 | `j : X₁(N) → ℙ¹` finite, `deg j = [K_N:ℚ(j)] ≤ N²`; étale over `ℙ¹ ∖ {0, 1728, ∞}`; base change to `ℚ̄` is a Belyi map after `j ↦ j/1728` | MC4; good reduction of `E_j` away from `j ∈ {0,1728,∞}` (`Δ(E_j)` explicit); `E[N]` étale in char 0 | medium-large | unramifiedness from `disc(ψ_N)` being a unit times a power of `Δ(E_j)` (STANDARD, UNVERIFIED reference) or from the moduli (`Aut E = ±1` away from `0,1728`) | open |
| MC5' | Riemann–Hurwitz: `2g − 2 = −2d + Σ(e_P − 1)`; for a Belyi map `g ≤ (d − 1)/2` | genus of a curve (absent from Mathlib; Anthropic FLT `genusFF`) | (leaf) / large | state as a textbook leaf (Hartshorne IV, Cor. 2.4, UNVERIFIED) over a genus definition `g = dim_ℚ H⁰(X, Ω¹)` or `genusFF` | leaf |
| **MC6** | `IsJacobian X P₀ J aj`: `J : AbVar ℚ`, `aj : X ⟶ J.X` over `ℚ`, `P₀ ≫ aj = η`, and every pointed `ℚ`-morphism `X → A` to an abelian variety factors uniquely through a homomorphism `J → A`; plus `dim J = g` (not in the predicate) | `PkgI3.AbVar` (copied); Tau Ceti `IsAlbanese` | small | Albanese predicate (no Picard functor, no line bundles) | **definition done**, `IsJacobian.unique` proved (`Jacobian.lean`); `dim J = g` open |
| MC6' | **existence**: every smooth projective geometrically connected curve `X/k` with `X(k) ≠ ∅` has a Jacobian (Weil 1948; Chow; Milne 1986, Thm 1.1 and Prop. 6.1, UNVERIFIED) | — | (leaf) | state as a leaf | leaf |
| MC6b | `Pic⁰(X_ℚ̄)` := degree-0 Weil divisors mod `div(f)` with its `G_ℚ`-action; `J(ℚ̄) ≅ Pic⁰(X_ℚ̄)` equivariantly (Abel–Jacobi) | Mathlib `weilDivisors`, `degree`, `Scheme.ord` | medium (definition), leaf (iso) | only needed if one wants R16 over `Pic⁰` instead of over `J` | optional |
| MC7 | R16, existential form (§6) | MC6, `PkgI3.AbVar.V`, `HSyn.CF` | (leaf) | Shimura 1973 Thm 1 + the realization bridge | leaf (statement small once MC4, MC6 exist) |
| MC8 | Hecke correspondences `T_p`, `⟨d⟩` on `X₁(N)`; `𝕋 → End(J₁(N))`; `I_f`; `A_f = J₁(N)/I_f J₁(N)` | quotients of curves by finite groups, isogenies of elliptic curves (Vélu; absent), Picard/Albanese functoriality | very large | avoid (MC7); if wanted: `⟨d⟩` is cheap via MC2a (`(b,c) ↦ TateNF(E(b,c), d·(0,0))`), `T_p` is not | optional |

Notes on the table:

- **MC1's definition is canonical up to `ℚ(j)`-isomorphism.** Different choices of `P` give
  `ℚ(j)`-conjugate fields. For the bounds it is enough to fix any `P` (`Classical.choice` on
  MC3a's existence of a point of exact order `N`). The pair `(E,±P)` is the right moduli problem
  for `X₁(N)`: `−1 ∈ Aut(E)` identifies `(E,P)` with `(E,−P)`, and `ℚ(j, x(P))` is the field of
  the stabilizer of `±e₁` in `GL₂(ℤ/N)`, whose determinant is surjective. So `ℚ` is algebraically
  closed in `K_N`. This is the standard `ℚ`-model of `X₁(N)` in which the cusp `∞` is rational
  (Shimura 1971 §6.1-6.2 and Diamond–Im §7, UNVERIFIED). STANDARD.
- **Which `ℚ`-model.** Two `ℚ`-models of `X₁(N)` are in use: `(E, P)` with `P` of order `N`,
  and `(E, μ_N ↪ E)`. They differ by the Atkin–Lehner twist. Both have rational cusps, and the
  Albanese base point `P₀` must be a rational cusp of the chosen model. R16 must be stated for the
  same model as `J₁(N)` (`h-decomposition.md` §6 warns that R16 must not inherit the Fricke
  convention). Shimura's `A_f` is defined over `ℚ` in either model, and the two `J₁(N)` are
  `ℚ`-isomorphic via `w_N` composed with a Galois twist. The constituent statement G13 is
  insensitive to this. SPECULATIVE in the details; flag for the R16 statement writer.
- **Geometric connectedness (MC1') is needed only for R18.** Javanpeykar assumes `X` connected.
  Without MC1', `X₁(N)_ℚ̄` would be a disjoint union of conjugate components, and R18 would have
  to be applied componentwise with a product Jacobian. MC1' is a classical theorem, and stating
  it as a leaf is the cheapest option.

---

## §5. The Jacobian: three routes compared

| Route | What must be built | Tier | Verdict |
| --- | --- | --- | --- |
| **(A) Albanese predicate + existence leaf** | MC6 (definition over `PkgI3.AbVar`: **done**, `Jacobian.lean`); uniqueness up to unique isomorphism (glue: **done**, `IsJacobian.unique`); MC6' existence as a leaf; `dim J = g` as part of the leaf or from `T_ℓ J ≅ T_ℓ Pic⁰` and Anthropic FLT's rank `2g` | small + leaves | **recommended** |
| (B) Picard functor and representability for curves | line bundles on `X ×_ℚ T` (Mathlib has `Pic` of rings only; no invertible sheaves on schemes, no tensor structure on `Scheme.Modules` found); `Pic_{X/ℚ}` as an fppf sheaf; representability by `Sym^g X` and Weil's birational group laws (Milne 1986 §§3-5) or by Hilbert/Quot schemes (Grothendieck; Kleiman, FGA explained Thm 9.4.8, UNVERIFIED) | very large | the faithful formalization of MC6'; not on the critical path |
| (C) Analytic: `J(ℂ) = S₂(Γ₁(N))^∨ / H₁(X₁(N)(ℂ), ℤ)`, Riemann's relations, Lefschetz embedding, GAGA, descent to `ℚ` by canonical models (Shimura 1971 Ch. 6-7) | compact Riemann surface `Γ₁(N)\ℍ*` (absent), its `H₁`, period lattice, Riemann form, Tau Ceti `isRiemannForm_iff_isPolarization`, projectivity of polarized tori (absent), GAGA (absent), Shimura's canonical model over `ℚ` | very large (largest) | rejected for the variety. The analytic side survives only inside R16's statement (the `q`-expansion coefficients `a_p(f)` of a Mathlib `CuspForm`) |

**Is route (A) faithful?** The predicate is the standard universal property (Milne 1986 §6;
Lang, *Abelian varieties* Ch. II, UNVERIFIED). It is stated over Mathlib schemes and the
repository's abelian varieties, not over a structure invented for the purpose. A downstream
statement "∀ J, IsJacobian X P₀ J ι → …" would be vacuous if no Jacobian existed. So **the main
theorem must consume MC6' (existence) explicitly**, as a leaf hypothesis, exactly as it consumes
the other leaves. With the existence leaf among the hypotheses, a vacuous predicate cannot make the
conclusion cheaper. The acceptance test for MC6 is uniqueness: two Jacobians are isomorphic by a
unique isomorphism compatible with `ι`. This is provable glue and catches a wrongly stated
universal property (for example, one quantifying over too few targets `A`).

**`dim J = g`.** R18 is stated with `g` = genus of `X`, while E2 uses `g = dim J`. Either include
`dim J = g` in MC6' (Milne 1986, Prop. 2.1, UNVERIFIED) or derive it: the Tate module of `J` has
rank `2 dim J` (an abelian-variety fact) and is isomorphic to that of `Pic⁰`, which has rank `2g`
(Anthropic FLT's theorem, if proved there). The first is cheaper.

---

## §6. The Hecke algebra and `A_f`: the existential form of R16

The project needs from R16 only (§1): `ρ_{f,ℓ}` is a constituent of `V_ℓ(J₁(N))`, realized
through a `ℚ`-quotient. The following statement is a consequence of Shimura 1973, Thm 1
(`locators.md` row R16: Thm 1 pp. 526-527 read by the audit) together with the rank-2 realization
bridge that `locators.md` lists as still to be sourced. It is never stronger than the published
results:

> **R16 (existential).** Let `N ≥ 1`, let `f ∈ S₂(Γ₁(N))` be a newform (`HSyn.CF`,
> `IsNormalizedEigenform`, `IsNew`) with coefficient field `K_f = ℚ(a_n(f))`, and let `J` be a
> Jacobian of `X₁(N)` (MC6). There are an abelian variety `A : PkgI3.AbVar ℚ`, a surjective
> homomorphism `π : J ↠ A` over `ℚ`, and a ring embedding `θ : K_f ↪ End⁰_ℚ(A)` with
> `dim A = [K_f : ℚ]`, such that for every prime `ℓ`, every embedding `ι : K_f ↪ ℚ̄_ℓ` and every
> prime `p ∤ Nℓ`: the `ι`-component `V_ℓ(A) ⊗_{K_f ⊗ ℚ_ℓ, ι} ℚ̄_ℓ` has dimension 2 and the
> geometric (or arithmetic: fix one) Frobenius at `p` has trace `ι(a_p(f))` and determinant
> `ι(χ(p))·p`.

- **What it avoids**: Hecke correspondences on `X₁(N)`, the ideal `I_f`, and the definition
  `A_f = J/I_f J`. Every object in the statement exists in the repository or in this
  blueprint: `PkgI3.AbVar`, `homGroup`, `End⁰`, `AbVar.V`, `galRep`; `HSyn.CF` with Mathlib
  `qExpansion`; MC4 and MC6.
- **What it keeps**: the field `K_f` acting through `End⁰`, the dimension, and the
  individual-embedding rank-2 realization that `locators.md` requires (Shimura's total
  characteristic polynomial alone is insufficient: R16's audit note).
- **Fricke caveat (from `locators.md`)**: Shimura 1973 Thm 1's total Euler-factor clause carries
  an extra `Γ₀`/Fricke-stability condition. The existential form above uses only the
  unconditional clauses (quotient, `K_f`-action, dimension). The trace clause comes from the
  realization bridge (Shimura 1971 Thm 7.9 / Deligne–Rapoport / Diamond–Im §12.5, UNVERIFIED).
  Do not attach the Fricke condition to the unconditional clauses, and do not drop it if the
  total Euler factor is used.
- **G13 from R16 (glue, small)**: `V_ℓ(π) : V_ℓ(J) ↠ V_ℓ(A)` is `G_ℚ`-equivariant and surjective,
  because `π` is surjective and has finite-index image on Tate modules (a Poincaré-reducibility
  fact: T8 / `PkgI3`). So a 2-dimensional `ι`-component of `V_ℓ(A) ⊗ ℚ̄_ℓ` is a constituent of
  `V_ℓ(J) ⊗ ℚ̄_ℓ`. Inputs: `PkgI3.AbVar.V` functoriality (exists) and surjectivity on `V_ℓ`
  (medium).
- **If the Hecke algebra is wanted anyway (MC8)**: the cheap part is the diamond operators. `⟨d⟩`
  acts on `Y₁(N)` by `(E,P) ↦ (E,dP)`, which in Tate coordinates is
  `(b,c) ↦ TateNF(E(b,c), d·(0,0))`. This is computable from `exists_tateNF`, and its extension to
  `X₁(N)` is by normalization (MC4's universal property). The expensive part is `T_p`, which
  needs quotients `E/C` by cyclic subgroups (Vélu's formulas, absent from Mathlib), the
  correspondence `X₁(N,p) ⇉ X₁(N)`, and functoriality of the Albanese for correspondences.
  Very large. Mathlib's abstract `HeckeRing` (double cosets) gives the algebra `𝕋` but no action
  on `J₁(N)`. Tau Ceti's `heckeTCuspNat` gives the action on cusp forms, which is all that R16's
  statement needs (`IsNormalizedEigenform`).

---

## §7. Belyi degree and genus

**What E2 needs**: `g(X₁(N)) ≤ N²` and a Belyi map of degree `d ≤ N²` (then R18 gives
`h_F ≤ 13·10⁶·g·d⁵ ≤ 13·10⁶·N¹²`). Glazer: "the genus and the degree of its standard Belyi map are
at most `N²`" (L868-870, VERIFIED read).

**Route.**
1. **Degree.** `j : X₁(N) → ℙ¹` has degree `[K_N : ℚ(j)]` (MC4 and MC5: a finite morphism of
   normal curves has degree equal to the degree of the function-field extension). `x(P)` is a root
   of the polynomial whose roots are the `x`-coordinates of the points of exact order `N`. That
   polynomial has at most `#E[N]/2 ≤ N²/2` roots, so `d ≤ N²/2` (MC1, MC3a). The exact value
   `d = J₂(N)/2 = belyiDeg (Γ₁ N)` (for `N ≥ 3`) uses MC1' and is not needed.
2. **Belyi.** `j` is unramified over `ℙ¹ ∖ {0, 1728, ∞}`, since `E_j` has good reduction there and
   `E[N]` is étale in characteristic 0. So `j/1728` is a Belyi map defined over `ℚ` (MC5).
3. **Genus.** Riemann–Hurwitz for a Belyi map of degree `d`:
   `2g − 2 = −2d + (d − n₀) + (d − n₁) + (d − n_∞) = d − n₀ − n₁ − n_∞ ≤ d − 3`, so
   `g ≤ (d − 1)/2 < N²`. Here `n_•` counts the points over `0, 1, ∞`, each at least 1. Only the
   textbook Riemann–Hurwitz leaf MC5' is used. **The exact genus formula is not needed.**
4. **The group-theoretic layer (MC0a, done)** is the same computation in the monodromy model.
   `S`, `ST`, `T` are the monodromies over `j = 1728, 0, ∞`. `belyiDeg = μ`, and
   `genus Γ = 1 + μ/12 − ν₂/4 − ν₃/3 − ν∞/2` is Riemann–Hurwitz with `n_{1728} = ν₂ + (μ−ν₂)/2`,
   `n₀ = ν₃ + (μ−ν₃)/3`, `n_∞ = ν∞`. It becomes the genus of the algebraic `X₁(N)` once the
   monodromy of `j` is identified with the action of `SL₂(ℤ)` on `SL₂(ℤ)/±Γ₁(N)`. That
   identification is analytic (uniformization `Γ₁(N)\ℍ* ≅ X₁(N)(ℂ)`, Shimura 1971 §1.5, §6.7,
   UNVERIFIED) or algebraic (monodromy of `E[N]` over `ℚ̄(j)` is `SL₂(ℤ/N)`, plus MC0b). Either
   way it is optional for the project. MC0a's value is as an **acceptance test**: whatever `X₁(N)`
   and genus definitions the team builds, `g(X₁(N)) = genus (Γ₁ N)` must hold. The table in
   `genus_check.py` (`N ≤ 30`) is a ready-made test set for `decide`/`norm_num` computations.

---

## §8. Lean layer 0 (what compiles)

All in namespace `BPModCurves`, 1 130 lines in 5 files. Each file is checked with `lake env lean`
(exit 0, no errors, no warnings, no `sorry`). `#print axioms` gives `propext`, `Classical.choice`,
`Quot.sound` for every headline theorem (VERIFIED, `log.md` entries 11:45-12:20).

`scratch/bp-modcurves/Gamma1Genus.lean` (424 lines):

```lean
def pmSubgroup (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ)          -- ±Γ
abbrev Cosets (Γ) := SL(2, ℤ) ⧸ pmSubgroup Γ
noncomputable def belyiDeg (Γ) : ℕ := (pmSubgroup Γ).index
noncomputable def nu2 (Γ) : ℕ := Nat.card {x : Cosets Γ // S • x = x}
noncomputable def nu3 (Γ) : ℕ := Nat.card {x : Cosets Γ // (S * T) • x = x}
noncomputable def nuInf (Γ) : ℕ := Nat.card (orbitRel.Quotient (Subgroup.zpowers T) (Cosets Γ))
noncomputable def genus (Γ) : ℚ := 1 + belyiDeg Γ / 12 - nu2 Γ / 4 - nu3 Γ / 3 - nuInf Γ / 2
theorem nu2_Gamma1 (N : ℕ) (hN : 3 ≤ N) : nu2 (Gamma1 N) = 0
theorem nu3_Gamma1 (N : ℕ) (hN : 4 ≤ N) : nu3 (Gamma1 N) = 0
theorem genus_Gamma1 (N : ℕ) (hN : 4 ≤ N) :
    genus (Gamma1 N) = 1 + belyiDeg (Gamma1 N) / 12 - nuInf (Gamma1 N) / 2
theorem belyiDeg_Gamma1_le (N : ℕ) [NeZero N] : belyiDeg (Gamma1 N) ≤ N ^ 2
theorem genus_le (Γ) [Γ.FiniteIndex] : genus Γ ≤ 1 / 2 + belyiDeg Γ / 12
theorem genus_Gamma1_le (N : ℕ) [NeZero N] : genus (Gamma1 N) ≤ (N : ℚ) ^ 2
theorem index_Gamma1_le (N : ℕ) [NeZero N] : (Gamma1 N).index ≤ N ^ 2  -- copied from glue-assembly
def PrimVec (N : ℕ) := {v : ZMod N × ZMod N // ∃ x y : ZMod N, x * v.1 + y * v.2 = 1}
theorem exists_SL2_firstColMod (N : ℕ) [NeZero N] (v : ZMod N × ZMod N)
    (hv : ∃ x y : ZMod N, x * v.1 + y * v.2 = 1) : ∃ γ : SL(2, ℤ), firstColMod N γ = v
noncomputable def cosetEquivPrimVec (N : ℕ) [NeZero N] : SL(2, ℤ) ⧸ Gamma1 N ≃ PrimVec N
theorem index_Gamma1_eq_card (N : ℕ) [NeZero N] : (Gamma1 N).index = Nat.card (PrimVec N)
theorem two_mul_belyiDeg_Gamma1 (N : ℕ) (hN : 3 ≤ N) : 2 * belyiDeg (Gamma1 N) = Nat.card (PrimVec N)
example : (CongruenceSubgroup.Gamma1 5).index = 24   -- by decide
```

`scratch/bp-modcurves/TateNormalForm.lean` (162 lines):

```lean
def tateNF (b c : K) : WeierstrassCurve K := ⟨1 - c, -b, -b, 0, 0⟩
theorem exists_tateNF_coord [DecidableEq K] (W : WeierstrassCurve K) (x₀ y₀ : K)
    (heq : W.toAffine.Equation x₀ y₀) (h2 : y₀ ≠ W.toAffine.negY x₀ y₀)
    (h3 : W.toAffine.addX x₀ x₀ (W.toAffine.slope x₀ x₀ y₀ y₀) ≠ x₀) :
    ∃ (C : VariableChange K) (b c : K), C • W = tateNF b c ∧ C.r = x₀ ∧ C.t = y₀
theorem exists_tateNF [DecidableEq K] (W) (h : W.toAffine.Nonsingular x₀ y₀)
    (h2P : some h + some h ≠ 0) (h3P : some h + some h + some h ≠ 0) : ∃ C b c, …
theorem tateNF_unique (b c b' c' : K) (hb : b ≠ 0) (C : VariableChange K)
    (hC : C • tateNF b c = tateNF b' c') (hr : C.r = 0) (ht : C.t = 0) :
    C = 1 ∧ b = b' ∧ c = c'
theorem tateNF_Δ (b c : K) : (tateNF b c).Δ =
    b ^ 3 * (16 * b ^ 2 - 8 * b * c ^ 2 - 20 * b * c + b + c * (c - 1) ^ 3)
theorem tateNF_unique' (b c b' c' : K) [(tateNF b c).IsElliptic] (C) (hC) (hr) (ht) : C = 1 ∧ b = b' ∧ c = c'
```

(`C.r = x₀ ∧ C.t = y₀` says exactly that `C` sends `(x₀, y₀)` to `(0,0)`. Mathlib's change of
variables is `x = u²x' + r`, `y = u³y' + u²sx' + t`.)

`scratch/bp-modcurves/Jacobian.lean` (94 lines):

```lean
structure AbVar (K) [Field K]   -- copied from PkgI3.AbVar (proper, smooth, geometrically integral group scheme)
class IsCurve (X : Over (Spec (CommRingCat.of K))) : Prop  -- proper, SmoothOfRelativeDimension 1, GeometricallyConnected
structure IsJacobian (X) (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) (J : AbVar K) (aj : X ⟶ J.X) : Prop where
  base : P₀ ≫ aj = η[J.X]
  univ : ∀ (A : AbVar K) (f : X ⟶ A.X), P₀ ≫ f = η[A.X] → ∃! φ : J.X ⟶ A.X, IsMonHom φ ∧ aj ≫ φ = f
def JacobianExists (K) [Field K] : Prop      -- leaf MC6' (statement only)
theorem IsJacobian.unique (h : IsJacobian X P₀ J aj) (h' : IsJacobian X P₀ J' aj') :
    ∃ e : J.X ≅ J'.X, IsMonHom e.hom ∧ aj ≫ e.hom = aj' ∧ ∀ φ, IsMonHom φ → aj ≫ φ = aj' → φ = e.hom
noncomputable def jacobian (hJ : JacobianExists K) (X) [IsCurve X] (P₀) : AbVar K
```

`scratch/bp-modcurves/ModularCurveDefs.lean` (99 lines):

```lean
abbrev Qj := RatFunc ℚ
noncomputable def Ej : WeierstrassCurve Qj := ofJNe0Or1728 (RatFunc.X : Qj)
instance : Ej.IsElliptic
theorem Ej_j : Ej.j = RatFunc.X
noncomputable def EjBar : WeierstrassCurve Kbar := Ej.baseChange Kbar     -- Kbar = AlgebraicClosure Qj
noncomputable def fieldX1 (P : EjBar.toAffine.Point) : IntermediateField Qj Kbar := Qj⟮xCoord P⟯
noncomputable def Y1j (P) : Scheme := (Spec.map (CommRingCat.ofHom (jLineToField P))).normalization
noncomputable def jMap (P) : Y1j P ⟶ Spec (CommRingCat.of (Polynomial ℚ))
def TorsionCardLe : Prop      -- MC3a, open
def FieldX1DegreeLe : Prop    -- MC1 bound, open
def FieldX1Degree : Prop      -- MC1', leaf (2·[K_N:ℚ(j)] = #PrimVec N)
```

`scratch/bp-modcurves/AnalyticModuli.lean` (351 lines):

```lean
def lat (τ : ℂ) : Set ℂ := {z | ∃ m n : ℤ, z = m * τ + n}
def jfac (γ : SL(2, ℤ)) (τ : ℂ) : ℂ := (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)
theorem lattice_homothety (γ : SL(2, ℤ)) (τ : ℍ) : (fun z => jfac γ τ * z) '' lat (γ • τ : ℍ) = lat τ
theorem point_preserved_iff (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (τ : ℍ) :
    jfac γ τ * (1 / N) - 1 / N ∈ lat τ ↔ γ ∈ Gamma1 N
theorem exactOrder (N : ℕ) [NeZero N] (τ : ℍ) (k : ℤ) : (k : ℂ) * (1 / N) ∈ lat τ ↔ (N : ℤ) ∣ k
theorem exists_SL2_of_homothety (τ τ' : ℍ) (α : ℂ) (h : (fun z => α * z) '' lat τ' = lat τ) :
    ∃ γ : SL(2, ℤ), (τ' : ℂ) = (γ • τ : ℍ) ∧ α = jfac γ τ
theorem pair_iso_iff (N : ℕ) [NeZero N] (τ τ' : ℍ) :
    (∃ α : ℂ, (fun z => α * z) '' lat τ' = lat τ ∧ α * (1 / N) - 1 / N ∈ lat τ) ↔ ∃ γ ∈ Gamma1 N, τ' = γ • τ
theorem exists_normalize (N : ℕ) [NeZero N] (τ : ℍ) (c d : ℤ)
    (hv : ∃ x y : ZMod N, x * c + y * d = 1) : ∃ γ : SL(2, ℤ), jfac γ τ * (1 / N) - (c * τ + d) / N ∈ lat τ
```

Faithfulness notes:
- `genus Γ` is a **definition by formula**. It is the genus of `X_Γ` only after the monodromy
  identification of §7.4. In the project it should be used as an acceptance test, never as the
  definition of the genus of `X₁(N)` in a leaf. Its integrality is not claimed.
- `tateNF_unique` assumes `b ≠ 0`; `tateNF_unique'` derives it from `IsElliptic` through `tateNF_Δ`.
- `IsJacobian` quantifies over all abelian varieties in the same universe. `IsJacobian.unique` is
  its acceptance test: a universal property quantifying over too few targets would still be
  unique, but then `JacobianExists` would be a stronger statement than Milne's, so the leaf
  writer must check that `AbVar` is the standard notion (it is, up to the smooth/geometrically
  integral packaging). `JacobianExists` must appear as an explicit hypothesis of the main theorem.
- `Y1j P` depends on the choice of `P`. Different `P` of exact order `N` give `ℚ(j)`-conjugate
  fields (by MC1'), hence isomorphic schemes over the `j`-line. `fieldX1 P` with `P = 0` is the
  junk value `ℚ(j)`.

---

## §9. Proposed next-layer Lean statements (signatures, not compiled)

These are the remaining targets, written against Mathlib v4.35 names, and SPECULATIVE until
compiled. The compiled ones are in §8.

```lean
-- point transport under a change of variables (needed for MC2c)
def VariableChange.mapPoint (C : VariableChange K) : W.toAffine.Point ≃+ (C • W).toAffine.Point

-- MC2c: Y₁(N) at the level of points (N ≥ 4)
def Y1Points (K) [Field K] (N : ℕ) : Type _ :=
  Quot (fun (p q : Σ W : WeierstrassCurve K, W.toAffine.Point) =>
    ∃ C : VariableChange K, C • p.1 = q.1 ∧ C.mapPoint p.2 = q.2)  -- restricted to IsElliptic, addOrderOf = N
theorem Y1Points_equiv (N : ℕ) (hN : 4 ≤ N) :
    Y1Points K N ≃ {bc : K × K // (tateNF bc.1 bc.2).Δ ≠ 0 ∧ addOrderOf (origin bc) = N}

-- MC0b, last step: #PrimVec N = J₂(N) = N² ∏_{p | N} (1 − p⁻²)
theorem card_primVec (N : ℕ) [NeZero N] : Nat.card (PrimVec N) = N ^ 2 * ∏ p ∈ N.primeFactors, (1 - 1 / p ^ 2 : ℚ)

-- MC4 proper model: glue Y1j with the chart over Spec ℚ[1/j]; then
instance : IsProper (X1 N).hom;  instance : SmoothOfRelativeDimension 1 (X1 N).hom;  GeometricallyConnected (X1 N).hom

-- MC5
theorem finite_jMap : IsFinite (jMap P)   -- integral + finite type (Noether normalization finiteness)
theorem jMap_etale_away : ∀ x, jMap P x ∉ {0, 1728} → IsEtaleAt …

-- MC7 (leaf, §6): over IsJacobian (X1 N) cusp J aj, HSyn.CF, PkgI3.AbVar.V
```

---

## §10. Risks and open checks

1. **R18's "genus" and "Jacobian" must be the same objects as E2's `g = dim J` and G17's `J₁(N)`.**
   With route (A) this is MC6's `dim J = g`. If R18 is stated over Anthropic-FLT-style `genusFF`,
   the bridge `genusFF = dim H⁰(Ω)` is an extra node.
2. **Model of `X₁(N)` over `ℚ`** (§4 notes): fix one model for MC1, R16 and the cusp `P₀`.
   Shimura's statements are for his canonical model, which uses `(E, ±P)` conventions close to
   the `μ_N` model in some references (UNVERIFIED). Since `J₁(N)` is the same up to
   `ℚ`-isomorphism in both models, G13 is unaffected, but R16's text must say which model it is
   about.
3. **Smoothness of the normalization** in MC4: Mathlib has normality and the relative
   normalization. "Normal + dimension 1 ⇒ regular ⇒ smooth over `ℚ`" needs "regular ⇒ smooth over
   a perfect field", which I did not find (grep `Smooth` with `IsRegular`: not checked in detail).
   Possibly large.
4. **MC3a** (size of `E[N]`): if neither Tau Ceti nor Anthropic FLT proves it in usable form, the
   division-polynomial route needs the multiplication formula `x(nP) = φ_n/ψ_n²`, which is absent
   from Mathlib. Mathlib has `ψ_n`, `φ_n` and their degrees, but not their relation to `n • P`
   (grep for `nsmul` next to `ψ`: none). Medium-large.
5. **Faltings height** (WP10) is outside this blueprint. R18 cannot be stated without it, whatever
   is built here.
6. The cost estimates are SPECULATIVE. The other-library claims are from file names (prereq-survey).

---

## §11. Work packages

| WP | Nodes | Depends on | Tier | Deliverable |
| --- | --- | --- | --- | --- |
| MC-a | MC0b (last step), MC0c | layer 0 | small-medium | `#PrimVec N = J₂(N)` (the coset bijection is done); `nuInf = #CuspOrbits`; closed cusp formula; `decide` checks against `genus_check.py` |
| MC-b | point transport under `VariableChange`, MC2c, `⟨d⟩` on `Y₁(N)` | layer 0 (`tateNF_Δ` done) | medium | `VariableChange.mapPoint` as an additive equivalence; `Y1Points_equiv` |
| MC-c | MC3a, MC1 | Tau Ceti / FLT torsion or the multiplication formula | medium-large | proofs of `TorsionCardLe`, `FieldX1DegreeLe` (definitions `Ej`, `fieldX1` done) |
| MC-d | MC4, MC5 | MC-c | large | from the compiled chart `Y1j`: the proper `X1 N`, smooth and geometrically connected; `j` finite, Belyi, `deg j ≤ N²` |
| MC-e | statements of MC5' (Riemann–Hurwitz, over a genus definition) and `dim J = g`; fold `IsJacobian`, `JacobianExists`, `FieldX1Degree` into `Leaves.lean` | `Jacobian.lean`, `ModularCurveDefs.lean` (done) | small | leaf Props over genuine definitions |
| MC-f | MC7 (R16 existential), G13 from it | MC-d, MC-e, `HSyn.CF` | small-medium | R16 stated over genuine definitions in `Leaves.lean`; G13 proved from it |
| MC-g | MC8 (optional) | MC-d, Vélu | very large | Hecke correspondences on `J₁(N)` |
