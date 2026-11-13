# bp-analytic: formalization blueprint for the analytic uniformization of abelian varieties

Status: research note and blueprint (task bp-analytic, 2026-11-12), written for a crowdsourced
Lean team. Lean files, compiled and sorry-free: `scratch/bp-analytic/Torus.lean` (about 880
lines) and `scratch/bp-analytic/Uniformization.lean` (about 140 lines). Mathlib only; no project
imports. Results log: `scratch/bp-analytic/log.md`. No file under `ZInQKernel/` or `blueprint/`,
and no other task's notes or scratch files, was edited. Definitions copied from
`ZInQKernel/HDecomp/Objects.lean` and `scratch/pkg-I1/I1.lean` are marked "copied" in the Lean
files.

Marks:
- **VERIFIED**: read in a source in the repository or in Mathlib, computed, or compiled.
- **STANDARD**: a published result with a reference.
- **SPECULATIVE**: an estimate or a proposal.
- **UNVERIFIED**: a locator recalled from memory (there was no network access).
- **BUILT**: compiled in `scratch/bp-analytic/`, with `#print axioms` giving only `propext`,
  `Classical.choice`, `Quot.sound`.

The node is shared by three blueprints: AN3 of `bp-faltings.md` (archimedean term of the Faltings
height), N14/R1an of `bp-qmmoduli.md` (F1's theta form), and the leaves R22, T11, T12 of
`h-decomposition.md`.

## 0. Main result

1. **The uniformization does not block anyone: it can be stated today as one leaf, over genuine
   objects, with no analytification.** `UniformizationLeaf A` (`Uniformization.lean`, compiled)
   says that for an abelian variety `A/ℂ` (the project's `AbVar`, copied from `Objects.lean`)
   there are:
   - a full lattice `Λ ⊂ ℂ^g`;
   - a group isomorphism `φ : ℂ^g/Λ ≃ A(ℂ)`, where `A(ℂ)` is Mathlib's group of `ℂ`-points
     `Spec ℂ ⟶ A`;

   such that:
   - (i) every regular function `f ∈ Γ(U, 𝒪_A)` on a Zariski open `U` pulls back to an analytic
     function on the open set `φ⁻¹(U)`;
   - (ii) at every point, some `g` regular functions pull back to a local biholomorphism.

   Conditions (i) and (ii) characterize the analytic structure of `A(ℂ)`: it is the unique one in
   which regular functions are holomorphic and étale coordinates are charts. So the leaf is
   "`A(ℂ) ≅ ℂ^g/Λ` as complex Lie groups", i.e. Mumford, *Abelian varieties*, §1 applied to
   `A^an` (STANDARD; locators UNVERIFIED, §6). It is a consequence of the published statement
   and is not stronger.
   - Every consumer can build its glue against this leaf now (§1).
   - Its proof, the actual analytification, is the XL work package of §2-§3.
2. **The first concrete layer is built (VERIFIED: compiled, standard axioms only).**
   `Torus.lean` constructs the target of the uniformization and the analytic objects the
   consumers use:
   - **Compact complex tori as complex Lie groups.** For a discrete `Λ` in a complex normed
     space `E`, `E/Λ` is an analytic manifold (`IsManifold 𝓘(ℂ, E) ω`) and an analytic Lie group
     (`LieAddGroup 𝓘(ℂ, E) ω`). It is connected, and compact when `Λ` is a full lattice. This is
     the `IsManifold` instance listed as a TODO in Mathlib's
     `Geometry/Manifold/Instances/Quotient.lean` (VERIFIED, read).
   - **The exponential.** `torusExp : E →+ E/Λ`; its source is
     `AddGroupLieAlgebra 𝓘(ℂ, E) (E/Λ)`, which is `E` by `rfl`. It is surjective and analytic,
     with kernel exactly `Λ` (the period lattice is the kernel of the exponential), and its
     one-parameter subgroups are analytic.
   - **Liouville on tori.** Holomorphic functions on `E/Λ` are constant.
   - **Descent.** A map out of `E/Λ` is analytic iff its composite with the projection is.
   - **Changes of coordinates.** A `ℂ`-linear `T` with `T(Λ) = Λ'` gives a biholomorphic group
     isomorphism `E/Λ ≃ E'/Λ'` (`torusDiffeo`, a Mathlib `Diffeomorph` of class `ω`).
   - **Period matrices.** For `det Im Ω ≠ 0`, in particular `Ω ∈ 𝔥_g`, `Ωℤ^g + ℤ^g` is a full
     lattice (`periodLattice`). Conversely, independence of its generators forces
     `det Im Ω ≠ 0`.
   - **Theta functions.** Riemann's `θ(z, Ω)` is quasi-periodic under `Ωℤ^g + ℤ^g` (it is a
     section of a line bundle on `ℂ^g/Λ_Ω`). Moreover pkg-I1's theta constants `thetaConst m Ω`
     (copied verbatim) equal `exp(…)·θ(Ω a/2 + b/2, Ω)`, the values of `θ` at the 2-torsion
     points of `ℂ²/Λ_Ω` (`thetaConst_eq_riemannTheta`, `two_nsmul_proj_charPoint`). These
     identities are proved for `tsum` by reindexing, so they need no convergence hypothesis.
   - **pkg-I1's period matrix is a period matrix (F1's torus side).** For `Im τ ≠ 0`:
     - `Λ_τ = ι(𝒪)(τ,1)ᵀ` is a full lattice in `ℂ²`;
     - `F'(τ) = F₀(τ)P⁻¹` is invertible and carries `Ω(τ)ℤ² + ℤ²` onto `Λ_τ`;
     - hence `det Im Ω(τ) ≠ 0`, and `ℂ²/Λ_{Ω(τ)} ≃ ℂ²/Λ_τ` biholomorphically as groups
       (`qmPeriodDiffeo`).

     pkg-I1 §4 had stated "`Ω(τ)` is a period matrix of `(ℂ²/Λ_τ, E)`" from numerical checks
     (pkg-I1.md, "Faithfulness"). The lattice and torus part is now a theorem; the polarization
     part is not treated here.
3. **What each consumer needs (§1).** None of them needs the analytification of a general scheme.
   - **The Faltings height (AN3)** needs only the period lattice `Λ_σ ⊂ Lie(A_σ)` and the
     identification of `η ∈ ω_A` with `c·dz₁∧⋯∧dz_g`. bp-faltings' `torusMetricSq Λ c` is already
     `|c|²·covol(Λ)`.
     - In period-matrix terms the archimedean term is `|c|²·|det Ω₂|²·det Im Ω` for a normalized
       period matrix `Ω = Ω₂⁻¹Ω₁` (STANDARD; the Lean proof of `covol(Ωℤ^g + ℤ^g) = det Im Ω` is
       the M-size node P3, not built).
     - The integral over `A(ℂ)` is therefore expressible through a period matrix alone. Defining
       that period matrix from `A` still needs `Λ_σ`, i.e. the leaf.
   - **F1 (R1an)** needs, for one `σ`, an `𝒪`-equivariant `A_σ(ℂ) ≅ ℂ²/Λ_τ`. Over the leaf this
     is glue: endomorphisms act linearly (node T2), a rank-one `𝒪`-lattice is `ι(𝒪)v`
     (bp-qmmoduli's lattice algebra), and `qmPeriodDiffeo` (built). The theta side of F1 is now
     proved. One input is **not** part of AN3 and is flagged here: the analytic uniformization of
     the Shimura curve itself (holomorphy of `τ ↦ π(A_τ)`), which bp-qmmoduli's glue "two
     Hauptmoduln with the same three values coincide" uses (§1.2).
   - **R22, T11, T12**: §1.3-§1.5. T12 and the theta structure of R22 reduce to the leaf plus
     elementary glue. T11 needs, besides the leaf, a separate GAGA-type leaf (holomorphic maps of
     abelian varieties are algebraic).
4. **Sizes (SPECULATIVE, Lean lines).**
   - The proof of the leaf from Mathlib is about 15-30k lines. That agrees with bp-faltings' AN3
     estimate.
   - The largest parts are compactness of `X(ℂ)` for proper `X` (XL, A4) and the manifold
     structure on `X(ℂ)` for smooth `X` (L, A2).
   - The Lie-theory step "compact connected commutative complex Lie group ⇒ `ℂ^g/Λ`" is L
     (A5). Its last step (`ℂ^g/Λ` is such a group, with exponential and kernel `Λ`) is built
     here.
   - The consumer glue over the leaf is S-M per item.

## 1. What each consumer needs

### 1.1 Faltings height (bp-faltings AN3, used by M4/H1/H2)

- **Used:** for each `σ : L → ℂ`, a lattice `Λ_σ` in `Lie(A_σ) ≅ ℂ^g`, and, for `η ∈ ⋀^g ω_A`,
  the constant `c_σ(η)` with `φ^*η = c_σ(η)·dz₁∧⋯∧dz_g`. Then
  `(i/2)^g ∫_{A_σ(ℂ)} η∧η̄ = |c_σ(η)|²·covol(Λ_σ)` (bp-faltings AN1, BUILT there as
  `torusMetricSq_eq_setIntegral`).
- **Not used:** the complex-manifold structure of `A_σ(ℂ)` beyond the leaf, GAGA, Néron models.
- **Period-matrix form (the "integral through a period matrix alone").** Choose a basis
  `ω₁…ω_g` of `H⁰(A_σ, Ω¹)` and a `ℤ`-basis `γ₁…γ_{2g}` of `Λ_σ = H₁(A_σ(ℂ), ℤ)`. Put
  `Π = (∫_{γ_j} ω_i) = (Ω₁ | Ω₂)`, a `g × 2g` matrix. In the coordinates `z_i` dual to `ω_i`,
  `Λ_σ = Πℤ^{2g}` and `covol(Λ_σ) = |det(Π; Π̄)|/2^g = |det Ω₂|²·det Im(Ω₂⁻¹Ω₁)` (STANDARD; Riemann
  bilinear relations for the sign). With `η = ω₁∧⋯∧ω_g` one gets `c = 1`. So the archimedean
  term is a function of the period matrix only.
  - In Lean: `periodLattice Ω` (BUILT) is `Ωℤ^g + ℤ^g`, `torusDiffeo` (BUILT) handles the
    rescaling by `Ω₂`, and bp-faltings' `torusMetricSq_comap` handles the determinant factor.
    Node P3 (`covol(Ωℤ^g+ℤ^g) = |det Im Ω|`) closes the formula.
- **What still needs the leaf:** to *define* `Λ_σ` (or `Π`) from `A` one needs `H₁(A_σ(ℂ))` or
  `ker exp`, i.e. AN3. Algebraic substitutes do not give the integral lattice: the Tate module
  gives `Λ ⊗ ℤ_ℓ`, and algebraic de Rham cohomology gives `Λ ⊗ ℂ` without `Λ`.
- **Glue over the leaf (node A6, S-M).** The tangent identification.
  - `dφ₀ : ℂ^g → T_eA_σ` sends `v` to the derivation `f ↦ D(f∘φ∘proj)(0)·v`.
  - It is defined because of (i), and it is an isomorphism because of (ii).
  - Hence `c_σ(η) = η(dφ₀e₁, …, dφ₀e_g)` for `η` in bp-faltings' AV3 cotangent model `𝔪/𝔪²`.

### 1.2 F1 (bp-qmmoduli R1an)

- **Used (bp-qmmoduli §2.3, VERIFIED read):** for `K ⊆ ℂ` and `P : QML3 K` there are
  `τ ∈ ℍ^±` and an `𝒪`-equivariant isomorphism of complex Lie groups `P.A(ℂ) ≅ ℂ²/ι(𝒪)(τ,1)ᵀ`,
  carrying the polarization to `±E₀`.
- **Over the leaf this is glue (M), in four steps:**
  1. Each `α ∈ End(A)` becomes, via (i)-(ii), a holomorphic group endomorphism of `ℂ²/Λ`. By
     node T2 it is induced by a `ℂ`-linear `T_α` with `T_αΛ ⊆ Λ`. This gives an embedding
     `𝒪 → End(ℂ², Λ)`.
  2. `Λ` is then a torsion-free `𝒪`-module of `ℤ`-rank 4, i.e. a locally free right ideal class
     of `𝒪`, hence free of rank one: `Λ = ι(𝒪)v` for some `v`, after a choice of `ι` (Eichler:
     maximal orders of indefinite quaternion algebras over `ℚ` have one ideal class, STANDARD,
     locator UNVERIFIED). Scaling `v` to `(τ, 1)ᵀ` gives `τ ∉ ℝ`.
  3. **BUILT:** `qmPeriodDiffeo` identifies `ℂ²/Λ_τ` with `ℂ²/Λ_{Ω(τ)}`.
     `thetaConst_eq_riemannTheta` identifies pkg-I1's ten theta constants at `Ω(τ)` with values
     of `θ` at the 2-torsion points of that torus.
  4. Polarization: bp-qmmoduli's `eq_pm_E0_of_principal` (done there) gives `±E₀`.
- **Not part of AN3.** bp-qmmoduli derives `π(P) = j_θ(Ω(τ))` from "two holomorphic
  Hauptmoduln of `Γ*\ℍ` with the same values at three points coincide". That step needs
  `τ ↦ π(A_τ)` to be holomorphic on `ℍ`, i.e. the complex uniformization
  `Y₃(ℂ) ≅ Γ\ℍ^±×(finite)` of the Shimura curve as analytic spaces. That is a family statement
  (pkg-I1 I1-a item 1; part of R1), not a statement about one `A`. SPECULATIVE reading: R1an as
  written in bp-qmmoduli quantifies over single `P`, so this family input should be added to R1an
  or kept in R1. Flagged for the bp-qmmoduli owner.
- **Weaker statements suggested by the task.** "The explicit theta functions on the Siegel space
  that pkg-I1 defines" are now tied to the torus (§0 item 2). F1 still needs some `A ↦ Ω`. That
  map cannot be defined without `Λ_σ`, i.e. without the leaf.

### 1.3 R22 (Pazuki's theta height)

- **Used:** for a principally polarized abelian surface `A/K` and `σ`, a period matrix
  `Ω_σ ∈ 𝔥₂`, and the theta constants `θ[a,b](Ω_σ)` up to the action of `Sp₄(ℤ)` (Pazuki's
  Def. 2.6, locator in h-decomposition R22, VERIFIED read there).
- **Over the leaf:** the leaf gives `Λ_σ`. The polarization gives a Riemann form with a
  symplectic basis, hence `Ω_σ ∈ 𝔥₂` (node P4, M, Riemann bilinear relations; Tau Ceti proves
  "Riemann forms = polarizations of weight-one Hodge structures", prereq-survey A9, not
  re-checked). The theta constants are `thetaChar` (BUILT), equal to pkg-I1's `thetaConst`.
- **Missing beyond AN3:** the Faltings height (bp-faltings) and the theta-height normalization.

### 1.4 T11 (Riemann/GAGA/rigidity)

- **Used (h-decomposition §2.2, VERIFIED read):** `End⁰(A_ℂ)` = Hodge endomorphisms, and
  `Hom_ℚ̄ = Hom_ℂ`.
- **Statable over the leaf:** `End(A_ℂ) → End_ℂ(ℂ^g) ∩ End(Λ)` (from T2) is a bijection.
  - Injectivity is glue.
  - Surjectivity says that every holomorphic endomorphism of `A(ℂ)` is algebraic. That is
    GAGA/Chow (Serre 1956; UNVERIFIED locator), a **separate leaf**, not a consequence of AN3.
- `Hom_ℚ̄ = Hom_ℂ` is algebraic (rigidity and spreading out) and needs no analytification.

### 1.5 T12 (Artin comparison with complex conjugation)

- **Used (G10, h-decomposition):** complex conjugation `c` acts on `T_ℓA` with determinant
  `(−1)^g` (oddness of `r_ℓ`).
- **Over the leaf, elementary glue (M):**
  - `A(ℂ)[n] = φ((1/n)Λ/Λ)`, since `φ` is a group isomorphism and the torsion of `ℂ^g/Λ` is
    `(1/n)Λ/Λ`, so `T_ℓA ≅ Λ ⊗ ℤ_ℓ`.
  - For `A` defined over `ℝ`, `c` is antiholomorphic on `A(ℂ)`: by (i), `f∘c = conj∘f^c` for
    regular `f`. It lifts to an `ℝ`-linear antilinear involution of `ℂ^g` preserving `Λ` (the
    antiholomorphic analogue of T2).
  - An antilinear involution has eigenvalues `±1` with multiplicity `g` each, so
    `det(c | Λ⊗ℚ) = (−1)^g`.
- No étale cohomology is needed in this use: T10 already turns `H¹_et` into `T_ℓ`.

### 1.6 Summary

| Consumer | Needs the leaf | Needs more | Built here for it |
| --- | --- | --- | --- |
| AN3 (Faltings) | yes, to define `Λ_σ` and `c_σ(η)` | A6 (tangent glue), P3 (covolume) | torus, `periodLattice`, `torusDiffeo` |
| R1an (F1) | yes | T2, lattice algebra, and the Shimura-curve family uniformization (not AN3) | `qmLattice`, `qmPeriodDiffeo`, `thetaConst_eq_riemannTheta` |
| R22 | yes | P4 (polarization ⇒ `𝔥₂`), Faltings height | `thetaChar`, `riemannTheta_add_period` |
| T11 | yes | T2, a GAGA leaf | `torusDiffeo` |
| T12 | yes | torsion and conjugation glue | `proj`, `torusExp`, `ker_torusExp` |

## 2. Dependency graph

Tiers (SPECULATIVE, Lean lines): **S** ≤ 300, **M** 300-2 000, **L** 2 000-10 000,
**XL** > 10 000. Status: **Mathlib** (VERIFIED in `.lake/packages/mathlib` v4.35 unless marked),
**BUILT** (here), **lit** (literature only), **absent** (searched, not found).

```
 Mathlib: manifolds, LieAddGroup, GroupLieAlgebra, covering maps, ZLattice/ZSpan,
          analytic inverse function thm, schemes, ValuativeCriterion, AlgClosed points
   │
   ├── T1 torus E/Λ: manifold, Lie group, compact, exp, Liouville  [BUILT]
   │      ├── T2 holomorphic homs of tori are linear  (M)
   │      ├── P1 period lattice Ωℤ^g+ℤ^g  [BUILT]   P2 theta quasi-periodicity [BUILT]
   │      ├── P3 covol(Ωℤ^g+ℤ^g) = |det Im Ω|  (M)   P4 polarization ⇒ Ω ∈ 𝔥_g (M)
   │      └── Q1 QM lattice ι(𝒪)(τ,1)ᵀ ≅ Siegel lattice of Ω(τ)  [BUILT]
   │
   ├── A1 analytic topology on X(ℂ), X loc. finite type over ℂ  (M-L)
   │      └── A2 complex manifold structure on X(ℂ), X smooth  (L)
   │             └── A3 morphisms holomorphic; G(ℂ) complex Lie group  (M)
   ├── A4 X proper ⇒ X(ℂ) compact  (XL);  A4' X geom. integral ⇒ X(ℂ) connected  (L)
   └── A5 compact connected commutative complex Lie group ≅ Lie(G)/Λ  (L)
                │
   LEAF  UniformizationLeaf A  (stated, BUILT as a Prop)  ◄── proof: A1-A5 + T1
                │
   consumer glue: A6 tangent/η ↦ c·dz (S-M), T2-based End action (M), torsion/conjugation (M)
                │
   AN3 (bp-faltings) · R1an (bp-qmmoduli) · R22 · T11 (+ GAGA leaf) · T12
```

### 2.1 Mathlib foundations (VERIFIED)

| Node | Content | Where |
| --- | --- | --- |
| M-man | `ChartedSpace`, `IsManifold I n` with `n = ω` the analytic groupoid, `isManifold_of_contDiffOn`, `contMDiffOn_chart`, `ContMDiffAt.comp`, products of manifolds | `Geometry/Manifold/ChartedSpace.lean`, `IsManifold/Basic.lean`, `ContMDiff/*` |
| M-lie | `LieAddGroup I n G`, `ContMDiffAdd`; `GroupLieAlgebra` / `AddGroupLieAlgebra` (tangent space at `1`, with the Lie bracket of invariant vector fields) | `Geometry/Manifold/Algebra/LieGroup.lean`, `GroupLieAlgebra.lean` |
| M-quot | `ChartedSpace` on quotients by free properly discontinuous actions (TODO there: `IsManifold`); `AddSubgroup.isAddQuotientCoveringMap_of_comm` (quotient by a discrete subgroup is a covering); `IsLocalHomeomorph.localInverseAt` | `Geometry/Manifold/Instances/Quotient.lean`, `Topology/Covering/Quotient.lean`, `Topology/IsLocalHomeomorph.lean` |
| M-lift | lifting of maps from simply connected spaces through coverings (`IsCoveringMap.existsUnique_continuousMap_lifts`) | `Topology/Homotopy/Lifting.lean` |
| M-cpx | Liouville on compact complex manifolds (`MDifferentiable.exists_eq_const_of_compactSpace`), maximum modulus on manifolds | `Geometry/Manifold/Complex.lean` |
| M-ana | analytic inverse function theorem (`OpenPartialHomeomorph.analyticAt_symm`, with `HasStrictFDerivAt.toOpenPartialHomeomorph`); implicit function theorem (`HasStrictFDerivAt.implicitFunction`); `AnalyticAt`/`AnalyticOnNhd` in several variables | `Analysis/Calculus/FDeriv/Analytic.lean`, `Analysis/Calculus/Implicit.lean` |
| M-ode | integral curves: local existence/uniqueness, global existence with uniform time (`exists_isMIntegralCurve_of_isMIntegralCurveOn`); **real** manifolds only | `Geometry/Manifold/IntegralCurve/*` |
| M-lat | `ZLattice`, `IsZLattice`, `ZSpan.fundamentalDomain`, `fract`, `floor`, `Basis.ofZLatticeBasis(_span)`, `Basis.parallelepiped` (compact), `ZLattice.covolume`, `ZSpan.measure_fundamentalDomain` (`= |b₀.det b|·μ(F b₀)`) | `Algebra/Module/ZLattice/*`, `MeasureTheory/Measure/Haar/OfBasis.lean` |
| M-ag | schemes, `Over`, `GrpObj`, `IsProper`, `Smooth`, `ValuativeCriterion` (and `UniversallyClosed.eq_valuativeCriterion`), `Proj` separated/proper, `pointEquivClosedPoint` (closed points = `k`-points over `k = k̄`), `smooth_of_grpObj`, commutativity of abelian varieties | `AlgebraicGeometry/*` |
| M-hom | singular homology (`AlgebraicTopology/SingularHomology/Basic.lean`) | (route to `H₁(A(ℂ),ℤ) ≅ Λ`, not needed if `Λ := ker exp`) |

**Absent from Mathlib v4.35** (searched): analytification or an analytic topology on `X(ℂ)`;
Hartogs/Osgood (no file mentions them); the exponential map of a Lie group; holomorphic ODE or
complex flows; an API restricting a complex manifold to a real one, needed to use M-ode on a
complex Lie group (only internal `NormedSpace.restrictScalars` uses found in `IsManifold/Basic`);
Chow's lemma; GAGA; projective space as a manifold.

### 2.2 Nodes

| Node | Statement | Tier | Status / cheapest faithful route |
| --- | --- | --- | --- |
| T1 | `E/Λ` (Λ discrete) is an analytic manifold and Lie group, connected; compact if Λ is full; `exp = proj` with kernel Λ; descent of analytic maps; Liouville; linear isos give biholomorphic group isos | M | **BUILT** (`Torus.lean` §1-3, §6). Route: charts are the local inverses of the covering `proj`; transition maps are locally translations by lattice vectors (`eventuallyEq_add_const`, from discreteness), so analytic |
| T2 | A holomorphic group homomorphism `f : V/Λ → V'/Λ'` is induced by a `ℂ`-linear `T` with `TΛ ⊆ Λ'` | M | Route: lift `f∘proj` through the covering `proj'` (M-lift; `V` is simply connected); `F(x+y) − F(x) − F(y) ∈ Λ'` is continuous in `(x, y)` and so constant, hence `F` is additive and continuous, hence `ℝ`-linear; holomorphic implies `ℂ`-linear. The antiholomorphic variant (for T12) gives antilinear `T` |
| P1 | `Ωℤ^g + ℤ^g` is a full lattice iff `det Im Ω ≠ 0` | S | **BUILT** (`periodVec_linearIndependent`, `det_im_ne_zero_of_linearIndependent`, `periodLattice`) |
| P2 | `θ(z + Ωm + n) = e(−½mᵀΩm − mᵀz)θ(z)`; `θ[c,d](Ω) = e(½cᵀΩc + cᵀd)·θ(Ωc + d)` | S | **BUILT** (`riemannTheta_add_period`, `thetaChar_eq`; no convergence needed) |
| P3 | `covol(Ωℤ^g + ℤ^g) = |det Im Ω|` for Lebesgue measure on `ℂ^g` | M | Route: `ZSpan.measure_fundamentalDomain` with `b₀` the standard real basis `(e_j, i e_j)`; its fundamental domain has volume 1 (via `Complex.volume_preserving_equiv_pi`, UNVERIFIED name); the coordinate matrix of `periodBasis` in `b₀` is `[[Re Ω, I], [Im Ω, 0]]` up to a permutation, with `|det| = |det Im Ω|` (block determinant). For `g = 1` bp-faltings has `PeriodPair.covolume_lattice1` |
| P4 | A principal polarization (positive unimodular Riemann form `E` on Λ, `E(iu, iv) = E(u, v)`) gives a symplectic basis in which the period matrix lies in `𝔥_g` | M | Route: symplectic basis of a unimodular alternating `ℤ`-form (Frobenius normal form, M), then Riemann's bilinear relations (S given the basis). Tau Ceti (prereq-survey A9) has Riemann forms = polarizations (not re-checked) |
| Q1 | pkg-I1: `Λ_τ = ι(𝒪)(τ,1)ᵀ` is a full lattice and `F'(τ)` maps `Ω(τ)ℤ² + ℤ²` onto it, for `Im τ ≠ 0` | S | **BUILT** (`qmLattice`, `map_periodLattice_Omega`, `qmPeriodDiffeo`). Symmetry of `Ω(τ)` and `Im Ω(τ) > 0` for `Im τ > 0`: VERIFIED by sympy only (`det Im Ω(x+iy) = 12y²/(((x−3)²+y²)((x+1)²+y²))`); in Lean they follow from P4 with N5's Riemann form, or by direct computation (S-M) |
| A1 | Analytic topology on `X(ℂ)` for `X` locally of finite type over `ℂ` | M-L | Cheapest faithful definition: the coarsest topology for which every `{P ∈ U}` (`U` Zariski open) is open and every `evalAt U f` is continuous on it (the "function topology"; `evalAt` is BUILT in `Uniformization.lean`). Then prove that on an affine `U ↪ 𝔸^n` it is the subspace topology of `ℂ^n` (M). Points: Mathlib's `Spec ℂ ⟶ X`, or closed points via `pointEquivClosedPoint` |
| A2 | For `X` smooth of relative dimension `g`, `X(ℂ)` is a complex manifold, with charts given by `g` local parameters | L | Route: at a point, choose `f₁…f_g` whose differentials span `𝔪/𝔪²` (algebraic: smoothness, bp-faltings AV3); on an affine chart `U = V(h₁…h_r) ⊂ ℂ^n` the Jacobian criterion and the analytic inverse function theorem (M-ana) make `(f_i)` a local biholomorphism onto an open subset of `ℂ^g`; transition maps are analytic because they are again regular functions. Main cost: the Jacobian criterion for smooth `ℂ`-algebras (Mathlib has `Smooth` and Kähler differentials, not the Jacobian criterion in this form; M-L) |
| A3 | Morphisms of `ℂ`-schemes give holomorphic maps; for a group scheme `G`, `G(ℂ)` is a complex Lie group (product of points ↔ points of the product) | M | from A2 and (i): pulled-back coordinates are regular. `G(ℂ)` as a group is Mathlib (`MonObj.Hom.group`) |
| A4 | `X` proper over `ℂ` ⇒ `X(ℂ)` compact | XL | Routes: (a) Chow's lemma + `ℂP^N` compact (both absent; XL); (b) for abelian varieties, projectivity (Mumford §6, XL algebraic) + `ℂP^N`; (c) a direct analytic valuative criterion: a sequence leaving every compact set yields, by curve selection, a map from a punctured disc, and properness extends it (research-level formalization). **This is the most expensive node.** SGA 1 XII 3.2 (UNVERIFIED) is the standard reference |
| A4' | `X` geometrically integral ⇒ `X(ℂ)` connected | L | SGA 1 XII 2.4 (UNVERIFIED), via irreducible curves through two points. A5 needs `A(ℂ)` connected as an input, so A4' cannot be avoided by the Lie-theoretic argument |
| A5 | A compact connected commutative complex Lie group `G` is `Lie(G)/Λ` with `Λ = ker exp` a full lattice | L | Route: (1) one-parameter subgroups: flows of invariant vector fields exist for all time by translation invariance (M-ode, uniform time) after restricting `G` to a real manifold (absent API, S-M); (2) commutativity makes `exp` a homomorphism; holomorphic because flows of holomorphic invariant fields commute with `J` (M); (3) `d exp₀ = id`, so `exp` is a local biholomorphism (M-ana); (4) the image is an open subgroup, hence all of `G` (connected); (5) the kernel is discrete; (6) `G` compact forces the kernel to span `Lie(G)` over `ℝ`, and T1's `torusDiffeo` finishes. Commutativity is algebraic for abelian varieties (Mathlib), so the Lie-theoretic proof of commutativity (Liouville applied to `Ad`, M-cpx) is not needed |
| A6 | Tangent identification `dφ₀ : ℂ^g ≅ T_eA` and `φ^*η = c(η)·dz` | S-M | glue over the leaf, §1.1 |
| G1 | GAGA for abelian varieties: holomorphic homomorphisms `A(ℂ) → B(ℂ)` are algebraic | XL | **lit** (Serre 1956; Mumford §3, UNVERIFIED); a separate leaf for T11 |

### 2.3 Cheaper special cases

- **Elliptic curves (`g = 1`, bp-faltings AN4).** Mathlib has `℘` and `℘'² = 4℘³ − g₂℘ − g₃`
  (VERIFIED). The uniformization of a Weierstrass curve is
  `z ↦ (℘(z), ℘'(z))`, a group isomorphism `ℂ/Λ ≅ E(ℂ)`. It needs surjectivity of `j`
  (or of `(g₂, g₃)`) and the addition theorem (L). This is the leaf for `g = 1`, and it is
  cheaper than A1-A5.
- **Jacobians (route (b) of bp-faltings).** Abel-Jacobi needs A1-A2 only for curves, plus path
  integrals on a Riemann surface (L-XL). It does not apply to the QM surface of F1 without first
  proving `A ≅ Jac(C)`.
- **Using the leaf.** Nothing in §1 needs the proof of the leaf. The team can treat it as a
  textbook leaf and schedule A1-A5 last.

## 3. Recommended order of work

1. **WP-U0 (done).** T1, P1, P2, Q1, and the leaf statement (`Torus.lean`, `Uniformization.lean`).
2. **WP-U1 (M, can start now; unblocks every consumer).** T2 and its antiholomorphic variant, P3,
   A6. Then restate bp-faltings' `HodgeData` construction M4 as "Hodge data from
   `UniformizationLeaf`" and bp-qmmoduli's R1an as glue over the leaf (plus the family input of
   §1.2).
3. **WP-U2 (M).** P4 (polarizations, symplectic bases, `𝔥_g`), and the Lean proof that
   `Ω(τ) ∈ 𝔥₂` with N5's Riemann form, completing pkg-I1's faithfulness claim.
4. **WP-U3 (L).** A1-A3: analytic topology and complex-manifold structure of `X(ℂ)` for smooth
   `X`, morphisms holomorphic, `G(ℂ)` a complex Lie group.
5. **WP-U4 (L).** A5, including real flows on complex Lie groups. Together with T1 this proves
   the leaf modulo compactness and connectedness.
6. **WP-U5 (XL).** A4 and A4'. The g = 1 case can be done first through `℘` (§2.3).

## 4. What compiles (VERIFIED)

`lake env lean scratch/bp-analytic/Torus.lean` and `lake env lean scratch/bp-analytic/Uniformization.lean`
report no errors and no warnings. `#print axioms` on `isManifold_torus`, `lieAddGroup_torus`,
`compactSpace_torus`, `holomorphic_const`, `ker_torusExp`, `contMDiff_torusExp_smul`,
`torusDiffeo`, `thetaConst_eq_riemannTheta`, `riemannTheta_add_period`,
`two_nsmul_proj_charPoint`, `QM.det_im_Omega_ne_zero`, `QM.qmPeriodDiffeo`,
`QM.qmPeriodDiffeo_add` lists only `propext`, `Classical.choice`, `Quot.sound`.

### 4.1 `Torus.lean` (namespace `BPAnalytic`)

| § | Declarations | Content |
| --- | --- | --- |
| 1 | `exists_gap`, `eventuallyEq_add_const`, `contDiffOn_of_sub_mem`, `Torus`, `proj`, `proj_eq_iff`, `isAddQuotientCoveringMap_proj`, `isCoveringMap_proj`, `isLocalHomeomorph_proj`, `chartOf` (+ 4 API lemmas), `ChartedSpace E (Torus Λ)`, `chartAt_torus`, `transition_sub_mem`, `isManifold_torus` | `E/Λ` is an analytic manifold for any discrete `Λ` |
| 2 | `contMDiff_proj`, `contMDiff_of_comp_proj`, `contMDiff_of_comp_proj₂`, `lieAddGroup_torus` | analytic projection, descent, Lie group |
| 3 | `connectedSpace_torus`, `compactSpace_torus`, `AddGroupLieAlgebra … = E` (`rfl`), `torusExp`, `torusExp_apply`, `torusExp_surjective`, `ker_torusExp`, `contMDiff_torusExp`, `contMDiff_torusExp_smul`, `holomorphic_const` | compactness, exponential, kernel = Λ, Liouville |
| 4 | `SiegelSpace`, `periodVec`, `periodVec_linearIndependent`, `card_periodIndex`, `periodBasis`, `coe_periodBasis`, `periodLattice` (+ `DiscreteTopology`, `IsZLattice ℝ`), `det_im_ne_zero_of_mem_siegelSpace`, `mem_periodLattice_iff`, `SiegelTorus` | the period lattice of `Ω` |
| 5 | `intVec`, `riemannTheta`, `dotProduct_mulVec_symm`, `riemannTheta_add_int`, `riemannTheta_add_mulVec`, `riemannTheta_add_period`, `thetaChar`, `thetaChar_eq`, `Char2`, `thetaConst` (copied from pkg-I1), `charHalf`, `thetaConst_eq_thetaChar`, `thetaConst_eq_riemannTheta`, `two_nsmul_proj_charPoint` | theta functions as sections; theta constants at 2-torsion points |
| 6 | `torusAddEquiv`, `torusAddEquiv_proj`, `torusAddEquiv_symm_proj`, `torusDiffeo`, `torusDiffeo_apply` | linear changes of coordinates |
| 7 | `QM.B`, `QM.oBasis`, `QM.Mi`, `QM.Mj`, `QM.iota`, `QM.latVec`, `QM.Emat`, `QM.F0mat`, `QM.Pinv`, `QM.Omega` (copied from pkg-I1); `latVec0`-`latVec3`, `Emat_eq`, `F0mat_eq`, `Fp`, `det_Fp`, `sqrt2_ne_zero`, `det_Fp_ne_zero`, `Fp_mul_Omega`, `qmVec`, `qmVec_linearIndependent`, `qmBasis`, `qmLattice` (+ instances), `qmLattice_eq`, `QMTorus`, `mulVec_col`, `Fp_mulVec_periodVec`, `det_im_ne_zero_of_linearIndependent`, `imgVec`, `Fp_mulVec_periodVec'`, `imgVec_linearIndependent`, `span_imgVec`, `FpEquiv`, `FpEquiv_apply`, `det_im_Omega_ne_zero`, `map_periodLattice_Omega`, `qmPeriodDiffeo`, `qmPeriodDiffeo_add`, `qmPeriodDiffeo_proj` | pkg-I1's QM torus and its period matrix |

Key statements (abridged):

```lean
instance isManifold_torus : IsManifold 𝓘(ℂ, E) ω (Torus Λ)          -- Λ : Submodule ℤ E, discrete
instance lieAddGroup_torus : LieAddGroup 𝓘(ℂ, E) ω (Torus Λ)
instance compactSpace_torus [FiniteDimensional ℂ E] [IsZLattice ℝ Λ] : CompactSpace (Torus Λ)
theorem ker_torusExp : (torusExp Λ).ker = Λ.toAddSubgroup
theorem holomorphic_const [FiniteDimensional ℂ E] [IsZLattice ℝ Λ] {f : Torus Λ → F}
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) : ∃ v : F, f = Function.const _ v
def torusDiffeo (Λ' : Submodule ℤ E') [DiscreteTopology Λ'] (T : E ≃L[ℂ] E')
    (hT : Λ.map (T.toLinearEquiv.toLinearMap.restrictScalars ℤ) = Λ') :
    Torus Λ ≃ₘ^ω⟮𝓘(ℂ, E), 𝓘(ℂ, E')⟯ Torus Λ'
theorem riemannTheta_add_period (Ω) (hΩ : Ωᵀ = Ω) (z) (m n : Fin g → ℤ) :
    riemannTheta Ω (z + (Ω *ᵥ intVec m + intVec n)) =
      exp (-(π * I * (intVec m ⬝ᵥ (Ω *ᵥ intVec m))) - 2 * π * I * (intVec m ⬝ᵥ z)) *
        riemannTheta Ω z
theorem thetaConst_eq_riemannTheta (m : Char2) (Ω) (hΩ : Ωᵀ = Ω) :
    thetaConst m Ω = exp (π * I * (charHalf m.1 ⬝ᵥ (Ω *ᵥ charHalf m.1)) +
        2 * π * I * (charHalf m.1 ⬝ᵥ charHalf m.2)) *
      riemannTheta Ω (Ω *ᵥ charHalf m.1 + charHalf m.2)
theorem QM.map_periodLattice_Omega {τ : ℂ} (hτ : τ.im ≠ 0) :
    (periodLattice (Omega τ) (det_im_Omega_ne_zero hτ)).map
      ((FpEquiv hτ).toLinearEquiv.toLinearMap.restrictScalars ℤ) = qmLattice hτ
def QM.qmPeriodDiffeo {τ : ℂ} (hτ : τ.im ≠ 0) :
    SiegelTorus (Omega τ) (det_im_Omega_ne_zero hτ) ≃ₘ^ω⟮𝓘(ℂ, Fin 2 → ℂ), 𝓘(ℂ, Fin 2 → ℂ)⟯
      QMTorus hτ
```

### 4.2 `Uniformization.lean` (namespace `BPAnalytic.Uniformization`)

`AbVar`, `AbVar.ptObj`, `AbVar.Pt` (copied from `Objects.lean`, namespace `PkgI3`), `Torus`,
`proj` (the same two-line definitions as `Torus.lean`; scratch files cannot import each other),
`PtIn`, `evalAt`, `UniformizationLeaf`, `UniformizationLeafAll`.

```lean
/-- The value of `f ∈ Γ(U, 𝒪_A)` at a ℂ-point `P ∈ U` (0 off `U`). -/
def evalAt (U : A.X.left.Opens) (f : Γ(A.X.left, U)) (P : A.Pt ℂ) : ℂ :=
  if h : PtIn A P U then ((P.left.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom f
  else 0
def UniformizationLeaf : Prop :=
  ∃ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
    (φ : Torus Λ ≃+ Additive (A.Pt ℂ)),
    (∀ (U : A.X.left.Opens) (f : Γ(A.X.left, U)),
      IsOpen {v | PtIn A (Additive.toMul (φ (proj Λ v))) U} ∧
      AnalyticOnNhd ℂ (fun v => evalAt A U f (Additive.toMul (φ (proj Λ v))))
        {v | PtIn A (Additive.toMul (φ (proj Λ v))) U}) ∧
    (∀ v₀ : Fin g → ℂ, ∃ (U : A.X.left.Opens) (f : Fin g → Γ(A.X.left, U))
      (e : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)),
      PtIn A (Additive.toMul (φ (proj Λ v₀))) U ∧
      HasFDerivAt (fun v i => evalAt A U (f i) (Additive.toMul (φ (proj Λ v))))
        (e : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀)
```

**Faithfulness review of the leaf (SPECULATIVE; to be checked by a reviewer).**
- *Not vacuous.* It asserts the existence of a lattice and of a group isomorphism with
  properties, over Mathlib's points and regular functions. It invents no structure.
- *Not stronger than the source.*
  - (i) holds because regular functions are holomorphic on `A^an`, and Zariski opens are open.
  - (ii) holds because local parameters at a smooth point are étale coordinates, hence analytic
    charts.
  - The group isomorphism and the lattice are Mumford §1.
- *Strong enough.* (i) and (ii) determine the analytic structure, so consumers can derive the
  tangent map (A6), the action of endomorphisms (via T2), torsion and complex conjugation.
- *Junk values.* `evalAt` is `0` off `U`. Clause (i) asks for openness of `φ⁻¹(U)` and
  analyticity only at points of that open set, so the junk value is never seen.
- *Dimension.* `g` is existential. Clause (ii) forces `g = dim A` analytically. A consumer that
  needs `g = dim A` algebraically can add it as a conjunct, a consequence of Mumford §1.

## 5. Findings that affect other notes

1. pkg-I1's "Faithfulness" claim (that `Ω(τ)` is a period matrix of `ℂ²/Λ_τ`) is now proved in
   Lean for the lattice and torus part, for every `τ ∉ ℝ` (`qmPeriodDiffeo`). Symmetry of `Ω(τ)`
   and `Im Ω(τ) > 0` remain numerical/symbolic (sympy, VERIFIED computation here).
2. bp-qmmoduli R1an, as written, is pointwise in `P`. The glue that turns it into F1 also uses
   the holomorphy of `τ ↦ π(A_τ)`, a family statement about the Shimura curve (§1.2). Recommend
   recording it in R1an or R1.
3. bp-faltings AN3 can be replaced, for stating M4/H1-H3 and the leaves R18-R22, by
   `UniformizationLeaf` plus glue A6 and P3. "`GroupModel.height` cannot be defined until AN3
   exists" (bp-faltings §5 WP-D) is then no longer true. The height can be defined from
   the leaf's data, as a function of the chosen `(Λ, φ)`, and shown independent of that choice
   (`torusDiffeo`, T2; bp-faltings `torusMetricSq_comap`). SPECULATIVE until the glue is built.
4. Mathlib's `Instances/Quotient.lean` TODO (`IsManifold` for quotients by smooth properly
   discontinuous actions) is done here in the special case of lattices in normed spaces. The
   argument (`eventuallyEq_add_const`) generalizes to any action by isometries with discrete
   orbits. A candidate upstream contribution.

## 6. Unchecked items (UNVERIFIED or not done)

1. Locators recalled from memory: Mumford, *Abelian varieties*, §1 (analytic theory: `A(ℂ)` is
   a complex torus), §3 (GAGA consequences), §6 (projectivity); Serre, *Géométrie algébrique et
   géométrie analytique* (1956), §2; SGA 1 XII 2.4, 3.2; Silverman AEC VI; the period-matrix
   covolume formula and Riemann's bilinear relations (Birkenhake-Lange, *Complex abelian
   varieties*, Ch. 1 and 4).
2. Not built: T2, P3, P4, A1-A5, A6, G1. Not proved in Lean: symmetry of `Ω(τ)`, `Ω(τ) ∈ 𝔥₂`,
   the polarization of `ℂ²/Λ_τ`.
3. Library items not re-checked: Tau Ceti Riemann forms (prereq-survey A9). The Mathlib name
   `Complex.volume_preserving_equiv_pi` in P3's route is UNVERIFIED.
4. The size tiers and line estimates are SPECULATIVE. The faithfulness review of
   `UniformizationLeaf` (§4.2) is the author's. It has had no independent review.
