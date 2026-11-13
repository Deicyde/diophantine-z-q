# bp-analytic: formalization blueprint for the analytic uniformization of abelian varieties

Status: research note and blueprint (task bp-analytic, 2026-11-12), written for a crowdsourced
Lean team.
- Lean file: `scratch/bp-analytic/Torus.lean`, about 1 650 lines. It compiles with no errors and
  no warnings (with `linter.unusedSectionVars` disabled at Torus.lean:20) and has no `sorry`.
- It uses Mathlib only, with no project imports. Definitions copied from
  `ZInQKernel/HDecomp/Objects.lean` and `scratch/pkg-I1/I1.lean` are marked "copied" in the file.
- Results log: `scratch/bp-analytic/log.md`.
- No file under `ZInQKernel/` or `blueprint/`, and no other task's notes or scratch files, was
  edited.

Marks:
- **VERIFIED**: read in a source in the repository or in Mathlib, computed, or compiled.
- **STANDARD**: a published result with a reference.
- **SPECULATIVE**: an estimate or a proposal.
- **UNVERIFIED**: a locator recalled from memory (there was no network access).
- **BUILT**: compiled in `scratch/bp-analytic/Torus.lean`, with `#print axioms` giving only
  `propext`, `Classical.choice`, `Quot.sound`.

The node is shared by three blueprints:
- AN3 of `bp-faltings.md`, the archimedean term of the Faltings height;
- N14/R1an of `bp-qmmoduli.md`, F1's theta form;
- the leaves R22, T11 and T12 of `h-decomposition.md`.

## 0. Main result

1. **The uniformization does not block anyone. It is stated today as one leaf over genuine
   objects, with no analytification, and the glue every consumer needs on top of it is proved.**

   The leaf is `UniformizationLeaf A` (`Torus.lean` §10). For an abelian variety `A/ℂ` (the
   project's `AbVar`, copied from `Objects.lean`) it asserts a full lattice `Λ ⊂ ℂ^g` and a group
   isomorphism `φ : ℂ^g/Λ ≃ A(ℂ)`, where `A(ℂ)` is Mathlib's group of `ℂ`-points `Spec ℂ ⟶ A`.
   The predicate `IsUniformization A Λ φ` requires three things:
   - (i) every regular function `f ∈ Γ(U, 𝒪_A)` on a Zariski open `U` pulls back to an analytic
     function on the open set `φ⁻¹(U)`;
   - (ii) at every point, `g` regular functions pull back to local holomorphic coordinates;
   - (iii) `φ⁻¹` is continuous for the topology defined by regular functions.

   So `φ` is an isomorphism of complex Lie groups for the analytic structure of `A(ℂ)`. The
   statement is Mumford, *Abelian varieties*, §1, applied to `A^an` (STANDARD; locators
   UNVERIFIED, §6). It is a consequence of the published statement and not stronger
   (faithfulness review in §4.2).

   **Glue proved over the leaf (BUILT):**
   - *Uniqueness.* Two uniformizations of the same `A` differ by a `ℂ`-linear isomorphism `T`
     with `T(Λ) = Λ'`, and `g` is the same for all of them (`IsUniformization.exists_equiv`,
     `IsUniformization.dim_eq`). So the period lattice, and everything computed from it, does
     not depend on the choice.
   - *Endomorphisms act linearly.* Every endomorphism `α` of the group scheme `A` acts on `ℂ^g`
     by a `ℂ`-linear map `ρ(α)` preserving `Λ` (`exists_complexLinear_endo`, `analyticRep`).
     - `ρ` is unital, additive and multiplicative: `analyticRep_id`, `analyticRep_mul`,
       `analyticRep_comp`.
     - This is the analytic representation `End(A) → M_g(ℂ)` that R1an, T11 and T12 use.
   - *Torsion.* `A(ℂ)[n] = φ((1/n)Λ/Λ)` (`torsion_iff`), the input of T12.

   The leaf's *proof*, i.e. analytification, is the XL work package of §2-§3. No consumer needs
   it in order to be stated or glued.
2. **The analytic objects are built (VERIFIED: compiled, standard axioms only).**
   - **Compact complex tori as complex Lie groups (T1).** For a discrete `Λ` in a complex normed
     space `E`, `E/Λ` is an analytic manifold (`IsManifold 𝓘(ℂ, E) ω`) and an analytic Lie group
     (`LieAddGroup 𝓘(ℂ, E) ω`). It is connected, and compact for a full lattice. This is the
     `IsManifold` instance that Mathlib's `Geometry/Manifold/Instances/Quotient.lean` lists as a
     TODO (VERIFIED, read).
   - **The exponential.** The exponential `Lie(E/Λ) = E → E/Λ` is surjective and analytic, with
     kernel exactly `Λ`; its one-parameter subgroups are analytic.
   - **Further properties.** Liouville (holomorphic functions on `E/Λ` are constant, for a full lattice `Λ` in
     finite-dimensional `E`: `holomorphic_const`); descent of
     analytic maps along the projection; linear changes of coordinates give biholomorphic group
     isomorphisms (`torusDiffeo`).
   - **Homomorphisms of tori (T2).** A continuous group homomorphism `E/Λ → E'/Λ'` is induced by
     an `ℝ`-linear `T` with `TΛ ⊆ Λ'`. If it is holomorphic, `T` is `ℂ`-linear
     (`exists_realLinear_lift`, `exists_complexLinear_lift`; covering-space lifting from
     Mathlib).
   - **Period matrices (P1, P3).** For `det Im Ω ≠ 0`, `Ωℤ^g + ℤ^g` is a full lattice
     (`periodLattice`; conversely, independence of the generators forces `det Im Ω ≠ 0`). Its
     covolume for Lebesgue measure on `ℂ^g` is `|det Im Ω|` (`covolume_periodLattice`), so
     `det Im Ω` on the Siegel space. With bp-faltings' `torusMetricSq Λ c = ‖c‖²·covol(Λ)`, the
     archimedean Faltings term of a torus with normalized period matrix `Ω` is `‖c‖²·det Im Ω`:
     **the integral over `A(ℂ)` through the period matrix alone.**
   - **Theta functions (P2).**
     - Riemann's `θ(z, Ω)` is quasi-periodic under `Ωℤ^g + ℤ^g`, i.e. a section of a line bundle
       on `ℂ^g/Λ_Ω`.
     - pkg-I1's theta constants `thetaConst m Ω` (copied verbatim) are `exp(…)·θ(Ωa/2 + b/2, Ω)`:
       values of `θ` at the 2-torsion points of `ℂ²/Λ_Ω` (`thetaConst_eq_riemannTheta`,
       `two_nsmul_proj_charPoint`).
     - These identities are proved for `tsum` by reindexing, so they need no convergence
       hypothesis.
   - **pkg-I1's period matrix is a period matrix (Q1).** For `Im τ ≠ 0`:
     - `Λ_τ = ι(𝒪)(τ,1)ᵀ` is a full lattice in `ℂ²` (`qmLattice`);
     - `F'(τ) = F₀(τ)P⁻¹` is invertible and carries `Ω(τ)ℤ² + ℤ²` onto `Λ_τ`
       (`map_periodLattice_Omega`);
     - so `det Im Ω(τ) ≠ 0`, `Ω(τ)ᵀ = Ω(τ)` (`Omega_transpose`), and
       `ℂ²/Λ_{Ω(τ)} ≃ ℂ²/Λ_τ` biholomorphically as groups (`qmPeriodDiffeo`);
     - for `Im τ > 0`, `Ω(τ) ∈ 𝔥₂` (`Omega_mem_siegelSpace`, via the partial-fraction form
       `Ω(τ) = A₀ + C/(τ+1) + B/(τ−3)` with `−C`, `−B` positive semidefinite of rank one).

     pkg-I1 §4 stated "`Ω(τ)` is a period matrix of `(ℂ²/Λ_τ, E)`" from numerical checks
     (pkg-I1.md, "Faithfulness"). The lattice, torus, symmetry and positivity parts are now
     theorems. The compatibility with N5's Riemann form holds by pkg-I1's construction and is
     not re-proved here.
3. **What each consumer needs (§1).** None of them needs the analytification of a general scheme.
   - **The Faltings height (AN3)** needs the period lattice `Λ_σ ⊂ Lie(A_σ)` and the
     identification of `η ∈ ω_A` with `c·dz₁∧⋯∧dz_g`. The lattice and its independence of
     choices come from the leaf and the glue. The archimedean term is `‖c‖²·covol(Λ_σ)`, which is
     `‖c‖²·det Im Ω` for a normalized period matrix (BUILT). The identification of `η`
     (node A6) is S-M glue over the leaf and bp-faltings' cotangent model.
   - **F1 (R1an)** needs an `𝒪`-equivariant `A_σ(ℂ) ≅ ℂ²/Λ_τ`.
     - The `𝒪`-action on `(ℂ², Λ)` by `ℂ`-linear maps, multiplicatively (unbundled, not a `RingHom`), is BUILT over
       the leaf.
     - "A rank-one `𝒪`-lattice is `ι(𝒪)v`" is lattice algebra.
     - The torus and theta side is BUILT.
     - Flagged (§1.2): bp-qmmoduli's step "two Hauptmoduln coincide" also needs the analytic
       uniformization of the Shimura curve in families, which is not part of AN3.
   - **R22, T11, T12** (§1.3-§1.5).
     - T12 reduces to the leaf plus elementary glue (torsion, complex conjugation).
     - R22's theta constants are `thetaChar` (BUILT). Its period matrix in `𝔥₂` needs node P4
       (polarizations). For the QM family this is BUILT (`Omega_mem_siegelSpace`).
     - T11 needs, besides the leaf, a separate GAGA-type leaf: every holomorphic endomorphism is
       algebraic. The algebraic-to-linear direction is BUILT (`exists_complexLinear_endo`).
4. **Sizes (SPECULATIVE, Lean lines).**
   - The proof of the leaf from Mathlib: about 15-30k lines, in agreement with bp-faltings' AN3
     estimate. The largest parts are compactness of `X(ℂ)` for proper `X` (XL, A4) and the
     manifold structure on `X(ℂ)` for smooth `X` (L, A2).
   - The Lie-theory step "compact connected commutative complex Lie group ⇒ `ℂ^g/Λ`" is L (A5).
     Its last step (`ℂ^g/Λ` is such a group, with exponential, kernel `Λ` and linear
     homomorphisms) is built here.
   - The remaining consumer glue over the leaf (A6, torsion, complex conjugation, P4) is S-M per
     item.

## 1. What each consumer needs

### 1.1 Faltings height (bp-faltings AN3, used by M4/H1/H2)

- **Used:** for each `σ : L → ℂ`, a lattice `Λ_σ` in `Lie(A_σ) ≅ ℂ^g`, and, for `η ∈ ⋀^g ω_A`,
  the constant `c_σ(η)` with `φ^*η = c_σ(η)·dz₁∧⋯∧dz_g`. Then
  `(i/2)^g ∫_{A_σ(ℂ)} η∧η̄ = |c_σ(η)|²·covol(Λ_σ)` (bp-faltings AN1, BUILT there as
  `torusMetricSq_eq_setIntegral`).
- **Not used:** the complex-manifold structure of `A_σ(ℂ)` beyond the leaf, GAGA, Néron models.
- **Period-matrix form (the integral through a period matrix alone).**
  - Choose a basis `ω₁…ω_g` of `H⁰(A_σ, Ω¹)` and a `ℤ`-basis `γ₁…γ_{2g}` of `Λ_σ`. Put
    `Π = (∫_{γ_j} ω_i) = (Ω₂ | Ω₁)`, ordered so that `Ω = Ω₂⁻¹Ω₁` is normalized.
  - In the coordinates `z_i` dual to `ω_i` one has `Λ_σ = Πℤ^{2g} = Ω₂(Ωℤ^g + ℤ^g)`. So
    `covol(Λ_σ) = |det Ω₂|²·covol(Ωℤ^g + ℤ^g) = |det Ω₂|²·|det Im Ω|`.
  - In Lean: the first factor is bp-faltings' `covolume_comap_mul_det` with
    `det_ℝ = |det_ℂ|²`; the second is `covolume_periodLattice` (BUILT here).
  - With `η = ω₁∧⋯∧ω_g` one gets `c = 1`, so the archimedean term is a function of the period
    matrix only.
- **Independence of the choice of uniformization:** `IsUniformization.exists_complexLinear`
  (BUILT). Any two uniformizations differ by a `ℂ`-linear `T` with `TΛ ⊆ Λ'`; by symmetry `T` is
  invertible on lattices. bp-faltings' `torusMetricSq_comap` then shows that the metric is
  unchanged.
- **Still needs the leaf:** to *define* `Λ_σ` (or `Π`) from `A` one needs `H₁(A_σ(ℂ))` or
  `ker exp`, i.e. AN3. Algebraic substitutes do not give the integral lattice: the Tate module
  gives `Λ ⊗ ℤ_ℓ`, and algebraic de Rham cohomology gives `Λ ⊗ ℂ` without `Λ`.
- **Remaining glue A6 (S-M): the tangent identification.**
  - `dφ₀ : ℂ^g → T_eA_σ` sends `v` to the derivation `f ↦ D(f∘φ∘proj)(0)·v`.
  - It is defined because of (i), and it is an isomorphism because of (ii).
  - Hence `c_σ(η) = η(dφ₀e₁, …, dφ₀e_g)` for `η` in bp-faltings' AV3 cotangent model `𝔪/𝔪²`.

### 1.2 F1 (bp-qmmoduli R1an)

- **Used (bp-qmmoduli §2.3, VERIFIED read):** for `K ⊆ ℂ` and `P : QML3 K` there are
  `τ ∈ ℍ^±` and an `𝒪`-equivariant isomorphism of complex Lie groups `P.A(ℂ) ≅ ℂ²/ι(𝒪)(τ,1)ᵀ`,
  carrying the polarization to `±E₀`.
- **Over the leaf:**
  1. **BUILT.** Each endomorphism of `A`, in particular each `ι(x)`, `x ∈ 𝒪`, acts on `ℂ²` by a
     `ℂ`-linear `ρ(x)` with `ρ(x)Λ ⊆ Λ` (`exists_complexLinear_endo`, `analyticRep`).
     - `ρ` is multiplicative and unital (`analyticRep_id`, `analyticRep_mul`, `analyticRep_comp`: three
       lemmas, not a bundled `RingHom`).
     - This makes `Λ` an `𝒪`-module and `ℂ²` an `𝒪 ⊗ ℂ`-module.
  2. **Lattice algebra (M).** `Λ` is a torsion-free `𝒪`-module of `ℤ`-rank 4. So it is a
     locally free right ideal class of `𝒪`, and free of rank one: `Λ = ι(𝒪)v` for some `v`, after
     a choice of `ι`. The reason is Eichler's theorem: maximal orders of indefinite quaternion
     algebras over `ℚ` have one ideal class (STANDARD, locator UNVERIFIED). Scaling `v` to
     `(τ, 1)ᵀ` gives `τ ∉ ℝ`.
  3. **BUILT.**
     - `qmPeriodDiffeo` identifies `ℂ²/Λ_τ` with `ℂ²/Λ_{Ω(τ)}`.
     - `Omega_transpose` gives `Ω(τ)ᵀ = Ω(τ)`, so `θ(·, Ω(τ))` is quasi-periodic for that
       torus (`riemannTheta_Omega_add_period`).
     - `Omega_mem_siegelSpace` gives `Ω(τ) ∈ 𝔥₂` for `Im τ > 0`.
     - `thetaConst_eq_riemannTheta` identifies pkg-I1's ten theta constants at `Ω(τ)` with
       values of `θ` at 2-torsion points.
  4. **Polarization.** bp-qmmoduli's `eq_pm_E0_of_principal` (done there) gives `±E₀`.
- **Not part of AN3.** bp-qmmoduli derives `π(P) = j_θ(Ω(τ))` from "two holomorphic
  Hauptmoduln of `Γ*\ℍ` with the same values at three points coincide".
  - That step needs `τ ↦ π(A_τ)` to be holomorphic on `ℍ`, i.e. the complex uniformization of
    the Shimura curve `Y₃(ℂ)` as an analytic space.
  - That is a family statement (pkg-I1 I1-a item 1; part of R1), not a statement about one `A`.
  - SPECULATIVE reading: R1an, as written in bp-qmmoduli, quantifies over single `P`. So this
    family input should be added to R1an or kept in R1. Flagged for the bp-qmmoduli owner.
- **Weaker statements suggested by the task.** The explicit theta functions on the Siegel space
  that pkg-I1 defines are now tied to the torus (§0 item 2). F1 still needs some map `A ↦ Ω`,
  which cannot be defined without `Λ_σ`, i.e. without the leaf.

### 1.3 R22 (Pazuki's theta height)

- **Used:** for a principally polarized abelian surface `A/K` and `σ`, a period matrix
  `Ω_σ ∈ 𝔥₂`, and the theta constants `θ[a,b](Ω_σ)` up to the action of `Sp₄(ℤ)` (Pazuki's Def.
  2.6, locator in h-decomposition R22, VERIFIED read there).
- **Over the leaf:**
  - The leaf gives `Λ_σ`.
  - The polarization gives a Riemann form with a symplectic basis, hence `Ω_σ ∈ 𝔥₂` (node P4,
    M, Riemann bilinear relations). Tau Ceti proves "Riemann forms = polarizations of
    weight-one Hodge structures" (prereq-survey A9, not re-checked).
  - The theta constants are `thetaChar` (BUILT), equal to pkg-I1's `thetaConst`.
- **Missing beyond AN3:** the Faltings height (bp-faltings) and the theta-height normalization.

### 1.4 T11 (Riemann/GAGA/rigidity)

- **Used (h-decomposition §2.2, VERIFIED read):** `End⁰(A_ℂ)` = Hodge endomorphisms, and
  `Hom_ℚ̄ = Hom_ℂ`.
- **Over the leaf:** `End(A_ℂ) → End_ℂ(ℂ^g) ∩ End(Λ)`.
  - The map exists: `exists_complexLinear_endo`, BUILT.
  - Injectivity is glue (S): `T_α = 0` forces `α = 0` on `ℂ`-points, hence `α = 0`, since `A` is
    reduced and `ℂ`-points are dense.
  - Surjectivity says that every holomorphic endomorphism of `A(ℂ)` is algebraic. That is
    GAGA/Chow (Serre 1956; UNVERIFIED locator), a **separate leaf**, not a consequence of AN3.
- `Hom_ℚ̄ = Hom_ℂ` is algebraic (rigidity and spreading out) and needs no analytification.

### 1.5 T12 (Artin comparison with complex conjugation)

- **Used (G10, h-decomposition):** complex conjugation `c` acts on `T_ℓA` with determinant
  `(−1)^g` (oddness of `r_ℓ`).
- **Over the leaf, elementary glue (M):**
  - `A(ℂ)[n] = φ((1/n)Λ/Λ)`, because `φ` is a group isomorphism and the torsion of `ℂ^g/Λ` is
    `(1/n)Λ/Λ` (BUILT: `torsion_iff`, `nsmul_proj_eq_zero_iff`). So `T_ℓA ≅ Λ ⊗ ℤ_ℓ`.
  - For `A` defined over `ℝ`, `c` acts on `A(ℂ)` antiholomorphically: by (i),
    `f∘c = conj∘f^c` for regular `f`.
  - The argument of `continuous_endo` and `exists_realLinear_endo` adapts to the map `φ⁻¹cφ`, so
    `c` lifts to an `ℝ`-linear involution of `ℂ^g` preserving `Λ`.
  - The lift is antilinear: run the proof of `exists_complexLinear_endo` with `conj∘G`. An
    antilinear involution has eigenvalues `±1`, each with multiplicity `g`, so
    `det(c | Λ⊗ℚ) = (−1)^g`.
- No étale cohomology is needed in this use: T10 already turns `H¹_et` into `T_ℓ`.

### 1.6 Summary

| Consumer | Needs the leaf | Needs more | Built here for it |
| --- | --- | --- | --- |
| AN3 (Faltings) | yes, to define `Λ_σ` and `c_σ(η)` | A6 (tangent glue) | torus, `periodLattice`, `covolume_periodLattice`, `torusDiffeo`, `exists_complexLinear` (independence of choices) |
| R1an (F1) | yes | lattice algebra (M); the Shimura-curve family uniformization (not AN3) | `analyticRep` (with `_id/_comp/_mul`; not a bundled `RingHom`), `qmLattice`, `qmPeriodDiffeo`, `Omega_transpose`, `Omega_mem_siegelSpace`, `thetaConst_eq_riemannTheta` |
| R22 | yes | P4 (polarization ⇒ `𝔥₂`), Faltings height | `thetaChar`, `riemannTheta_add_period` |
| T11 | yes | a GAGA leaf | `analyticRep`, `exists_complexLinear_lift` |
| T12 | yes | conjugation glue (M) | `torsion_iff`, `exists_realLinear_lift`, `continuous_endo` pattern |

## 2. Dependency graph

Tiers (SPECULATIVE, Lean lines): **S** ≤ 300, **M** 300-2 000, **L** 2 000-10 000,
**XL** > 10 000.

Statuses:
- **Mathlib**: VERIFIED in `.lake/packages/mathlib` v4.35 unless marked;
- **BUILT**: here;
- **lit**: in the literature only;
- **absent**: searched for, not found.

```
 Mathlib: manifolds, LieAddGroup, GroupLieAlgebra, covering maps and lifting, ZLattice/ZSpan,
          covolume, analytic inverse function thm, schemes, ValuativeCriterion, AlgClosed points
   │
   ├── T1 torus E/Λ: manifold, Lie group, compact, exp, Liouville, torusDiffeo   [BUILT]
   │      ├── T2 continuous/holomorphic homs of tori are ℝ-/ℂ-linear            [BUILT]
   │      ├── P1 period lattice Ωℤ^g+ℤ^g [BUILT]   P2 theta quasi-periodicity   [BUILT]
   │      ├── P3 covol(Ωℤ^g+ℤ^g) = |det Im Ω|  [BUILT]   P4 polarization ⇒ Ω ∈ 𝔥_g (M)
   │      └── Q1 QM lattice ι(𝒪)(τ,1)ᵀ ≅ Siegel lattice of Ω(τ), Ω(τ) symmetric [BUILT]
   │
   ├── A1 analytic topology on X(ℂ), X loc. finite type over ℂ  (M-L)
   │      └── A2 complex manifold structure on X(ℂ), X smooth  (L)
   │             └── A3 morphisms holomorphic; G(ℂ) complex Lie group  (M)
   ├── A4 X proper ⇒ X(ℂ) compact  (XL);  A4' X geom. integral ⇒ X(ℂ) connected  (L)
   └── A5 compact connected commutative complex Lie group ≅ Lie(G)/Λ  (L)
                │
   LEAF  UniformizationLeaf A = ∃ g Λ φ, IsUniformization A Λ φ   [stated, BUILT as a Prop]
                │                                     ◄── its proof: A1-A5 + T1
   glue over the leaf:  U1 uniqueness up to ℂ-linear maps [BUILT]
                        U2 End(A) acts ℂ-linearly on (ℂ^g, Λ) [BUILT]
                        A6 tangent / η ↦ c·dz (S-M)   U3 torsion, complex conjugation (M)
                │
   AN3 (bp-faltings) · R1an (bp-qmmoduli) · R22 · T11 (+ GAGA leaf) · T12
```

### 2.1 Mathlib foundations (VERIFIED)

| Node | Content | Where |
| --- | --- | --- |
| M-man | `ChartedSpace`, `IsManifold I n` with `n = ω` the analytic groupoid, `isManifold_of_contDiffOn`, `contMDiffOn_chart`, `ContMDiffAt.comp`, products of manifolds, `Diffeomorph` | `Geometry/Manifold/ChartedSpace.lean`, `IsManifold/Basic.lean`, `ContMDiff/*`, `Diffeomorph.lean` |
| M-lie | `LieAddGroup I n G`, `ContMDiffAdd`; `GroupLieAlgebra` / `AddGroupLieAlgebra` (tangent space at `1`, with the Lie bracket of invariant vector fields) | `Geometry/Manifold/Algebra/LieGroup.lean`, `GroupLieAlgebra.lean` |
| M-quot | `ChartedSpace` on quotients by free properly discontinuous actions (TODO there: `IsManifold`); `AddSubgroup.isAddQuotientCoveringMap_of_comm` (quotient by a discrete subgroup is a covering); `IsLocalHomeomorph.localInverseAt` | `Geometry/Manifold/Instances/Quotient.lean`, `Topology/Covering/Quotient.lean`, `Topology/IsLocalHomeomorph.lean` |
| M-lift | lifting through coverings from simply connected spaces (`IsCoveringMap.existsUnique_continuousMap_lifts`); real vector spaces are contractible, hence simply connected | `Topology/Homotopy/Lifting.lean`, `Analysis/Convex/Contractible.lean` |
| M-cpx | Liouville on compact complex manifolds (`MDifferentiable.exists_eq_const_of_compactSpace`), maximum modulus on manifolds | `Geometry/Manifold/Complex.lean` |
| M-ana | analytic inverse function theorem (`HasStrictFDerivAt.localInverse`, `to_localInverse`, `OpenPartialHomeomorph.analyticAt_symm`); `AnalyticAt.hasStrictFDerivAt`, `AnalyticAt.pi`; implicit function theorem (`HasStrictFDerivAt.implicitFunction`) | `Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`, `Analysis/Calculus/FDeriv/Analytic.lean`, `Analysis/Analytic/Constructions.lean`, `Analysis/Calculus/Implicit.lean` |
| M-ode | integral curves: local existence/uniqueness, global existence with uniform time (`exists_isMIntegralCurve_of_isMIntegralCurveOn`); **real** manifolds only | `Geometry/Manifold/IntegralCurve/*` |
| M-lat | `ZLattice`, `IsZLattice`, `ZSpan.fundamentalDomain`, `fract`, `floor`, `Basis.ofZLatticeBasis(_span)`, `Basis.parallelepiped` (compact), `ZLattice.covolume`, `covolume_eq_measure_fundamentalDomain`, `ZSpan.measureReal_fundamentalDomain` (`= |b₀.det b|·μ(F b₀)`), `Complex.volume_preserving_equiv_real_prod` | `Algebra/Module/ZLattice/*`, `MeasureTheory/Measure/Haar/OfBasis.lean`, `MeasureTheory/Measure/Lebesgue/Complex.lean` |
| M-ag | schemes, `Over`, `GrpObj` (group of points `MonObj.Hom.group`), `IsProper`, `Smooth`, `Scheme.Hom.appLE` with `comp_appLE`, `Scheme.ΓSpecIso`, `ValuativeCriterion` (and `UniversallyClosed.eq_valuativeCriterion`), `Proj` separated/proper, `pointEquivClosedPoint` (closed points = `k`-points over `k = k̄`), `smooth_of_grpObj`, commutativity of abelian varieties | `AlgebraicGeometry/*` |
| M-hom | singular homology | `AlgebraicTopology/SingularHomology/Basic.lean` (a route to `H₁(A(ℂ),ℤ) ≅ Λ`; not needed if `Λ := ker exp`) |

**Absent from Mathlib v4.35** (searched):
- analytification, or an analytic topology on `X(ℂ)`;
- Hartogs/Osgood (no file mentions them);
- the exponential map of a Lie group;
- holomorphic ODE or complex flows;
- an API restricting a complex manifold to a real one, needed to use M-ode on a complex Lie
  group (only internal `NormedSpace.restrictScalars` uses were found in `IsManifold/Basic`);
- Chow's lemma; GAGA; projective space as a manifold.

### 2.2 Nodes

| Node | Statement | Tier | Status / cheapest faithful route |
| --- | --- | --- | --- |
| T1 | `E/Λ` (Λ discrete) is an analytic manifold and Lie group, connected; compact if Λ is full; `exp = proj` with kernel Λ; descent of analytic maps; Liouville (full `Λ`, finite-dimensional `E`); linear isos give biholomorphic group isos | M | **BUILT** (§1-3, §6). Route: charts are the local inverses of the covering `proj`; transition maps are locally translations by lattice vectors (`eventuallyEq_add_const`, from discreteness), hence analytic |
| T2 | A continuous group homomorphism `E/Λ → E'/Λ'` is induced by an `ℝ`-linear `T` with `TΛ ⊆ Λ'`; `ℂ`-linear if the homomorphism is holomorphic | M | **BUILT** (§8, about 94 lines). Route: lift through the covering (M-lift); `F(x+y) − F(x) − F(y) ∈ Λ'` is continuous on the connected `E × E`, hence 0; `AddMonoidHom.toRealLinearMap`; compare `fderiv ℂ` with the `ℝ`-derivative. The antiholomorphic variant (for T12) is the same with `conj` |
| P1 | `Ωℤ^g + ℤ^g` is a full lattice iff `det Im Ω ≠ 0` | S | **BUILT** (`periodVec_linearIndependent`, `QM.det_im_ne_zero_of_linearIndependent`, `periodLattice`) |
| P2 | `θ(z + Ωm + n) = e(−½mᵀΩm − mᵀz)θ(z)`; `θ[c,d](Ω) = e(½cᵀΩc + cᵀd)·θ(Ωc + d)` | S | **BUILT** (`riemannTheta_add_period`, `thetaChar_eq`; no convergence needed) |
| P3 | `covol(Ωℤ^g + ℤ^g) = |det Im Ω|` for Lebesgue measure on `ℂ^g` | M | **BUILT** (§9, `covolume_periodLattice`): `ZSpan.measureReal_fundamentalDomain` with the standard real basis (fundamental domain of volume 1, `volume_fundamentalDomain_stdRealBasis`) and coordinate matrix `[[Im Ω, 0], [Re Ω, 1]]` (`toMatrix_periodVec`) |
| P4 | A principal polarization (positive unimodular Riemann form `E` on Λ, `E(iu, iv) = E(u, v)`) gives a symplectic basis in which the period matrix lies in `𝔥_g` | M | Route: symplectic basis of a unimodular alternating `ℤ`-form (Frobenius normal form, M), then Riemann's bilinear relations (S given the basis). Tau Ceti has Riemann forms = polarizations (prereq-survey A9, not re-checked) |
| Q1 | pkg-I1: `Λ_τ = ι(𝒪)(τ,1)ᵀ` is a full lattice; `F'(τ)` maps `Ω(τ)ℤ² + ℤ²` onto it; `Ω(τ)` symmetric; `Ω(τ) ∈ 𝔥₂` for `Im τ > 0` | S | **BUILT** (§7). Positivity by the partial-fraction form (`OmegaPF`, `Omega_mem_siegelSpace`); sympy cross-check `det Im Ω(x+iy) = 12y²/(((x−3)²+y²)((x+1)²+y²))` (VERIFIED computation) |
| A1 | Analytic topology on `X(ℂ)` for `X` locally of finite type over `ℂ` | M-L | Cheapest faithful definition: the coarsest topology for which every `{P ∈ U}` (`U` Zariski open) is open and every `evalAt U f` is continuous on it (the "function topology"; `evalAt` is BUILT). This is the topology of the leaf's clause (iii). Then prove that on an affine `U ↪ 𝔸^n` it is the subspace topology of `ℂ^n` (M). Points: Mathlib's `Spec ℂ ⟶ X`, or closed points via `pointEquivClosedPoint` |
| A2 | For `X` smooth of relative dimension `g`, `X(ℂ)` is a complex manifold, with charts given by `g` local parameters | L | Route: at a point, choose `f₁…f_g` whose differentials span `𝔪/𝔪²` (algebraic: smoothness; bp-faltings AV3). On an affine chart `U = V(h₁…h_r) ⊂ ℂ^n`, the Jacobian criterion and the analytic inverse function theorem (M-ana) make `(f_i)` a local biholomorphism onto an open subset of `ℂ^g`. Transition maps are analytic because they are again regular functions. Main cost: the Jacobian criterion for smooth `ℂ`-algebras (Mathlib has `Smooth` and Kähler differentials, not the criterion in this form; M-L) |
| A3 | Morphisms of `ℂ`-schemes give holomorphic maps; for a group scheme `G`, `G(ℂ)` is a complex Lie group | M | from A2 and (i), since pulled-back coordinates are regular. `G(ℂ)` as a group is Mathlib (`MonObj.Hom.group`); `evalAt_comp` (BUILT) is the pull-back rule |
| A4 | `X` proper over `ℂ` ⇒ `X(ℂ)` compact | XL | Routes: (a) Chow's lemma + `ℂP^N` compact (both absent; XL); (b) for abelian varieties, projectivity (Mumford §6, XL algebraic) + `ℂP^N`; (c) a direct analytic valuative criterion (curve selection + extension over a puncture; research-level formalization). **The most expensive node.** Standard reference SGA 1 XII 3.2 (UNVERIFIED) |
| A4' | `X` geometrically integral ⇒ `X(ℂ)` connected | L | SGA 1 XII 2.4 (UNVERIFIED), via irreducible curves through two points. A5 needs `A(ℂ)` connected as an input, so A4' cannot be avoided by the Lie-theoretic argument |
| A5 | A compact connected commutative complex Lie group `G` is `Lie(G)/Λ` with `Λ = ker exp` a full lattice | L | Route: (1) one-parameter subgroups: flows of invariant vector fields exist for all time by translation invariance (M-ode, uniform time), after restricting `G` to a real manifold (absent API, S-M); (2) commutativity makes `exp` a homomorphism; it is holomorphic because flows of holomorphic invariant fields commute with `J` (M); (3) `d exp₀ = id`, so `exp` is a local biholomorphism (M-ana); (4) the image is an open subgroup, hence all of `G`; (5) the kernel is discrete; (6) compactness forces the kernel to span `Lie(G)` over `ℝ`, and `torusDiffeo` finishes. Commutativity is algebraic for abelian varieties (Mathlib), so the Lie-theoretic proof (Liouville applied to `Ad`) is not needed |
| U1 | Two uniformizations differ by a `ℂ`-linear isomorphism of lattices; `g` is invariant | M | **BUILT** (`continuous_comparison` from (i)+(iii); `exists_realLinear` from T2; `exists_complexLinear` from (i)+(ii) and the analytic inverse function theorem; `eq_of_proj_eq`, `exists_equiv`, `dim_eq`) |
| U2 | `End(A)` acts on `(ℂ^g, Λ)` by `ℂ`-linear maps, as a ring homomorphism | M | **BUILT** (`ptMap`, `evalAt_comp`, `continuous_endo`, `exists_realLinear_endo`, `exists_complexLinear_endo`, `analyticRep`, `analyticRep_unique`, `analyticRep_id`, `analyticRep_comp`, `isMonHom_mul`, `analyticRep_mul`; three lemmas, not a bundled `RingHom`) |
| U3 | Torsion `A(ℂ)[n] = φ((1/n)Λ/Λ)`; complex conjugation lifts to an antilinear involution | M | torsion **BUILT** (`torsion_iff`); conjugation: route in §1.5 |
| A6 | Tangent identification `dφ₀ : ℂ^g ≅ T_eA` and `φ^*η = c(η)·dz` | S-M | glue over the leaf, §1.1; needs bp-faltings' AV3 (`𝔪/𝔪²`) |
| G1 | GAGA for abelian varieties: holomorphic homomorphisms `A(ℂ) → B(ℂ)` are algebraic | XL | **lit** (Serre 1956; Mumford §3, UNVERIFIED); a separate leaf for T11 |

### 2.3 Cheaper special cases

- **Elliptic curves (`g = 1`, bp-faltings AN4).** Mathlib has `℘` and
  `℘'² = 4℘³ − g₂℘ − g₃` (VERIFIED). The uniformization `z ↦ (℘(z), ℘'(z))`, a group
  isomorphism `ℂ/Λ ≅ E(ℂ)`, needs surjectivity of `j` (or of `(g₂, g₃)`) and the addition
  theorem (L). It proves the leaf for `g = 1` more cheaply than A1-A5.
- **Jacobians (route (b) of bp-faltings).** Abel-Jacobi needs A1-A2 only for curves, plus path
  integrals on a Riemann surface (L-XL). It does not apply to the QM surface of F1 without first
  proving `A ≅ Jac(C)`.
- **Using the leaf.** Nothing in §1 needs the proof of the leaf, so the team can schedule
  A1-A5 last.

## 3. Recommended order of work

1. **WP-U0 (done here).** T1, T2, P1-P3, Q1, the leaf, U1, U2, and the torsion half of U3.
2. **WP-U1 (S-M, can start now; unblocks every consumer).**
   - A6 and the conjugation half of U3.
   - Restate bp-faltings' `HodgeData` construction (M4) as "Hodge data from
     `IsUniformization`", using `covolume_periodLattice` and `exists_complexLinear`.
   - Restate bp-qmmoduli's R1an as glue over the leaf (plus the family input of §1.2).
3. **WP-U2 (M).** P4 (polarizations, symplectic bases, `𝔥_g`) for a general principally
   polarized `A`.
4. **WP-U3 (L).** A1-A3: analytic topology and complex-manifold structure of `X(ℂ)` for smooth
   `X`; morphisms are holomorphic; `G(ℂ)` is a complex Lie group.
5. **WP-U4 (L).** A5, including real flows on complex Lie groups. With T1 this proves the leaf
   modulo compactness and connectedness.
6. **WP-U5 (XL).** A4 and A4'. The `g = 1` case can be done first through `℘` (§2.3).

## 4. What compiles (VERIFIED)

`lake env lean scratch/bp-analytic/Torus.lean` reports no errors and no warnings
(`linter.unusedSectionVars` is disabled at Torus.lean:20). `#print axioms`
lists only `propext`, `Classical.choice`, `Quot.sound` for each of these:
- `isManifold_torus`, `lieAddGroup_torus`, `compactSpace_torus`, `holomorphic_const`,
  `ker_torusExp`, `contMDiff_torusExp_smul`, `torusDiffeo`;
- `thetaConst_eq_riemannTheta`, `riemannTheta_add_period`, `two_nsmul_proj_charPoint`;
- `QM.det_im_Omega_ne_zero`, `QM.qmPeriodDiffeo`, `QM.qmPeriodDiffeo_add`,
  `QM.Omega_transpose`, `QM.riemannTheta_Omega_add_period`, `QM.Omega_eq_PF`,
  `QM.Omega_mem_siegelSpace`;
- `exists_realLinear_lift`, `exists_complexLinear_lift`;
- `covolume_periodLattice`, `covolume_periodLattice_of_mem`;
- `Uniformization.evalAt_comp`, `IsUniformization.continuous_comparison`,
  `IsUniformization.exists_realLinear`, `IsUniformization.exists_realLinear_endo`,
  `IsUniformization.exists_complexLinear_endo`, `IsUniformization.exists_complexLinear`,
  `IsUniformization.exists_equiv`, `IsUniformization.dim_eq`, `analyticRep_id`,
  `analyticRep_comp`, `analyticRep_mul`, `torsion_iff`.

### 4.1 Contents of `Torus.lean`

| § | Declarations | Content |
| --- | --- | --- |
| 1 | `exists_gap`, `eventuallyEq_add_const`, `contDiffOn_of_sub_mem`, `Torus`, `proj`, `proj_eq_iff`, `isAddQuotientCoveringMap_proj`, `isCoveringMap_proj`, `isLocalHomeomorph_proj`, `chartOf` (+ 4 API lemmas), `ChartedSpace E (Torus Λ)`, `chartAt_torus`, `transition_sub_mem`, `isManifold_torus` | `E/Λ` is an analytic manifold for any discrete `Λ` |
| 2 | `contMDiff_proj`, `contMDiff_of_comp_proj`, `contMDiff_of_comp_proj₂`, `lieAddGroup_torus` | analytic projection, descent, Lie group |
| 3 | `connectedSpace_torus`, `compactSpace_torus`, `AddGroupLieAlgebra … = E` (`rfl`), `torusExp`, `torusExp_apply`, `torusExp_surjective`, `ker_torusExp`, `contMDiff_torusExp`, `contMDiff_torusExp_smul`, `holomorphic_const` | compactness, exponential, kernel = Λ, Liouville |
| 4 | `SiegelSpace`, `periodVec`, `periodVec_linearIndependent`, `card_periodIndex`, `periodBasis`, `coe_periodBasis`, `periodLattice` (+ `DiscreteTopology`, `IsZLattice ℝ`), `det_im_ne_zero_of_mem_siegelSpace`, `mem_periodLattice_iff`, `SiegelTorus` | the period lattice of `Ω` (P1) |
| 5 | `intVec`, `riemannTheta`, `dotProduct_mulVec_symm`, `riemannTheta_add_int`, `riemannTheta_add_mulVec`, `riemannTheta_add_period`, `thetaChar`, `thetaChar_eq`, `Char2`, `thetaConst` (copied from pkg-I1), `charHalf`, `thetaConst_eq_thetaChar`, `thetaConst_eq_riemannTheta`, `two_nsmul_proj_charPoint` | theta functions (P2) |
| 6 | `torusAddEquiv`, `torusAddEquiv_proj`, `torusAddEquiv_symm_proj`, `torusDiffeo`, `torusDiffeo_apply` | linear changes of coordinates |
| 7 | namespace `QM`: `B`, `oBasis`, `Mi`, `Mj`, `iota`, `latVec`, `Emat`, `F0mat`, `Pinv`, `Omega` (copied from pkg-I1); `latVec0`-`latVec3`, `Emat_eq`, `F0mat_eq`, `Fp`, `det_Fp`, `sqrt2_ne_zero`, `det_Fp_ne_zero`, `Fp_mul_Omega`, `qmVec`, `qmVec_linearIndependent`, `qmBasis`, `qmLattice` (+ instances), `qmLattice_eq`, `QMTorus`, `mulVec_col`, `Fp_mulVec_periodVec`, `det_im_ne_zero_of_linearIndependent`, `imgVec`, `Fp_mulVec_periodVec'`, `imgVec_linearIndependent`, `span_imgVec`, `FpEquiv`, `FpEquiv_apply`, `det_im_Omega_ne_zero`, `map_periodLattice_Omega`, `qmPeriodDiffeo`, `qmPeriodDiffeo_add`, `qmPeriodDiffeo_proj`, `sqrt2_sq`, `Fp_mul_Emat_transpose`, `Omega_transpose`, `riemannTheta_Omega_add_period`, `OmegaPF`, `Fp_mul_OmegaPF`, `Omega_eq_PF`, `Omega_mem_siegelSpace` | pkg-I1's QM torus and its period matrix (Q1) |
| 8 | `eventuallyEq_const_of_mem`, `exists_realLinear_lift`, `exists_complexLinear_lift` | homomorphisms of tori are linear (T2) |
| 9 | `sigmaEquiv`, `stdRealBasis`, `stdRealBasis_repr_inl/inr`, `volume_unitSquare`, `volume_fundamentalDomain_stdRealBasis`, `toMatrix_periodVec`, `covolume_periodLattice`, `covolume_periodLattice_of_mem` | covolume = `|det Im Ω|` (P3) |
| 10 | namespace `Uniformization`: `AbVar`, `AbVar.ptObj`, `AbVar.Pt` (copied from `Objects.lean`), `PtIn`, `evalAt`, `IsUniformization`, `UniformizationLeaf`, `UniformizationLeafAll`, `IsUniformization.continuous_comparison`, `IsUniformization.exists_realLinear`, `ptMap`, `evalAt_comp`, `IsUniformization.continuous_endo`, `IsUniformization.exists_realLinear_endo`, `IsUniformization.exists_complexLinear_endo`, `IsUniformization.exists_complexLinear`, `eq_of_proj_eq`, `IsUniformization.exists_equiv`, `IsUniformization.dim_eq`, `analyticRep`, `analyticRep_mem`, `analyticRep_spec`, `analyticRep_unique`, `analyticRep_id`, `analyticRep_comp`, `isMonHom_mul`, `analyticRep_mul`, `nsmul_proj_eq_zero_iff`, `torsion_iff` | the leaf (AN3) and its glue (U1, U2, U3 torsion) |

Key statements (abridged):

```lean
instance isManifold_torus : IsManifold 𝓘(ℂ, E) ω (Torus Λ)          -- Λ : Submodule ℤ E, discrete
instance lieAddGroup_torus : LieAddGroup 𝓘(ℂ, E) ω (Torus Λ)
instance compactSpace_torus [FiniteDimensional ℂ E] [IsZLattice ℝ Λ] : CompactSpace (Torus Λ)
theorem ker_torusExp : (torusExp Λ).ker = Λ.toAddSubgroup
def torusDiffeo (Λ' : Submodule ℤ E') [DiscreteTopology Λ'] (T : E ≃L[ℂ] E')
    (hT : Λ.map (T.toLinearEquiv.toLinearMap.restrictScalars ℤ) = Λ') :
    Torus Λ ≃ₘ^ω⟮𝓘(ℂ, E), 𝓘(ℂ, E')⟯ Torus Λ'
theorem exists_complexLinear_lift (f : Torus Λ →+ Torus Λ')
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, E') f) :
    ∃ T : E →L[ℂ] E', (∀ v ∈ Λ, T v ∈ Λ') ∧ ∀ v, f (proj Λ v) = proj Λ' (T v)
theorem covolume_periodLattice (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : (Ω.map Complex.im).det ≠ 0) :
    ZLattice.covolume (periodLattice Ω hΩ) = |(Ω.map Complex.im).det|
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
theorem QM.Omega_transpose {τ : ℂ} (hτ : τ.im ≠ 0) : (Omega τ)ᵀ = Omega τ
def QM.qmPeriodDiffeo {τ : ℂ} (hτ : τ.im ≠ 0) :
    SiegelTorus (Omega τ) (det_im_Omega_ne_zero hτ) ≃ₘ^ω⟮𝓘(ℂ, Fin 2 → ℂ), 𝓘(ℂ, Fin 2 → ℂ)⟯
      QMTorus hτ
```

### 4.2 The leaf and its glue (`Torus.lean` §10)

```lean
/-- The value of `f ∈ Γ(U, 𝒪_A)` at a ℂ-point `P ∈ U` (0 off `U`). -/
def evalAt (U : A.X.left.Opens) (f : Γ(A.X.left, U)) (P : A.Pt ℂ) : ℂ :=
  if h : PtIn A P U then ((P.left.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom f
  else 0

structure IsUniformization {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (φ : Torus Λ ≃+ Additive (A.Pt ℂ)) : Prop where
  holo : ∀ (U : A.X.left.Opens) (f : Γ(A.X.left, U)),
    IsOpen {v : Fin g → ℂ | PtIn A (Additive.toMul (φ (proj Λ v))) U} ∧
    AnalyticOnNhd ℂ (fun v => evalAt A U f (Additive.toMul (φ (proj Λ v))))
      {v | PtIn A (Additive.toMul (φ (proj Λ v))) U}
  coords : ∀ v₀ : Fin g → ℂ, ∃ (U : A.X.left.Opens) (f : Fin g → Γ(A.X.left, U))
    (e : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)),
    PtIn A (Additive.toMul (φ (proj Λ v₀))) U ∧
    HasFDerivAt (fun v i => evalAt A U (f i) (Additive.toMul (φ (proj Λ v))))
      (e : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀
  open_map : ∀ v₀ : Fin g → ℂ, ∀ N ∈ 𝓝 (proj Λ v₀), ∃ (U : A.X.left.Opens) (k : ℕ)
    (f : Fin k → Γ(A.X.left, U)) (ε : ℝ), 0 < ε ∧
    PtIn A (Additive.toMul (φ (proj Λ v₀))) U ∧
    ∀ P : A.Pt ℂ, PtIn A P U →
      (∀ i, ‖evalAt A U (f i) P - evalAt A U (f i) (Additive.toMul (φ (proj Λ v₀)))‖ < ε) →
      ∃ q ∈ N, Additive.toMul (φ q) = P

def UniformizationLeaf : Prop :=
  ∃ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
    (φ : Torus Λ ≃+ Additive (A.Pt ℂ)), IsUniformization A Λ φ

theorem IsUniformization.exists_complexLinear (hφ : IsUniformization A Λ φ)
    (hφ' : IsUniformization A Λ' φ') :            -- [DiscreteTopology Λ] [DiscreteTopology Λ']
    ∃ T : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ), (∀ v ∈ Λ, T v ∈ Λ') ∧
      ∀ v, φ' (proj Λ' (T v)) = φ (proj Λ v)
theorem IsUniformization.exists_complexLinear_endo (hφ : IsUniformization A Λ φ)
    (α : A.X ⟶ A.X) [IsMonHom α] :
    ∃ T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ), (∀ v ∈ Λ, T v ∈ Λ) ∧
      ∀ v, Additive.toMul (φ (proj Λ (T v))) = Additive.toMul (φ (proj Λ v)) ≫ α
```

**Faithfulness review of the leaf.** This is the author's review (SPECULATIVE), plus one
independent model read-through. The read-through found no problem: it judged every clause true for
every `AbVar ℂ`, `evalAt` correct, and the statement not vacuous. It made three minor remarks,
recorded at the end of this list. A human reviewer should still check it.
- *Not vacuous.* The leaf asserts the existence of a lattice and of a group isomorphism with
  properties, over Mathlib's points and regular functions. It invents no structure.
- *Not stronger than the source.* Each clause follows from `A^an ≅ ℂ^g/Λ` (Mumford §1) and the
  construction of `A^an` (Serre GAGA §2; SGA 1 XII §1; UNVERIFIED locators):
  - (i): regular functions are holomorphic on `A^an`, and Zariski opens are open.
  - (ii): local parameters at a smooth point are étale coordinates, hence charts.
  - (iii): the analytic topology of an affine open `U ⊂ 𝔸^n` is the subspace topology of
    `ℂ^n`, so it is generated by finitely many regular functions. A neighbourhood `N` of
    `φ⁻¹(P₀)` maps onto a neighbourhood of `P₀`, which contains such a basic set.
- *Strong enough.* Clause (iii) was added after a first draft, which had only (i) and (ii).
  Without it, the comparison of two uniformizations could not be shown continuous, because
  (i) and (ii) alone do not exclude a discontinuous `φ'⁻¹φ`.

  With (iii), uniqueness and the endomorphism action are theorems: `continuous_comparison`,
  `exists_complexLinear`, `continuous_endo`, `exists_complexLinear_endo`. They are proved
  using only the clauses.
- *Junk values.* `evalAt` is `0` off `U`. Clause (i) asks for openness of `φ⁻¹(U)` and
  analyticity only at points of that open set, so the junk value is never seen. Clause (iii)
  only evaluates at points of `U`.
- *Dimension.* `g` is existential. Clause (ii) forces `g = dim A` analytically. A consumer that
  needs `g = dim A` algebraically can add it as a conjunct, which is a consequence of Mumford §1.
  `dim_eq` (BUILT) shows that `g` is the same for all uniformizations.
- *Model read-through, remarks.*
  - **Locators.** In Mumford, "a compact connected complex Lie group is a torus" is §1, but its
    application to `A(ℂ)` is §4. Compactness and connectedness of `A^an` are SGA 1 XII 3.2 and
    2.4 (with 3.1). All of these are UNVERIFIED.
  - **Functions, not differentials.** The leaf speaks about functions only. Comparing `Λ` with
    `H⁰(A, Ω¹)` (glue A6, needed for the Faltings metric) is extra glue. It looks derivable,
    because forms are locally `f·dh` with `f`, `h` regular.
  - **Torsion.** `torsion_iff` uses only the group isomorphism `φ`, not the analytic clauses.

## 5. Findings that affect other notes

1. **pkg-I1's "Faithfulness" claim** (that `Ω(τ)` is a period matrix of `ℂ²/Λ_τ`) is now proved
   in Lean: for every `τ ∉ ℝ`, the lattice, torus and symmetry parts (`qmPeriodDiffeo`,
   `Omega_transpose`); for `Im τ > 0`, `Ω(τ) ∈ 𝔥₂` (`Omega_mem_siegelSpace`). The compatibility
   with N5's Riemann form is by pkg-I1's construction and is not re-proved here.
2. **bp-qmmoduli R1an**, as written, is pointwise in `P`. The glue that turns it into F1 also uses
   the holomorphy of `τ ↦ π(A_τ)`, a family statement about the Shimura curve (§1.2). Recommend
   recording that input in R1an or R1.
3. **bp-faltings AN3** can be replaced by `UniformizationLeaf` plus glue A6 for stating M4/H1-H3
   and the leaves R18-R22.
   - bp-faltings §5 WP-D says "`GroupModel.height` cannot be defined until AN3 exists". That is
     no longer true.
   - The height can be defined from the leaf's data. Its independence of the choice of
     `(Λ, φ)` follows from `exists_complexLinear` (BUILT) and bp-faltings' `torusMetricSq_comap`.
   - The archimedean term in period-matrix form is `covolume_periodLattice` (BUILT).
4. **Mathlib TODO.** The `IsManifold` instance that `Instances/Quotient.lean` lists as a TODO
   (quotients by smooth properly discontinuous actions) is done here in the special case of
   lattices in normed spaces. The argument (`eventuallyEq_add_const`) generalizes to actions by
   isometries with discrete orbits. A candidate upstream contribution, together with T2.

## 6. Unchecked items (UNVERIFIED or not done)

1. **Locators recalled from memory:**
   - Mumford, *Abelian varieties*: §1 (a compact connected complex Lie group is a torus), §3
     (GAGA consequences), §4 (application to `A(ℂ)`), §6 (projectivity);
   - Serre, *Géométrie algébrique et géométrie analytique* (1956), §2;
   - SGA 1 XII 2.4, 3.1, 3.2;
   - Eichler's class-number theorem for indefinite quaternion orders;
   - Silverman, AEC VI;
   - Birkenhake-Lange, *Complex abelian varieties*, Ch. 1 and 4 (period matrices, Riemann
     relations).
2. **Not built:** P4, A1-A5, A6, the conjugation half of U3, G1. **Not proved in Lean:** the
   polarization of `ℂ²/Λ_τ` (N5's Riemann form in the symplectic basis).
3. **Library items not re-checked:** Tau Ceti Riemann forms (prereq-survey A9).
4. **Estimates and review:** the size tiers and line estimates are SPECULATIVE. The faithfulness
   review of `IsUniformization` (§4.2) is the author's, plus one model read-through. No human
   has reviewed it.
