# g0-thetapoint: `ThetaPointOfFibre` (g0-split missing piece 9) from smaller named Props

Task g0-thetapoint, 2026-11-13. Lean: `scratch/g0-thetapoint/ThetaPoint.lean`. `build.sh` assembles
it from g0-split's `Split.lean` (verbatim, plus one import) and the new section
`scratch/g0-thetapoint/part_theta.lean`. Log: `scratch/g0-thetapoint/log.md`.

## 1. Result

**Verdict: the piece is true as far as model review can tell, and it is not vacuous.** It is now
proved in Lean, with no `sorry`, from two strictly smaller named Props: one glue Prop
(`FibreQMPeriod`) and one leaf candidate (`ThetaRatiosAlgebraic`). The piece's statement is
unchanged: it is the `def` in g0-split's `Split.lean`, included verbatim.

```
theorem HSyn.G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios
    (hQM : FibreQMPeriod) (hAlg : ThetaRatiosAlgebraic) : ThetaPointOfFibre

theorem HSyn.G0Split.ThetaPt.thetaPointOfFibre_of_parts (hDim : DimBaseChange)
    (hU : UniformizationExistsNF) (hQM : FibreQMPeriodAll) (hAlg : ThetaNullAlgebraic) :
    ThetaPointOfFibre

theorem HSyn.glueOutputs_of_leaves_thetaParts ... (hQM : FibreQMPeriod)
    (hAlg : ThetaRatiosAlgebraic) ... : GlueAssembly.GlueOutputs ZInQ.Mult.S_mul
```

VERIFIED: `lake env lean scratch/g0-thetapoint/ThetaPoint.lean` reports 0 errors and no
`declaration uses sorry` (run8, 2m40s). `#print axioms` gives `[propext, Classical.choice,
Quot.sound]` for `thetaConst_odd`, `thetaPointOfFibre_of`, `fibreThetaF1_of`,
`fibreQMPeriod_of_all`, `thetaPointOfFibre_of_qm`, `thetaNullAlgebraic_of_ratios`,
`thetaPointOfFibre_of_qm_ratios`, `thetaPointOfFibre_of_parts` and
`HSyn.glueOutputs_of_leaves_thetaParts`. The last theorem is g0-split's main theorem with piece 9
replaced by its parts. Prerequisites: `lake build ZInQKernel.HDecomp.Analytic.QMLattice` and
`lake build ZInQKernel.Hypotheses.JHeight`. The second builds the upstream `lean/` helpers that
`Split.lean` imports.

There are two routes, and both compile:

* **Route E (existential, weakest hypotheses):** `FibreQMPeriod` + `ThetaRatiosAlgebraic`
  (or `ThetaNullAlgebraic`, which `ThetaRatiosAlgebraic` implies).
* **Route A (universal):** `DimBaseChange` (g0-split piece 2, unchanged) +
  `UniformizationExistsNF` + `FibreQMPeriodAll` + `ThetaNullAlgebraic`. These imply route E's
  hypothesis (`fibreQMPeriod_of_all`). This route separates the textbook existence of a
  uniformization from the moduli-theoretic content.

## 2. The named Props

All of them are in namespace `HSyn.G0Split.ThetaPt`, each a `def … : Prop` with a docstring.
Sizes are SPECULATIVE.

| Prop | kind | statement (informal) | sources | size |
|---|---|---|---|---|
| `UniformizationExistsNF` | TEXTBOOK leaf candidate | an abelian surface `A/K` over a number field has an analytic uniformization `Φ : ℂ² → A(ℂ)_σ` (`IsUniformization`) at some `σ : K → ℂ` | Mumford, *Abelian Varieties* §1, with GAGA (UNVERIFIED locators). The build already has it over `ℂ` from bp-analytic's leaf: `ZInQ.LeafPush2.exists_isUniformization_of_leaf` (UnifBridge.lean), for some `g` | medium (base change `K → ℂ`, `g = dim A`) |
| `FibreQMPeriodAll` | GLUE | for `u ∉ 𝒞`, every model `A` of the fibre over `J(u)`, every `σ` and every uniformization with kernel `Λ`: a `ℂ`-linear `F` carries `Λ` onto bp-analytic's `qmLattice τ = ι(𝒪)(τ,1)ᵀ` for some `τ ∈ ℍ`, and `jNum(Ω(τ))/jDen(Ω(τ)) = J(u)` | R1(b) (placeholder `R01b_ComplexUniformization`; Shimura 1967), `PkgI1.QMHauptmodul` (from R2-R4), `R2fpProps`'s CM values, uniqueness of uniformizations (bp-analytic `IsUniformization.exists_complexLinear`, proved in the build over `ℂ`) | large |
| `FibreQMPeriod` | GLUE | the same with "some `σ`, some uniformization" | as above | large |
| `ThetaNullAlgebraic` | LEAF-COMPOSITE (leaf candidate) | for `A` over a number field, a uniformization with kernel `Λ` and any `Ω ∈ 𝔥₂` that is a period matrix of `Λ`: `c·θ_m(0,Ω) = emb(z_m)` for some `c ≠ 0` and a point `z ∈ L¹⁶` of a number field `L` | algebraicity of polarizations (`NS(A_ℚ̄) = NS(A_ℂ)`) plus algebraicity of theta-constant ratios: Thomae (Mumford, *Tata Lectures on Theta II*, IIIa §8) or Shimura (Duke 43, 1976), Faltings–Chai Ch. V (all UNVERIFIED) | — (cited) |
| `ThetaRatiosAlgebraic` | LEAF candidate (the literature form) | same hypotheses; some `θ_{m₀}(0,Ω) ≠ 0` and every ratio `θ_m(0,Ω)/θ_{m₀}(0,Ω)` is an algebraic number. It implies `ThetaNullAlgebraic` (**proved**, `thetaNullAlgebraic_of_ratios`: `L = ℚ(ratios) ⊆ ℂ`, `c = θ_{m₀}⁻¹`) | as for `ThetaNullAlgebraic`; nonvanishing: at most one even theta constant vanishes in genus 2 (Igusa, UNVERIFIED locator) | — (cited) |
| `FibreThetaF1` | GLUE, **proved** from `FibreQMPeriod` | some uniformization of the fibre has a period matrix `Ω ∈ 𝔥₂` with `j_θ(Ω) = J(u)` | — | done |

Neither `ThetaNullAlgebraic` nor `ThetaRatiosAlgebraic` is one printed theorem. Each composes
published results (algebraicity of the polarization given by `Ω`, then algebraicity of theta
ratios for a principally polarized abelian variety over `ℚ̄`), so both are leaf *candidates*
for a human to check, not leaves in the strict sense of the task. `ThetaRatiosAlgebraic` is the
closer of the two to the printed form. Splitting either along the composition needs a
polarization object on `PkgI3.AbVar`, which the project does not have.

### Proved glue (new Lean, all in `part_theta.lean`)

* `f1_of_theta`: if `emb(z_m) = c·θ_m(Ω)` with `c ≠ 0` and `j_θ(Ω) = q ∈ ℚ`, then the ten even
  coordinates `z'` satisfy `3779136(∏z')⁴/(Σz'⁸)⁵ = q` in `L`. The proof uses that `j_θ` is
  homogeneous of degree 0 (`c⁴⁰` cancels, even when the denominator is 0) and that `emb` is
  injective.
* `height_even`: `h(z') ≤ h(z)`, from Mathlib's `Height.logHeight_comp_le`. Dropping coordinates
  never raises the height, so the odd theta constants are not needed.
* `thetaConst_odd`: the six odd theta constants vanish, for every `Ω`. The proof reindexes by
  `n ↦ -n-a` and uses `Equiv.tsum_eq`, so no summability is needed. This confirms the remark in
  the piece's docstring.
* `thetaConst_eq_pkgI1`, `jTheta_eq`: leaf-push2's `θ_m` is pkg-I1's, and `j_θ = jNum/jDen` (the
  function of `PkgI1.QMHauptmodul`).
* `omega_eq`: `PkgI1.Omega τ = BPAnalytic.QM.Omega τ`, by `rfl` (two copies of the same text).
* `isSiegel_Omega` and `isPeriodMatrix_qmLattice` (from bp-analytic's kernel lemmas), and
  `isPeriodMatrix_of_map`, `isPeriodMatrix_of_comap`: `Ω(τ)` is a period matrix of every lattice
  that is linearly isomorphic to `Λ_τ`.
* `exists_nf_of_isAlgebraic`: finitely many algebraic complex numbers lie in the image of a
  number field (`IntermediateField.adjoin`, `finiteDimensional_adjoin`).
* `thetaPointOfFibre_of`, `fibreThetaF1_of_qm`, `thetaNullAlgebraic_of_ratios`,
  `thetaPointOfFibre_of_qm_ratios`, `fibreQMPeriod_of_all`, `fibreThetaF1_of`,
  `thetaPointOfFibre_of_qm`, `thetaPointOfFibre_of_parts`, `HSyn.glueOutputs_of_leaves_thetaParts`.

## 3. Checks on the piece and on the new Props

These are model checks, with no human review.

* **The height clause carries no theta content (VERIFIED, Lean).** In `ThetaPointOfFibre`, `z'`
  (in `K'`) is not tied to the theta point `z`. Taking `K' = L` and `z'` = the even coordinates
  of `z` makes `h(z') ≤ h(z)` automatic. The piece's real content is therefore (i) a
  uniformization with a Siegel period matrix, (ii) algebraicity of the theta point, and (iii) F1
  for its even coordinates.
* **Not vacuous.** The hypotheses `R1fpProps`, `R2fpProps`, `u ∉ 𝒞`, `FibreOver` are those of
  g0-split's other pieces. The conclusion is existential, and every existential is witnessed by
  genuine objects (bp-analytic: `Ω(τ) ∈ 𝔥₂` is a period matrix of `Λ_τ`, VERIFIED in the build).
* **`IsUniformization` cannot be satisfied degenerately.** Its conditions make `Φ` a surjective
  holomorphic homomorphism `ℂ² → A(ℂ)`. Its differential at 0 must then be invertible (otherwise
  the image has dimension `< 2`), so `Λ` is a lattice. If `dim A ≠ 2`, either no `Φ` exists or
  `Λ` has rank `≠ 4`, in which case no period matrix exists and the hypotheses of
  `ThetaNullAlgebraic` are contradictory. This is a model argument.
* **`ThetaNullAlgebraic` is quantified over every `Ω`**, that is, over every principal
  polarization of `ℂ²/Λ` and every symplectic basis (see the docstring of `IsPeriodMatrix`). It is
  true because every Riemann form on `A(ℂ)_σ` is algebraic and defined over `ℚ̄`, and theta
  ratios of a principally polarized abelian surface over `ℚ̄` are algebraic. It does not need
  `Ω` to be "the" polarization of the QM object.
* **`FibreQMPeriodAll` is quantified over every `σ`.** `σ` is a Galois conjugate of
  `ℚ̄ → ℂ` composed with the embedding of `FibreOver`. `π` is defined over `ℚ` and
  `J(u) ∈ ℚ`, so the conjugate object again lies over `J(u)`. Uniformizations of one torus differ
  by a `ℂ`-linear automorphism, which bp-analytic proves over `ℂ`. The value comes from
  comparing Hauptmoduln: `τ ↦ π(P_τ)` (R1(b)(c)) and `QMHauptmodul`'s `f` have the same values
  `0, ∞, -16/27` at the CM points of discriminants `-4, -3, -24`, so they are equal (Möbius). The
  QM object's polarization plays no role. `jDen(Ω(τ)) ≠ 0` holds because `J(u)` is finite and
  `χ₁₀ ≠ 0` on the simple surface. The Prop inherits the SPECULATIVE premise bp-qmmoduli §2.2,
  like every leaf-qm-fp object.
* **Numerical checks (`scratch/g0-thetapoint/theta_check.py`, 220-430 digits).**
  * At the CM point `τ₋₂₄`: `j_θ(Ω(τ)) = -16/27`, the odd theta constants are `< 10⁻²²⁰`, and
    every `(θ_m/θ_{m₀})⁴` satisfies an integer polynomial of degree 2 or 4 with coefficients
    `< 10³`. This is evidence for `ThetaRatiosAlgebraic` at one point (VERIFIED numerically).
  * At a non-CM fibre (`u = 1`): `τ_u ≈ 1.3933 + 0.8693i` solves `j_θ(Ω(τ)) = J(1)`, the odd theta
    constants vanish there, and no even one does. Algebraicity there is inconclusive: no relation
    of degree `≤ 12` and small height; the degree-12 relations seen at 220 digits did not survive
    at 430 digits.
* `Jmap` in the piece is `ZInQ.JHeight.Jmap u = -57600F(u)²/G(u)⁶` (VERIFIED, read).

## 4. What compiles, what remains

* **Compiles (VERIFIED):** all of `ThetaPoint.lean` (20 300 lines), with no `sorry`.
* **Remains:** `FibreQMPeriod` (or `UniformizationExistsNF` + `FibreQMPeriodAll`) and
  `ThetaRatiosAlgebraic` (or `ThetaNullAlgebraic`).
  * Next split of `FibreQMPeriod`, the Hauptmodul route: R1(b) made concrete (it is opaque in
    `ResearchLeaves`) plus the Möbius uniqueness of a Hauptmodul with three prescribed values.
  * Next split of `FibreQMPeriod`, Glazer's own F1 route: R3 (leaf-push2's concrete
    `R03_LinYang`: the fibre is the Jacobian of a sextic on the Lin–Yang locus at `j = J(u)`),
    plus Igusa's comparison of the algebraic `ψ₄`, `χ₁₀` of the curve with the theta expressions
    at its period matrix, plus `PkgI1.f1_algebra`. This route needs the period matrix of the
    *canonical* polarization of `Jac(C)`, so `IsPeriodMatrix` (which allows any principal
    polarization) would have to be refined first. Whether a QM surface of discriminant 6 has a
    unique principal polarization is UNVERIFIED (Rotger's counts).
  * `UniformizationExistsNF`: from bp-analytic's `UniformizationLeafAll` via base change along
    `σ`. This needs (a) a transport between the kernel's `AbVar` and `PkgI3.AbVar` and between
    `ℂ`-points of `A_ℂ` and `CPts A σ`, and (b) the identification of the uniformization's `g`
    with `dim A = 2`. UnifBridge's docstring says (b) is not yet done. Neither is done here.
* **Integration:** append `part_theta.lean` after g0-split's section, and add
  `import ZInQKernel.HDecomp.Analytic.QMLattice` (needed for `qmLattice`, `Omega_mem_siegelSpace`,
  `map_periodLattice_Omega`). No name in `Split.lean` clashes with bp-analytic's `BPAnalytic`
  namespace (VERIFIED by compiling). In `MissingPieces`, the field `thetaPoint` can then be
  replaced by `FibreQMPeriod` and `ThetaRatiosAlgebraic`.
