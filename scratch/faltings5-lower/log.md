# faltings5-lower results log

Base: 9a100aa72 (leaf-fold22b). Started 2026-11-15 05:16 PST.

## Statement analysis (VERIFIED, read)
- `GroupModel.height 𝒢 = ⨅ g (M : MetrizedModel A L g) (_ : M.model = 𝒢), M.hodge.modelHeight` (EReal),
  ZInQKernel/HDecomp/Faltings/Height.lean:235.
- Direction: FaltingsLemma5Lower ⟺ h(𝒩B) ≤ h(𝒩A) + ½ log deg φ. Upper bound of an infimum by an infimum:
  for each metrization M of 𝒩A, build a metrization M' of 𝒩B with modelHeight M' ≤ modelHeight M + ½ log deg φ.
  No product formula / uniformization uniqueness needed (no `AnalyticUniformizationUnique`).
- `modelHeight_eq`: for η ∈ lattice, η ≠ 0: h = (log secIndex Λ η − ½ Σ_σ log (‖coeff σ η‖² covol(periods σ)))/[K:ℚ].
- Bundle-field help: `AvSplit.MilneIsogenyQuasiInverse` (TailQ.lean:1207; field `OpenAddedLeaves17.milneIsogenyQuasiInverse`,
  available at TailZ23 L814 as `l.milneIsogenyQuasiInverse`, l : OpenAddedLeaves12). Plan: use it for the étaleness
  of φ at the origin (dφ injective on tangent vectors via Tangent.lean `eq_one_of_comp_intCast`).

## Plan (05:55)
Reduction `faltingsLemma5Lower_of` from three glue statements, then prove them:
- P1 `cotMap 𝒩A 𝒩B φ_N` bijective (étale at origin; Milne + Tangent.lean + dims).
- P2 surjectivity of `p ↦ p ≫ φ_N` on `Pts τ` (lifting ℂ-points along finite surjective).
- P3 `{p : 𝒩A.Pts τ // p ≫ φ_N = 1}` finite with card ≤ isogDeg φ.
Archimedean: Λ_B := Φ_A⁻¹(ker φ_N(ℂ)) ⊇ Λ_A, index = #ker φ_N(ℂ)_τ ≤ deg φ; covol Λ_A = index · covol Λ_B
(Mathlib `ZLattice.covolume_div_covolume_eq_relIndex` is for ι → ℝ only; transfer needed).

## Results so far (all compiled with `lake env lean`, no sorry)
Module dir ZInQKernel/Contrib/OneProof/FaltingsLemma5Lower/:
- Gen.lean: H5Glue transport lemmas (genMap, cotMap, hodgeMap, jacDet_comp_genMap, cotMap_omega ...) for
  models of different abelian varieties A, B (VERIFIED, compiled 06:00).
- Lattice.lean: `covolume_eq_relIndex_mul` (any Haar measure, any fin-dim real normed space; via Haar uniqueness
  `isAddLeftInvariant_eq_smul` + Mathlib's pi case), `discreteTopology_of_le_of_relIndex`, `isZLattice_of_le` (VERIFIED).
- Assembly.lean: `height_le_of_metrized` — for f : M.model → 𝒩 a mon hom bijective on cotangent spaces, surjective
  on complex points, with complex kernels of order ≤ d: 𝒩.height ≤ M.modelHeight + ½ log d (VERIFIED).
- Reduction.lean: `faltingsLemma5Lower_of (IsogCotBijective) (IsogPtsSurjective) (IsogKerCard)` (VERIFIED).
- Transport.lean: theta (points of 𝒩 over O_K with values in K-schemes T = T-points of A), multiplicative,
  natural; `kerEquiv` (VERIFIED).
- Surj.lean: `isogPtsSurjective : IsogPtsSurjective` (Mathlib `pointOfClosedPoint` on the finite fibre) (VERIFIED).
- Ker.lean: `isogKerCard : IsogKerCard` (kernel scheme pullback φ e, ring maps of points via Tangent.ptRing,
  algebraic elements of ℂ lie in ι(K̄), `Finite.algHom`) (VERIFIED).
Remaining: `IsogCotBijective` (étaleness at the origin). Plan: Milne quasi-inverse (bundle field) + Tangent.lean.

## 06:20 — main theorem proved (VERIFIED: `lake build ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower` succeeds;
`#print axioms` = [propext, Classical.choice, Quot.sound])
- `GapHeight.faltingsLemma5Lower (hM : AvSplit.MilneIsogenyQuasiInverse) : ZInQ.HeightSplit.FaltingsLemma5Lower`.
- P1 `isogCotBijective (hM) : IsogCotBijective` (CotPts/Cot/CotTan/CotFinal): derivation at origin killing f^* →
  tangent vector v of A with v ≫ φ = 1 → (Milne) v ≫ [d] = 1 → v = 1 (Tangent.eq_one_of_comp_intCast) → D = 0;
  dims via kernel TangentDim (tangentDim_of_regular ∘ regularOrigin_of/dimOrigin_of ∘ originStalkIso_of genericFibreStalkIso)
  and topologicalKrullDim_eq_of_finite_surjective.
- Semistability hypotheses of FaltingsLemma5Lower unused; Néron property of 𝒩B used only via CToPrinted.exists_extension.

## 06:25 deliverables
- `#discharges` (VERIFIED, run): 63 open, 1765 checked, 5 discharge one (no new match; manual fold).
- LiveUses.lean (VERIFIED): closure of frozenTarget (244035 consts) contains faltingsLemma5Lower_of_printed,
  faltingsLemma5BCLower_of_printed, OpenResearchLeaves14..21.faltingsLemma5Printed; not faltingsLemma5BC_of_printed
  (TailZ19 L1898) nor OpenResearchLeaves12/13 projections.
- FoldCheck.lean (VERIFIED, compiled): open17' (replacement term) .. open28', frozenTarget' with standard axioms; its
  closure lacks faltingsLemma5Lower_of_printed / faltingsLemma5BCLower_of_printed / OpenResearchLeaves14 projection.
- Report docs/research/faltings5-lower.md, .fleet/faltings5-lower.md written.

## 07:00 Milne hypothesis removed (VERIFIED, compiled)
- KerRing.lean: kernel points over any K-algebra Λ ↔ ring maps Γ(ker) → Λ (ringOf/ptOf, natural).
- TanFinite.lean: `tangent_trivial` (char 0, finite φ): Cartier's argument (universal point × tangent vector in
  G(R[ε]) gives derivation D̃ of R with e∘D̃ = D; Artinian R via IsArtinian.exists_pow_succ_smul_dvd; descending
  induction). Axioms standard.
- `GapHeight.faltingsLemma5Lower : ZInQ.HeightSplit.FaltingsLemma5Lower` now with no hypotheses; module builds.
- #discharges rerun: 63 open, 1806 checked, 5 discharge one. FoldCheck rerun with replacement
  `ReductSplit.faltingsLemma5BCLower_final GapHeight.faltingsLemma5Lower`: frozenTarget' standard axioms.
