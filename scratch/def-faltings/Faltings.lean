import Mathlib

/-!
# def-faltings: the stable Faltings height as an infimum of model heights

Task def-faltings (2026-11-12). Mathlib-only, self-contained (scratch files cannot import each
other). Sections 1-14 are copied from `scratch/bp-faltings/Hodge.lean` (namespace renamed); they
build the Arakelov degree of a Hermitian line on `Spec 𝓞_K`, the torus metric and `HodgeData`.
Sections 15-22 are new:

* 15. `AbVar`, `GroupModel` (copied from `scratch/bp-faltings/Models.lean`).
* 16. The Hodge line of a smooth group model `𝒢/𝓞_L` (nodes AV3, M2, M3), built from the local
  ring `𝒪_{𝒢,ξ}` at the identity `ξ` of the generic fibre: `cotangent = 𝔪_ξ/𝔪_ξ²`,
  `omega = ω_𝒢 = ⋂_s (image of I_{e(s)})`, `hodgeSpace g = L ⊗_{𝓞_L} ⋀^g cotangent`,
  `detLattice g = ⋀^g ω_𝒢`.
* 17. Complex points `𝒢(ℂ)_τ` with their group law (Mathlib), evaluation of regular functions,
  and **`IsAnalyticUniformization`**: the concrete Prop saying that `Φ : ℂ^g → 𝒢(ℂ)_τ` is a
  holomorphic surjective homomorphism with kernel `Λ`. This is where node AN3 enters: the
  *definition* constrains the archimedean data by this Prop; the *missing theorem* is
  `AnalyticUniformizationExists` (stated, unproved).
* 18. `MetrizedModel A L g`, `stableFaltingsHeight A : EReal` (node H3), Deligne's normalization.
* 19-20. Acceptance tests AT1 (elliptic curves) and AT2 (genus 2), statements and conditional
  forms (proved).
* 21. Leaves R19-R21 stated over `stableFaltingsHeight`; R18, R22: what is missing.
-/

namespace ZInQ.DefFaltings

open NumberField MeasureTheory

/-! ## 1. Norms and complex embeddings -/

section Embeddings

variable {K : Type*} [Field K] [NumberField K]

/-- `∑_{σ : K → ℂ} log |σ x| = log |N_{K/ℚ}(x)|` (the archimedean half of the product formula). -/
theorem sum_log_norm_embeddings (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ x‖ = Real.log |(Algebra.norm ℚ x : ℝ)| := by
  rw [← Real.log_prod (fun σ _ => by simpa using hx)]
  congr 1
  have h := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  simp only [norm_prod] at h
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f x‖) (fun φ => ‖φ x‖)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← h]
  simp

/-- The same for an algebraic integer, with the integer norm. -/
theorem sum_log_norm_embeddings_int (a : 𝓞 K) (ha : a ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ (a : K)‖ = Real.log ((Algebra.norm ℤ a).natAbs : ℝ) := by
  rw [sum_log_norm_embeddings _ (by simpa using ha), ← Algebra.coe_norm_int]
  simp [Nat.cast_natAbs]

end Embeddings

/-! ## 2. Hermitian line bundles on `Spec 𝓞_K` and the Arakelov degree -/

section Arakelov

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/-- The index `#(M / 𝓞_K s)` (as a natural number; `0` if infinite). -/
noncomputable def secIndex (M : Submodule (𝓞 K) V) (s : V) : ℕ :=
  (Submodule.span (𝓞 K) {s}).toAddSubgroup.relIndex M.toAddSubgroup

/-- **Change of section.** For `a ∈ 𝓞_K` and `0 ≠ s ∈ M`:
`#(M / 𝓞_K·as) = |N(a)| · #(M / 𝓞_K·s)`. -/
theorem secIndex_smul (M : Submodule (𝓞 K) V) {s : V} (hsM : s ∈ M) (hs : s ≠ 0) (a : 𝓞 K) :
    secIndex M (a • s) = (Algebra.norm ℤ a).natAbs * secIndex M s := by
  classical
  let φ : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V s
  have hφ : Function.Injective φ := by
    intro x y hxy
    simp only [φ, LinearMap.toSpanSingleton_apply] at hxy
    have h1 : algebraMap (𝓞 K) K (x - y) • s = 0 := by
      rw [algebraMap_smul, sub_smul, hxy, sub_self]
    rcases smul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp (IsFractionRing.injective (𝓞 K) K (by simpa using h))
    · exact absurd h hs
  have h1 : Submodule.span (𝓞 K) {a • s} = Submodule.map φ (Ideal.span {a}) := by
    rw [Submodule.map_span, Set.image_singleton]
    simp [φ]
  have h2 : Submodule.span (𝓞 K) {s} = Submodule.map φ (⊤ : Ideal (𝓞 K)) := by
    rw [Submodule.map_top, LinearMap.span_singleton_eq_range]
  have hle1 : Submodule.span (𝓞 K) {a • s} ≤ Submodule.span (𝓞 K) {s} :=
    Submodule.span_le.mpr (by
      simpa using Submodule.smul_mem _ a (Submodule.mem_span_singleton_self s))
  have hle2 : Submodule.span (𝓞 K) {s} ≤ M := Submodule.span_le.mpr (by simpa using hsM)
  unfold secIndex
  rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hle1)
    (Submodule.toAddSubgroup_mono hle2)]
  congr 1
  rw [h1, h2, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ hφ, Submodule.top_toAddSubgroup,
    AddSubgroup.relIndex_top_right, ← Ideal.absNorm_span_singleton, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  rfl

/-- **A Hermitian line bundle on `Spec 𝓞_K`**, in generic-fibre form. `V` is a one-dimensional
`K`-vector space (the generic fibre), `lattice` is the `𝓞_K`-module of global sections (an
invertible `𝓞_K`-module, i.e. a rank-one lattice in `V`), and `norm σ` is a norm on the complex
line `V ⊗_{K,σ} ℂ`, recorded through its values on `V`. Conjugation symmetry
(`‖v‖_σ̄ = ‖v‖_σ`) is not needed for the degree and is not imposed. -/
structure HermitianLattice (K : Type*) [Field K] [NumberField K] (V : Type*) [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] where
  /-- The `𝓞_K`-module of sections. -/
  lattice : Submodule (𝓞 K) V
  /-- `V` is a line. -/
  finrank_eq_one : Module.finrank K V = 1
  /-- `lattice` is a full lattice: some nonzero section generates a subgroup of finite index
  (then every nonzero section does, `secIndex_ne_zero`). -/
  isLattice : ∃ s ∈ lattice, s ≠ 0 ∧ secIndex lattice s ≠ 0
  /-- The norm on `V ⊗_{K,σ} ℂ`. -/
  norm : (K →+* ℂ) → V → ℝ
  norm_smul : ∀ σ (a : K) (v : V), norm σ (a • v) = ‖σ a‖ * norm σ v
  norm_pos : ∀ σ (v : V), v ≠ 0 → 0 < norm σ v

namespace HermitianLattice

variable (L : HermitianLattice K V)

/-- The Arakelov degree computed with the section `s`:
`log #(M / 𝓞_K s) − ∑_{σ : K → ℂ} log ‖s‖_σ`. -/
noncomputable def degreeAt (s : V) : ℝ :=
  Real.log (secIndex L.lattice s) - ∑ σ : K →+* ℂ, Real.log (L.norm σ s)

theorem degreeAt_smul {s : V} (hsM : s ∈ L.lattice) (hs : s ≠ 0)
    (hi : secIndex L.lattice s ≠ 0) {a : 𝓞 K} (ha : a ≠ 0) :
    L.degreeAt (a • s) = L.degreeAt s := by
  have hN : (Algebra.norm ℤ a).natAbs ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using (Algebra.norm_ne_zero_iff (R := ℤ)).mpr ha
  have has : a • s = (a : K) • s := (algebraMap_smul K a s).symm
  have hσ : ∀ σ : K →+* ℂ, Real.log (L.norm σ ((a : K) • s)) =
      Real.log ‖σ (a : K)‖ + Real.log (L.norm σ s) := by
    intro σ
    rw [L.norm_smul, Real.log_mul]
    · simpa using ha
    · exact (L.norm_pos σ s hs).ne'
  unfold degreeAt
  rw [secIndex_smul _ hsM hs, has, Finset.sum_congr rfl (fun σ _ => hσ σ), Finset.sum_add_distrib,
    sum_log_norm_embeddings_int a ha]
  push_cast
  rw [Real.log_mul (by exact_mod_cast hN) (by exact_mod_cast hi)]
  ring

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem _root_.ZInQ.DefFaltings.exists_smul_eq (hV : Module.finrank K V = 1)
    {s t : V} (hs : s ≠ 0) :
    ∃ b d : 𝓞 K, d ≠ 0 ∧ (d : K) • t = (b : K) • s := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' s hs).mp hV t
  obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
  refine ⟨b, d, nonZeroDivisors.ne_zero hd, ?_⟩
  have hd' : (algebraMap (𝓞 K) K d) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  rw [← hc, smul_smul, mul_div_cancel₀ _ hd']

/-- Every nonzero section has finite index. -/
theorem secIndex_ne_zero {t : V} (htM : t ∈ L.lattice) (ht : t ≠ 0) :
    secIndex L.lattice t ≠ 0 := by
  obtain ⟨s, hsM, hs, hi⟩ := L.isLattice
  obtain ⟨b, d, hd, h⟩ := exists_smul_eq L.finrank_eq_one (t := t) hs
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_smul, smul_eq_zero] at h
    rcases h with h | h
    · exact hd (by exact_mod_cast h)
    · exact ht h
  have e1 := secIndex_smul L.lattice htM ht d
  have e2 := secIndex_smul L.lattice hsM hs b
  have h' : d • t = b • s := by
    rw [← algebraMap_smul K d t, ← algebraMap_smul K b s]; exact h
  have : (Algebra.norm ℤ d).natAbs * secIndex L.lattice t =
      (Algebra.norm ℤ b).natAbs * secIndex L.lattice s := by
    rw [← e1, ← e2, h']
  intro h0
  rw [h0, mul_zero] at this
  have hN : (Algebra.norm ℤ b).natAbs ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using (Algebra.norm_ne_zero_iff (R := ℤ)).mpr hb
  exact hi (by simpa [hN] using this.symm)

/-- **Independence of the section.** -/
theorem degreeAt_eq {s t : V} (hsM : s ∈ L.lattice) (hs : s ≠ 0) (htM : t ∈ L.lattice)
    (ht : t ≠ 0) : L.degreeAt s = L.degreeAt t := by
  obtain ⟨b, d, hd, h⟩ := exists_smul_eq L.finrank_eq_one (t := t) hs
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_smul, smul_eq_zero] at h
    rcases h with h | h
    · exact hd (by exact_mod_cast h)
    · exact ht h
  have e1 := L.degreeAt_smul htM ht (L.secIndex_ne_zero htM ht) hd
  have e2 := L.degreeAt_smul hsM hs (L.secIndex_ne_zero hsM hs) hb
  have h' : d • t = b • s := by
    rw [← algebraMap_smul K d t, ← algebraMap_smul K b s]; exact h
  rw [← e1, ← e2, h']

/-- **The Arakelov degree** `deg(M̄) = log #(M / 𝓞_K s) − ∑_σ log ‖s‖_σ` for any `0 ≠ s ∈ M`. -/
noncomputable def arakelovDegree : ℝ := L.degreeAt L.isLattice.choose

theorem degreeAt_eq_arakelovDegree {s : V} (hsM : s ∈ L.lattice) (hs : s ≠ 0) :
    L.degreeAt s = L.arakelovDegree :=
  L.degreeAt_eq hsM hs L.isLattice.choose_spec.1 L.isLattice.choose_spec.2.1

end HermitianLattice

end Arakelov

/-! ## 3. The archimedean term: a translation-invariant top form on a complex torus

For an abelian variety `A` over `ℂ` of dimension `g`, `A(ℂ) ≅ ℂ^g / Λ` with `Λ` the period lattice
(the analytic uniformization; not in Mathlib, see the blueprint node `AN3`). In these linear
coordinates every invariant top form is `η = c · dz₁ ∧ ⋯ ∧ dz_g`, and `(i/2) dz ∧ dz̄ = dx ∧ dy` is
Lebesgue measure on `ℂ = ℝ²` (Mathlib's `volume` on `ℂ`), so the Faltings metric
`‖η‖² = (i/2)^g ∫_{A(ℂ)} η ∧ η̄` (sign convention: the positive value, i.e. with the factor
`(-1)^{g(g-1)/2}` that reorders `η ∧ η̄` into `∏ (dz_k ∧ dz̄_k)`) is `|c|²` times the volume of a
fundamental domain. -/

section Torus

/-- Real-linear change of variables and covolume: `covol(e⁻¹ Λ) · |det e| = covol Λ`. -/
theorem covolume_comap_mul_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] E) :
    ZLattice.covolume (ZLattice.comap ℝ L e.toLinearMap) μ *
      |LinearMap.det (e.toLinearMap : E →ₗ[ℝ] E)| = ZLattice.covolume L μ := by
  set ν : Measure E := Measure.map e.symm μ with hνdef
  have hmp : MeasurePreserving e ν μ := by
    refine ⟨e.continuous.measurable, ?_⟩
    rw [hνdef, Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
    simp
  have h1 := ZLattice.covolume_comap L μ ν hmp
  have hdet : LinearMap.det (e.symm.toLinearMap : E →ₗ[ℝ] E) ≠ 0 := by
    rw [show (e.symm.toLinearMap : E →ₗ[ℝ] E) = (e.toLinearEquiv.symm : E →ₗ[ℝ] E) from rfl,
      LinearEquiv.det_coe_symm]
    exact inv_ne_zero (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hν : ν = ENNReal.ofReal |LinearMap.det (e.toLinearMap : E →ₗ[ℝ] E)| • μ := by
    rw [hνdef, show (⇑e.symm : E → E) = ⇑(e.symm.toLinearMap : E →ₗ[ℝ] E) from rfl,
      Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet,
      show (e.symm.toLinearMap : E →ₗ[ℝ] E) = (e.toLinearEquiv.symm : E →ₗ[ℝ] E) from rfl,
      LinearEquiv.det_coe_symm, inv_inv]
  rw [← h1]
  have hF := ZLattice.isAddFundamentalDomain
    (Module.Free.chooseBasis ℤ (ZLattice.comap ℝ L e.toLinearMap)) μ
  have hFν := ZLattice.isAddFundamentalDomain
    (Module.Free.chooseBasis ℤ (ZLattice.comap ℝ L e.toLinearMap)) ν
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ μ hF,
    ZLattice.covolume_eq_measure_fundamentalDomain _ ν hFν, hν]
  simp only [Measure.real, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  ring

/-- The real determinant of a complex-linear map is `|det_ℂ|²`. -/
theorem det_restrictScalars_complex {g : ℕ} (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    LinearMap.det (T.restrictScalars ℝ) = Complex.normSq (LinearMap.det T) := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

variable {g : ℕ}

/-- **The archimedean Faltings metric** of `η = c · dz₁ ∧ ⋯ ∧ dz_g` on `ℂ^g / Λ`:
`‖η‖² = (i/2)^g ∫_{ℂ^g/Λ} η ∧ η̄ = |c|² · covol(Λ)`. -/
noncomputable def torusMetricSq (Λ : Submodule ℤ (Fin g → ℂ)) (c : ℂ) : ℝ :=
  ‖c‖ ^ 2 * ZLattice.covolume Λ

variable (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- The metric as an integral over a fundamental domain of `Λ` (i.e. over `A(ℂ)`). -/
theorem torusMetricSq_eq_setIntegral {F : Set (Fin g → ℂ)} (hF : IsAddFundamentalDomain Λ F)
    (c : ℂ) : torusMetricSq Λ c = ∫ _ in F, ‖c‖ ^ 2 := by
  rw [torusMetricSq, ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hF,
    setIntegral_const, smul_eq_mul, mul_comm]

/-- Integrals over `A(ℂ) = ℂ^g/Λ` of `Λ`-periodic densities do not depend on the fundamental
domain (Mathlib's `IsAddFundamentalDomain.setIntegral_eq`). -/
theorem torus_setIntegral_indep {F F' : Set (Fin g → ℂ)} (hF : IsAddFundamentalDomain Λ F)
    (hF' : IsAddFundamentalDomain Λ F') (f : (Fin g → ℂ) → ℝ)
    (hf : ∀ (l : Λ) (x : Fin g → ℂ), f (l +ᵥ x) = f x) :
    ∫ x in F, f x = ∫ x in F', f x := by
  have : MeasurableVAdd Λ (Fin g → ℂ) := (inferInstance : MeasurableVAdd Λ.toAddSubgroup _)
  have : VAddInvariantMeasure Λ (Fin g → ℂ) volume :=
    (inferInstance : VAddInvariantMeasure Λ.toAddSubgroup _ volume)
  exact hF.setIntegral_eq hF' hf

theorem torusMetricSq_pos {c : ℂ} (hc : c ≠ 0) : 0 < torusMetricSq Λ c :=
  mul_pos (by positivity) (ZLattice.covolume_pos Λ volume)

omit [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem torusMetricSq_smul (a c : ℂ) : torusMetricSq Λ (a * c) = ‖a‖ ^ 2 * torusMetricSq Λ c := by
  simp only [torusMetricSq, norm_mul]; ring

/-- The real-linear equivalence underlying a complex coordinate change. -/
noncomputable def realify (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) ≃L[ℝ] (Fin g → ℂ) :=
  (T.restrictScalars ℝ).toContinuousLinearEquiv

/-- **Independence of the linear coordinates.** In coordinates `z'` with `z = T z'`, the lattice
becomes `T⁻¹ Λ` and `c · dz₁∧⋯∧dz_g = (c · det T) · dz'₁∧⋯∧dz'_g`; the metric is unchanged. -/
theorem torusMetricSq_comap (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (c : ℂ) :
    torusMetricSq (ZLattice.comap ℝ Λ (realify T).toLinearMap)
      (c * LinearMap.det (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) = torusMetricSq Λ c := by
  have h := covolume_comap_mul_det Λ volume (realify T)
  have hd : LinearMap.det ((realify T).toLinearMap : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) =
      Complex.normSq (LinearMap.det (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) :=
    det_restrictScalars_complex (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
  rw [hd, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq] at h
  simp only [torusMetricSq, norm_mul]
  rw [← h]
  ring

end Torus

/-! ## 4. The metrized Hodge bundle of an abelian variety given with a model

`HodgeData K g V` is what an abelian variety `A/K` of dimension `g`, *given with* a smooth
group-scheme model `𝒢/𝓞_K` and complex uniformizations, contributes to Faltings' definition:

* `V = ∧^g H⁰(A, Ω¹) = ∧^g Lie(A)^∨`, a `K`-line (blueprint node `AV4`);
* `lattice = ∧^g ω_𝒢 = ∧^g e*Ω¹_{𝒢/𝓞_K}` inside `V` (node `M3`);
* `periods σ`: the period lattice `H₁(A_σ(ℂ), ℤ)` in linear coordinates `z₁, …, z_g` of
  `Lie(A_σ(ℂ))` (node `AN3`);
* `coeff σ`: the `σ`-semilinear map `V → ℂ`, `η ↦ c` where `η ⊗_σ 1 = c · dz₁ ∧ ⋯ ∧ dz_g`.

These fields are **data produced by the missing nodes**, not hypotheses about an abstract
structure: in the full formalization `HodgeData.ofModel 𝒢 (uniformization)` constructs them, and
the theorems below then apply. -/

section Hodge

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/-- The Hodge data of an abelian variety of dimension `g` over `K` with a model. -/
structure HodgeData (K : Type*) [Field K] [NumberField K] (g : ℕ) (V : Type*) [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] where
  /-- `∧^g ω_𝒢 ⊆ ∧^g H⁰(A, Ω¹)`. -/
  lattice : Submodule (𝓞 K) V
  finrank_eq_one : Module.finrank K V = 1
  isLattice : ∃ s ∈ lattice, s ≠ 0 ∧ secIndex lattice s ≠ 0
  /-- The period lattice of `A_σ(ℂ)` in linear coordinates. -/
  periods : (K →+* ℂ) → Submodule ℤ (Fin g → ℂ)
  periods_discrete : ∀ σ, DiscreteTopology (periods σ)
  periods_isZLattice : ∀ σ, IsZLattice ℝ (periods σ)
  /-- `η ↦ c` with `η ⊗_σ 1 = c · dz₁ ∧ ⋯ ∧ dz_g`. -/
  coeff : ∀ σ : K →+* ℂ, V →ₛₗ[σ] ℂ
  coeff_ne_zero : ∀ σ, coeff σ ≠ 0

namespace HodgeData

variable {g : ℕ} (D : HodgeData K g V)

omit [IsScalarTower (𝓞 K) K V] in
theorem coeff_apply_ne_zero (σ : K →+* ℂ) {v : V} (hv : v ≠ 0) : D.coeff σ v ≠ 0 := by
  intro h0
  apply D.coeff_ne_zero σ
  ext w
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp D.finrank_eq_one w
  simp [h0]

/-- `‖η‖_σ = (‖η‖²_σ)^{1/2}`, `‖η‖²_σ = (i/2)^g ∫_{A_σ(ℂ)} η ∧ η̄`. -/
noncomputable def norm (σ : K →+* ℂ) (v : V) : ℝ :=
  ‖D.coeff σ v‖ * Real.sqrt (ZLattice.covolume (D.periods σ))

omit [IsScalarTower (𝓞 K) K V] in
theorem norm_sq (σ : K →+* ℂ) (v : V) :
    D.norm σ v ^ 2 = torusMetricSq (D.periods σ) (D.coeff σ v) := by
  have := D.periods_discrete σ
  have := D.periods_isZLattice σ
  rw [norm, torusMetricSq, mul_pow,
    Real.sq_sqrt (ZLattice.covolume_pos (D.periods σ) volume).le]

/-- **The metrized Hodge bundle** `ω̄_𝒢 = (det ω_𝒢, ‖·‖_Faltings)`. -/
noncomputable def hodgeBundle : HermitianLattice K V where
  lattice := D.lattice
  finrank_eq_one := D.finrank_eq_one
  isLattice := D.isLattice
  norm := D.norm
  norm_smul σ a v := by
    simp only [norm, map_smulₛₗ, smul_eq_mul, norm_mul]; ring
  norm_pos σ v hv := by
    have := D.periods_discrete σ
    have := D.periods_isZLattice σ
    exact mul_pos (norm_pos_iff.mpr (D.coeff_apply_ne_zero σ hv))
      (Real.sqrt_pos.mpr (ZLattice.covolume_pos (D.periods σ) volume))

/-- **Faltings' height of `A` relative to the model**: `deg(ω̄_𝒢) / [K:ℚ]`. -/
noncomputable def modelHeight : ℝ := D.hodgeBundle.arakelovDegree / Module.finrank ℚ K

/-- **Faltings' formula** (pkg-I5 §2.1), for every nonzero `η ∈ ∧^g ω_𝒢`:
`h(A, 𝒢) = [K:ℚ]⁻¹ (log #(∧^g ω_𝒢 / 𝓞_K η) − ½ ∑_σ log ((i/2)^g ∫_{A_σ(ℂ)} η ∧ η̄))`. -/
theorem modelHeight_eq {η : V} (hηM : η ∈ D.lattice) (hη : η ≠ 0) :
    D.modelHeight = (Real.log (secIndex D.lattice η) -
      (1 / 2) * ∑ σ : K →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ η))) /
        Module.finrank ℚ K := by
  rw [modelHeight, ← D.hodgeBundle.degreeAt_eq_arakelovDegree hηM hη]
  unfold HermitianLattice.degreeAt
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← D.norm_sq, Real.log_pow]
  simp only [hodgeBundle]
  push_cast; ring

/-- Change of the linear coordinates at every `σ`: `z = T_σ z'`. -/
noncomputable def recoord (T : (K →+* ℂ) → ((Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))) : HodgeData K g V where
  lattice := D.lattice
  finrank_eq_one := D.finrank_eq_one
  isLattice := D.isLattice
  periods σ := ZLattice.comap ℝ (D.periods σ) (realify (T σ)).toLinearMap
  periods_discrete σ := by
    have := D.periods_discrete σ
    infer_instance
  periods_isZLattice σ := by
    have := D.periods_discrete σ
    have := D.periods_isZLattice σ
    infer_instance
  coeff σ := LinearMap.det (T σ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) • D.coeff σ
  coeff_ne_zero σ := by
    intro h
    obtain ⟨v, hvM, hv, -⟩ := D.isLattice
    have := congr_arg (fun f => f v) h
    simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply, mul_eq_zero] at this
    rcases this with h1 | h1
    · exact (LinearEquiv.isUnit_det' (T σ)).ne_zero h1
    · exact D.coeff_apply_ne_zero σ hv h1

omit [IsScalarTower (𝓞 K) K V] in
/-- **Independence of the coordinates on `Lie(A_σ)`.** -/
theorem modelHeight_recoord (T : (K →+* ℂ) → ((Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))) :
    (D.recoord T).modelHeight = D.modelHeight := by
  have hn : ∀ σ v, (D.recoord T).norm σ v = D.norm σ v := by
    intro σ v
    have := D.periods_discrete σ
    have := D.periods_isZLattice σ
    have h2 : (D.recoord T).norm σ v ^ 2 = D.norm σ v ^ 2 := by
      rw [norm_sq, norm_sq]
      simp only [recoord, LinearMap.smul_apply, smul_eq_mul]
      rw [mul_comm]
      exact torusMetricSq_comap (D.periods σ) (T σ) _
    have h0 : 0 ≤ (D.recoord T).norm σ v := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    have h0' : 0 ≤ D.norm σ v := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    exact (pow_left_inj₀ h0 h0' two_ne_zero).mp h2
  unfold modelHeight HermitianLattice.arakelovDegree HermitianLattice.degreeAt
  simp only [hodgeBundle, hn]
  rfl

/-- **Change of model.** If `D'` has the same generic fibre and uniformizations and a smaller
lattice (`ω_𝒢' ⊆ ω_𝒢`, e.g. `𝒢'` the Néron model, which receives a map from every smooth model),
then `h(A, 𝒢) = h(A, 𝒢') + [K:ℚ]⁻¹ log [ω_𝒢 : ω_𝒢']`. -/
theorem modelHeight_eq_add_of_le (D' : HodgeData K g V) (hp : D'.periods = D.periods)
    (hc : D'.coeff = D.coeff) (hle : D'.lattice ≤ D.lattice) :
    D.modelHeight = D'.modelHeight +
      Real.log (D'.lattice.toAddSubgroup.relIndex D.lattice.toAddSubgroup) /
        Module.finrank ℚ K := by
  obtain ⟨η, hηM', hη, -⟩ := D'.isLattice
  have hηM : η ∈ D.lattice := hle hηM'
  rw [D.modelHeight_eq hηM hη, D'.modelHeight_eq hηM' hη, hp, hc, ← add_div]
  congr 1
  have hle1 : Submodule.span (𝓞 K) {η} ≤ D'.lattice := Submodule.span_le.mpr (by simpa using hηM')
  have hmul : secIndex D'.lattice η *
      D'.lattice.toAddSubgroup.relIndex D.lattice.toAddSubgroup = secIndex D.lattice η :=
    AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hle1)
      (Submodule.toAddSubgroup_mono hle)
  have hne : secIndex D.lattice η ≠ 0 := D.hodgeBundle.secIndex_ne_zero hηM hη
  rw [← hmul] at hne ⊢
  have h1 : secIndex D'.lattice η ≠ 0 := left_ne_zero_of_mul hne
  have h2 : D'.lattice.toAddSubgroup.relIndex D.lattice.toAddSubgroup ≠ 0 :=
    right_ne_zero_of_mul hne
  push_cast
  rw [Real.log_mul (by exact_mod_cast h1) (by exact_mod_cast h2)]
  ring

/-- Hence a smaller lattice gives a smaller height; the Néron lattice gives the infimum. -/
theorem modelHeight_le_of_le (D' : HodgeData K g V) (hp : D'.periods = D.periods)
    (hc : D'.coeff = D.coeff) (hle : D'.lattice ≤ D.lattice) :
    D'.modelHeight ≤ D.modelHeight := by
  rw [D.modelHeight_eq_add_of_le D' hp hc hle]
  have : 0 ≤ Real.log (D'.lattice.toAddSubgroup.relIndex D.lattice.toAddSubgroup) /
      Module.finrank ℚ K :=
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  linarith

end HodgeData

end Hodge

/-! ## 5. Acceptance-test interface: elliptic curves

The definitions `hypGram`, `hypVol`, `finiteHeightPart`, `faltingsHeightEC` are copied verbatim
from `scratch/pkg-I5/I5.lean` (task pkg-I5), so that the acceptance test can be stated here. -/

section Acceptance

open Polynomial

/-- (copied from pkg-I5) `2 ∫_ℂ xⁱ x̄ʲ / |P(x)| dλ`. -/
noncomputable def hypGram (P : ℂ[X]) (i j : ℕ) : ℂ :=
  2 * ∫ x : ℂ, x ^ i * (starRingEnd ℂ x) ^ j / ((‖P.eval x‖ : ℝ) : ℂ)

/-- (copied from pkg-I5) `det` of the Gram matrix. -/
noncomputable def hypVol (g : ℕ) (P : ℂ[X]) : ℝ :=
  (Matrix.of fun i j : Fin g => hypGram P i j).det.re

/-- (copied from pkg-I5) `∑_{v finite} log max(1, |x|_v)`. -/
noncomputable def finiteHeightPart {K : Type*} [Field K] [NumberField K] (x : K) : ℝ :=
  Height.logHeight₁ x - ∑ σ : K →+* ℂ, Real.log (max 1 ‖σ x‖)

/-- (copied from pkg-I5) The closed formula for the stable Faltings height of an elliptic curve. -/
noncomputable def faltingsHeightEC {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic] : ℝ :=
  let d : ℝ := Module.finrank ℚ K
  let P : K[X] := 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆
  (finiteHeightPart W.j - ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖) / (12 * d) -
    (∑ σ : K →+* ℂ, Real.log (hypVol 1 (P.map σ))) / (2 * d)

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/-- A free Hodge lattice `𝓞_K · η₀`: `h(A, 𝒢) = −(2[K:ℚ])⁻¹ ∑_σ log ‖η₀‖²_σ`. -/
theorem HodgeData.modelHeight_of_span {g : ℕ} (D : HodgeData K g V) {η₀ : V}
    (h : D.lattice = Submodule.span (𝓞 K) {η₀}) (hη₀ : η₀ ≠ 0) :
    D.modelHeight = -((1 / 2) * ∑ σ : K →+* ℂ,
      Real.log (torusMetricSq (D.periods σ) (D.coeff σ η₀))) / Module.finrank ℚ K := by
  have hm : η₀ ∈ D.lattice := h ▸ Submodule.mem_span_singleton_self η₀
  rw [D.modelHeight_eq hm hη₀]
  have h1 : secIndex D.lattice η₀ = 1 := by
    unfold secIndex; rw [h, AddSubgroup.relIndex_self]
  rw [h1]
  simp

/-- The period lattice of a `PeriodPair` as a lattice in `ℂ¹ = Fin 1 → ℂ`. -/
noncomputable def _root_.PeriodPair.lattice1 (L : PeriodPair) : Submodule ℤ (Fin 1 → ℂ) :=
  ZLattice.comap ℝ L.lattice (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ).toLinearMap

instance (L : PeriodPair) : DiscreteTopology L.lattice1 := by
  unfold PeriodPair.lattice1; infer_instance

instance (L : PeriodPair) : IsZLattice ℝ L.lattice1 := by
  unfold PeriodPair.lattice1; infer_instance

theorem _root_.PeriodPair.covolume_lattice1 (L : PeriodPair) :
    ZLattice.covolume L.lattice1 = ZLattice.covolume L.lattice :=
  ZLattice.covolume_comap L.lattice volume volume
    (e := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ) (volume_preserving_funUnique (Fin 1) ℂ)

/-- **Node AT1c (the area formula).** For the lattice `Λ` of a period pair and
`P = 4x³ − g₂(Λ)x − g₃(Λ)`: `covol(Λ) = 2 ∫_ℂ dλ(x)/|P(x)|`. A classical theorem (the map
`z ↦ ℘(z)` is a degree-2 cover `ℂ/Λ → ℙ¹` with `d℘ = ℘' dz` and `℘'² = P(℘)`; Mathlib has `℘` and
`PeriodPair.derivWeierstrassP_sq`); numerically checked in pkg-I5 (`area_check.py`). Stated as a
Prop here, unproved. -/
def PeriodAreaFormula : Prop :=
  ∀ L : PeriodPair, ZLattice.covolume L.lattice =
    hypVol 1 (4 * X ^ 3 - C L.g₂ * X - C L.g₃)

/-- **Acceptance test AT1, conditional form.** Let `D` be Hodge data of dimension 1 whose lattice
is free on `η₀`, whose period lattices are those of period pairs `L σ` with `η₀ ↦ dz`
(i.e. `η₀ = dx/(2y + a₁x + a₃)` and `L σ` the period lattice of `W^σ`: node AT1b), where the
Weierstrass polynomial of `W^σ` is `4x³ − g₂(L σ) x − g₃(L σ)` and the finite part of
`faltingsHeightEC` vanishes (`W` semistable and minimal at every prime, which is when `𝓞_K η₀` is
the Néron lattice: node AT1a). Then, given the area formula AT1c, `modelHeight D` equals pkg-I5's
`faltingsHeightEC W`. Proved. -/
theorem modelHeight_eq_faltingsHeightEC (hA : PeriodAreaFormula)
    (W : WeierstrassCurve K) [W.IsElliptic] (D : HodgeData K 1 V) {η₀ : V}
    (hspan : D.lattice = Submodule.span (𝓞 K) {η₀}) (hη₀ : η₀ ≠ 0)
    (L : (K →+* ℂ) → PeriodPair) (hper : ∀ σ, D.periods σ = (L σ).lattice1)
    (hco : ∀ σ, D.coeff σ η₀ = 1)
    (hP : ∀ σ, (4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ =
      4 * X ^ 3 - C (L σ).g₂ * X - C (L σ).g₃)
    (hfin : finiteHeightPart W.j = ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖) :
    D.modelHeight = faltingsHeightEC W := by
  rw [D.modelHeight_of_span hspan hη₀, faltingsHeightEC]
  rw [hfin, sub_self, zero_div, zero_sub]
  have hterm : ∀ σ : K →+* ℂ, torusMetricSq (D.periods σ) (D.coeff σ η₀) =
      hypVol 1 ((4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ) := by
    intro σ
    rw [hco, hper, hP, torusMetricSq, PeriodPair.covolume_lattice1, hA]
    simp
  simp only [hterm]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  field_simp

end Acceptance

/-! ## 6. Rescaling, and a sanity check that `HodgeData` is inhabited -/

section Sanity

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/-- Rescale the metrics by `c σ > 0`. -/
noncomputable def HermitianLattice.rescale (L : HermitianLattice K V) (c : (K →+* ℂ) → ℝ)
    (hc : ∀ σ, 0 < c σ) : HermitianLattice K V where
  lattice := L.lattice
  finrank_eq_one := L.finrank_eq_one
  isLattice := L.isLattice
  norm σ v := c σ * L.norm σ v
  norm_smul σ a v := by rw [L.norm_smul]; ring
  norm_pos σ v hv := mul_pos (hc σ) (L.norm_pos σ v hv)

omit [IsScalarTower (𝓞 K) K V] in
/-- **Rescaling (part of node AR3):** `deg(M, c·‖·‖) = deg(M, ‖·‖) − ∑_σ log c_σ`. -/
theorem HermitianLattice.arakelovDegree_rescale (L : HermitianLattice K V)
    (c : (K →+* ℂ) → ℝ) (hc : ∀ σ, 0 < c σ) :
    (L.rescale c hc).arakelovDegree = L.arakelovDegree - ∑ σ : K →+* ℂ, Real.log (c σ) := by
  obtain ⟨hsM, hs, -⟩ := L.isLattice.choose_spec
  unfold HermitianLattice.arakelovDegree HermitianLattice.degreeAt
  simp only [HermitianLattice.rescale]
  rw [Finset.sum_congr rfl fun σ _ => Real.log_mul (hc σ).ne' (L.norm_pos σ _ hs).ne',
    Finset.sum_add_distrib]
  ring

/-- The square lattice `ℤ + ℤi`. -/
noncomputable def gaussianPair : PeriodPair where
  ω₁ := 1
  ω₂ := Complex.I
  indep := by simpa [Complex.coe_basisOneI] using Complex.basisOneI.linearIndependent

/-- `σ : ℚ → ℂ` as a `σ`-semilinear map. -/
def ratCoeff (σ : ℚ →+* ℂ) : ℚ →ₛₗ[σ] ℂ where
  toFun := σ
  map_add' := map_add σ
  map_smul' a v := by simp

/-- **Sanity check: `HodgeData` is inhabited** (the elliptic curve `ℂ/(ℤ + ℤi)` over `ℚ`, with
the lattice `ℤ · 1`; this is a consistency check of the structure, not a claim about a curve over
`ℚ`). -/
noncomputable def exampleHodge : HodgeData ℚ 1 ℚ where
  lattice := Submodule.span (𝓞 ℚ) {1}
  finrank_eq_one := Module.finrank_self ℚ
  isLattice := ⟨1, Submodule.mem_span_singleton_self 1, one_ne_zero, by
    unfold secIndex; rw [AddSubgroup.relIndex_self]; exact one_ne_zero⟩
  periods _ := gaussianPair.lattice1
  periods_discrete _ := inferInstance
  periods_isZLattice _ := inferInstance
  coeff σ := ratCoeff σ
  coeff_ne_zero σ h := by
    have := congr_arg (fun f => f 1) h
    simp [ratCoeff] at this

theorem exampleHodge_modelHeight :
    exampleHodge.modelHeight = -(1 / 2) * Real.log (ZLattice.covolume gaussianPair.lattice) := by
  rw [HodgeData.modelHeight_of_span exampleHodge (η₀ := (1 : ℚ)) rfl one_ne_zero]
  have hu : (Finset.univ : Finset (ℚ →+* ℂ)) = {Rat.castHom ℂ} := by
    ext σ; simp [Subsingleton.elim σ (Rat.castHom ℂ)]
  rw [hu, Finset.sum_singleton]
  simp [exampleHodge, torusMetricSq, ratCoeff, PeriodPair.covolume_lattice1]

end Sanity

/-! ## 7. Hermitian lines given by fractional ideals: the closed formula (part of node AR3)

Every invertible `𝓞_K`-module with a trivialization of its generic fibre is a fractional ideal
`I ⊆ K`. For such lines `#(I / 𝓞_K x) · N(I) = |N_{K/ℚ}(x)|` (`secIndex_mul_absNorm`), so
`deg(I, ρ·|σ(·)|) = −log N(I) − ∑_σ log ρ_σ` (`arakelovDegree_ofFractionalIdeal`). This is the form
in which AT1a meets a Néron lattice `𝔞 · dx/(2y + a₁x + a₃)` that is not free (class number > 1). -/

section FractionalIdeal

open Pointwise
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- **Index formula.** For a fractional ideal `I` and `0 ≠ x ∈ I`:
`#(I / 𝓞_K x) · N(I) = |N_{K/ℚ}(x)|`. -/
theorem secIndex_mul_absNorm (I : FractionalIdeal (𝓞 K)⁰ K) {x : K} (hx : x ∈ I) (hx0 : x ≠ 0) :
    (secIndex (I : Submodule (𝓞 K) K) x : ℚ) * FractionalIdeal.absNorm I =
      |Algebra.norm ℚ x| := by
  classical
  set d : 𝓞 K := (I.den : 𝓞 K) with hd
  have hd0' : d ≠ 0 := nonZeroDivisors.ne_zero I.den.2
  have hd0 : (d : K) ≠ 0 := by exact_mod_cast hd0'
  let f : K →ₗ[𝓞 K] K := DistribSMul.toLinearMap (𝓞 K) K I.den
  have hf_apply : ∀ z, f z = (d : K) * z := by
    intro z
    show I.den • z = (d : K) * z
    rw [Submonoid.smul_def, ← algebraMap_smul K, smul_eq_mul]
  have hf : Function.Injective f := fun a b h => by
    rw [hf_apply, hf_apply] at h
    exact mul_left_cancel₀ hd0 h
  have hfI : Submodule.map f (I : Submodule (𝓞 K) K) =
      Submodule.map (Algebra.linearMap (𝓞 K) K) I.num :=
    FractionalIdeal.den_mul_self_eq_num I
  -- `d x = y` with `y ∈ I.num`
  have hdx : f x ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num :=
    hfI ▸ Submodule.mem_map_of_mem hx
  obtain ⟨y, hy, hyx⟩ := hdx
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hyx
    exact hx0 (hf (by rw [← hyx, map_zero]))
  let ι : 𝓞 K →ₗ[𝓞 K] K := Algebra.linearMap (𝓞 K) K
  have hι : Function.Injective ι := IsFractionRing.injective (𝓞 K) K
  have hspan : Submodule.map f (Submodule.span (𝓞 K) {x}) =
      Submodule.map ι (Ideal.span {y}) := by
    rw [Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton]
    simp only [ι] at hyx ⊢
    rw [hyx]
  -- transport the index
  have h1 : secIndex (I : Submodule (𝓞 K) K) x =
      (Ideal.span {y}).toAddSubgroup.relIndex I.num.toAddSubgroup := by
    unfold secIndex
    have e1 := AddSubgroup.relIndex_map_map_of_injective
      (Submodule.span (𝓞 K) {x}).toAddSubgroup (I : Submodule (𝓞 K) K).toAddSubgroup
      (f := (f : K →+ K)) hf
    rw [← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup, hspan, hfI,
      Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective _ _ hι] at e1
    exact e1.symm
  have hle : Ideal.span {y} ≤ I.num := (Ideal.span_singleton_le_iff_mem _).mpr hy
  have h2 : (Ideal.span {y}).toAddSubgroup.relIndex I.num.toAddSubgroup *
      Ideal.absNorm I.num = (Algebra.norm ℤ y).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact AddSubgroup.relIndex_mul_index (Submodule.toAddSubgroup_mono hle)
  have hnum0 : Ideal.absNorm I.num ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    have : Algebra.norm ℤ y ≠ 0 := (Algebra.norm_ne_zero_iff (R := ℤ)).mpr hy0
    omega
  -- norms
  have hNy : (Algebra.norm ℚ (y : K)) = Algebra.norm ℚ (d : K) * Algebra.norm ℚ x := by
    have : (y : K) = (d : K) * x := by rw [← hf_apply]; exact hyx
    rw [this, map_mul]
  rw [FractionalIdeal.absNorm_eq, h1]
  have hNyz : ((Algebra.norm ℤ y).natAbs : ℚ) = |Algebra.norm ℚ (y : K)| := by
    rw [← Algebra.coe_norm_int]; simp [Nat.cast_natAbs]
  have hNdz : ((Algebra.norm ℤ d : ℤ) : ℚ) = Algebra.norm ℚ (d : K) := Algebra.coe_norm_int d
  have hNd0 : Algebra.norm ℚ (d : K) ≠ 0 := by
    rw [← hNdz]; exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℤ)).mpr hd0'
  have key : ((Ideal.span {y}).toAddSubgroup.relIndex I.num.toAddSubgroup : ℚ) *
      (Ideal.absNorm I.num : ℚ) = |Algebra.norm ℚ (d : K)| * |Algebra.norm ℚ x| := by
    rw [← abs_mul, ← hNy, ← hNyz]; exact_mod_cast h2
  have hden : ((|Algebra.norm ℤ (I.den : 𝓞 K)| : ℤ) : ℚ) = |Algebra.norm ℚ (d : K)| := by
    rw [Int.cast_abs]; exact congr_arg _ hNdz
  rw [hden, ← mul_div_assoc, key]
  field_simp

/-- The Hermitian line `(I, ρ_σ · |σ(·)|)` on `Spec 𝓞_K`. -/
noncomputable def HermitianLattice.ofFractionalIdeal (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (ρ : (K →+* ℂ) → ℝ) (hρ : ∀ σ, 0 < ρ σ) : HermitianLattice K K where
  lattice := I
  finrank_eq_one := Module.finrank_self K
  isLattice := by
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
    refine ⟨x, hxI, hx0, fun h0 => ?_⟩
    have := secIndex_mul_absNorm I hxI hx0
    rw [h0, Nat.cast_zero, zero_mul] at this
    exact (Algebra.norm_ne_zero_iff.mpr hx0) (abs_eq_zero.mp this.symm)
  norm σ x := ρ σ * ‖σ x‖
  norm_smul σ a x := by rw [smul_eq_mul, map_mul, norm_mul]; ring
  norm_pos σ x hx := mul_pos (hρ σ) (by simpa using hx)

/-- **Closed formula:** `deg(I, ρ·|σ(·)|) = −log N(I) − ∑_σ log ρ_σ`. -/
theorem HermitianLattice.arakelovDegree_ofFractionalIdeal (I : FractionalIdeal (𝓞 K)⁰ K)
    (hI : I ≠ 0) (ρ : (K →+* ℂ) → ℝ) (hρ : ∀ σ, 0 < ρ σ) :
    (HermitianLattice.ofFractionalIdeal I hI ρ hρ).arakelovDegree =
      -Real.log (FractionalIdeal.absNorm I : ℝ) - ∑ σ : K →+* ℂ, Real.log (ρ σ) := by
  set L := HermitianLattice.ofFractionalIdeal I hI ρ hρ
  obtain ⟨hxI, hx0, hi⟩ := L.isLattice.choose_spec
  set x := L.isLattice.choose
  have hidx := secIndex_mul_absNorm I hxI hx0
  have hN0 : FractionalIdeal.absNorm I ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hidx
    exact (Algebra.norm_ne_zero_iff.mpr hx0) (abs_eq_zero.mp hidx.symm)
  unfold HermitianLattice.arakelovDegree HermitianLattice.degreeAt
  have hsum : ∑ σ : K →+* ℂ, Real.log (L.norm σ x) =
      ∑ σ : K →+* ℂ, Real.log (ρ σ) + Real.log |(Algebra.norm ℚ x : ℝ)| := by
    rw [← sum_log_norm_embeddings x hx0, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact Real.log_mul (hρ σ).ne' (by simpa using hx0)
  rw [hsum]
  have hidxR : (secIndex L.lattice x : ℝ) * (FractionalIdeal.absNorm I : ℝ) =
      |(Algebra.norm ℚ x : ℝ)| := by exact_mod_cast hidx
  have hlog : Real.log (secIndex L.lattice x : ℝ) + Real.log (FractionalIdeal.absNorm I : ℝ) =
      Real.log |(Algebra.norm ℚ x : ℝ)| := by
    rw [← Real.log_mul (by exact_mod_cast hi) (by exact_mod_cast hN0), hidxR]
  linarith

end FractionalIdeal

/-! ## 8. Acceptance test AT1 for a non-free Hodge lattice

For an elliptic curve with semistable reduction everywhere, the Néron lattice of invariant
differentials is `𝔞 · ω` with `ω = dx/(2y + a₁x + a₃)` and `𝔞` the fractional ideal with
`ord_𝔭 𝔞 = (ord_𝔭 Δ − ord_𝔭 Δ_min)/12` (`Δ_min` the minimal discriminant at `𝔭`). With
`ord_𝔭 Δ_min = max(0, −ord_𝔭 j)` (semistable) and the product formula,
`−12 log N(𝔞) = ∑_{v∤∞} log⁺|j|_v − ∑_σ log|σΔ|`. That identity is node AT1a (literature: Néron
models of elliptic curves); here it is the hypothesis `hNeron`. -/

section AcceptanceIdeal

open Polynomial
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- `σ : K → ℂ` as a `σ`-semilinear map. -/
def embCoeff (σ : K →+* ℂ) : K →ₛₗ[σ] ℂ where
  toFun := σ
  map_add' := map_add σ
  map_smul' a v := by simp

/-- The Hodge data `(𝔞 ⊆ K, Λ_σ)` of dimension 1: `V = K` (`ω ↦ 1`), lattice `𝔞`, period lattices
`(L σ).lattice1`, `ω ↦ dz`. -/
noncomputable def HodgeData.ofIdeal (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (L : (K →+* ℂ) → PeriodPair) : HodgeData K 1 K where
  lattice := 𝔞
  finrank_eq_one := Module.finrank_self K
  isLattice := (HermitianLattice.ofFractionalIdeal 𝔞 h𝔞 (fun _ => 1) (fun _ => one_pos)).isLattice
  periods σ := (L σ).lattice1
  periods_discrete _ := inferInstance
  periods_isZLattice _ := inferInstance
  coeff σ := embCoeff σ
  coeff_ne_zero σ h := by
    have := congr_arg (fun f => f 1) h
    simp [embCoeff] at this

theorem HodgeData.modelHeight_ofIdeal (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (L : (K →+* ℂ) → PeriodPair) :
    (HodgeData.ofIdeal 𝔞 h𝔞 L).modelHeight =
      (-Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) -
        (1 / 2) * ∑ σ : K →+* ℂ, Real.log (ZLattice.covolume (L σ).lattice)) /
          Module.finrank ℚ K := by
  set ρ : (K →+* ℂ) → ℝ := fun σ => Real.sqrt (ZLattice.covolume (L σ).lattice)
  have hρ : ∀ σ, 0 < ρ σ := fun σ => Real.sqrt_pos.mpr (ZLattice.covolume_pos _ volume)
  have hdeg := HermitianLattice.arakelovDegree_ofFractionalIdeal 𝔞 h𝔞 ρ hρ
  have heq : (HodgeData.ofIdeal 𝔞 h𝔞 L).hodgeBundle.arakelovDegree =
      (HermitianLattice.ofFractionalIdeal 𝔞 h𝔞 ρ hρ).arakelovDegree := by
    unfold HermitianLattice.arakelovDegree HermitianLattice.degreeAt
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    simp only [HodgeData.hodgeBundle, HodgeData.norm, HermitianLattice.ofFractionalIdeal,
      HodgeData.ofIdeal, embCoeff, LinearMap.coe_mk, AddHom.coe_mk, ρ,
      PeriodPair.covolume_lattice1]
    ring
  rw [HodgeData.modelHeight, heq, hdeg]
  congr 1
  have hs : ∀ σ : K →+* ℂ, Real.log (ρ σ) = (1 / 2) * Real.log (ZLattice.covolume (L σ).lattice) := by
    intro σ
    simp only [ρ]
    rw [Real.log_sqrt (ZLattice.covolume_pos _ volume).le]
    ring
  rw [Finset.sum_congr rfl fun σ _ => hs σ, ← Finset.mul_sum]

/-- **Acceptance test AT1 (semistable elliptic curves, any class number), conditional form.**
Given the area formula AT1c (`PeriodAreaFormula`), period pairs `L σ` with Weierstrass polynomial
`4x³ − g₂(L σ)x − g₃(L σ)` equal to that of `W^σ` (AT1b), and a Hodge lattice `𝔞 · ω` satisfying the
Néron identity AT1a (`hNeron`), the model height equals pkg-I5's `faltingsHeightEC W`. Proved. -/
theorem modelHeight_ofIdeal_eq_faltingsHeightEC (hA : PeriodAreaFormula)
    (W : WeierstrassCurve K) [W.IsElliptic] (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (L : (K →+* ℂ) → PeriodPair)
    (hP : ∀ σ, (4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ =
      4 * X ^ 3 - C (L σ).g₂ * X - C (L σ).g₃)
    (hNeron : -12 * Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) =
      finiteHeightPart W.j - ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖) :
    (HodgeData.ofIdeal 𝔞 h𝔞 L).modelHeight = faltingsHeightEC W := by
  rw [HodgeData.modelHeight_ofIdeal, faltingsHeightEC, ← hNeron]
  have hterm : ∀ σ : K →+* ℂ, ZLattice.covolume (L σ).lattice =
      hypVol 1 ((4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ) := by
    intro σ; rw [hP, hA]
  simp only [hterm]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  field_simp

end AcceptanceIdeal

/-! ## 9. Base change: the archimedean count (part of nodes AR3, H4)

Each complex embedding `σ` of `K` has exactly `[L:K]` extensions to `L`, so sums over the
embeddings of `L` of functions of the restriction are `[L:K]` times the sums over `K`. -/

section BaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open Classical in
theorem card_embeddings_over (σ : K →+* ℂ) :
    (Finset.univ.filter (fun τ : L →+* ℂ => τ.comp (algebraMap K L) = σ)).card =
      Module.finrank K L := by
  let _ : Algebra K ℂ := σ.toAlgebra
  have hc : ∀ τ : {τ : L →+* ℂ // τ.comp (algebraMap K L) = σ}, ∀ k : K,
      τ.1 (algebraMap K L k) = algebraMap K ℂ k := fun τ k => by
    have := congr_arg (fun f : K →+* ℂ => f k) τ.2
    simpa [RingHom.algebraMap_toAlgebra] using this
  have hc' : ∀ φ : L →ₐ[K] ℂ, (φ : L →+* ℂ).comp (algebraMap K L) = σ := fun φ => by
    ext k
    simp [RingHom.algebraMap_toAlgebra]
  rw [← AlgHom.card K L ℂ, ← Fintype.card_subtype]
  exact Fintype.card_congr
    { toFun := fun τ => ⟨τ.1, hc τ⟩
      invFun := fun φ => ⟨(φ : L →+* ℂ), hc' φ⟩
      left_inv := fun τ => by ext; rfl
      right_inv := fun φ => by ext; rfl }

open Classical in
/-- `∑_{τ : L → ℂ} f(τ|_K) = [L:K] · ∑_{σ : K → ℂ} f(σ)`. -/
theorem sum_embeddings_comp (f : (K →+* ℂ) → ℝ) :
    ∑ τ : L →+* ℂ, f (τ.comp (algebraMap K L)) =
      Module.finrank K L * ∑ σ : K →+* ℂ, f σ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun τ : L →+* ℂ => τ.comp (algebraMap K L))
    (fun τ => f (τ.comp (algebraMap K L))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_congr rfl (fun τ hτ => by rw [(Finset.mem_filter.mp hτ).2]),
    Finset.sum_const, card_embeddings_over, nsmul_eq_mul]

end BaseChange

/-! ## 10. AT1 for every Weierstrass model: translation invariance

`ω ↦ dz` forces `g₂ = c₄/12`, `g₃ = c₆/216` but `P_W = 4x³ + b₂x² + 2b₄x + b₆` equals
`4x³ − g₂x − g₃` only after the translation `x ↦ x − b₂/12`. The archimedean term is translation
invariant (Lebesgue measure on `ℂ`), so AT1 holds with a translation at each `σ`. -/

section Translate

open Polynomial
open scoped nonZeroDivisors

theorem hypGram_comp_add (P : ℂ[X]) (c : ℂ) :
    hypGram (P.comp (X + C c)) 0 0 = hypGram P 0 0 := by
  simp only [hypGram, pow_zero, one_mul, eval_comp, eval_add, eval_X, eval_C]
  congr 1
  exact integral_add_right_eq_self (fun x => 1 / ((‖P.eval x‖ : ℝ) : ℂ)) c

theorem hypVol_one_comp_add (P : ℂ[X]) (c : ℂ) : hypVol 1 (P.comp (X + C c)) = hypVol 1 P := by
  simp only [hypVol, Matrix.det_fin_one, Matrix.of_apply, Fin.val_zero, hypGram_comp_add]

variable {K : Type*} [Field K] [NumberField K]

/-- **Acceptance test AT1, conditional form, any Weierstrass model with semistable reduction.**
As `modelHeight_ofIdeal_eq_faltingsHeightEC`, with the Weierstrass polynomial of `W^σ` equal to
`4x³ − g₂(L σ)x − g₃(L σ)` after a translation `x ↦ x + c σ`. -/
theorem modelHeight_ofIdeal_eq_faltingsHeightEC' (hA : PeriodAreaFormula)
    (W : WeierstrassCurve K) [W.IsElliptic] (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (L : (K →+* ℂ) → PeriodPair) (c : (K →+* ℂ) → ℂ)
    (hP : ∀ σ, (4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ =
      (4 * X ^ 3 - C (L σ).g₂ * X - C (L σ).g₃).comp (X + C (c σ)))
    (hNeron : -12 * Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) =
      finiteHeightPart W.j - ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖) :
    (HodgeData.ofIdeal 𝔞 h𝔞 L).modelHeight = faltingsHeightEC W := by
  rw [HodgeData.modelHeight_ofIdeal, faltingsHeightEC, ← hNeron]
  have hterm : ∀ σ : K →+* ℂ, ZLattice.covolume (L σ).lattice =
      hypVol 1 ((4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ) := by
    intro σ; rw [hP, hypVol_one_comp_add, hA]
  simp only [hterm]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  field_simp

end Translate

/-! ## 11. Base change of fractional-ideal Hermitian lines (node AR3, finite half)

`N_L(I𝓞_L) = N_K(I)^{[L:K]}` for fractional ideals (from Mathlib's `Ideal.absNorm_algebraMap` for
integral ideals), hence `deg_L((I, ρ)_{𝓞_L}) = [L:K] · deg_K(I, ρ)`: the Arakelov degree divided
by the absolute degree, i.e. the height, is invariant under base change. -/

section BaseChangeNorm

open scoped nonZeroDivisors

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem finrank_ringOfIntegers : Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L :=
  (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L).symm

theorem absNorm_map_ringOfIntegers (I : Ideal (𝓞 K)) :
    Ideal.absNorm (I.map (algebraMap (𝓞 K) (𝓞 L))) = Ideal.absNorm I ^ Module.finrank K L := by
  rw [Ideal.absNorm_algebraMap, finrank_ringOfIntegers]

theorem norm_algebraMap_tower (x : K) :
    Algebra.norm ℚ (algebraMap K L x) = Algebra.norm ℚ x ^ Module.finrank K L := by
  rw [← Algebra.norm_norm (S := K), Algebra.norm_algebraMap, map_pow]

/-- **Norm of an extended fractional ideal.** -/
theorem absNorm_extendedHom (I : FractionalIdeal (𝓞 K)⁰ K) :
    FractionalIdeal.absNorm (FractionalIdeal.extendedHom L (𝓞 L) I) =
      FractionalIdeal.absNorm I ^ Module.finrank K L := by
  have hnum := FractionalIdeal.den_mul_self_eq_num' (𝓞 K)⁰ K I
  set d : 𝓞 K := (I.den : 𝓞 K) with hd
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.den.2
  have hK := congr_arg FractionalIdeal.absNorm hnum
  rw [map_mul, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.coeIdeal_absNorm] at hK
  have hL := congr_arg (fun J => FractionalIdeal.absNorm (FractionalIdeal.extendedHom L (𝓞 L) J))
    hnum
  simp only [map_mul, FractionalIdeal.extendedHom_spanSingleton,
    FractionalIdeal.extendedHom_coeIdeal_eq_map, FractionalIdeal.absNorm_span_singleton,
    FractionalIdeal.coeIdeal_absNorm, absNorm_map_ringOfIntegers] at hL
  have hmap : IsFractionRing.map (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))
      (algebraMap (𝓞 K) K d) = algebraMap K L (algebraMap (𝓞 K) K d) := by
    simp only [IsFractionRing.map]
    rw [IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      ← IsScalarTower.algebraMap_apply (𝓞 K) K L]
  rw [hmap, norm_algebraMap_tower, Nat.cast_pow, ← hK, abs_pow, mul_pow] at hL
  have hN0 : |Algebra.norm ℚ (algebraMap (𝓞 K) K d)| ^ Module.finrank K L ≠ 0 :=
    pow_ne_zero _ (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hd0))
  exact mul_left_cancel₀ hN0 hL

/-- **Base change of the Arakelov degree** for Hermitian lines given by fractional ideals:
`deg_L(I𝓞_L, ρ∘res) = [L:K] · deg_K(I, ρ)`. -/
theorem arakelovDegree_ofFractionalIdeal_baseChange (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (ρ : (K →+* ℂ) → ℝ) (hρ : ∀ σ, 0 < ρ σ) :
    (HermitianLattice.ofFractionalIdeal (FractionalIdeal.extendedHom L (𝓞 L) I)
      ((FractionalIdeal.extendedHom_eq_zero_iff L (𝓞 L)).not.mpr hI)
      (fun τ => ρ (τ.comp (algebraMap K L))) (fun _ => hρ _)).arakelovDegree =
      Module.finrank K L * (HermitianLattice.ofFractionalIdeal I hI ρ hρ).arakelovDegree := by
  rw [HermitianLattice.arakelovDegree_ofFractionalIdeal,
    HermitianLattice.arakelovDegree_ofFractionalIdeal, absNorm_extendedHom,
    sum_embeddings_comp (fun σ => Real.log (ρ σ))]
  push_cast
  rw [Real.log_pow]
  ring

end BaseChangeNorm

/-! ## 12. Base-change invariance of the model height (node H4, dimension-1 Hodge data) -/

section BaseChangeHeight

open scoped nonZeroDivisors

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The model height does not change under base change** (Hodge data of the form
`HodgeData.ofIdeal`): extending the lattice to `𝓞_L` and restricting the period lattices,
`h_L = h_K`. This is the Arakelov-theoretic content of "the Faltings height of a model with good
(or semistable) base change is invariant", node H4. -/
theorem HodgeData.modelHeight_ofIdeal_baseChange (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (P : (K →+* ℂ) → PeriodPair) :
    (HodgeData.ofIdeal (FractionalIdeal.extendedHom L (𝓞 L) 𝔞)
      ((FractionalIdeal.extendedHom_eq_zero_iff L (𝓞 L)).not.mpr h𝔞)
      (fun τ => P (τ.comp (algebraMap K L)))).modelHeight =
      (HodgeData.ofIdeal 𝔞 h𝔞 P).modelHeight := by
  rw [HodgeData.modelHeight_ofIdeal, HodgeData.modelHeight_ofIdeal, absNorm_extendedHom,
    sum_embeddings_comp (L := L) (fun σ => Real.log (ZLattice.covolume (P σ).lattice volume)),
    ← Module.finrank_mul_finrank ℚ K L]
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hL : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  push_cast
  rw [Real.log_pow]
  field_simp

end BaseChangeHeight

/-! ## 13. A numerical normalization check: `covol(ℤ + ℤi) = 1`, so `exampleHodge` has height 0 -/

section Gaussian

theorem covolume_gaussianPair : ZLattice.covolume gaussianPair.lattice = 1 := by
  have hspan : gaussianPair.lattice = Submodule.span ℤ (Set.range Complex.basisOneI) := by
    rw [Complex.coe_basisOneI, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.singleton_union]
    rfl
  have hF : IsAddFundamentalDomain gaussianPair.lattice
      (ZSpan.fundamentalDomain Complex.basisOneI) volume := by
    rw [hspan]; exact ZSpan.isAddFundamentalDomain _ volume
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume hF]
  have himg : Complex.measurableEquivPi ⁻¹'
      ZSpan.fundamentalDomain (Complex.basisOneI.map Complex.basisOneI.equivFun) =
      ZSpan.fundamentalDomain Complex.basisOneI := by
    rw [← ZSpan.map_fundamentalDomain]
    ext z
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨w, hw, hwz⟩
      have : w = z := Complex.basisOneI.equivFun.injective (by
        rw [hwz]; rfl)
      exact this ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  rw [Measure.real, ← himg, Complex.volume_preserving_equiv_pi.measure_preimage
    (ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet, ZSpan.volume_fundamentalDomain]
  have : Matrix.of (Complex.basisOneI.map Complex.basisOneI.equivFun) = 1 := by
    ext i j
    simp [Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp
  rw [this, Matrix.det_one, abs_one, ENNReal.ofReal_one, ENNReal.toReal_one]

theorem exampleHodge_modelHeight_eq_zero : exampleHodge.modelHeight = 0 := by
  rw [exampleHodge_modelHeight, covolume_gaussianPair, Real.log_one, mul_zero]

end Gaussian

/-! ## 14. Tensor products of fractional-ideal Hermitian lines (node AR3)

For invertible `𝓞_K`-modules inside `K`, `I ⊗ J ≅ IJ`, and the tensor-product metric is the
product metric; the degree is additive. -/

section Tensor

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

theorem arakelovDegree_ofFractionalIdeal_mul (I J : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (hJ : J ≠ 0) (ρ ρ' : (K →+* ℂ) → ℝ) (hρ : ∀ σ, 0 < ρ σ) (hρ' : ∀ σ, 0 < ρ' σ) :
    (HermitianLattice.ofFractionalIdeal (I * J) (mul_ne_zero hI hJ) (fun σ => ρ σ * ρ' σ)
      (fun σ => mul_pos (hρ σ) (hρ' σ))).arakelovDegree =
      (HermitianLattice.ofFractionalIdeal I hI ρ hρ).arakelovDegree +
        (HermitianLattice.ofFractionalIdeal J hJ ρ' hρ').arakelovDegree := by
  simp only [HermitianLattice.arakelovDegree_ofFractionalIdeal, map_mul, Rat.cast_mul]
  have hI0 : (FractionalIdeal.absNorm I : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hI)
  have hJ0 : (FractionalIdeal.absNorm J : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hJ)
  rw [Real.log_mul hI0 hJ0, Finset.sum_congr rfl fun σ _ =>
    Real.log_mul (hρ σ).ne' (hρ' σ).ne', Finset.sum_add_distrib]
  ring

end Tensor

/-! ## 15. Abelian varieties and smooth group models (copied from `bp-faltings/Models.lean`) -/

section ModelsSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ExteriorAlgebra

/-- (copied from `ZInQKernel/HDecomp/Objects.lean`) An abelian variety over a field `K`: a group
object in schemes over `Spec K`, proper, smooth and geometrically integral. -/
structure AbVar (K : Type) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

/-- (copied) Base change `A_L`. -/
noncomputable def AbVar.baseChange {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L]
    [Algebra K L] : AbVar L :=
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  letI : GrpObj ((Over.pullback f).obj A.X) := Functor.grpObjObj
  haveI : IsProper ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : Smooth ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  { X := (Over.pullback f).obj A.X }

/-- (copied from `ZInQKernel/HDecomp/Objects.lean`) The dimension of `A` (Krull dimension of the
underlying space). -/
noncomputable def AbVar.dim {K : Type} [Field K] (A : AbVar K) : WithBot ℕ∞ := topologicalKrullDim A.X.left

/-- The generic fibre `𝒢_L` of a scheme `𝒢` over `𝓞_L`. -/
noncomputable def genericFibre (L : Type) [Field L] [NumberField L]
    (G : Over (Spec (CommRingCat.of (𝓞 L)))) : Over (Spec (CommRingCat.of L)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).obj G

/-- **Node M1** (copied from `bp-faltings/Models.lean`). A smooth, separated, quasi-compact group
scheme over `𝓞_L` with an isomorphism of group schemes from its generic fibre to `A_L`. -/
structure GroupModel {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] where
  /-- the model -/
  G : Over (Spec (CommRingCat.of (𝓞 L)))
  [grp : GrpObj G]
  [smooth : Smooth G.hom]
  [separated : IsSeparated G.hom]
  [qc : QuasiCompact G.hom]
  /-- the identification of the generic fibre with `A_L` -/
  gen : genericFibre L G ≅ (A.baseChange L).X
  /-- ... as group schemes -/
  gen_hom : letI : GrpObj (genericFibre L G) := Functor.grpObjObj
    IsMonHom gen.hom

attribute [instance] GroupModel.grp GroupModel.smooth GroupModel.separated GroupModel.qc

/-- The generic point of `Spec 𝓞_L`. -/
def genericPt (L : Type) [Field L] [NumberField L] : Spec (CommRingCat.of (𝓞 L)) :=
  (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (𝓞 L))

/-! ## 16. The Hodge line of a smooth group model (nodes AV3, M2, M3)

Let `e : S = Spec 𝓞_L → 𝒢` be the unit section and `ξ = e(η_S)` the image of the generic point
(the identity of the generic fibre `𝒢_L ≅ A_L`). The local ring `𝒪_{𝒢,ξ}` is the local ring of
`A_L` at its origin, so `cotangent = 𝔪_ξ/𝔪_ξ²` is `ω_{A_L} = e*Ω¹_{A_L/L}` (an `L`-space of
dimension `g`; STANDARD, not proved here). For a point `s ∈ S`, `x = e(s)` specializes from `ξ`,
and `I_x = ker(𝒪_{𝒢,x} → 𝒪_{S,s})` is the ideal of the section at `x`; the image of `I_x` in
`𝔪_ξ/𝔪_ξ²` is the stalk at `s` of the conormal sheaf `e*(I/I²) = e*Ω¹_{𝒢/S}` (`𝒢/S` smooth;
EGA IV 17.2.5, UNVERIFIED locator). A locally free sheaf on the integral scheme `S` has global
sections the intersection of its stalks inside the generic stalk, hence

`ω_𝒢 = Γ(S, e*Ω¹_{𝒢/S}) = ⋂_s image(I_{e(s)})`   (`GroupModel.omega`).

Every module structure below is definitional (no proof obligations): the `𝓞_L`-module structure
on `cotangent` is restriction of scalars along the structure map `𝓞_L → 𝒪_{𝒢,ξ}`, and the
`L`-line is `hodgeSpace g = L ⊗_{𝓞_L} ⋀^g_{𝓞_L} cotangent` (`≅ ⋀^g_L ω_{A_L}` since `cotangent`
is an `L`-space; STANDARD). -/

namespace GroupModel

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- The unit section `e : Spec 𝓞_L → 𝒢`. -/
noncomputable def unitSection : Spec (CommRingCat.of (𝓞 L)) ⟶ 𝒢.G.left :=
  (η[𝒢.G] : 𝟙_ (Over (Spec (CommRingCat.of (𝓞 L)))) ⟶ 𝒢.G).left

/-- `ξ = e(generic point)`: the identity of the generic fibre. -/
noncomputable def genericUnit : 𝒢.G.left := 𝒢.unitSection (genericPt L)

/-- The local ring `𝒪_{𝒢,ξ} = 𝒪_{A_L,0}`. -/
noncomputable abbrev genStalk : CommRingCat := 𝒢.G.left.presheaf.stalk 𝒢.genericUnit

/-- The structure map `𝓞_L = Γ(S) → Γ(𝒢) → 𝒪_{𝒢,ξ}`. -/
noncomputable def structMap : 𝓞 L →+* 𝒢.genStalk :=
  ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv ≫ 𝒢.G.hom.appTop ≫
    𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial).hom

/-- **Node AV3.** `ω_{A_L} = 𝔪_ξ/𝔪_ξ²`, the invariant differentials of the generic fibre. -/
def cotangent : Type := IsLocalRing.CotangentSpace 𝒢.genStalk

noncomputable instance : AddCommGroup 𝒢.cotangent :=
  inferInstanceAs (AddCommGroup (IsLocalRing.CotangentSpace 𝒢.genStalk))

noncomputable instance : Module 𝒢.genStalk 𝒢.cotangent :=
  inferInstanceAs (Module 𝒢.genStalk (IsLocalRing.CotangentSpace 𝒢.genStalk))

noncomputable instance : Module (𝓞 L) 𝒢.cotangent := Module.compHom _ 𝒢.structMap

/-- `df ∈ 𝔪_ξ/𝔪_ξ²` for a germ `f ∈ 𝔪_ξ`. -/
noncomputable def dCls (f : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.cotangent :=
  (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent f

/-- `ξ ⤳ e(s)` for every `s ∈ Spec 𝓞_L`. -/
theorem specializes_genericUnit (s : Spec (CommRingCat.of (𝓞 L))) :
    𝒢.genericUnit ⤳ 𝒢.unitSection s :=
  ((PrimeSpectrum.le_iff_specializes (genericPt L) s).mp bot_le).map
    𝒢.unitSection.continuous

/-- The stalk at `s` of `e*Ω¹_{𝒢/S}` inside `ω_{A_L}`: the `𝓞_L`-span of the image of
`I_{e(s)} = ker(𝒪_{𝒢,e(s)} → 𝒪_{S,s})` under specialization `𝒪_{𝒢,e(s)} → 𝒪_{𝒢,ξ}`. (The
condition that the image lies in `𝔪_ξ` always holds; it is imposed so that no proof is needed in
the definition. The image is already an `𝒪_{S,s}`-module, so the span adds nothing.) -/
noncomputable def omegaAt (s : Spec (CommRingCat.of (𝓞 L))) : Submodule (𝓞 L) 𝒢.cotangent :=
  Submodule.span (𝓞 L) {m | ∃ f ∈ RingHom.ker (𝒢.unitSection.stalkMap s).hom,
    ∃ h : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) f ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk, m = 𝒢.dCls ⟨_, h⟩}

/-- **Node M2.** `ω_𝒢 = Γ(Spec 𝓞_L, e*Ω¹_{𝒢/𝓞_L}) = ⋂_s (ω_𝒢)_s ⊆ ω_{A_L}`. -/
noncomputable def omega : Submodule (𝓞 L) 𝒢.cotangent := ⨅ s, 𝒢.omegaAt s

/-- **Node AV4.** The Hodge line `⋀^g ω_{A_L}`, as `L ⊗_{𝓞_L} ⋀^g_{𝓞_L} (𝔪_ξ/𝔪_ξ²)`. -/
abbrev hodgeSpace (g : ℕ) : Type :=
  TensorProduct (𝓞 L) L (exteriorPower (𝓞 L) g 𝒢.cotangent)

/-- **Node M3.** The Hodge lattice `⋀^g ω_𝒢 ⊆ ⋀^g ω_{A_L}`: the `𝓞_L`-span of the wedges of
elements of `ω_𝒢`. -/
noncomputable def detLattice (g : ℕ) : Submodule (𝓞 L) (𝒢.hodgeSpace g) :=
  Submodule.span (𝓞 L) (Set.range fun v : Fin g → 𝒢.omega =>
    (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => (v i : 𝒢.cotangent)))

/-- The wedge `1 ⊗ df₁ ∧ ⋯ ∧ df_g ∈ hodgeSpace g` of germs `f_i ∈ 𝔪_ξ`. -/
noncomputable def wedge {g : ℕ} (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.hodgeSpace g :=
  (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => 𝒢.dCls (f i))

/-! ## 17. Complex points and the analytic uniformization (node AN3: the gap)

For `τ : L → ℂ`, the `ℂ`-points of `A_L` at `τ` are the `𝓞_L`-morphisms `Spec ℂ → 𝒢` with
`Spec ℂ → Spec 𝓞_L` given by `τ|_{𝓞_L}` (they factor through the generic fibre since `τ` is
injective). Mathlib gives them a group structure (`MonObj.Hom.group`). A regular function
`s ∈ Γ(U, 𝒪_𝒢)` has a value `evalAt p U s ∈ ℂ` at a point `p ∈ U(ℂ)`.

**`IsAnalyticUniformization 𝒢 τ Λ Φ`** says: `Φ : ℂ^g → 𝒢(ℂ)_τ` is a group homomorphism, onto,
with kernel exactly `Λ`; each `Φ⁻¹(U(ℂ))` is open and each regular function is holomorphic along
`Φ` there. With `Λ` a full lattice, `Φ` is then continuous for the analytic topology, so it
induces a continuous bijection of the compact `ℂ^g/Λ` onto the Hausdorff `A_τ(ℂ)`, a
homeomorphism, holomorphic, hence biholomorphic. Any two such `(Λ, Φ)` differ by a `ℂ`-linear
automorphism of `ℂ^g` (a holomorphic homomorphism of complex tori lifts to a linear map). These
are STANDARD facts of complex analysis, not proved here.

**The gap (AN3).** That such `(Λ, Φ)` *exists* is `AnalyticUniformizationExists` below: a
precisely stated Prop over Mathlib's objects, unproved (it is the uniformization theorem
`A(ℂ) ≅ ℂ^g/Λ`, Mumford, *Abelian varieties* §1, with GAGA-type input; locator UNVERIFIED). The
definition of the height does **not** assume it: the infimum ranges over models *together with*
a uniformization satisfying the Prop. Without the theorem one cannot prove the index set
nonempty, i.e. that the height is `< ⊤`. -/

/-- `Spec ℂ` over `Spec 𝓞_L` via `τ`. -/
noncomputable def ptC (τ : L →+* ℂ) : Over (Spec (CommRingCat.of (𝓞 L))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))))

/-- The complex points `𝒢(ℂ)_τ = A_L(ℂ)_τ`, a group (`MonObj.Hom.group`). -/
noncomputable abbrev Pts (τ : L →+* ℂ) : Type := ptC τ ⟶ 𝒢.G

noncomputable example (τ : L →+* ℂ) : Group (𝒢.Pts τ) := inferInstance

/-- The value `s(p) ∈ ℂ` of a regular function `s ∈ Γ(U, 𝒪_𝒢)` at a complex point `p ∈ U(ℂ)`
(and `0` if `p ∉ U(ℂ)`). -/
noncomputable def evalAt {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens)
    (s : Γ(𝒢.G.left, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ p.left ⁻¹ᵁ U then
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.left.appLE U ⊤ h s) else 0

/-- `Φ⁻¹(U(ℂ)) ⊆ ℂ^g`. -/
def dom {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (U : 𝒢.G.left.Opens) :
    Set (Fin g → ℂ) := {z | ⊤ ≤ (Φ z).left ⁻¹ᵁ U}

/-- **The analytic uniformization at `τ`** (the Prop that pins down the archimedean data). -/
def IsAnalyticUniformization (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ) : Prop :=
  (∀ z w, Φ (z + w) = Φ z * Φ w) ∧
  (∀ z, Φ z = 1 ↔ z ∈ Λ) ∧
  Function.Surjective Φ ∧
  (∀ U, IsOpen (𝒢.dom Φ U)) ∧
  (∀ U (s : Γ(𝒢.G.left, U)), DifferentiableOn ℂ (fun z => 𝒢.evalAt (Φ z) U s) (𝒢.dom Φ U))

theorem exists_rep (t : 𝒢.genStalk) : ∃ (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U)
    (s : Γ(𝒢.G.left, U)), 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s = t :=
  TopCat.Presheaf.exists_germ_eq _ t

/-- A germ `t ∈ 𝒪_{𝒢,ξ}` composed with `Φ`, through a chosen representative `(U, s)`. Since
`Φ(0) = 1` lies over `ξ` and `Φ⁻¹(U(ℂ))` is open, the germ at `0` of this function, hence its
derivative at `0`, does not depend on the representative (for an analytic uniformization). -/
noncomputable def germAlong {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (t : 𝒢.genStalk) : (Fin g → ℂ) → ℂ := fun z =>
  𝒢.evalAt (Φ z) (𝒢.exists_rep t).choose (𝒢.exists_rep t).choose_spec.choose_spec.choose

/-- `det(∂(f_i ∘ Φ)/∂z_j (0))`: the coefficient of `Φ*(df₁ ∧ ⋯ ∧ df_g)` on `dz₁ ∧ ⋯ ∧ dz_g`
(an invariant form is determined by its value at `0`). -/
noncomputable def jacDet {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) : ℂ :=
  (Matrix.of fun i j : Fin g =>
    fderiv ℂ (𝒢.germAlong Φ (f i : 𝒢.genStalk)) 0 (Pi.single j 1)).det

end GroupModel

/-- **The gap AN3, stated.** For every smooth group model `𝒢` of `A_L` and every `τ : L → ℂ` there
are `g`, a full lattice `Λ ⊂ ℂ^g` and an analytic uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` with kernel
`Λ`. (The uniformization theorem for complex abelian varieties; unproved, absent from Mathlib:
it needs the analytification of `A_τ` as a compact complex Lie group.) -/
def AnalyticUniformizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ), ∃ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
      (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ 𝒢.IsAnalyticUniformization τ Λ Φ

/-- **The uniqueness half of AN3, stated.** Two analytic uniformizations differ by a `ℂ`-linear
automorphism `T` of `ℂ^g`: `Φ' = Φ ∘ T`, `Λ' = T⁻¹Λ`. (A holomorphic homomorphism of complex
tori lifts to a linear map; unproved.) With `HodgeData.modelHeight_recoord` this is what makes the
model height independent of the uniformization. -/
def AnalyticUniformizationUnique : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ Λ' : Submodule ℤ (Fin g → ℂ))
    (Φ Φ' : (Fin g → ℂ) → 𝒢.Pts τ),
    𝒢.IsAnalyticUniformization τ Λ Φ → 𝒢.IsAnalyticUniformization τ Λ' Φ' →
    ∃ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, Φ' z = Φ (T z)) ∧ (∀ z, z ∈ Λ' ↔ T z ∈ Λ)

/-- **The algebraic half (AV2-AV4, M2-M3), stated.** For a model of relative dimension `g`
(`g` = the dimension of `A`), `hodgeSpace g` is an `L`-line and `detLattice g` is a full
`𝓞_L`-lattice in it. (Smoothness: `ω_𝒢` is projective of rank `g`; unproved.) -/
def HodgeLatticeTheorem : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (g : ℕ), A.dim = g →
    Module.finrank L (𝒢.hodgeSpace g) = 1 ∧
      ∃ s ∈ 𝒢.detLattice g, s ≠ 0 ∧ secIndex (𝒢.detLattice g) s ≠ 0

/-! ## 18. Metrized models and the stable Faltings height (node H3) -/

/-- **A metrized model of `A_L` of dimension `g`**: a smooth group model `𝒢` (node M1) with its
metrized Hodge line. The lattice is the genuine `⋀^g ω_𝒢` (`lattice_eq`), and at every `τ` the
period lattice and the coefficient map come from an analytic uniformization of `𝒢(ℂ)_τ`
(`arch`): `coeff_τ(1 ⊗ df₁ ∧ ⋯ ∧ df_g) = det(∂(f_i ∘ Φ)/∂z_j(0))`. Since the wedges `wedge f`
span `hodgeSpace g` over `L`, `arch` determines `coeff`; by `AnalyticUniformizationUnique` and
`HodgeData.modelHeight_recoord`, `hodge.modelHeight` depends only on `𝒢`. A wrong `g` makes the
structure empty (`hodge.finrank_eq_one` fails). -/
structure MetrizedModel {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] (g : ℕ) where
  /-- the smooth group model -/
  model : GroupModel A L
  /-- its Hodge data: lattice, period lattices, coefficient maps -/
  hodge : HodgeData L g (model.hodgeSpace g)
  /-- the lattice is `⋀^g ω_𝒢` -/
  lattice_eq : hodge.lattice = model.detLattice g
  /-- the archimedean data come from analytic uniformizations -/
  arch : ∀ τ : L →+* ℂ, ∃ Φ : (Fin g → ℂ) → model.Pts τ,
    model.IsAnalyticUniformization τ (hodge.periods τ) Φ ∧
    ∀ f : Fin g → IsLocalRing.maximalIdeal model.genStalk,
      hodge.coeff τ (model.wedge f) = model.jacDet Φ f

/-- A number field `L` with a `K`-algebra structure (the index type of the infimum). -/
structure FinExt (K : Type) [Field K] where
  /-- the field -/
  L : Type
  [field : Field L]
  [numberField : NumberField L]
  [algebra : Algebra K L]

attribute [instance] FinExt.field FinExt.numberField FinExt.algebra

/-- **Node H3. The stable Faltings height** (Faltings' original normalization `(i/2)^g`):
`h_F^st(A) = inf_{L, 𝒢} h(A_L, 𝒢) ∈ EReal`, over all number fields `L ⊇ K` and all smooth
separated finite-type group models `𝒢/𝓞_L` of `A_L`, each with its metrized Hodge line.
(pkg-I5 §2.1; equal to the Néron-model value over a semistable `L` by the Néron mapping property
and SGA 7 IX: node H5, not proved. `⊤` if there is no metrized model, which
`AnalyticUniformizationExists` and `HodgeLatticeTheorem` exclude once proved.) -/
noncomputable def stableFaltingsHeight {K : Type} [Field K] (A : AbVar K) : EReal :=
  ⨅ (E : FinExt K) (g : ℕ) (M : MetrizedModel A E.L g), (M.hodge.modelHeight : EReal)

/-- **Node H6. Deligne's normalization** `(i/2π)^g`: each model height shifts by `(g/2) log π`. -/
noncomputable def stableFaltingsHeightDeligne {K : Type} [Field K] (A : AbVar K) : EReal :=
  ⨅ (E : FinExt K) (g : ℕ) (M : MetrizedModel A E.L g),
    ((M.hodge.modelHeight + g / 2 * Real.log Real.pi : ℝ) : EReal)

section HeightLemmas

variable {K : Type} [Field K] (A : AbVar K)

theorem stableFaltingsHeight_le {L : Type} [Field L] [NumberField L] [Algebra K L] {g : ℕ}
    (M : MetrizedModel A L g) : stableFaltingsHeight A ≤ (M.hodge.modelHeight : EReal) :=
  iInf_le_of_le (FinExt.mk L) (iInf_le_of_le g (iInf_le_of_le M le_rfl))

theorem le_stableFaltingsHeight {x : EReal}
    (h : ∀ (E : FinExt K) (g : ℕ) (M : MetrizedModel A E.L g), x ≤ (M.hodge.modelHeight : EReal)) :
    x ≤ stableFaltingsHeight A :=
  le_iInf fun E => le_iInf fun g => le_iInf fun M => h E g M

theorem EReal.add_coe_add_neg_coe (x : EReal) (c : ℝ) : x + (c : EReal) + ((-c : ℝ) : EReal) = x := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe a => rw [← EReal.coe_add, ← EReal.coe_add]; congr 1; ring

/-- **H6 for the infimum**: if every metrized model of `A` has dimension `g` (true for
`g = dim A`), `h_D^st(A) = h_F^st(A) + (g/2) log π`. Proved. -/
theorem stableFaltingsHeightDeligne_eq (g : ℕ)
    (hg : ∀ (E : FinExt K) (g' : ℕ), Nonempty (MetrizedModel A E.L g') → g' = g) :
    stableFaltingsHeightDeligne A =
      stableFaltingsHeight A + ((g / 2 * Real.log Real.pi : ℝ) : EReal) := by
  set c : ℝ := g / 2 * Real.log Real.pi
  apply le_antisymm
  · -- `hD + (-c) ≤ hF`
    have key : stableFaltingsHeightDeligne A + ((-c : ℝ) : EReal) ≤ stableFaltingsHeight A := by
      refine le_stableFaltingsHeight A fun E g' M => ?_
      obtain rfl := hg E g' ⟨M⟩
      have h1 : stableFaltingsHeightDeligne A ≤
          ((M.hodge.modelHeight + g' / 2 * Real.log Real.pi : ℝ) : EReal) :=
        iInf_le_of_le E (iInf_le_of_le g' (iInf_le_of_le M le_rfl))
      calc stableFaltingsHeightDeligne A + ((-c : ℝ) : EReal)
          ≤ ((M.hodge.modelHeight + c : ℝ) : EReal) + ((-c : ℝ) : EReal) := by gcongr
        _ = (M.hodge.modelHeight : EReal) := by
          rw [← EReal.coe_add]; congr 1; ring
    calc stableFaltingsHeightDeligne A
        = stableFaltingsHeightDeligne A + ((-c : ℝ) : EReal) + ((c : ℝ) : EReal) := by
          have := EReal.add_coe_add_neg_coe (stableFaltingsHeightDeligne A) (-c)
          rw [neg_neg] at this; exact this.symm
      _ ≤ stableFaltingsHeight A + (c : EReal) := by gcongr
  · refine le_iInf fun E => le_iInf fun g' => le_iInf fun M => ?_
    obtain rfl := hg E g' ⟨M⟩
    rw [EReal.coe_add]
    gcongr
    exact stableFaltingsHeight_le A M

end HeightLemmas

end ModelsSec

end ZInQ.DefFaltings
