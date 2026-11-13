import Mathlib

section DefFaltingsSec
/-! ### leaf-adopt (2026-11-12): copied from `scratch/def-faltings/Faltings.lean` (compiled there).
Only changes: imports and `#print axioms` lines dropped. Note: its `ZInQ.DefFaltings.AbVar` is a
second copy of the kernel's abelian-variety structure (same four fields as `PkgI3.AbVar`), so
R19-R21 and H5 are over that copy; `LeafAdopt.abVarEquiv` (proved) identifies the two, and
unifying the declarations is WP1 work. -/


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

/-- Sanity check of `omegaAt`: at the generic point of `Spec 𝓞_L` the local lattice is all of
`ω_{A_L}` (the stalk of `e*Ω¹` at the generic point is the generic stalk), so `omega` is the
intersection of genuine local lattices at the closed points. Proved. -/
theorem omegaAt_genericPt : 𝒢.omegaAt (genericPt L) = ⊤ := by
  rw [eq_top_iff]
  rintro m -
  obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective m
  have hspec : ∀ x, (𝒢.G.left.presheaf.stalkSpecializes
      (𝒢.specializes_genericUnit (genericPt L))).hom x = x := by
    intro x
    rw [show 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit (genericPt L)) =
      𝟙 _ from TopCat.Presheaf.stalkSpecializes_refl _ _]
    rfl
  have hfield : IsField ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L)) := by
    have : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) :=
      (genericPoint_eq_bot_of_affine (CommRingCat.of (𝓞 L))).symm
    rw [this]
    exact Field.toIsField _
  apply Submodule.subset_span
  refine ⟨(f : 𝒢.genStalk), ?_, ?_, ?_⟩
  · show (𝒢.unitSection.stalkMap (genericPt L)).hom (f : 𝒢.genStalk) = 0
    have hloc : (𝒢.unitSection.stalkMap (genericPt L)).hom (f : 𝒢.genStalk) ∈
        IsLocalRing.maximalIdeal _ :=
      map_nonunit _ _ ((IsLocalRing.mem_maximalIdeal _).mp f.2)
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield] at hloc
    exact hloc
  · convert f.2 using 1
    exact hspec _
  · unfold dCls
    congr 1
    exact Subtype.ext (hspec _).symm

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
structure empty: for `0 < g ≠ dim A`, `hodge.finrank_eq_one` fails (and for `g > dim A` also
`periods_discrete`); `g = 0` passes `finrank_eq_one` (`hodgeSpace 0 ≅ L`) but is excluded for
`dim A ≥ 1` by surjectivity of `Φ : ℂ⁰ → A_τ(ℂ)` (STANDARD reasoning, not proved). -/
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

/-! ### Independence of the uniformization (node H2, archimedean part)

Under the uniqueness half of AN3, the height of a metrized model depends only on the group model:
the coefficient map is determined by its values on the wedges `1 ⊗ df₁ ∧ ⋯ ∧ df_g`
(`GroupModel.semilinear_ext_wedge`), which change by `det T` under `Φ ↦ Φ ∘ T`
(`GroupModel.jacDet_comp`, the chain rule), and `HodgeData.modelHeight_recoord` absorbs `T`. -/

section UnifIndep

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

namespace GroupModel

variable (𝒢 : GroupModel A L)

/-- A `τ`-semilinear functional on the Hodge line is determined by its values on the wedges
`1 ⊗ df₁ ∧ ⋯ ∧ df_g` of germs `f_i ∈ 𝔪_ξ`. -/
theorem semilinear_ext_wedge {g : ℕ} {τ : L →+* ℂ} (φ ψ : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ)
    (h : ∀ f, φ (𝒢.wedge f) = ψ (𝒢.wedge f)) : φ = ψ := by
  have h1 : ∀ n : exteriorPower (𝓞 L) g 𝒢.cotangent,
      φ ((1 : L) ⊗ₜ[𝓞 L] n) = ψ ((1 : L) ⊗ₜ[𝓞 L] n) := by
    intro n
    have hn : n ∈ Submodule.span (𝓞 L) (Set.range (exteriorPower.ιMulti (𝓞 L) g)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      have hm : ∀ i, ∃ f, 𝒢.dCls f = m i := fun i =>
        (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective (m i)
      choose f hf using hm
      have := h f
      simp only [wedge, hf] at this
      exact this
    | zero => simp
    | add x y _ _ hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | smul c x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul L c, map_smulₛₗ, map_smulₛₗ, hx]
  ext v
  induction v using TensorProduct.inductionOn with
  | tmul l n =>
    have : l ⊗ₜ[𝓞 L] n = l • ((1 : L) ⊗ₜ[𝓞 L] n) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [this, map_smulₛₗ, map_smulₛₗ, h1]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Chain rule**: `jacDet (Φ ∘ T) f = jacDet Φ f · det T`. -/
theorem jacDet_comp {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet (fun z => Φ (T z)) f =
      𝒢.jacDet Φ f * LinearMap.det (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) := by
  set Tc := T.toContinuousLinearEquiv
  have hd : ∀ t, fderiv ℂ (𝒢.germAlong (fun z => Φ (T z)) t) 0 =
      (fderiv ℂ (𝒢.germAlong Φ t) 0).comp (Tc : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := by
    intro t
    have : 𝒢.germAlong (fun z => Φ (T z)) t = 𝒢.germAlong Φ t ∘ Tc := rfl
    rw [this, Tc.comp_right_fderiv, map_zero]
  unfold jacDet
  simp only [hd]
  rw [← LinearMap.det_toMatrix', ← Matrix.det_mul]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, LinearMap.toMatrix'_apply,
    ContinuousLinearMap.comp_apply]
  show (fderiv ℂ (𝒢.germAlong Φ ↑(f i)) 0) (T (Pi.single j 1)) = _
  conv_lhs => rw [← Finset.univ_sum_single (T (Pi.single j 1))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : (Pi.single k ((T (Pi.single j 1)) k) : Fin g → ℂ) =
      ((T (Pi.single j 1)) k) • (Pi.single k (1 : ℂ) : Fin g → ℂ) := by
    ext m; by_cases hm : m = k
    · subst hm; simp
    · simp [hm]
  rw [hs, map_smul, smul_eq_mul, mul_comm]
  rfl

end GroupModel

/-- **The model height does not depend on the uniformization** (given the uniqueness half of
AN3): two metrized models with the same group model have the same height. Proved. -/
theorem MetrizedModel.modelHeight_eq_of_model_eq (hU : AnalyticUniformizationUnique) {g : ℕ}
    (M M' : MetrizedModel A L g) (h : M.model = M'.model) :
    M.hodge.modelHeight = M'.hodge.modelHeight := by
  obtain ⟨𝒢, D, hl, ha⟩ := M
  obtain ⟨𝒢', D', hl', ha'⟩ := M'
  dsimp only at h ⊢
  subst h
  have key : ∀ τ, ∃ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ z, z ∈ D'.periods τ ↔ T z ∈ D.periods τ) ∧
      D'.coeff τ = LinearMap.det (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) • D.coeff τ := by
    intro τ
    obtain ⟨Φ, hΦ, hc⟩ := ha τ
    obtain ⟨Φ', hΦ', hc'⟩ := ha' τ
    obtain ⟨T, hT, hΛ⟩ := hU K A L 𝒢 τ g _ _ Φ Φ' hΦ hΦ'
    refine ⟨T, hΛ, ?_⟩
    apply GroupModel.semilinear_ext_wedge
    intro f
    have hΦ'T : Φ' = fun z => Φ (T z) := funext hT
    rw [hc', LinearMap.smul_apply, hc, smul_eq_mul, hΦ'T, GroupModel.jacDet_comp, mul_comm]
  choose T hTp hTc using key
  have hD' : D' = D.recoord T := by
    obtain ⟨l', f1', il', p', pd', pz', c', cn'⟩ := D'
    obtain ⟨l, f1, il, p, pd, pz, c, cn⟩ := D
    simp only [HodgeData.recoord, HodgeData.mk.injEq]
    refine ⟨hl'.trans hl.symm, ?_, ?_⟩
    · funext τ
      ext z
      rw [hTp τ z]
      rfl
    · funext τ
      exact hTc τ
  show D.modelHeight = D'.modelHeight
  rw [hD', HodgeData.modelHeight_recoord]

/-- **The height of a group model** `h(A_L, 𝒢)`: the infimum over its metrizations (all of which
have the same height, `MetrizedModel.modelHeight_eq_of_model_eq`, given the uniqueness half of
AN3). -/
noncomputable def GroupModel.height (𝒢 : GroupModel A L) : EReal :=
  ⨅ (g : ℕ) (M : MetrizedModel A L g) (_ : M.model = 𝒢), (M.hodge.modelHeight : EReal)

/-- Given the uniqueness half of AN3, a metrized model computes the height of its group model
(among metrizations of the same dimension; the dimension is unique by `hodge.finrank_eq_one` and
the surjectivity in `IsAnalyticUniformization`). -/
theorem GroupModel.height_eq (hU : AnalyticUniformizationUnique) {g : ℕ} (M : MetrizedModel A L g)
    (hg : ∀ (g' : ℕ), Nonempty (MetrizedModel A L g') → g' = g) :
    M.model.height = (M.hodge.modelHeight : EReal) := by
  refine le_antisymm (iInf_le_of_le g (iInf_le_of_le M (iInf_le_of_le rfl le_rfl))) ?_
  refine le_iInf fun g' => le_iInf fun M' => le_iInf fun hM' => ?_
  obtain rfl := hg g' ⟨M'⟩
  rw [MetrizedModel.modelHeight_eq_of_model_eq hU M M' hM'.symm]

/-- `stableFaltingsHeight A = inf_{L, 𝒢} h(A_L, 𝒢)`. -/
theorem stableFaltingsHeight_eq_iInf_height (A : AbVar K) :
    stableFaltingsHeight A = ⨅ (E : FinExt K) (𝒢 : GroupModel A E.L), 𝒢.height := by
  unfold stableFaltingsHeight GroupModel.height
  refine le_antisymm ?_ ?_
  · refine le_iInf fun E => le_iInf fun 𝒢 => le_iInf fun g => le_iInf fun M => le_iInf fun _ => ?_
    exact iInf_le_of_le E (iInf_le_of_le g (iInf_le_of_le M le_rfl))
  · refine le_iInf fun E => le_iInf fun g => le_iInf fun M => ?_
    exact iInf_le_of_le E (iInf_le_of_le M.model (iInf_le_of_le g (iInf_le_of_le M
      (iInf_le_of_le rfl le_rfl))))

end UnifIndep

/-! ### The theorems that tie the definition to the literature (node H5), stated

`IsNeronModel` is the Néron mapping property (BLR 1.2/1, UNVERIFIED locator), stated with
Mathlib's objects: every morphism from the generic fibre of a smooth `𝓞_L`-scheme to `A_L`
extends uniquely. H5 is unproved; it needs Néron models (existence: BLR 1.4/3), semistable
reduction (SGA 7 IX 3.6) and the base change of semistable Néron models (SGA 7 IX 3.3), all
absent from Mathlib (locators UNVERIFIED). -/

section NeronSec

variable {K : Type} [Field K]

/-- **The Néron mapping property** for a group model `𝒩` of `A_L`. -/
def GroupModel.IsNeronModel {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒩 : GroupModel A L) : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of (𝓞 L)))) [Smooth Y.hom],
    Function.Bijective fun f : Y ⟶ 𝒩.G =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map f ≫ 𝒩.gen.hom

/-- **H5, finiteness (statement).** Over a number field, the stable height is a real number. -/
def StableHeightFinite : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K),
    stableFaltingsHeight A ≠ ⊤ ∧ stableFaltingsHeight A ≠ ⊥

/-- **H5, minimality of the Néron model (statement).** Over any `L`, the Néron model has the
least height among group models (from the mapping property, `ω_𝒩 ⊆ ω_𝒢`, and
`HodgeData.modelHeight_le_of_le`). -/
def NeronModelMinimal : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒩 𝒢 : GroupModel A L), 𝒩.IsNeronModel → 𝒩.height ≤ 𝒢.height

/-- The real-valued stable Faltings height. Meaningful only together with `StableHeightFinite`
(`EReal.toReal` sends `⊤` and `⊥` to `0`); the leaves above therefore never use it. -/
noncomputable def faltingsHeight (A : AbVar K) : ℝ := (stableFaltingsHeight A).toReal

theorem faltingsHeight_coe (hfin : StableHeightFinite) [NumberField K] (A : AbVar K) :
    (faltingsHeight A : EReal) = stableFaltingsHeight A :=
  EReal.coe_toReal (hfin K A).1 (hfin K A).2

end NeronSec

/-! ## 19. Acceptance test AT1: elliptic curves

`IsEllipticCurveOf A W` identifies an abelian variety with the elliptic curve of a Weierstrass
equation using only Mathlib objects: the complement of the origin is an affine open whose ring of
functions is `K`-isomorphic to the affine coordinate ring `K[x, y]/(W)`. (Then `A` is the smooth
projective model of the function field of `W` with origin `O`, so `A ≅ E_W` as pointed curves,
and the group law with a given origin is unique by rigidity: STANDARD.) Mathlib v4.35 cannot yet
construct such an `A` from `W` (node AV7), so `AcceptanceEC` is a statement, not a theorem. -/

section AT1

open Polynomial

variable {K : Type} [Field K]

/-- The structure map `K → Γ(U, 𝒪_A)`. -/
noncomputable def AbVar.structMapOn (A : AbVar K) (U : A.X.left.Opens) : K →+* Γ(A.X.left, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ A.X.hom.appTop ≫
    A.X.left.presheaf.map (homOfLE le_top).op).hom

/-- The origin of `A` (image of the unit section). -/
noncomputable def AbVar.origin (A : AbVar K) : A.X.left :=
  (η[A.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X).left
    ((⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) : Spec (CommRingCat.of K))

/-- `A` is the elliptic curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`: `A ∖ {O}` is affine with
ring of functions `K[x, y]/(W)`, compatibly with `K`. -/
def IsEllipticCurveOf (A : AbVar K) (W : WeierstrassCurve K) : Prop :=
  ∃ U : A.X.left.Opens, (U : Set A.X.left) = {A.origin}ᶜ ∧ IsAffineOpen U ∧
    ∃ e : W.toAffine.CoordinateRing ≃+* Γ(A.X.left, U),
      ∀ c : K, e (algebraMap K W.toAffine.CoordinateRing c) = A.structMapOn U c

/-- **Acceptance test AT1 (statement).** For an elliptic curve over a number field, the general
definition agrees with pkg-I5's closed formula. Unproved: needs AV7 (an `A` with
`IsEllipticCurveOf A W` exists), AN3 for `g = 1` (AN4: `℘`), AN5 (`PeriodAreaFormula`), M2 for
the minimal Weierstrass model, AT1a (the Néron lattice) and H5 (the infimum is attained at the
Néron model over a semistable field). -/
def AcceptanceEC : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic] (A : AbVar K),
    IsEllipticCurveOf A W → stableFaltingsHeight A = (faltingsHeightEC W : EReal)

/-- **AT1, conditional form over the general definition (proved).** Let `M` be a metrized model
of `A` over `K` itself whose Hodge lattice is free on `η₀` with `η₀ ↦ dz` for period pairs
`Lp σ` (outputs of AN4 and M2 for a minimal semistable Weierstrass model: `η₀ = dx/(2y+a₁x+a₃)`),
with the Weierstrass polynomial equal to `4x³ − g₂x − g₃` after a translation `x ↦ x + c_σ`
(so any `b₂` is allowed: `g₂ = σ(c₄)/12`, `g₃ = σ(c₆)/216`) and the finite part of
`faltingsHeightEC` vanishing (AT1a: the model is semistable and minimal everywhere). Then, given
the area formula AN5, `M.hodge.modelHeight = faltingsHeightEC W` (the content of the theorem),
and with `hmin` the stable height equals it.

Caveat: `hmin` ("no metrized model of `A` has smaller height") is literally the `≥` half of the
conclusion. It is the output H5 must supply for this `A`: the Néron mapping property
(`GroupModel.IsNeronModel`, `NeronModelMinimal`) plus semistable base change (SGA 7 IX), none of
which is proved. The theorem ties `M` to `W` only through the hypotheses on `M`; it does not
assume `IsEllipticCurveOf A W`. -/
theorem stableFaltingsHeight_eq_faltingsHeightEC [NumberField K] (hA : PeriodAreaFormula)
    (W : WeierstrassCurve K) [W.IsElliptic] (A : AbVar K) (M : MetrizedModel A K 1)
    {η₀ : M.model.hodgeSpace 1}
    (hspan : M.hodge.lattice = Submodule.span (𝓞 K) {η₀}) (hη₀ : η₀ ≠ 0)
    (Lp : (K →+* ℂ) → PeriodPair) (hper : ∀ σ, M.hodge.periods σ = (Lp σ).lattice1)
    (hco : ∀ σ, M.hodge.coeff σ η₀ = 1) (c : (K →+* ℂ) → ℂ)
    (hP : ∀ σ, (4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ =
      (4 * X ^ 3 - C (Lp σ).g₂ * X - C (Lp σ).g₃).comp (X + C (c σ)))
    (hfin : finiteHeightPart W.j = ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖)
    (hmin : ∀ (E : FinExt K) (g : ℕ) (M' : MetrizedModel A E.L g),
      faltingsHeightEC W ≤ M'.hodge.modelHeight) :
    stableFaltingsHeight A = (faltingsHeightEC W : EReal) := by
  have hM : M.hodge.modelHeight = faltingsHeightEC W := by
    rw [M.hodge.modelHeight_of_span hspan hη₀, faltingsHeightEC, hfin, sub_self, zero_div,
      zero_sub]
    have hterm : ∀ σ : K →+* ℂ, torusMetricSq (M.hodge.periods σ) (M.hodge.coeff σ η₀) =
        hypVol 1 ((4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ) := by
      intro σ
      rw [hco, hper, hP, hypVol_one_comp_add, torusMetricSq, PeriodPair.covolume_lattice1, hA]
      simp
    simp only [hterm]
    have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    field_simp
  refine le_antisymm ?_ ?_
  · exact (stableFaltingsHeight_le A M).trans_eq (by rw [hM])
  · exact le_stableFaltingsHeight A fun E g M' => EReal.coe_le_coe_iff.mpr (hmin E g M')

end AT1

/-! ## 20. Acceptance test AT2: genus-2 curves with a smooth model

`Genus2Eq`, `Genus2Eq.P`, `Genus2Eq.binDisc`, `Genus2Eq.Good` and `faltingsHeightGood` are copied
from `scratch/pkg-I5/I5.lean`. A statement "`stableFaltingsHeight (Jac C) = faltingsHeightGood E`"
cannot be written: Mathlib v4.35 has no Jacobians (node AV7) and no way to say that an `AbVar` is
the Jacobian of a curve. What is proved is the conditional form: a metrized model whose Hodge
lattice is free on `η₀` (M8: for a smooth Weierstrass model `𝒞/𝓞_K`, the Néron lattice is
`∧² H⁰(𝒞, ω) = 𝓞_K · (dx/(2y+h)) ∧ (x dx/(2y+h))`, BLR 9.5 Thm 4, Liu, UNVERIFIED locators) and
whose archimedean metric of `η₀` is the Gram determinant `hypVol 2` (AN6: Riemann's bilinear
relations), with `hmin` (H5), has `stableFaltingsHeight = faltingsHeightGood E`. -/

section AT2

open Polynomial

/-- (copied from pkg-I5) A genus-2 Weierstrass equation `y² + h(x) y = f(x)`. -/
structure Genus2Eq (R : Type*) [CommRing R] where
  f : R[X]
  h : R[X]
  deg_f : f.natDegree ≤ 6
  deg_h : h.natDegree ≤ 3

namespace Genus2Eq

variable {R : Type*} [CommRing R]

/-- (copied) `P = 4f + h²`. -/
noncomputable def P (E : Genus2Eq R) : R[X] := 4 * E.f + E.h ^ 2

/-- (copied) The discriminant of `P` as a binary sextic. -/
noncomputable def binDisc (E : Genus2Eq R) : R :=
  if E.P.natDegree = 6 then E.P.discr
  else if E.P.natDegree = 5 then E.P.leadingCoeff ^ 2 * E.P.discr else 0

/-- (copied) Smooth Weierstrass model over `𝓞 K`: `disc₆(P) = 2¹²·u`, `u` a unit. -/
def Good {K : Type*} [Field K] [NumberField K] (E : Genus2Eq (𝓞 K)) : Prop :=
  ∃ u : (𝓞 K)ˣ, E.binDisc = 2 ^ 12 * (u : 𝓞 K)

end Genus2Eq

/-- (copied from pkg-I5) `h_F(Jac C) = −(2[K:ℚ])⁻¹ ∑_σ log ‖ω₀∧ω₁‖²_σ` for a good equation. -/
noncomputable def faltingsHeightGood {K : Type*} [Field K] [NumberField K]
    (E : Genus2Eq (𝓞 K)) : ℝ :=
  -(∑ σ : K →+* ℂ, Real.log (hypVol 2 ((E.P.map (algebraMap (𝓞 K) K)).map σ))) /
    (2 * Module.finrank ℚ K)

/-- **AT2 bridge at the level of Hodge data (proved).** -/
theorem HodgeData.modelHeight_eq_faltingsHeightGood {K : Type*} [Field K] [NumberField K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (E : Genus2Eq (𝓞 K)) (D : HodgeData K 2 V) {η₀ : V}
    (hspan : D.lattice = Submodule.span (𝓞 K) {η₀}) (hη₀ : η₀ ≠ 0)
    (hgram : ∀ σ, torusMetricSq (D.periods σ) (D.coeff σ η₀) =
      hypVol 2 ((E.P.map (algebraMap (𝓞 K) K)).map σ)) :
    D.modelHeight = faltingsHeightGood E := by
  rw [D.modelHeight_of_span hspan hη₀, faltingsHeightGood]
  simp only [hgram]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  field_simp

/-- **AT2, conditional form over the general definition (proved).** As in AT1, `hmin` is the `≥`
half of the conclusion (the output H5 must supply); the content is
`HodgeData.modelHeight_eq_faltingsHeightGood`. -/
theorem stableFaltingsHeight_eq_faltingsHeightGood {K : Type} [Field K] [NumberField K]
    (E : Genus2Eq (𝓞 K)) (A : AbVar K) (M : MetrizedModel A K 2) {η₀ : M.model.hodgeSpace 2}
    (hspan : M.hodge.lattice = Submodule.span (𝓞 K) {η₀}) (hη₀ : η₀ ≠ 0)
    (hgram : ∀ σ, torusMetricSq (M.hodge.periods σ) (M.hodge.coeff σ η₀) =
      hypVol 2 ((E.P.map (algebraMap (𝓞 K) K)).map σ))
    (hmin : ∀ (F : FinExt K) (g : ℕ) (M' : MetrizedModel A F.L g),
      faltingsHeightGood E ≤ M'.hodge.modelHeight) :
    stableFaltingsHeight A = (faltingsHeightGood E : EReal) := by
  have hM := HodgeData.modelHeight_eq_faltingsHeightGood E M.hodge hspan hη₀ hgram
  refine le_antisymm ?_ ?_
  · exact (stableFaltingsHeight_le A M).trans_eq (by rw [hM])
  · exact le_stableFaltingsHeight A fun F g M' => EReal.coe_le_coe_iff.mpr (hmin F g M')

end AT2

/-! ## 21. The leaves R19-R21 over `stableFaltingsHeight`

Normalizations (docs/research/locators.md): Gaudron-Rémond (R19) and Faltings (R20) use the
stable height in Faltings' original normalization, which is `stableFaltingsHeight`; Bost's bound
(R21) is used in the form `h_F ≥ −(3/2) dim A` printed by Gaudron-Rémond §9; Pazuki (R22) uses
Deligne's metric, `stableFaltingsHeightDeligne = stableFaltingsHeight + (g/2) log π`
(`stableFaltingsHeightDeligne_eq`).

Where the height is an input of an upper bound (R19, R20), it is taken through a real `x` with
`stableFaltingsHeight A = x`, never through `EReal.toReal` (whose junk value `0` at `⊤` would
make the statement stronger than the published one). Isogenies: homomorphisms of group schemes
that are finite and surjective (project's `IsIsogenyMor`); the degree is the order of the kernel
on `K̄`-points, which equals the degree in characteristic `0` (STANDARD). -/

section Leaves

open MonObj

/-- `Spec L` as a `K`-scheme (copied from `ZInQKernel/HDecomp/Objects.lean`). -/
noncomputable def ptObj (K L : Type) [Field K] [Field L] [Algebra K L] :
    Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

variable {K : Type} [Field K]

/-- An isogeny: a homomorphism of group schemes, finite and surjective. -/
def IsIsogeny {A B : AbVar K} (φ : A.X ⟶ B.X) : Prop :=
  IsMonHom φ ∧ IsFinite φ.left ∧ Surjective φ.left

/-- The degree of an isogeny in characteristic `0`: `# ker(φ)(K̄)`. -/
noncomputable def isogDeg {A B : AbVar K} (φ : A.X ⟶ B.X) : ℕ :=
  Nat.card {P : ptObj K (AlgebraicClosure K) ⟶ A.X // P ≫ φ = 1}

/-- Gaudron-Rémond's `κ(A) = ((14g)^{64g²} [k:ℚ] max(h_F(A), log[k:ℚ], 1)²)^{1024g³}`. -/
noncomputable def grKappa (g d : ℕ) (x : ℝ) : ℝ :=
  ((14 * g : ℝ) ^ (64 * g ^ 2) * d * (max (max x (Real.log d)) 1) ^ 2) ^ (1024 * g ^ 3)

/-- **R19. Gaudron-Rémond**, Duke Math. J. 163 (2014), Thm 1.4 (p. 2060; `κ` and
`α(g) = 1024g³`, p. 2058), specialized to `k = K` (locators read by the audit, locators.md).
Isogenous abelian varieties over a number field admit isogenies in both directions of degree
`≤ κ(A)`. -/
def R19_GaudronRemond : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : AbVar K) (g : ℕ) (x : ℝ),
    A.dim = (g : WithBot ℕ∞) → stableFaltingsHeight A = x →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

/-- **R20. Faltings' height lemma** (Faltings 1983, Lemma 5; Raynaud, Astérisque 127, VII
Cor. 2.1.3): for an isogeny `φ : A → B`, `|h_F(A) − h_F(B)| ≤ ½ log deg φ`. Locator audit: Lemma 5
unread, UNVERIFIED (including direction and the stable/semistable hypotheses). -/
def R20_FaltingsLemma5 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ x y : ℝ, stableFaltingsHeight A = x → stableFaltingsHeight B = y →
      |x - y| ≤ (1 / 2) * Real.log (isogDeg φ)

/-- **R21. Bost's lower bound**, in the form printed by Gaudron-Rémond 2014 §9 (proof of
Lemma 9.1, p. 2098): `h_F(A) ≥ −(3/2) dim A`. Bost's own display UNVERIFIED (locators.md). -/
def R21_Bost : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ((-(3 / 2) * g : ℝ) : EReal) ≤ stableFaltingsHeight A

/-- R21 excludes `h = ⊥`. -/
theorem stableFaltingsHeight_ne_bot_of_R21 (h : R21_Bost) {K : Type} [Field K] [NumberField K]
    (A : AbVar K) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) : stableFaltingsHeight A ≠ ⊥ := by
  intro hb
  have := h K A g hg
  rw [hb] at this
  exact EReal.coe_ne_bot _ (le_bot_iff.mp this)

end Leaves

/-! ## 22. R18 and R22: not stated

* **R22 (Pazuki, Bull. SMF 140 (2012), Cor. 1.3(2)).** The height side is available:
  `stableFaltingsHeightDeligne` and `stableFaltingsHeightDeligne_eq` give
  `h_D = h_F + log π` for surfaces, so the condition `X_D ≥ max(1, h_D(A))` of the consequence
  form is expressible. Missing: principal polarizations, level-2 theta structures and the theta
  (Fubini-Study) height `h_Θ(A)` of a principally polarized abelian surface (the theta constants
  need the period matrix, i.e. AN3 together with the Riemann form). The genus-2 special case over
  `faltingsHeightGood` is `PkgI5.PazukiGoodGenus2Literal` (scratch/rv-loc-leaves).
* **R18 (Javanpeykar, ANT 8 (2014), Thm 1.1.1).** Missing: the genus of a smooth projective
  curve over `ℚ̄` (differentials or `H¹`), Belyi maps (finite morphisms to `ℙ¹` unramified outside
  `{0, 1, ∞}`, with their degree) and the Jacobian as an `AbVar` (node AV7). -/

end ModelsSec

end ZInQ.DefFaltings

end DefFaltingsSec

/-! ## g0-heightadd (2026-11-13): additivity `h(A) + h(Z) ≤ h(A × Z)` (glue E4)

Everything above this line is copied verbatim from `scratch/g0-split/Split.lean` lines
16667-18603 (= `scratch/def-faltings/Faltings.lean`: the definitions of `ZInQ.DefFaltings`,
in particular its `AbVar`, `GroupModel`, `MetrizedModel`, `stableFaltingsHeight`,
`NeronModelMinimal`). Below: h5-neron's Néron-model glue (copied from
`scratch/h5-neron/H5Neron.lean`, parts A and E, with `PkgI3.AbVar` replaced by
`ZInQ.DefFaltings.AbVar`, i.e. the line `open PkgI3 (AbVar)` dropped), then the piece. -/

namespace ZInQ.H5Neron

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory

section General

variable {S S' : Scheme.{0}} (j : S' ⟶ S) (P : Over S → Prop)

/-- The Néron mapping property of `N` (over `S`) for `A` (over `S'`) along `j`, tested on the
objects satisfying `P`. -/
def NeronProp (N : Over S) (A : Over S') (e : (Over.pullback j).obj N ≅ A) : Prop :=
  ∀ Y : Over S, P Y → Function.Bijective fun f : Y ⟶ N => (Over.pullback j).map f ≫ e.hom

variable {j P}

/-- Existence and uniqueness of the extension. -/
theorem NeronProp.lift {N : Over S} {A : Over S'} {e : (Over.pullback j).obj N ≅ A}
    (h : NeronProp j P N A e) {Y : Over S} (hY : P Y) (g : (Over.pullback j).obj Y ⟶ A) :
    ∃! f : Y ⟶ N, (Over.pullback j).map f ≫ e.hom = g := by
  obtain ⟨f, hf⟩ := (h Y hY).2 g
  exact ⟨f, hf, fun f' hf' => (h Y hY).1 (hf'.trans hf.symm)⟩

/-- **Uniqueness of Néron models**: two Néron models of `A` (each a test object) are isomorphic,
compatibly with the identifications of their generic fibres. -/
theorem NeronProp.uniqueIso {N N' : Over S} {A : Over S'} {e : (Over.pullback j).obj N ≅ A}
    {e' : (Over.pullback j).obj N' ≅ A} (h : NeronProp j P N A e) (h' : NeronProp j P N' A e')
    (hN : P N) (hN' : P N') :
    ∃ φ : N ≅ N', (Over.pullback j).map φ.hom ≫ e'.hom = e.hom := by
  obtain ⟨f, hf⟩ := (h' N hN).2 e.hom
  obtain ⟨f', hf'⟩ := (h N' hN').2 e'.hom
  simp only at hf hf'
  have h1 : f ≫ f' = 𝟙 N := by
    apply (h N hN).1
    simp only [Functor.map_comp, Category.assoc, hf', hf]
    erw [(Over.pullback j).map_id, Category.id_comp]
  have h2 : f' ≫ f = 𝟙 N' := by
    apply (h' N' hN').1
    simp only [Functor.map_comp, Category.assoc, hf', hf]
    erw [(Over.pullback j).map_id, Category.id_comp]
  exact ⟨⟨f, f', h1, h2⟩, hf⟩

/-- The identification of the generic fibre of `N₁ ⊗ N₂` with `A₁ ⊗ A₂`. -/
noncomputable def tensorGen {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    (e₁ : (Over.pullback j).obj N₁ ≅ A₁) (e₂ : (Over.pullback j).obj N₂ ≅ A₂) :
    (Over.pullback j).obj (N₁ ⊗ N₂) ≅ A₁ ⊗ A₂ :=
  prodComparisonIso (Over.pullback j) N₁ N₂ ≪≫ tensorIso e₁ e₂

theorem tensorGen_fst {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    (e₁ : (Over.pullback j).obj N₁ ≅ A₁) (e₂ : (Over.pullback j).obj N₂ ≅ A₂) :
    (tensorGen e₁ e₂).hom ≫ fst A₁ A₂ = (Over.pullback j).map (fst N₁ N₂) ≫ e₁.hom := by
  rw [tensorGen, Iso.trans_hom, prodComparisonIso_hom, tensorIso_hom, Category.assoc, tensorHom_fst,
    CartesianMonoidalCategory.prodComparison_fst_assoc]

theorem tensorGen_snd {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    (e₁ : (Over.pullback j).obj N₁ ≅ A₁) (e₂ : (Over.pullback j).obj N₂ ≅ A₂) :
    (tensorGen e₁ e₂).hom ≫ snd A₁ A₂ = (Over.pullback j).map (snd N₁ N₂) ≫ e₂.hom := by
  rw [tensorGen, Iso.trans_hom, prodComparisonIso_hom, tensorIso_hom, Category.assoc, tensorHom_snd,
    CartesianMonoidalCategory.prodComparison_snd_assoc]

/-- **A product of Néron models is a Néron model of the product.** -/
theorem NeronProp.tensor {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    {e₁ : (Over.pullback j).obj N₁ ≅ A₁} {e₂ : (Over.pullback j).obj N₂ ≅ A₂}
    (h₁ : NeronProp j P N₁ A₁ e₁) (h₂ : NeronProp j P N₂ A₂ e₂) :
    NeronProp j P (N₁ ⊗ N₂) (A₁ ⊗ A₂) (tensorGen e₁ e₂) := by
  intro Y hY
  have hfst : ∀ f : Y ⟶ N₁ ⊗ N₂, ((Over.pullback j).map f ≫ (tensorGen e₁ e₂).hom) ≫
      fst A₁ A₂ = (Over.pullback j).map (f ≫ fst N₁ N₂) ≫ e₁.hom := by
    intro f
    rw [Category.assoc, tensorGen_fst, Functor.map_comp, Category.assoc]
  have hsnd : ∀ f : Y ⟶ N₁ ⊗ N₂, ((Over.pullback j).map f ≫ (tensorGen e₁ e₂).hom) ≫
      snd A₁ A₂ = (Over.pullback j).map (f ≫ snd N₁ N₂) ≫ e₂.hom := by
    intro f
    rw [Category.assoc, tensorGen_snd, Functor.map_comp, Category.assoc]
  constructor
  · intro f f' hff'
    have a := hfst f
    have b := hfst f'
    have c := hsnd f
    have d := hsnd f'
    simp only at hff'
    rw [hff'] at a c
    apply CartesianMonoidalCategory.hom_ext
    · exact (h₁ Y hY).1 (a.symm.trans b)
    · exact (h₂ Y hY).1 (c.symm.trans d)
  · intro g
    obtain ⟨f₁, hf₁⟩ := (h₁ Y hY).2 (g ≫ fst A₁ A₂)
    obtain ⟨f₂, hf₂⟩ := (h₂ Y hY).2 (g ≫ snd A₁ A₂)
    refine ⟨CartesianMonoidalCategory.lift f₁ f₂, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [hfst, CartesianMonoidalCategory.lift_fst]; exact hf₁
    · rw [hsnd, CartesianMonoidalCategory.lift_snd]; exact hf₂

end General

section GroupModels

open NumberField DefFaltings

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev jL (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

/-- The project's `IsNeronModel` is `NeronProp` for smooth test objects. -/
theorem GroupModel.isNeronModel_iff (𝒩 : GroupModel A L) :
    𝒩.IsNeronModel ↔ NeronProp (jL L) (fun Y => Smooth Y.hom) 𝒩.G (A.baseChange L).X 𝒩.gen :=
  ⟨fun h Y hY => @h Y hY, fun h Y hY => h Y hY⟩

/-- The comparison morphism `𝒢 → 𝒩` from any group model to a Néron model, compatible with the
identifications of the generic fibres with `A_L`, and unique with this property. -/
theorem GroupModel.IsNeronModel.lift {𝒩 : GroupModel A L} (h𝒩 : 𝒩.IsNeronModel)
    (𝒢 : GroupModel A L) :
    ∃! f : 𝒢.G ⟶ 𝒩.G, (Over.pullback (jL L)).map f ≫ 𝒩.gen.hom = 𝒢.gen.hom :=
  ((GroupModel.isNeronModel_iff 𝒩).mp h𝒩).lift (P := fun Y => Smooth Y.hom)
    (show Smooth 𝒢.G.hom from inferInstance) 𝒢.gen.hom

/-- Two Néron models of `A_L` are isomorphic over `𝓞_L`, compatibly with `gen`. -/
theorem GroupModel.IsNeronModel.uniqueIso {𝒩 𝒩' : GroupModel A L} (h : 𝒩.IsNeronModel)
    (h' : 𝒩'.IsNeronModel) :
    ∃ φ : 𝒩.G ≅ 𝒩'.G, (Over.pullback (jL L)).map φ.hom ≫ 𝒩'.gen.hom = 𝒩.gen.hom :=
  ((GroupModel.isNeronModel_iff 𝒩).mp h).uniqueIso ((GroupModel.isNeronModel_iff 𝒩').mp h')
    (show Smooth 𝒩.G.hom from inferInstance) (show Smooth 𝒩'.G.hom from inferInstance)

end GroupModels

/-! ## Transport along isomorphisms, and the additivity direction `h(A) + h(B) ≤ h(A × B)` -/

section Transport

variable {S S' : Scheme.{0}} {j : S' ⟶ S} {P : Over S → Prop}

/-- The Néron property is invariant under isomorphisms of `N` and of `A`. -/
theorem NeronProp.of_iso {N N' : Over S} {A A' : Over S'} {e : (Over.pullback j).obj N ≅ A}
    (h : NeronProp j P N A e) (φ : N' ≅ N) (ψ : A ≅ A') (e' : (Over.pullback j).obj N' ≅ A')
    (he : (Over.pullback j).map φ.hom ≫ e.hom ≫ ψ.hom = e'.hom) : NeronProp j P N' A' e' := by
  intro Y hY
  have key : (fun f : Y ⟶ N' => (Over.pullback j).map f ≫ e'.hom) =
      (fun g => g ≫ ψ.hom) ∘ (fun f : Y ⟶ N => (Over.pullback j).map f ≫ e.hom) ∘
        (fun f => f ≫ φ.hom) := by
    funext f
    simp only [Function.comp, Functor.map_comp, Category.assoc, ← he]
  rw [key]
  refine Function.Bijective.comp ?_ ((h Y hY).comp ?_)
  · exact ⟨fun a b hab => (cancel_mono ψ.hom).mp hab, fun c => ⟨c ≫ ψ.inv, by simp⟩⟩
  · exact ⟨fun a b hab => (cancel_mono φ.hom).mp hab, fun c => ⟨c ≫ φ.inv, by simp⟩⟩

end Transport

section Additivity

open NumberField DefFaltings

variable {K : Type} [Field K]

/-- `C ≅ A × B` as abelian varieties: an isomorphism `C ≅ A ⊗ B` of `K`-schemes whose two
components are homomorphisms. (Mathlib v4.35 cannot form `A × B` as an `AbVar`: it lacks the
stability of geometric integrality under composition; so the product enters as `C`.) -/
def IsProductAbVar (C A B : AbVar K) : Prop :=
  ∃ e : C.X ≅ A.X ⊗ B.X, IsMonHom (e.hom ≫ fst A.X B.X) ∧ IsMonHom (e.hom ≫ snd A.X B.X)

/-- `C_L ≅ A_L ⊗ B_L`. -/
noncomputable def bcProd {A B C : AbVar K} (L : Type) [Field L] [Algebra K L]
    (eC : C.X ≅ A.X ⊗ B.X) : (C.baseChange L).X ≅ (A.baseChange L).X ⊗ (B.baseChange L).X :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso eC ≪≫
    prodComparisonIso (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))) A.X B.X

/-- `𝒢P ≅ 𝒢₁ × 𝒢₂` as group models of `C_L ≅ A_L × B_L`. -/
def IsProductModel {A B C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (eC : C.X ≅ A.X ⊗ B.X) (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) :
    Prop :=
  ∃ e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G, IsMonHom (e.hom ≫ fst _ _) ∧ IsMonHom (e.hom ≫ snd _ _) ∧
    (Over.pullback (jL L)).map e.hom ≫ (tensorGen 𝒢₁.gen 𝒢₂.gen).hom =
      𝒢P.gen.hom ≫ (bcProd L eC).hom

/-- **A product of Néron models is a Néron model** (for group models). -/
theorem isNeronModel_of_isProductModel {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
    [Algebra K L] {eC : C.X ≅ A.X ⊗ B.X} {𝒢P : GroupModel C L} {𝒩₁ : GroupModel A L}
    {𝒩₂ : GroupModel B L} (h₁ : 𝒩₁.IsNeronModel) (h₂ : 𝒩₂.IsNeronModel)
    (hP : IsProductModel eC 𝒢P 𝒩₁ 𝒩₂) : 𝒢P.IsNeronModel := by
  obtain ⟨e, -, -, he⟩ := hP
  rw [GroupModel.isNeronModel_iff] at h₁ h₂ ⊢
  refine (h₁.tensor h₂).of_iso e (bcProd L eC).symm 𝒢P.gen ?_
  rw [← Category.assoc, he]
  erw [Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]

/-- **Leaf N1 (Néron)**, as in `Reduction.lean` (BLR §1.4 Thm 3, UNVERIFIED locator). -/
def NeronModelExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L],
    ∃ 𝒩 : GroupModel A L, 𝒩.IsNeronModel

/-- **Glue P1.** Group models of `A_L` and `B_L` give a group model of `C_L ≅ A_L × B_L`
(the fibre product over `𝓞_L`; smooth, separated, quasi-compact; `GrpObj` of a product). -/
def ProductGroupModelExists : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X),
    IsMonHom (eC.hom ≫ fst A.X B.X) → IsMonHom (eC.hom ≫ snd A.X B.X) →
    ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] (𝒢₁ : GroupModel A L)
      (𝒢₂ : GroupModel B L), ∃ 𝒢P : GroupModel C L, IsProductModel eC 𝒢P 𝒢₁ 𝒢₂

/-- **Glue P2** (the direction used). The height of a product model is at least the sum of the
heights: `ω_{𝒢₁×𝒢₂} = ω_{𝒢₁} ⊕ ω_{𝒢₂}`, `det(ω₁ ⊕ ω₂) = det ω₁ ⊗ det ω₂`, the Arakelov degree is
additive, and a product of uniformizations is a uniformization of the product (equality holds). -/
def ProductModelHeight : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ → 𝒢₁.height + 𝒢₂.height ≤ 𝒢P.height

/-- **`h(A) + h(B) ≤ h(A × B)`** (rv-blueprints F1, the direction step E4 uses) from Néron
existence, Néron minimality and the two product glue statements. No semistable reduction is
needed: the comparison is made over each `L` separately. -/
theorem stableFaltingsHeight_add_le (hN1 : NeronModelExists) (hmin : NeronModelMinimal)
    (hP : ProductGroupModelExists) (hH : ProductModelHeight) (A B C : AbVar K)
    (hC : IsProductAbVar C A B) :
    stableFaltingsHeight A + stableFaltingsHeight B ≤ stableFaltingsHeight C := by
  obtain ⟨eC, h1, h2⟩ := hC
  rw [stableFaltingsHeight_eq_iInf_height C]
  refine le_iInf fun E => le_iInf fun 𝒢 => ?_
  obtain ⟨𝒩₁, hN₁⟩ := hN1 K A E.L
  obtain ⟨𝒩₂, hN₂⟩ := hN1 K B E.L
  obtain ⟨𝒢P, h𝒢P⟩ := hP K A B C eC h1 h2 E.L 𝒩₁ 𝒩₂
  have hA : stableFaltingsHeight A ≤ 𝒩₁.height := by
    rw [stableFaltingsHeight_eq_iInf_height]; exact iInf_le_of_le E (iInf_le_of_le 𝒩₁ le_rfl)
  have hB : stableFaltingsHeight B ≤ 𝒩₂.height := by
    rw [stableFaltingsHeight_eq_iInf_height]; exact iInf_le_of_le E (iInf_le_of_le 𝒩₂ le_rfl)
  calc stableFaltingsHeight A + stableFaltingsHeight B ≤ 𝒩₁.height + 𝒩₂.height :=
        add_le_add hA hB
    _ ≤ 𝒢P.height := hH K A B C eC E.L 𝒢P 𝒩₁ 𝒩₂ h𝒢P
    _ ≤ 𝒢.height :=
        hmin K C E.L 𝒢P 𝒢 (isNeronModel_of_isProductModel hN₁ hN₂ h𝒢P)

end Additivity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField MeasureTheory DefFaltings
open scoped TensorProduct

/-! ## Part E: the glue `ProductGroupModelExists`, proved; additivity from three hypotheses -/

section ProductProof

open scoped Obj

/-- `prodComparison` of a braided monoidal functor between cartesian categories is a monoid
morphism. -/
theorem isMonHom_prodComparisonIso {S S' : Scheme.{0}} (j : S' ⟶ S) (X Y : Over S) [GrpObj X]
    [GrpObj Y] :
    IsMonHom (prodComparisonIso (Over.pullback j) X Y).hom := by
  have h : (prodComparisonIso (Over.pullback j) X Y).hom =
      (Functor.Monoidal.μIso (Over.pullback j) X Y).inv := by
    rw [prodComparisonIso_hom, ← Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory]
    rfl
  have h0 : IsMonHom (Functor.Monoidal.μIso (Over.pullback j) X Y).hom :=
    (inferInstance : IsMonHom (Functor.LaxMonoidal.μ (Over.pullback j) X Y))
  rw [h]
  infer_instance

/-- **Glue P1, proved.** -/
theorem productGroupModelExists : ProductGroupModelExists := by
  unfold ProductGroupModelExists
  intro K _ A B C eC h1 h2 L _ _ _ 𝒢₁ 𝒢₂
  haveI : Smooth (𝒢₁.G ⊗ 𝒢₂.G).hom := by
    show Smooth (pullback.fst 𝒢₁.G.hom 𝒢₂.G.hom ≫ 𝒢₁.G.hom); infer_instance
  haveI : IsSeparated (𝒢₁.G ⊗ 𝒢₂.G).hom := by
    show IsSeparated (pullback.fst 𝒢₁.G.hom 𝒢₂.G.hom ≫ 𝒢₁.G.hom); infer_instance
  haveI : QuasiCompact (𝒢₁.G ⊗ 𝒢₂.G).hom := by
    show QuasiCompact (pullback.fst 𝒢₁.G.hom 𝒢₂.G.hom ≫ 𝒢₁.G.hom); infer_instance
  haveI : IsMonHom eC.hom := by
    have : eC.hom = lift (eC.hom ≫ fst A.X B.X) (eC.hom ≫ snd A.X B.X) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [this]; infer_instance
  let F := Over.pullback (jL L)
  let F' := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  let gen : genericFibre L (𝒢₁.G ⊗ 𝒢₂.G) ≅ (C.baseChange L).X :=
    tensorGen 𝒢₁.gen 𝒢₂.gen ≪≫ (bcProd L eC).symm
  have gen_hom : letI : GrpObj (genericFibre L (𝒢₁.G ⊗ 𝒢₂.G)) := Functor.grpObjObj
      IsMonHom gen.hom := by
    let g₁ : F.obj 𝒢₁.G ⟶ F'.obj A.X := 𝒢₁.gen.hom
    let g₂ : F.obj 𝒢₂.G ⟶ F'.obj B.X := 𝒢₂.gen.hom
    have g1 : IsMonHom g₁ := 𝒢₁.gen_hom
    have g2 : IsMonHom g₂ := 𝒢₂.gen_hom
    have p1 := isMonHom_prodComparisonIso (jL L) 𝒢₁.G 𝒢₂.G
    have p2 := isMonHom_prodComparisonIso (Spec.map (CommRingCat.ofHom (algebraMap K L))) A.X B.X
    have : IsMonHom ((prodComparisonIso F 𝒢₁.G 𝒢₂.G).hom ≫
        (g₁ ⊗ₘ g₂) ≫
        (prodComparisonIso F' A.X B.X).inv ≫ F'.map eC.inv) := inferInstance
    exact this
  refine ⟨⟨𝒢₁.G ⊗ 𝒢₂.G, gen, gen_hom⟩, Iso.refl _, ?_, ?_, ?_⟩
  · show IsMonHom (𝟙 _ ≫ fst _ _); infer_instance
  · show IsMonHom (𝟙 _ ≫ snd _ _); infer_instance
  · show F.map (𝟙 _) ≫ _ = (tensorGen 𝒢₁.gen 𝒢₂.gen ≪≫ (bcProd L eC).symm).hom ≫ _
    rw [F.map_id, Category.id_comp, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]


/-- **`h(A) + h(B) ≤ h(A × B)` from N1, `NeronModelMinimal` and `ProductModelHeight` only.** -/
theorem stableFaltingsHeight_add_le' (hN1 : NeronModelExists) (hmin : NeronModelMinimal)
    (hH : ProductModelHeight) {K : Type} [Field K] (A B C : AbVar K) (hC : IsProductAbVar C A B) :
    stableFaltingsHeight A + stableFaltingsHeight B ≤ stableFaltingsHeight C :=
  stableFaltingsHeight_add_le hN1 hmin productGroupModelExists hH A B C hC

end ProductProof

end ZInQ.H5Neron

/-! ## The leaf bundle field used: `LeafAdopt.H5` (copied verbatim from `Split.lean` l. 18755-18768;
it is the field `h5` of `HSyn.ResearchLeaves`) -/

namespace LeafAdopt

/-- **H5 (rv-blueprints F2): the stable Faltings height is the published one, as an explicit
leaf.** `StableHeightFinite` (over a number field, `stableFaltingsHeight A ∈ ℝ`) and
`NeronModelMinimal` (over each `L`, a group model with the Néron mapping property has the least
height). Each of R18-R22 is a consequence of its publication only together with H5
(rv-blueprints §1.2), and the direction `h(A) + h(Z) ≤ h(A × Z)` of additivity that E4 uses needs
Néron models and H5 (F1). *Published*: Faltings 1983 §1; Deligne, Sém. Bourbaki 616 (1983);
Bosch–Lütkebohmert–Raynaud, *Néron models* (1990) 1.2/1, 1.4/3; SGA 7 I, Exp. IX 3.3, 3.6
(locators UNVERIFIED). **Caveat**: `StableHeightFinite` holds for def-faltings' infimum only if
its index set is nonempty, which is what the open Props `AnalyticUniformizationExists` and
`HodgeLatticeTheorem` (with `AnalyticUniformizationUnique` for independence of the
uniformization) assert; they are true theorems (Mumford §1 with GAGA; smoothness of `𝒢`) but
unproved in Lean. So H5 as stated is "published theorem + correctness of the definition". -/
def H5 : Prop :=
  ZInQ.DefFaltings.StableHeightFinite ∧ ZInQ.DefFaltings.NeronModelMinimal

end LeafAdopt

noncomputable section

namespace HSyn

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.DefFaltings

/-! ### The piece, copied verbatim from `Split.lean` (l. 19461-19465 and 19553-19559) -/

/-- `P ≅ A × Z` as group schemes: homomorphisms `p₁ : P → A`, `p₂ : P → Z` with
`(p₁, p₂) : P → A × Z` an isomorphism. -/
def IsProductOf {K : Type} [Field K] (P A Z : Over (Spec (CommRingCat.of K))) [MonObj P]
    [MonObj A] [MonObj Z] : Prop :=
  ∃ (p₁ : P ⟶ A) (p₂ : P ⟶ Z), IsMonHom p₁ ∧ IsMonHom p₂ ∧ IsIso (lift p₁ p₂)

/-- **Missing piece 5 (glue E4, the additivity half that the transfer uses).**
`h_F(A) + h_F(Z) ≤ h_F(A × Z)` for abelian varieties over a number field (equality holds;
Faltings 1983 §1; needs Néron models and H5, rv-blueprints F1). -/
def HeightAdditivity : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (P A Z : ZInQ.DefFaltings.AbVar L),
    IsProductOf P.X A.X Z.X → ∀ a z p : ℝ, stableFaltingsHeight A = a →
      stableFaltingsHeight Z = z → stableFaltingsHeight P = p → a + z ≤ p

/-! ### g0-heightadd: the proof -/

/-- **Bridge (glue, proved).** g0-split's `IsProductOf` gives h5-neron's `IsProductAbVar`
(the isomorphism is `lift p₁ p₂`, whose components are `p₁`, `p₂`). -/
theorem isProductAbVar_of_isProductOf {K : Type} [Field K] {P A Z : ZInQ.DefFaltings.AbVar K}
    (h : IsProductOf P.X A.X Z.X) : H5Neron.IsProductAbVar P A Z := by
  obtain ⟨p₁, p₂, h₁, h₂, hI⟩ := h
  refine ⟨asIso (lift p₁ p₂), ?_, ?_⟩
  · rw [asIso_hom, lift_fst]; exact h₁
  · rw [asIso_hom, lift_snd]; exact h₂

/-- **`HeightAdditivity` from Néron existence (leaf N1), the bundle field `h5` and the product
height glue P2** (h5-neron's `stableFaltingsHeight_add_le'` plus the bridge and the passage from
`EReal` to `ℝ`). -/
theorem heightAdditivity_of (hN1 : H5Neron.NeronModelExists) (h5 : LeafAdopt.H5)
    (hH : H5Neron.ProductModelHeight) : HeightAdditivity := by
  intro L _ _ P A Z hP a z p ha hz hp
  have key := H5Neron.stableFaltingsHeight_add_le' hN1 h5.2 hH A Z P
    (isProductAbVar_of_isProductOf hP)
  rw [ha, hz, hp, ← EReal.coe_add, EReal.coe_le_coe_iff] at key
  exact key

end G0Split

end HSyn

end

/-! ## Glue P2 (`ProductModelHeight`) from four smaller Props

`ProductModelHeight` (h5-neron) compares, for a product model `𝒢P ≅ 𝒢₁ × 𝒢₂`, the heights of
the three group models (infima over metrizations). It follows from:
* `AnalyticUniformizationUnique` (def-faltings, already stated: the uniqueness half of AN3);
* `MetrizationDimUnique` (new glue): two metrizations of one group model have the same `g`;
* `MetrizationExists` (new glue): every group model has a metrization;
* `ProductMetrization` (new glue P2a): metrizations of `𝒢₁`, `𝒢₂` give one of `𝒢P` whose height
  is the sum (the construction direction; equality). -/

namespace ZInQ.G0HeightAdd

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings H5Neron

/-- **Glue P2a (product of metrized models).** If `𝒢P ≅ 𝒢₁ × 𝒢₂` (`IsProductModel`) and `M₁`, `M₂`
are metrizations of `𝒢₁`, `𝒢₂` of dimensions `g₁`, `g₂`, then `𝒢P` has a metrization of
dimension `g₁ + g₂` whose model height is the sum. Why true (STANDARD): the cotangent space at
the identity of `𝒢₁ ×_{𝓞_L} 𝒢₂` is `ω₁ ⊕ ω₂` (and `ω_{𝒢P} = ω_{𝒢₁} ⊕ ω_{𝒢₂}` as lattices),
`⋀^{g₁+g₂}(ω₁ ⊕ ω₂) = ⋀^{g₁}ω₁ ⊗ ⋀^{g₂}ω₂`, the product `Φ₁ × Φ₂ : ℂ^{g₁+g₂} → 𝒢₁(ℂ) × 𝒢₂(ℂ)`
is an analytic uniformization with kernel `Λ₁ × Λ₂` whose Jacobian determinant on product
wedges is the product, `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`, and the Arakelov degree of a
tensor product of Hermitian lines is the sum (Faltings 1983 §1; Deligne, Sém. Bourbaki 616, §1;
locators UNVERIFIED). Unproved: Mathlib has no computation of the stalk of a fibre product of
schemes. -/
def ProductMetrization : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ →
    ∀ (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂),
      M₁.model = 𝒢₁ → M₂.model = 𝒢₂ →
      ∃ MP : MetrizedModel C L (g₁ + g₂), MP.model = 𝒢P ∧
        MP.hodge.modelHeight = M₁.hodge.modelHeight + M₂.hodge.modelHeight

/-- **Glue (existence of metrizations; correctness of def-faltings' definition).** Every smooth
group model `𝒢` of `A_L` carries a metrization (of dimension `dim A`). Why true (STANDARD): the
Hodge data of `𝒢` exist by `HodgeLatticeTheorem` and the uniformization of each `𝒢(ℂ)_τ` by
`AnalyticUniformizationExists` (Mumford, *Abelian varieties* §1, UNVERIFIED), with the
coefficient map `coeff_τ(1 ⊗ df) = jacDet Φ f`. This is the same caveat as on `LeafAdopt.H5`
(the index set of the infimum is nonempty), for each model separately. Unproved. -/
def MetrizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L), ∃ (g : ℕ) (M : MetrizedModel A L g), M.model = 𝒢

/-- **Glue (the dimension of a metrization).** Two metrizations of the same group model have
the same dimension (both equal `dim A`: the `MetrizedModel` docstring's argument: for
`0 < g ≠ dim A` the Hodge space is not a line, and `g = 0` is excluded for `dim A ≥ 1` by the
surjectivity of `Φ : ℂ⁰ → A_τ(ℂ)`; STANDARD, unproved). -/
def MetrizationDimUnique : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (g g' : ℕ) (M : MetrizedModel A L g) (M' : MetrizedModel A L g'), M.model = M'.model → g = g'

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A metrization bounds the height of its model from above. -/
theorem height_le_of_model {g : ℕ} (M : MetrizedModel A L g) {𝒢 : GroupModel A L}
    (h : M.model = 𝒢) : 𝒢.height ≤ (M.hodge.modelHeight : EReal) :=
  iInf_le_of_le g (iInf_le_of_le M (iInf_le_of_le h le_rfl))

/-- Given AN3-uniqueness and `MetrizationDimUnique`, a metrization computes the height of its
model (from below; with `height_le_of_model`, equality). -/
theorem le_height_of_model (hU : AnalyticUniformizationUnique) (hD : MetrizationDimUnique)
    {g : ℕ} (M : MetrizedModel A L g) {𝒢 : GroupModel A L} (h : M.model = 𝒢) :
    (M.hodge.modelHeight : EReal) ≤ 𝒢.height := by
  refine le_iInf fun g' => le_iInf fun M' => le_iInf fun hM' => ?_
  obtain rfl := hD K A L g g' M M' (h.trans hM'.symm)
  rw [MetrizedModel.modelHeight_eq_of_model_eq hU M M' (h.trans hM'.symm)]

/-- **Glue P2 (`ProductModelHeight`) from `AnalyticUniformizationUnique`,
`MetrizationDimUnique`, `MetrizationExists` and `ProductMetrization`.** -/
theorem productModelHeight_of (hU : AnalyticUniformizationUnique) (hD : MetrizationDimUnique)
    (hE : MetrizationExists) (hP : ProductMetrization) : ProductModelHeight := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hPM
  obtain ⟨g₁, M₁, h₁⟩ := hE K A L 𝒢₁
  obtain ⟨g₂, M₂, h₂⟩ := hE K B L 𝒢₂
  obtain ⟨MP, hMP, hh⟩ := hP K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hPM g₁ g₂ M₁ M₂ h₁ h₂
  calc 𝒢₁.height + 𝒢₂.height
      ≤ (M₁.hodge.modelHeight : EReal) + (M₂.hodge.modelHeight : EReal) :=
        add_le_add (height_le_of_model M₁ h₁) (height_le_of_model M₂ h₂)
    _ = (MP.hodge.modelHeight : EReal) := by rw [hh, EReal.coe_add]
    _ ≤ 𝒢P.height := le_height_of_model hU hD MP hMP

end ZInQ.G0HeightAdd

namespace HSyn.G0Split

/-- **`HeightAdditivity` from one leaf (N1), the bundle field `h5`, the stated
`AnalyticUniformizationUnique`, and three glue Props.** -/
theorem heightAdditivity_of_split (hN1 : ZInQ.H5Neron.NeronModelExists) (h5 : LeafAdopt.H5)
    (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hD : ZInQ.G0HeightAdd.MetrizationDimUnique) (hE : ZInQ.G0HeightAdd.MetrizationExists)
    (hP : ZInQ.G0HeightAdd.ProductMetrization) : HeightAdditivity :=
  heightAdditivity_of hN1 h5 (ZInQ.G0HeightAdd.productModelHeight_of hU hD hE hP)

end HSyn.G0Split

#print axioms HSyn.G0Split.isProductAbVar_of_isProductOf
#print axioms HSyn.G0Split.heightAdditivity_of
#print axioms ZInQ.H5Neron.productGroupModelExists
#print axioms ZInQ.G0HeightAdd.productModelHeight_of
#print axioms HSyn.G0Split.heightAdditivity_of_split

/-! ## Consistency check in dimension 0 (the only abelian variety Mathlib v4.35 can construct)

`AbVar.zero` is copied from `ZInQKernel/HDecomp/Objects.lean` (`PkgI3.AbVar.zero`) for
def-faltings' copy of the structure; h5-neron's part B (`scratch/h5-neron/H5Neron.lean`
l. 245-559, the zero abelian variety: every metrization has dimension 0 and height 0) is copied
with `open PkgI3 (AbVar)` dropped. Then the three new glue Props are checked for `A = B = C = 0`. -/

namespace ZInQ.DefFaltings.AbVar

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory

/-- (copied from `PkgI3.AbVar.geometricallyIntegral_id_spec`) -/
instance geometricallyIntegral_id_spec (K : Type) [Field K] :
    GeometricallyIntegral (𝟙 (Spec (CommRingCat.of K))) := by
  constructor
  intro L _ y Z fst snd h
  have : IsIso snd := h.isIso_snd_of_isIso
  have : Nonempty Z := ⟨(inv snd) (IsLocalRing.closedPoint L)⟩
  exact isIntegral_of_isOpenImmersion snd

/-- (copied from `PkgI3.AbVar.zero`) The zero abelian variety `Spec K`. -/
noncomputable def zero (K : Type) [Field K] : AbVar K :=
  haveI : IsProper (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by dsimp; infer_instance
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by
    dsimp; infer_instance
  { X := 𝟙_ (Over (Spec (CommRingCat.of K))) }

end ZInQ.DefFaltings.AbVar

namespace ZInQ.H5Neron



open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField MeasureTheory DefFaltings
open scoped TensorProduct

/-- Maps into an object isomorphic to the unit are equal. -/
theorem hom_ext_of_iso_unit {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y : C}
    (i : X ≅ 𝟙_ C) (f g : Y ⟶ X) : f = g := by
  rw [← cancel_mono i.hom]; exact toUnit_unique _ _

section DimZero

variable {L : Type} [Field L] [NumberField L] {K : Type} [Field K] [Algebra K L] {A : AbVar K}

/-- `⋀^0 ω ≅ L`. -/
noncomputable def hodgeZeroEquiv (𝒢 : GroupModel A L) : 𝒢.hodgeSpace 0 ≃ₗ[L] L :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
      (exteriorPower.zeroEquiv (𝓞 L) 𝒢.cotangent) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid (𝓞 L) L L

/-- The empty wedge `1 ⊗ 1 ∈ ⋀^0`. -/
noncomputable def wedge0 (𝒢 : GroupModel A L) : 𝒢.hodgeSpace 0 :=
  (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) 0 (fun i : Fin 0 => (i.elim0 : 𝒢.cotangent))

theorem hodgeZeroEquiv_wedge0 (𝒢 : GroupModel A L) : hodgeZeroEquiv 𝒢 (wedge0 𝒢) = 1 := by
  simp [hodgeZeroEquiv, wedge0]

theorem wedge0_ne_zero (𝒢 : GroupModel A L) : wedge0 𝒢 ≠ 0 := by
  intro h
  have := congrArg (hodgeZeroEquiv 𝒢) h
  rw [hodgeZeroEquiv_wedge0, LinearEquiv.map_zero] at this
  exact one_ne_zero this

theorem wedge_eq_wedge0 (𝒢 : GroupModel A L) (f : Fin 0 → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.wedge f = wedge0 𝒢 := by
  unfold GroupModel.wedge wedge0
  congr 2
  funext i
  exact i.elim0

theorem detLattice_zero (𝒢 : GroupModel A L) :
    𝒢.detLattice 0 = Submodule.span (𝓞 L) {wedge0 𝒢} := by
  unfold GroupModel.detLattice
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, rfl⟩
    unfold wedge0
    congr 2
    funext i
    exact i.elim0
  · rintro rfl
    refine ⟨fun i => i.elim0, ?_⟩
    unfold wedge0
    congr 2
    funext i
    exact i.elim0

/-- The covolume of the (only) lattice in `ℂ⁰` is `1`. -/
theorem covolume_fin_zero (Λ : Submodule ℤ (Fin 0 → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ZLattice.covolume Λ = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume (F := Set.univ)
    (IsAddFundamentalDomain.mk' nullMeasurableSet_univ fun x =>
      ⟨0, Set.mem_univ _, fun y _ => Subsingleton.elim _ _⟩)]
  simp [Measure.real, volume_pi]

/-- **Every metrized model of dimension `0` has height `0`** (for every `A`). -/
theorem modelHeight_dim_zero (M : MetrizedModel A L 0) : M.hodge.modelHeight = 0 := by
  have hs : M.hodge.lattice = Submodule.span (𝓞 L) {wedge0 M.model} :=
    M.lattice_eq.trans (detLattice_zero _)
  rw [M.hodge.modelHeight_of_span hs (wedge0_ne_zero _)]
  have hc : ∀ τ, M.hodge.coeff τ (wedge0 M.model) = 1 := by
    intro τ
    obtain ⟨Φ, -, hΦ⟩ := M.arch τ
    have := hΦ (fun i => i.elim0)
    rw [wedge_eq_wedge0] at this
    rw [this]
    simp [GroupModel.jacDet]
  have hcov : ∀ τ, torusMetricSq (M.hodge.periods τ) 1 = 1 := by
    intro τ
    have := M.hodge.periods_discrete τ
    have := M.hodge.periods_isZLattice τ
    simp [torusMetricSq, covolume_fin_zero]
  simp [hc, hcov]

end DimZero

section ZeroAV

variable (K : Type) [Field K] (L : Type) [Field L] [NumberField L] [Algebra K L]

/-- `((Spec K)_L) ≅ 𝟙`. -/
noncomputable def bcUnitIso : ((AbVar.zero K).baseChange L).X ≅ 𝟙_ _ :=
  (Functor.Monoidal.εIso (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))).symm

/-- The trivial group model `Spec 𝓞_L` of `(Spec K)_L`. -/
noncomputable def trivModel : GroupModel (AbVar.zero K) L where
  G := 𝟙_ _
  smooth := by dsimp; infer_instance
  separated := by dsimp; infer_instance
  qc := by dsimp; infer_instance
  gen := (Functor.Monoidal.εIso (Over.pullback (jL L))).symm ≪≫ (bcUnitIso K L).symm
  gen_hom := by
    letI : GrpObj (genericFibre L (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L)))))) :=
      Functor.grpObjObj
    exact ⟨hom_ext_of_iso_unit (bcUnitIso K L) _ _, hom_ext_of_iso_unit (bcUnitIso K L) _ _⟩

/-- `Spec 𝓞_L` is a Néron model of `(Spec K)_L`. -/
theorem trivModel_isNeronModel : (trivModel K L).IsNeronModel := by
  intro Y _
  refine ⟨fun f g _ => toUnit_unique _ _, fun g => ⟨toUnit Y, hom_ext_of_iso_unit (bcUnitIso K L) _ _⟩⟩

/-- A group model of `(Spec K)_L` has exactly one complex point at each `τ`: `𝒢(ℂ)_τ` injects
into `(Spec K)_L(ℂ)_τ` (adjunction `Over.map ⊣ Over.pullback`), which is a point. -/
theorem pts_subsingleton (𝒢 : GroupModel (AbVar.zero K) L) (τ : L →+* ℂ) :
    Subsingleton (𝒢.Pts τ) := by
  constructor
  intro p q
  let P' : Over (Spec (CommRingCat.of L)) := Over.mk (Spec.map (CommRingCat.ofHom τ))
  let e : GroupModel.ptC τ ≅ (Over.map (jL L)).obj P' := Over.isoMk (Iso.refl _) (by
    simp only [GroupModel.ptC, P', jL, Over.map_obj_hom, Over.mk_hom, Iso.refl_hom,
      Category.id_comp, ← Spec.map_comp]
    rfl)
  let adj := Over.mapPullbackAdj (jL L)
  rw [← cancel_epi e.inv]
  apply (adj.homEquiv P' 𝒢.G).injective
  have := hom_ext_of_iso_unit (bcUnitIso K L) ((adj.homEquiv P' 𝒢.G) (e.inv ≫ p) ≫ 𝒢.gen.hom)
    ((adj.homEquiv P' 𝒢.G) (e.inv ≫ q) ≫ 𝒢.gen.hom)
  exact (cancel_mono 𝒢.gen.hom).mp this

/-- The zero abelian variety has no metrized model of dimension `g ≥ 1`: the kernel of a
uniformization `ℂ^g → 𝒢(ℂ)_τ = {pt}` would be all of `ℂ^g`, which is not discrete. -/
theorem no_metrized_succ (n : ℕ) (M : MetrizedModel (AbVar.zero K) L (n + 1)) : False := by
  haveI : Algebra.IsAlgebraic ℚ L := inferInstance
  let τ : L →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := L)).toRingHom
  obtain ⟨Φ, hΦ, -⟩ := M.arch τ
  have hall : ∀ z, z ∈ M.hodge.periods τ := fun z => by
    have := pts_subsingleton K L M.model τ
    exact (hΦ.2.1 z).mp (Subsingleton.elim _ _)
  have := M.hodge.periods_discrete τ
  obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.mp
    (isOpen_discrete ({⟨0, hall 0⟩} : Set (M.hodge.periods τ)))
  have h0 : (0 : Fin (n + 1) → ℂ) ∈ t := by
    have : (⟨0, hall 0⟩ : M.hodge.periods τ) ∈ Subtype.val ⁻¹' t := by
      rw [hpre]; exact Set.mem_singleton _
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ht 0 h0
  let y : Fin (n + 1) → ℂ := fun _ => ((ε / 2 : ℝ) : ℂ)
  have hy : y ∈ t := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, pi_norm_const, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  have : (⟨y, hall y⟩ : M.hodge.periods τ) ∈ ({⟨0, hall 0⟩} : Set (M.hodge.periods τ)) := by
    rw [← hpre]; exact hy
  have hy0 : y = 0 := congrArg Subtype.val (Set.mem_singleton_iff.mp this)
  have := congrFun hy0 0
  simp only [y, Pi.zero_apply, Complex.ofReal_eq_zero] at this
  linarith

/-- `τ` as a `τ`-semilinear map `L → ℂ`. -/
noncomputable def semσ (σ : L →+* ℂ) : L →ₛₗ[σ] ℂ where
  toFun := σ
  map_add' := map_add σ
  map_smul' a x := map_mul σ a x

/-- The Hodge data of a group model in dimension `0`. -/
noncomputable def trivHodge (𝒢 : GroupModel (AbVar.zero K) L) : HodgeData L 0 (𝒢.hodgeSpace 0) where
  lattice := 𝒢.detLattice 0
  finrank_eq_one := by rw [(hodgeZeroEquiv 𝒢).finrank_eq, Module.finrank_self]
  isLattice := ⟨wedge0 𝒢, by rw [detLattice_zero]; exact Submodule.mem_span_singleton_self _,
    wedge0_ne_zero 𝒢, by
      rw [detLattice_zero]; unfold secIndex; rw [AddSubgroup.relIndex_self]; norm_num⟩
  periods _ := ⊤
  periods_discrete _ := inferInstance
  periods_isZLattice _ := ⟨eq_top_iff.mpr fun x _ => by
    rw [Subsingleton.elim x 0]; exact zero_mem _⟩
  coeff σ := (semσ L σ).comp (hodgeZeroEquiv 𝒢).toLinearMap
  coeff_ne_zero σ h := by
    have := LinearMap.congr_fun h (wedge0 𝒢)
    simp [semσ, hodgeZeroEquiv_wedge0] at this

/-- The metrized trivial model. -/
noncomputable def trivMetrized : MetrizedModel (AbVar.zero K) L 0 where
  model := trivModel K L
  hodge := trivHodge K L (trivModel K L)
  lattice_eq := rfl
  arch τ := ⟨fun _ => toUnit _,
    ⟨fun _ _ => toUnit_unique _ _, fun z => ⟨fun _ => Submodule.mem_top, fun _ => toUnit_unique _ _⟩,
      fun p => ⟨0, toUnit_unique _ _⟩,
      fun U => by
        rcases Set.eq_empty_or_nonempty ((trivModel K L).dom (fun _ => toUnit _) U) with h | ⟨x, hx⟩
        · rw [h]; exact isOpen_empty
        · have : (trivModel K L).dom (fun _ => toUnit _) U = Set.univ :=
            Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
          rw [this]; exact isOpen_univ,
      fun U s => differentiableOn_const _⟩,
    fun f => by
      show semσ L τ (hodgeZeroEquiv _ ((trivModel K L).wedge f)) = _
      rw [wedge_eq_wedge0, hodgeZeroEquiv_wedge0]
      simp [semσ, GroupModel.jacDet]⟩

/-- **The stable Faltings height of the zero abelian variety is `0`.** -/
theorem stableFaltingsHeight_zero [NumberField K] : stableFaltingsHeight (AbVar.zero K) = 0 := by
  refine le_antisymm ?_ ?_
  · have := stableFaltingsHeight_le (AbVar.zero K) (trivMetrized K K)
    rwa [modelHeight_dim_zero, EReal.coe_zero] at this
  · refine le_stableFaltingsHeight _ fun E g M => ?_
    cases g with
    | zero => rw [modelHeight_dim_zero, EReal.coe_zero]
    | succ n => exact (no_metrized_succ K E.L n M).elim

/-- Every group model of `(Spec K)_L` has a metrized model of dimension `0`. -/
noncomputable def metrizedOf (𝒢 : GroupModel (AbVar.zero K) L) :
    MetrizedModel (AbVar.zero K) L 0 where
  model := 𝒢
  hodge := trivHodge K L 𝒢
  lattice_eq := rfl
  arch τ := by
    have hs := pts_subsingleton K L 𝒢 τ
    refine ⟨fun _ => 1, ⟨fun _ _ => Subsingleton.elim _ _,
      fun z => ⟨fun _ => Submodule.mem_top, fun _ => rfl⟩,
      fun p => ⟨0, Subsingleton.elim _ _⟩, fun U => ?_, fun U s => differentiableOn_const _⟩,
      fun f => ?_⟩
    · rcases Set.eq_empty_or_nonempty (𝒢.dom (fun _ => (1 : 𝒢.Pts τ)) U) with h | ⟨x, hx⟩
      · rw [h]; exact isOpen_empty
      · have : 𝒢.dom (fun _ => (1 : 𝒢.Pts τ)) U = Set.univ :=
          Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
        rw [this]; exact isOpen_univ
    · show semσ L τ (hodgeZeroEquiv _ (𝒢.wedge f)) = _
      rw [wedge_eq_wedge0, hodgeZeroEquiv_wedge0]
      simp [semσ, GroupModel.jacDet]

/-- **Every group model of the zero abelian variety has height `0`.** -/
theorem groupModel_height_zero (𝒢 : GroupModel (AbVar.zero K) L) : 𝒢.height = 0 := by
  refine le_antisymm ?_ ?_
  · refine iInf_le_of_le 0 (iInf_le_of_le (metrizedOf K L 𝒢) (iInf_le_of_le rfl ?_))
    rw [modelHeight_dim_zero, EReal.coe_zero]
  · refine le_iInf fun g => le_iInf fun M => le_iInf fun _ => ?_
    cases g with
    | zero => rw [modelHeight_dim_zero, EReal.coe_zero]
    | succ n => exact (no_metrized_succ K L n M).elim

/-- **`NeronModelMinimal` holds for the zero abelian variety.** -/
theorem neronModelMinimal_zero (𝒩 𝒢 : GroupModel (AbVar.zero K) L) (_ : 𝒩.IsNeronModel) :
    𝒩.height ≤ 𝒢.height := by
  rw [groupModel_height_zero, groupModel_height_zero]

/-- **`StableHeightFinite` holds for the zero abelian variety.** -/
theorem stableHeightFinite_zero [NumberField K] :
    stableFaltingsHeight (AbVar.zero K) ≠ ⊤ ∧ stableFaltingsHeight (AbVar.zero K) ≠ ⊥ := by
  rw [stableFaltingsHeight_zero]; exact ⟨EReal.zero_ne_top, EReal.zero_ne_bot⟩

/-- The identity of `Spec K` is an isogeny (so the hypothesis of R19 is satisfiable). -/
theorem isIsogeny_id_zero : IsIsogeny (𝟙 (AbVar.zero K).X) :=
  ⟨inferInstance, by rw [Over.id_left]; infer_instance, by rw [Over.id_left]; infer_instance⟩

/-- Every endomorphism of the zero abelian variety has degree `≤ 1`. -/
theorem isogDeg_zero_le_one (φ : (AbVar.zero K).X ⟶ (AbVar.zero K).X) : isogDeg φ ≤ 1 := by
  unfold isogDeg
  have : Subsingleton {P : ptObj K (AlgebraicClosure K) ⟶ (AbVar.zero K).X // P ≫ φ = 1} :=
    ⟨fun a b => Subtype.ext (toUnit_unique _ _)⟩
  rcases isEmpty_or_nonempty {P : ptObj K (AlgebraicClosure K) ⟶ (AbVar.zero K).X // P ≫ φ = 1}
    with h | h
  · rw [Nat.card_of_isEmpty]; exact zero_le_one
  · rw [Nat.card_of_subsingleton h.some]

/-- **R21 for the zero abelian variety** (for every `g`, not only `g = dim`). -/
theorem R21_zero [NumberField K] (g : ℕ) :
    ((-(3 / 2) * g : ℝ) : EReal) ≤ stableFaltingsHeight (AbVar.zero K) := by
  rw [stableFaltingsHeight_zero]
  exact_mod_cast (by nlinarith [(Nat.cast_nonneg g : (0 : ℝ) ≤ g)] : -(3 / 2) * (g : ℝ) ≤ 0)

/-- **R20 for the zero abelian variety.** -/
theorem R20_zero [NumberField K] (φ : (AbVar.zero K).X ⟶ (AbVar.zero K).X) (x y : ℝ)
    (hx : stableFaltingsHeight (AbVar.zero K) = x) (hy : stableFaltingsHeight (AbVar.zero K) = y) :
    |x - y| ≤ (1 / 2) * Real.log (isogDeg φ) := by
  rw [stableFaltingsHeight_zero] at hx hy
  have hx' : x = 0 := by exact_mod_cast hx.symm
  have hy' : y = 0 := by exact_mod_cast hy.symm
  rw [hx', hy', sub_zero, abs_zero]
  have := Real.log_natCast_nonneg (isogDeg φ)
  linarith

theorem one_le_grKappa (g d : ℕ) (hd : 1 ≤ d) (x : ℝ) : 1 ≤ grKappa g d x := by
  unfold grKappa
  apply one_le_pow₀
  have hm : 1 ≤ (max (max x (Real.log d)) 1) ^ 2 := one_le_pow₀ (le_max_right _ _)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h14 : (1 : ℝ) ≤ (14 * g : ℝ) ^ (64 * g ^ 2) := by
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · simp
    · apply one_le_pow₀
      have : (1 : ℝ) ≤ g := by exact_mod_cast hg
      linarith
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr

/-- **R19 for the zero abelian variety** (for every `g`). -/
theorem R19_zero [NumberField K] (g : ℕ) (x : ℝ) (_ : stableFaltingsHeight (AbVar.zero K) = x)
    (h : ∃ φ : (AbVar.zero K).X ⟶ (AbVar.zero K).X, IsIsogeny φ) :
    (∃ φ : (AbVar.zero K).X ⟶ (AbVar.zero K).X, IsIsogeny φ ∧
        (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
      (∃ ψ : (AbVar.zero K).X ⟶ (AbVar.zero K).X, IsIsogeny ψ ∧
        (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) := by
  obtain ⟨φ, hφ⟩ := h
  have hb : (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x :=
    le_trans (by exact_mod_cast isogDeg_zero_le_one K φ)
      (one_le_grKappa g _ Module.finrank_pos x)
  exact ⟨⟨φ, hφ, hb⟩, ⟨φ, hφ, hb⟩⟩

end ZeroAV

end ZInQ.H5Neron

namespace ZInQ.G0HeightAdd

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings H5Neron

variable (K : Type) [Field K] (L : Type) [Field L] [NumberField L] [Algebra K L]

/-- `MetrizationExists` holds for the zero abelian variety. -/
theorem metrizationExists_zero (𝒢 : GroupModel (AbVar.zero K) L) :
    ∃ (g : ℕ) (M : MetrizedModel (AbVar.zero K) L g), M.model = 𝒢 :=
  ⟨0, metrizedOf K L 𝒢, rfl⟩

/-- `MetrizationDimUnique` holds for the zero abelian variety. -/
theorem metrizationDimUnique_zero (g g' : ℕ) (M : MetrizedModel (AbVar.zero K) L g)
    (M' : MetrizedModel (AbVar.zero K) L g') : g = g' := by
  cases g with
  | succ n => exact (no_metrized_succ K L n M).elim
  | zero =>
    cases g' with
    | zero => rfl
    | succ n => exact (no_metrized_succ K L n M').elim

/-- `ProductMetrization` holds for `A = B = C = 0` (with every hypothesis allowed). -/
theorem productMetrization_zero (eC : (AbVar.zero K).X ≅ (AbVar.zero K).X ⊗ (AbVar.zero K).X)
    (𝒢P 𝒢₁ 𝒢₂ : GroupModel (AbVar.zero K) L) (_ : IsProductModel eC 𝒢P 𝒢₁ 𝒢₂) (g₁ g₂ : ℕ)
    (M₁ : MetrizedModel (AbVar.zero K) L g₁) (M₂ : MetrizedModel (AbVar.zero K) L g₂)
    (_ : M₁.model = 𝒢₁) (_ : M₂.model = 𝒢₂) :
    ∃ MP : MetrizedModel (AbVar.zero K) L (g₁ + g₂), MP.model = 𝒢P ∧
      MP.hodge.modelHeight = M₁.hodge.modelHeight + M₂.hodge.modelHeight := by
  cases g₁ with
  | succ n => exact (no_metrized_succ K L n M₁).elim
  | zero =>
    cases g₂ with
    | succ n => exact (no_metrized_succ K L n M₂).elim
    | zero =>
      refine ⟨metrizedOf K L 𝒢P, rfl, ?_⟩
      rw [modelHeight_dim_zero, modelHeight_dim_zero, modelHeight_dim_zero, add_zero]

end ZInQ.G0HeightAdd

#print axioms ZInQ.G0HeightAdd.metrizationExists_zero
#print axioms ZInQ.G0HeightAdd.metrizationDimUnique_zero
#print axioms ZInQ.G0HeightAdd.productMetrization_zero

/-! ## P2a split: the Arakelov-degree half proved

`ProductMetrization` (P2a) = a geometric construction (`ProductMetrizationGeo`: the product
metrization with a product section `η = η₁ ∧ η₂` for which the index, the coefficients and the
covolumes are multiplicative) + the height computation (`modelHeight_add_of`, proved). -/

namespace ZInQ.G0HeightAdd

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField MeasureTheory DefFaltings H5Neron

section HodgeAdd

variable {K : Type*} [Field K] [NumberField K]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V₁] [Module K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁]
  [AddCommGroup V₂] [Module K V₂] [Module (𝓞 K) V₂] [IsScalarTower (𝓞 K) K V₂]

/-- **Additivity of the model height (proved).** If the Hodge data `D` (dimension `g₁ + g₂`)
has a nonzero section `s` whose lattice index, coefficients and period covolumes are the
products of those of nonzero sections `s₁`, `s₂` of `D₁`, `D₂`, then
`h(D) = h(D₁) + h(D₂)` (Faltings' formula `HodgeData.modelHeight_eq` and `log` of products). -/
theorem modelHeight_add_of {g₁ g₂ : ℕ} (D : HodgeData K (g₁ + g₂) V) (D₁ : HodgeData K g₁ V₁)
    (D₂ : HodgeData K g₂ V₂) {s : V} {s₁ : V₁} {s₂ : V₂} (hs : s ∈ D.lattice) (hs0 : s ≠ 0)
    (hs₁ : s₁ ∈ D₁.lattice) (hs₁0 : s₁ ≠ 0) (hs₂ : s₂ ∈ D₂.lattice) (hs₂0 : s₂ ≠ 0)
    (hidx : secIndex D.lattice s = secIndex D₁.lattice s₁ * secIndex D₂.lattice s₂)
    (hcoeff : ∀ σ, D.coeff σ s = D₁.coeff σ s₁ * D₂.coeff σ s₂)
    (hcov : ∀ σ, ZLattice.covolume (D.periods σ) =
      ZLattice.covolume (D₁.periods σ) * ZLattice.covolume (D₂.periods σ)) :
    D.modelHeight = D₁.modelHeight + D₂.modelHeight := by
  rw [D.modelHeight_eq hs hs0, D₁.modelHeight_eq hs₁ hs₁0, D₂.modelHeight_eq hs₂ hs₂0]
  have ht : ∀ σ : K →+* ℂ, torusMetricSq (D.periods σ) (D.coeff σ s) =
      torusMetricSq (D₁.periods σ) (D₁.coeff σ s₁) *
        torusMetricSq (D₂.periods σ) (D₂.coeff σ s₂) := by
    intro σ
    simp only [torusMetricSq, hcoeff σ, hcov σ, norm_mul]
    ring
  have hlog : ∀ σ : K →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ s)) =
      Real.log (torusMetricSq (D₁.periods σ) (D₁.coeff σ s₁)) +
        Real.log (torusMetricSq (D₂.periods σ) (D₂.coeff σ s₂)) := by
    intro σ
    rw [ht σ]
    have := D₁.periods_discrete σ
    have := D₁.periods_isZLattice σ
    have := D₂.periods_discrete σ
    have := D₂.periods_isZLattice σ
    exact Real.log_mul (torusMetricSq_pos _ (D₁.coeff_apply_ne_zero σ hs₁0)).ne'
      (torusMetricSq_pos _ (D₂.coeff_apply_ne_zero σ hs₂0)).ne'
  have hi₁ : (secIndex D₁.lattice s₁ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D₁.hodgeBundle.secIndex_ne_zero hs₁ hs₁0)
  have hi₂ : (secIndex D₂.lattice s₂ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D₂.hodgeBundle.secIndex_ne_zero hs₂ hs₂0)
  rw [hidx, Nat.cast_mul, Real.log_mul hi₁ hi₂, Finset.sum_congr rfl (fun σ _ => hlog σ),
    Finset.sum_add_distrib]
  ring

end HodgeAdd

/-- **Glue P2a-geo (the product metrization, geometric half of P2a).** For `𝒢P ≅ 𝒢₁ × 𝒢₂` and
metrizations `M₁`, `M₂`, there is a metrization `MP` of `𝒢P` of dimension `g₁ + g₂` and nonzero
sections `s ∈ ⋀^{g₁+g₂}ω_{𝒢P}`, `sᵢ ∈ ⋀^{gᵢ}ω_{𝒢ᵢ}` such that the lattice index, the coefficients
and the period covolumes of `s` are the products of those of `s₁`, `s₂`. Why true (STANDARD):
take `s = p₁*s₁ ∧ p₂*s₂`; `ω_{𝒢P} = ω_{𝒢₁} ⊕ ω_{𝒢₂}` gives `⋀^{top}ω_{𝒢P} = ⋀ω_{𝒢₁} ⊗ ⋀ω_{𝒢₂}`, and
for invertible `𝓞_L`-modules the index of `𝓞s₁ ⊗ 𝓞s₂` is the product (norms of ideals are
multiplicative); `Φ₁ × Φ₂` (coordinates `Fin.append`) is an analytic uniformization of
`𝒢P(ℂ)_τ = 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` with period lattice `Λ₁ × Λ₂`, block-diagonal Jacobian
(so `jacDet` multiplies), and `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`. Unproved (stalks of fibre
products of schemes are not in Mathlib). -/
def ProductMetrizationGeo : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ →
    ∀ (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂),
      M₁.model = 𝒢₁ → M₂.model = 𝒢₂ →
      ∃ (MP : MetrizedModel C L (g₁ + g₂)) (s : MP.model.hodgeSpace (g₁ + g₂))
        (s₁ : M₁.model.hodgeSpace g₁) (s₂ : M₂.model.hodgeSpace g₂),
        MP.model = 𝒢P ∧ s ∈ MP.hodge.lattice ∧ s ≠ 0 ∧ s₁ ∈ M₁.hodge.lattice ∧ s₁ ≠ 0 ∧
        s₂ ∈ M₂.hodge.lattice ∧ s₂ ≠ 0 ∧
        secIndex MP.hodge.lattice s = secIndex M₁.hodge.lattice s₁ * secIndex M₂.hodge.lattice s₂ ∧
        (∀ σ, MP.hodge.coeff σ s = M₁.hodge.coeff σ s₁ * M₂.hodge.coeff σ s₂) ∧
        (∀ σ, ZLattice.covolume (MP.hodge.periods σ) =
          ZLattice.covolume (M₁.hodge.periods σ) * ZLattice.covolume (M₂.hodge.periods σ))

/-- **P2a from P2a-geo (proved).** -/
theorem productMetrization_of_geo (h : ProductMetrizationGeo) : ProductMetrization := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hP g₁ g₂ M₁ M₂ h₁ h₂
  obtain ⟨MP, s, s₁, s₂, hMP, hs, hs0, hs₁, hs₁0, hs₂, hs₂0, hidx, hc, hcov⟩ :=
    h K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hP g₁ g₂ M₁ M₂ h₁ h₂
  exact ⟨MP, hMP, modelHeight_add_of MP.hodge M₁.hodge M₂.hodge hs hs0 hs₁ hs₁0 hs₂ hs₂0 hidx hc hcov⟩

end ZInQ.G0HeightAdd

namespace HSyn.G0Split

/-- **`HeightAdditivity` from N1, `r.h5`, U and three glue Props, with P2a reduced to its
geometric half.** -/
theorem heightAdditivity_of_geo (hN1 : ZInQ.H5Neron.NeronModelExists) (h5 : LeafAdopt.H5)
    (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hD : ZInQ.G0HeightAdd.MetrizationDimUnique) (hE : ZInQ.G0HeightAdd.MetrizationExists)
    (hG : ZInQ.G0HeightAdd.ProductMetrizationGeo) : HeightAdditivity :=
  heightAdditivity_of_split hN1 h5 hU hD hE (ZInQ.G0HeightAdd.productMetrization_of_geo hG)

end HSyn.G0Split

#print axioms ZInQ.G0HeightAdd.modelHeight_add_of
#print axioms ZInQ.G0HeightAdd.productMetrization_of_geo
#print axioms HSyn.G0Split.heightAdditivity_of_geo

/-!
# metrization: the degree of a Hodge line is unique (pure algebra)

For a flat `R`-algebra `F` that is a field and any `R`-module `C`: if `F ⊗_R ⋀^g_R C` and
`F ⊗_R ⋀^{g'}_R C` are both `F`-lines and `0 < g`, `0 < g'`, then `g = g'`.
(Applied with `R = 𝓞_L`, `F = L`, `C = 𝔪_ξ/𝔪_ξ²`: `hodgeSpace g` determines `g ≥ 1`.)
-/

open scoped TensorProduct

namespace ZInQ.Metrization

variable {R F C : Type*} [CommRing R] [Field F] [Algebra R F] [AddCommGroup C] [Module R C]

/-- If `F ⊗ ⋀^n C ≠ 0` (positive finrank) some `1 ⊗ v₁ ∧ ⋯ ∧ vₙ` is nonzero. -/
theorem exists_one_tmul_ιMulti_ne_zero (n : ℕ)
    (h : Module.finrank F (F ⊗[R] ⋀[R]^n C) ≠ 0) :
    ∃ v : Fin n → C, (1 : F) ⊗ₜ[R] exteriorPower.ιMulti R n v ≠ 0 := by
  by_contra! hv
  apply h
  have hall : ∀ x : F ⊗[R] ⋀[R]^n C, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul a m =>
      have hm : m ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
        rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, rfl⟩ := hx
        rw [show a ⊗ₜ[R] exteriorPower.ιMulti R n v =
          a • ((1 : F) ⊗ₜ[R] exteriorPower.ιMulti R n v) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], hv v, smul_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, hx, hy, add_zero]
      | smul r x _ hx => rw [TensorProduct.tmul_smul, hx, smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  haveI : Subsingleton (F ⊗[R] ⋀[R]^n C) := ⟨fun a b => (hall a).trans (hall b).symm⟩
  exact Module.finrank_zero_of_subsingleton

/-- The core: `F ⊗ ⋀^g C` and `F ⊗ ⋀^{g+n} C` cannot both be lines when `g, n ≥ 1`. -/
theorem not_finrank_one_of_add [Module.Flat R F] {g n : ℕ} (hg : 0 < g) (hn : 0 < n)
    (h : Module.finrank F (F ⊗[R] ⋀[R]^g C) = 1)
    (h' : Module.finrank F (F ⊗[R] ⋀[R]^(g + n) C) = 1) : False := by
  obtain ⟨v, hv⟩ := exists_one_tmul_ιMulti_ne_zero (R := R) (F := F) (C := C) (g + n)
    (by rw [h']; exact one_ne_zero)
  -- `Z = 1 ⊗ ιMulti v ≠ 0` in `F ⊗ ⋀ C` (flatness)
  let ι' : ⋀[R]^(g + n) C →ₗ[R] ExteriorAlgebra R C := (⋀[R]^(g + n) C).subtype
  have hinj : Function.Injective (ι'.lTensor F) :=
    Module.Flat.lTensor_preserves_injective_linearMap ι' Subtype.val_injective
  have hZ : (1 : F) ⊗ₜ[R] ExteriorAlgebra.ιMulti R (g + n) v ≠ 0 := by
    intro h0
    apply hv
    apply hinj
    rw [LinearMap.lTensor_tmul, map_zero]
    exact h0
  let a : Fin g → C := fun i => v (Fin.castAdd n i)
  let b : Fin n → C := fun j => v (Fin.natAdd g j)
  have hab : Fin.append a b = v := Fin.append_castAdd_natAdd
  let i0 : Fin g := ⟨0, hg⟩
  let j0 : Fin n := ⟨0, hn⟩
  let a' : Fin g → C := Function.update a i0 (b j0)
  let b' : Fin n → C := Function.update b j0 (a i0)
  have hp : (Fin.castAdd n i0 : Fin (g + n)) ≠ Fin.natAdd g j0 := by
    intro hc
    have := congrArg Fin.val hc
    simp [i0, j0] at this
    omega
  -- the four products
  have h1 : ExteriorAlgebra.ιMulti R (g + n) (Fin.append a' b) = 0 := by
    apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
    intro hi
    apply hp
    apply hi
    simp [a', Fin.append_left, Fin.append_right]
  have h2 : ExteriorAlgebra.ιMulti R (g + n) (Fin.append a b') = 0 := by
    apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
    intro hi
    apply hp
    apply hi
    simp [b', Fin.append_left, Fin.append_right]
  have hswap : Fin.append a' b' = v ∘ Equiv.swap (Fin.castAdd n i0) (Fin.natAdd g j0) := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left, Function.comp_apply]
      by_cases hi : i = i0
      · subst hi
        rw [Equiv.swap_apply_left]
        simp [a', b]
      · rw [Equiv.swap_apply_of_ne_of_ne]
        · simp [a', hi, a]
        · exact fun hc => hi (Fin.castAdd_injective _ _ hc)
        · intro hc
          have := congrArg Fin.val hc
          simp at this
          omega
    · rw [Fin.append_right, Function.comp_apply]
      by_cases hj : j = j0
      · subst hj
        rw [Equiv.swap_apply_right]
        simp [b', a]
      · rw [Equiv.swap_apply_of_ne_of_ne]
        · simp [b', hj, b]
        · intro hc
          have := congrArg Fin.val hc
          simp at this
          omega
        · exact fun hc => hj (Fin.natAdd_injective _ _ hc)
  have h3 : ExteriorAlgebra.ιMulti R (g + n) (Fin.append a' b') =
      -ExteriorAlgebra.ιMulti R (g + n) v := by
    rw [hswap]
    exact (ExteriorAlgebra.ιMulti R (g + n)).map_swap v hp
  -- the two wedge maps, base changed
  let Φ := (LinearMap.mulRight R (ExteriorAlgebra.ιMulti R n b) ∘ₗ (⋀[R]^g C).subtype).baseChange F
  let Ψ := (LinearMap.mulRight R (ExteriorAlgebra.ιMulti R n b') ∘ₗ (⋀[R]^g C).subtype).baseChange F
  set XS : F ⊗[R] ⋀[R]^g C := (1 : F) ⊗ₜ[R] exteriorPower.ιMulti R g a
  set XT : F ⊗[R] ⋀[R]^g C := (1 : F) ⊗ₜ[R] exteriorPower.ιMulti R g a'
  have hΦS : Φ XS = (1 : F) ⊗ₜ[R] ExteriorAlgebra.ιMulti R (g + n) v := by
    simp only [Φ, XS, LinearMap.baseChange_tmul, LinearMap.comp_apply, Submodule.subtype_apply,
      exteriorPower.ιMulti_apply_coe, LinearMap.mulRight_apply, ExteriorAlgebra.ιMulti_mul_ιMulti,
      hab]
  have hΨS : Ψ XS = 0 := by
    simp only [Ψ, XS, LinearMap.baseChange_tmul, LinearMap.comp_apply, Submodule.subtype_apply,
      exteriorPower.ιMulti_apply_coe, LinearMap.mulRight_apply, ExteriorAlgebra.ιMulti_mul_ιMulti,
      h2, TensorProduct.tmul_zero]
  have hΨT : Ψ XT = -((1 : F) ⊗ₜ[R] ExteriorAlgebra.ιMulti R (g + n) v) := by
    simp only [Ψ, XT, LinearMap.baseChange_tmul, LinearMap.comp_apply, Submodule.subtype_apply,
      exteriorPower.ιMulti_apply_coe, LinearMap.mulRight_apply, ExteriorAlgebra.ιMulti_mul_ιMulti,
      h3, TensorProduct.tmul_neg]
  have hXS : XS ≠ 0 := by
    intro h0
    apply hZ
    rw [← hΦS, h0, map_zero]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' XS hXS).mp h XT
  apply hZ
  have : Ψ XT = 0 := by rw [← hc, map_smul, hΨS, smul_zero]
  rw [hΨT, neg_eq_zero] at this
  exact this

/-- **The degree of a Hodge line is unique.** -/
theorem eq_of_finrank_one [Module.Flat R F] {g g' : ℕ} (hg : 0 < g) (hg' : 0 < g')
    (h : Module.finrank F (F ⊗[R] ⋀[R]^g C) = 1)
    (h' : Module.finrank F (F ⊗[R] ⋀[R]^g' C) = 1) : g = g' := by
  rcases lt_trichotomy g g' with hlt | heq | hgt
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact (not_finrank_one_of_add hg (Nat.succ_pos n) h h').elim
  · exact heq
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    exact (not_finrank_one_of_add hg' (Nat.succ_pos n) h' h).elim

end ZInQ.Metrization


/-! ## metrization (2026-11-13): `MetrizationDimUnique`, proved -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- A discrete `ℤ`-submodule of `ℂ^g`, `g ≥ 1`, is not all of `ℂ^g`. -/
theorem exists_not_mem_of_discrete {g : ℕ} (hg : 0 < g) (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ] : ∃ z, z ∉ Λ := by
  by_contra! hall
  let e : Fin g → ℂ := Pi.single ⟨0, hg⟩ 1
  let f : ℝ → Λ := fun t => ⟨(t : ℂ) • e, hall _⟩
  have hf : Continuous f :=
    Continuous.subtype_mk (Complex.continuous_ofReal.smul continuous_const) _
  have h1 := PreconnectedSpace.constant inferInstance hf (x := 0) (y := 1)
  have h2 := congrArg (fun x : Λ => (x : Fin g → ℂ) ⟨0, hg⟩) h1
  simp [f, e] at h2

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A metrization of dimension `g ≥ 1` has a nontrivial complex point at every `τ`. -/
theorem metrized_exists_pts_ne_one {g : ℕ} (hg : 0 < g) (M : MetrizedModel A L g)
    (τ : L →+* ℂ) : ∃ p : M.model.Pts τ, p ≠ 1 := by
  obtain ⟨Φ, hΦ, -⟩ := M.arch τ
  haveI := M.hodge.periods_discrete τ
  obtain ⟨z, hz⟩ := exists_not_mem_of_discrete hg (M.hodge.periods τ)
  exact ⟨Φ z, fun h => hz ((hΦ.2.1 z).mp h)⟩

/-- A metrization of dimension `0` forces `𝒢(ℂ)_τ` to be trivial (`Φ : ℂ⁰ → 𝒢(ℂ)_τ` is onto). -/
theorem metrized_pts_subsingleton (M : MetrizedModel A L 0) (τ : L →+* ℂ) :
    Subsingleton (M.model.Pts τ) := by
  obtain ⟨Φ, hΦ, -⟩ := M.arch τ
  refine ⟨fun p q => ?_⟩
  obtain ⟨z, rfl⟩ := hΦ.2.2.1 p
  obtain ⟨w, rfl⟩ := hΦ.2.2.1 q
  rw [Subsingleton.elim z w]

/-- **`MetrizationDimUnique`, proved.** Two metrizations of one group model have the same
dimension. For `g, g' ≥ 1`: `hodgeSpace g = L ⊗ ⋀^g C` is a line for at most one `g ≥ 1`
(`eq_of_finrank_one`, `L` flat over `𝓞_L`). For `g = 0 < g'`: the dimension-`0` uniformization
makes `𝒢(ℂ)_τ` trivial, the dimension-`g'` one (discrete kernel) makes it nontrivial. -/
theorem metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique := by
  intro K _ A L _ _ _ g g' M M' h
  obtain ⟨τ⟩ := (inferInstance : Nonempty (L →+* ℂ))
  have key : ∀ {g g' : ℕ} (M : MetrizedModel A L g) (M' : MetrizedModel A L g'),
      M.model = M'.model → g = 0 → g' = 0 := by
    intro g g' M M' h hg0
    subst hg0
    by_contra hg'
    obtain ⟨p, hp⟩ := metrized_exists_pts_ne_one (Nat.pos_of_ne_zero hg') M' τ
    have hs := metrized_pts_subsingleton M τ
    rw [h] at hs
    exact hp (Subsingleton.elim _ _)
  by_cases hg : g = 0
  · rw [hg, key M M' h hg]
  by_cases hg' : g' = 0
  · rw [hg', key M' M h.symm hg']
  haveI : Module.Flat (𝓞 L) L := IsLocalization.flat L (nonZeroDivisors (𝓞 L))
  have h1 := M.hodge.finrank_eq_one
  have h2 := M'.hodge.finrank_eq_one
  rw [← h] at h2
  exact eq_of_finrank_one (R := 𝓞 L) (F := L) (C := M.model.cotangent)
    (Nat.pos_of_ne_zero hg) (Nat.pos_of_ne_zero hg') h1 h2

end ZInQ.Metrization


/-! ## g0-dim: `DimFinite` and `DimBaseChange` proved (task g0-dim; body of `scratch/g0-dim/Dim.lean` §1-§2) -/

section G0DimSec

set_option linter.style.haveILetI false

open Order TensorProduct

namespace G0Dim

/-! ## §1. Commutative algebra -/


/-- Integral injective extensions have the same Krull dimension (going up + incomparability;
Stacks 00OK, Matsumura Thm 9.4 — STANDARD). -/
theorem ringKrullDim_eq_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
    intro P Q hPQ
    have h : P.asIdeal < Q.asIdeal := hPQ
    exact Ideal.IsIntegral.under_lt_under (R := A) h
  · refine iSup_le fun l => ?_
    obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
      l.head.asIdeal ⊥ (by
        intro x hx
        have : algebraMap A B x = 0 := by simpa using hx
        have : x = 0 := hinj (by simpa using this)
        simp [this])
    haveI : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    rw [← hlen]
    exact L.length_le_krullDim

theorem ringKrullDim_mvPolynomial_field (k : Type*) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

/-- **Stacks 00P4 (affine case), proved.** For a finitely generated algebra `R` over a field `K`
and any field extension `L/K`, `dim (R ⊗_K L) = dim R`. Proof: Noether normalization
`K[X_1..X_s] → R` (finite, injective) base-changes to `L[X_1..X_s] → R ⊗ L` (finite, injective
since `L` is flat over `K`). -/
theorem ringKrullDim_tensor_field (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (L : Type*) [Field L] [Algebra K L] :
    ringKrullDim (R ⊗[K] L) = ringKrullDim R := by
  rcases subsingleton_or_nontrivial R with h | h
  · haveI : Subsingleton (R ⊗[K] L) := by
      have h1 : (1 : R ⊗[K] L) = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : R) 0, TensorProduct.zero_tmul]
      exact subsingleton_of_zero_eq_one h1.symm
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    have hR : ringKrullDim R = s := by
      letI := g.toRingHom.toAlgebra
      haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
      rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
        ringKrullDim_mvPolynomial_field]
    let g' := Algebra.TensorProduct.map g (AlgHom.id K L)
    have g'inj : Function.Injective g' :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := L) g.toLinearMap ginj
    have g'fin : g'.toRingHom.Finite := RingHom.Finite.tensorProductMap gfin (by exact RingHom.Finite.id L)
    have hP : ringKrullDim (MvPolynomial (Fin s) K ⊗[K] L) = s := by
      rw [ringKrullDim_eq_of_ringEquiv ((Algebra.TensorProduct.comm K _ L).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv), ringKrullDim_mvPolynomial_field]
    rw [hR, ← hP]
    letI := g'.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K ⊗[K] L) (R ⊗[K] L) := ⟨g'fin.to_isIntegral⟩
    exact ringKrullDim_eq_of_isIntegral_of_injective g'inj

/-- A finitely generated algebra over a field has finite Krull dimension (or is zero). -/
theorem ringKrullDim_le_of_finiteType (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] : ∃ n : ℕ, ringKrullDim R ≤ n := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact ⟨0, by rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le⟩
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    letI := g.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
    refine ⟨s, le_of_eq ?_⟩
    rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
      ringKrullDim_mvPolynomial_field]


/-! ## §2. Topology and schemes -/

open TopologicalSpace Topology


/-- The Krull dimension of a space is the supremum of the dimensions of the members of a cover
by open embeddings (Stacks 0055 for open covers; STANDARD). -/
theorem topologicalKrullDim_eq_iSup_of_openEmbedding {X : Type*} [TopologicalSpace X] {ι : Type*}
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    (hf : ∀ i, IsOpenEmbedding (f i)) (hcov : ∀ x, ∃ i, x ∈ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    obtain ⟨i, y, rfl⟩ := hcov x
    let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (f i) (hf i)
    have hmem : ∀ j, (f i ⁻¹' (p j : Set X)).Nonempty := fun j =>
      ⟨y, p.monotone (Fin.zero_le j) hx⟩
    let q : LTSeries {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} :=
      { length := p.length
        toFun := fun j => ⟨p j, hmem j⟩
        step := fun j => p.step j }
    calc (p.length : WithBot ℕ∞) = q.length := rfl
      _ ≤ krullDim {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} := q.length_le_krullDim
      _ = topologicalKrullDim (Y i) := (Order.krullDim_eq_of_orderIso e).symm
      _ ≤ ⨆ i, topologicalKrullDim (Y i) := le_iSup (fun i => topologicalKrullDim (Y i)) i
  · exact iSup_le fun i => (hf i).isInducing.topologicalKrullDim_le

open AlgebraicGeometry CategoryTheory Limits

theorem scheme_dim_eq_iSup_cover {X : Scheme} (𝒰 : X.OpenCover) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (𝒰.X i) :=
  topologicalKrullDim_eq_iSup_of_openEmbedding (fun i => 𝒰.f i) (fun i => (𝒰.f i).isOpenEmbedding)
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩)

theorem scheme_dim_eq_of_iso {X Y : Scheme} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph

theorem spec_dim (R : CommRingCat) : topologicalKrullDim (Spec R) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R


/-- **Stacks 00P4, affine piece over `Spec K`.** For `m : Spec R → Spec K` locally of finite
type, `Spec R ×_K Spec L ≅ Spec (R ⊗_K L)` has the dimension of `Spec R`. -/
theorem dim_pullback_spec {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]
    (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType m] :
    topologicalKrullDim (pullback m (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim (Spec R) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  have e := scheme_dim_eq_of_iso (pullbackSpecIso K R L)
  refine e.trans ?_
  rw [spec_dim, spec_dim]
  exact ringKrullDim_tensor_field K R L

/-- A scheme of finite type over a field: each affine piece `Spec R → Spec K` has bounded
dimension. -/
theorem dim_spec_le {K : Type} [Field K] (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType m] : ∃ n : ℕ, topologicalKrullDim (Spec R) ≤ n := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  rw [spec_dim]
  exact ringKrullDim_le_of_finiteType K R

/-- **Dimension is invariant under field base change** (Stacks 00P4 globalized; proved). For a
scheme `X` locally of finite type over a field `K` and any field extension `L/K`,
`dim (X ×_K L) = dim X`. -/
theorem dim_baseChange {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (X : Scheme.{0})
    (h : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h] :
    topologicalKrullDim (pullback h (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim X := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let 𝒰 := X.affineCover
  rw [scheme_dim_eq_iSup_cover 𝒰, scheme_dim_eq_iSup_cover (𝒰.pullback₁ (pullback.fst h g))]
  refine iSup_congr fun i => ?_
  have e : (𝒰.pullback₁ (pullback.fst h g)).X i ≅ pullback (𝒰.f i ≫ h) g :=
    (pullbackSymmetry _ _).trans (pullbackRightPullbackFstIso h g (𝒰.f i))
  rw [scheme_dim_eq_of_iso e]
  haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
  exact @dim_pullback_spec K _ L _ _ _ (𝒰.f i ≫ h) hc

theorem exists_nat_of_le (x : WithBot ℕ∞) (h0 : x ≠ ⊥) (N : ℕ) (h : x ≤ N) :
    ∃ n : ℕ, x = n := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((N : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      exact absurd (WithBot.coe_le_coe.mp h') (by simp)
    | coe n => exact ⟨n, rfl⟩

/-- **A nonempty scheme of finite type over a field has finite dimension** (proved). -/
theorem dim_finite {K : Type} [Field K] (X : Scheme.{0}) (h : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType h] [QuasiCompact h] [Nonempty X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace h
  let 𝒰 := X.affineCover.finiteSubcover
  have hb : ∀ i, ∃ n : ℕ, topologicalKrullDim (𝒰.X i) ≤ n := fun i => by
    haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
    exact @dim_spec_le K _ _ (𝒰.f i ≫ h) hc
  choose n hn using hb
  have hle : topologicalKrullDim X ≤ ((∑ i, n i : ℕ) : WithBot ℕ∞) := by
    rw [scheme_dim_eq_iSup_cover 𝒰]
    refine iSup_le fun i => (hn i).trans ?_
    exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  have hne : topologicalKrullDim X ≠ ⊥ := by
    obtain ⟨x⟩ := ‹Nonempty X›
    haveI : Nonempty (IrreducibleCloseds X) :=
      ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_ne_bot_iff.mpr inferInstance
  exact exists_nat_of_le _ hne _ hle

end G0Dim

end G0DimSec

/-! ## metrization (2026-11-13): `MetrizationExists` reduced to `HodgeLatticeTheorem`, one leaf
(the uniformization theorem with its dimension) and two glue Props on Jacobians -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- An abelian variety (def-faltings' copy) has finite dimension (proved, from g0-dim's
`G0Dim.dim_finite`; the same proof as g0-dim's `dimFinite` for `PkgI3.AbVar`). -/
theorem abVar_dim_finite (K : Type) [Field K] (A : AbVar K) : ∃ n : ℕ, A.dim = (n : WithBot ℕ∞) := by
  haveI : Nonempty A.X.left :=
    ⟨η[A.X].left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))⟩
  exact G0Dim.dim_finite A.X.left A.X.hom

/-- **Leaf (AN3 with its dimension: the uniformization theorem).** For every smooth group model
`𝒢` of `A_L`, every `τ : L → ℂ` and `g = dim A`, there are a full lattice `Λ ⊂ ℂ^g` and an analytic
uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` with kernel `Λ`. This is def-faltings'
`AnalyticUniformizationExists` with the dimension pinned to `dim A` (`𝒢(ℂ)_τ = A_τ(ℂ)` is a compact
connected complex Lie group of dimension `dim A`, hence `≅ ℂ^g/Λ`: Mumford, *Abelian varieties*,
§1 and §4 (UNVERIFIED locators), with Serre's GAGA for the analytic structure of `A_τ(ℂ)`).
Implies `AnalyticUniformizationExists` (`analyticUniformizationExists_of`). -/
def AnalyticUniformizationOfDim : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ), A.dim = g →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ 𝒢.IsAnalyticUniformization τ Λ Φ

/-- **Glue (the Jacobian descends to the Hodge line).** For an analytic uniformization `Φ` of
`𝒢(ℂ)_τ`, the Jacobian determinant `jacDet Φ f = det(∂(f_i ∘ Φ)/∂z_j(0))` depends only on the
classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`, is `𝓞_L`-multilinear (through `τ`) and alternating in them, hence is
the value on `1 ⊗ df₁ ∧ ⋯ ∧ df_g` of a `τ`-semilinear map `hodgeSpace g → ℂ`. Why true: `Φ 0 = 1`
lies over `ξ`; the germ `f ∘ Φ` at `0` is independent of the representative of `f` (`dom Φ U`
open); evaluation at a complex point is a ring map, so `(f f') ∘ Φ = (f ∘ Φ)(f' ∘ Φ)` near `0`,
and for `f, f' ∈ 𝔪_ξ` both vanish at `0`, so `d((ff') ∘ Φ)(0) = 0` (Leibniz); a function from
`𝓞_L` acts by the constant `τ(a)`. Then `⋀^g` (universal property) and `L ⊗_{𝓞_L} -` (extension
of scalars along `τ`) give the map. Elementary calculus plus Mathlib's scheme API; unproved. -/
def JacDetDescends : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ c : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ, ∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f

/-- **Glue (local parameters are analytic coordinates).** For `g = dim A` and an analytic
uniformization `Φ` of `𝒢(ℂ)_τ` with a full lattice as kernel, some `f₁, …, f_g ∈ 𝔪_ξ` have
`jacDet Φ f ≠ 0`. Why true (STANDARD): `𝒪_{𝒢,ξ} = 𝒪_{A_L,0}` is regular of dimension `g`
(smoothness); a regular system of parameters `f₁, …, f_g` gives holomorphic coordinates of the
complex manifold `A_τ(ℂ)` at `0` (Serre, GAGA, or the holomorphic implicit function theorem),
and `Φ` is a local biholomorphism at `0`, so `(f_i ∘ Φ)` has invertible Jacobian at `0`.
Unproved (needs the analytic structure of `A_τ(ℂ)`). -/
def JacDetNondegenerate : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ), A.dim = g →
    ∀ (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      IsZLattice ℝ Λ → 𝒢.IsAnalyticUniformization τ Λ Φ →
      ∃ f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk, 𝒢.jacDet Φ f ≠ 0

/-- `AnalyticUniformizationOfDim` is at least as strong as def-faltings'
`AnalyticUniformizationExists` (proved; with `abVar_dim_finite`). -/
theorem analyticUniformizationExists_of (h : AnalyticUniformizationOfDim) :
    AnalyticUniformizationExists := by
  intro K _ A L _ _ _ 𝒢 τ
  obtain ⟨g, hg⟩ := abVar_dim_finite K A
  exact ⟨g, h K A L 𝒢 τ g hg⟩

/-- The metrization at `g = dim A` (proved from the four hypotheses): lattice `⋀^g ω_𝒢`, periods
and coefficient maps from the uniformizations. -/
theorem exists_metrization_of_dim (hH : HodgeLatticeTheorem) (hU : AnalyticUniformizationOfDim)
    (hJ : JacDetDescends) (hN : JacDetNondegenerate) {K : Type} [Field K] {A : AbVar K}
    {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L) (g : ℕ)
    (hg : A.dim = g) : ∃ M : MetrizedModel A L g, M.model = 𝒢 := by
  obtain ⟨hfr, hlat⟩ := hH K A L 𝒢 g hg
  choose Λ Φ hdisc hZ hΦ using fun τ => hU K A L 𝒢 τ g hg
  choose c hc using fun τ => hJ K A L 𝒢 τ g (Λ τ) (Φ τ) (hΦ τ)
  have hc0 : ∀ τ, c τ ≠ 0 := by
    intro τ h0
    haveI := hdisc τ
    obtain ⟨f, hf⟩ := hN K A L 𝒢 τ g hg (Λ τ) (Φ τ) (hZ τ) (hΦ τ)
    apply hf
    rw [← hc τ f, h0]
    rfl
  exact ⟨{ model := 𝒢
           hodge :=
            { lattice := 𝒢.detLattice g
              finrank_eq_one := hfr
              isLattice := hlat
              periods := Λ
              periods_discrete := hdisc
              periods_isZLattice := hZ
              coeff := c
              coeff_ne_zero := hc0 }
           lattice_eq := rfl
           arch := fun τ => ⟨Φ τ, hΦ τ, hc τ⟩ }, rfl⟩

/-- **`MetrizationExists` from `HodgeLatticeTheorem`, the leaf `AnalyticUniformizationOfDim` and
the glue `JacDetDescends`, `JacDetNondegenerate` (proved).** -/
theorem metrizationExists_of (hH : HodgeLatticeTheorem) (hU : AnalyticUniformizationOfDim)
    (hJ : JacDetDescends) (hN : JacDetNondegenerate) : ZInQ.G0HeightAdd.MetrizationExists := by
  intro K _ A L _ _ _ 𝒢
  obtain ⟨g, hg⟩ := abVar_dim_finite K A
  obtain ⟨M, hM⟩ := exists_metrization_of_dim hH hU hJ hN 𝒢 g hg
  exact ⟨g, M, hM⟩

/-- Every metrization has dimension `dim A` (proved, from the four hypotheses and
`metrizationDimUnique`). -/
theorem metrized_dim_eq (hH : HodgeLatticeTheorem) (hU : AnalyticUniformizationOfDim)
    (hJ : JacDetDescends) (hN : JacDetNondegenerate) {K : Type} [Field K] {A : AbVar K}
    {L : Type} [Field L] [NumberField L] [Algebra K L] {g : ℕ} (M : MetrizedModel A L g) :
    A.dim = g := by
  obtain ⟨d, hd⟩ := abVar_dim_finite K A
  obtain ⟨M', hM'⟩ := exists_metrization_of_dim hH hU hJ hN M.model d hd
  rw [hd, metrizationDimUnique K A L d g M' M hM']

end ZInQ.Metrization


/-! ## metrization (2026-11-13): `ProductMetrizationGeo` reduced

`ProductMetrizationGeo` (P2a-geo) follows from `JacDetDescends` (shared with `MetrizationExists`),
`ProductUniformization` (glue: `Φ₁ × Φ₂` is an analytic uniformization of the product model),
`ProductLatticeFacts` (pure Mathlib glue: `Λ₁ × Λ₂` is a full lattice and covolumes multiply)
and `ProductHodgeCompat` (glue: `⋀^{top}ω_{𝒢P} = ⋀ω₁ ⊗ ⋀ω₂` with the block-diagonal Jacobian). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- The first `g₁` coordinates of `ℂ^{g₁+g₂}`. -/
noncomputable def leftBlock (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin g₁ → ℂ) :=
  LinearMap.pi fun i => LinearMap.proj (Fin.castAdd g₂ i)

/-- The last `g₂` coordinates of `ℂ^{g₁+g₂}`. -/
noncomputable def rightBlock (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ) :=
  LinearMap.pi fun j => LinearMap.proj (Fin.natAdd g₁ j)

/-- The product lattice `Λ₁ × Λ₂ ⊂ ℂ^{g₁} × ℂ^{g₂} = ℂ^{g₁+g₂}` (coordinates `Fin.append`). -/
noncomputable def prodLattice {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) : Submodule ℤ (Fin (g₁ + g₂) → ℂ) :=
  Λ₁.comap (leftBlock g₁ g₂).toAddMonoidHom.toIntLinearMap ⊓
    Λ₂.comap (rightBlock g₁ g₂).toAddMonoidHom.toIntLinearMap

/-- The product map `ℂ^{g₁+g₂} → 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ ≅ 𝒢P(ℂ)_τ`, `z ↦ e⁻¹(Φ₁(z'), Φ₂(z''))`. -/
noncomputable def prodPts {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L}
    {𝒢₂ : GroupModel B L} (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ}
    (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ) :
    (Fin (g₁ + g₂) → ℂ) → 𝒢P.Pts τ :=
  fun z => lift (Φ₁ (leftBlock g₁ g₂ z)) (Φ₂ (rightBlock g₁ g₂ z)) ≫ e.inv

/-- **Glue (pure Mathlib): product lattices.** If `Λ₁ ⊂ ℂ^{g₁}`, `Λ₂ ⊂ ℂ^{g₂}` are full lattices,
so is `Λ₁ × Λ₂ ⊂ ℂ^{g₁+g₂}`, and `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂` (the product of fundamental
domains is a fundamental domain; `volume` on `Fin (g₁+g₂) → ℂ` is the product measure under
`Fin.append`). STANDARD; provable from Mathlib, not yet proved. -/
def ProductLatticeFacts : Prop :=
  ∀ (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
    [DiscreteTopology Λ₁] [DiscreteTopology Λ₂], IsZLattice ℝ Λ₁ → IsZLattice ℝ Λ₂ →
    ∃ (_ : DiscreteTopology (prodLattice Λ₁ Λ₂)) (_ : IsZLattice ℝ (prodLattice Λ₁ Λ₂)),
      ZLattice.covolume (prodLattice Λ₁ Λ₂) = ZLattice.covolume Λ₁ * ZLattice.covolume Λ₂

/-- **Glue (the product uniformization).** For an isomorphism `e : 𝒢P ≅ 𝒢₁ ×_{𝓞_L} 𝒢₂` of
`𝓞_L`-schemes whose components are homomorphisms, and analytic uniformizations `Φᵢ` of `𝒢ᵢ(ℂ)_τ`
with kernels `Λᵢ`, `prodPts e Φ₁ Φ₂` is an analytic uniformization of `𝒢P(ℂ)_τ` with kernel
`Λ₁ × Λ₂`. Why true: the homomorphism, kernel and surjectivity clauses follow from `e` and the
universal property of `⊗` (points of a product are pairs of points); openness of `dom` and
holomorphy: a Zariski open of `𝒢₁ ×_{𝓞_L} 𝒢₂` is covered by basic opens `D(h)` of products
`Spec(R₁ ⊗ R₂)` of affine opens, and a regular function there is `a/hⁿ` with
`a, h ∈ R₁ ⊗_{𝓞_L} R₂`, i.e. sums of products of functions holomorphic along `Φ₁` resp. `Φ₂`
(STANDARD). Unproved (Mathlib lacks the affine-cover description of fibre products used here). -/
def ProductUniformization : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G), IsMonHom (e.hom ≫ fst _ _) → IsMonHom (e.hom ≫ snd _ _) →
    ∀ (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
      (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
      𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
      𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂)

/-- **Glue (the Hodge line of a product, with its coefficient).** For `e : 𝒢P ≅ 𝒢₁ × 𝒢₂` as in
`ProductUniformization` and metrizations `M₁`, `M₂` of `𝒢₁`, `𝒢₂`: `hodgeSpace (g₁+g₂)` of `𝒢P` is
an `L`-line, and there are nonzero `s ∈ ⋀^{g₁+g₂}ω_{𝒢P}`, `sᵢ ∈ ⋀^{gᵢ}ω_{𝒢ᵢ}` with
`[⋀ω_{𝒢P} : 𝓞s] = [⋀ω₁ : 𝓞s₁]·[⋀ω₂ : 𝓞s₂]` such that, at every `τ`, every `τ`-semilinear map `c`
that sends wedges to the Jacobians of `prodPts e Φ₁ Φ₂` (for uniformizations `Φᵢ` computing `Mᵢ`'s
coefficients) has `c s = coeff₁(s₁) · coeff₂(s₂)`. Why true (STANDARD): take `s₁ = a₁ · 1⊗df₁`,
`s₂ = a₂ · 1⊗df₂` and `s = p₁*s₁ ∧ p₂*s₂ = a₁a₂ · 1 ⊗ d(p₁*f₁) ∧ d(p₂*f₂)`. Algebra: for the
smooth group scheme `𝒢₁ ×_{𝓞_L} 𝒢₂`, `e*Ω¹ = e₁*Ω¹ ⊕ e₂*Ω¹`, so `ω_{𝒢P} = p₁*ω₁ ⊕ p₂*ω₂` (and the
cotangent space at `ξ` is the direct sum, so `⋀^{g₁+g₂}` is the tensor product of the two lines);
for invertible `𝓞_L`-modules the index of `𝓞s₁ ⊗ 𝓞s₂` in `⋀ω₁ ⊗ ⋀ω₂` is the product. Analysis:
`(p₁*f) ∘ prodPts = f ∘ Φ₁ ∘ leftBlock` near `0`, so the Jacobian matrix of `d(p₁*f₁) ∧ d(p₂*f₂)`
is block diagonal and `jacDet` is the product. Unproved (stalks and differentials of fibre products
of schemes are not in Mathlib). -/
def ProductHodgeCompat : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂)
    (e : 𝒢P.G ≅ M₁.model.G ⊗ M₂.model.G), IsMonHom (e.hom ≫ fst _ _) →
    IsMonHom (e.hom ≫ snd _ _) →
    Module.finrank L (𝒢P.hodgeSpace (g₁ + g₂)) = 1 ∧
    ∃ (s : 𝒢P.hodgeSpace (g₁ + g₂)) (s₁ : M₁.model.hodgeSpace g₁) (s₂ : M₂.model.hodgeSpace g₂),
      s ∈ 𝒢P.detLattice (g₁ + g₂) ∧ s ≠ 0 ∧ s₁ ∈ M₁.hodge.lattice ∧ s₁ ≠ 0 ∧
      s₂ ∈ M₂.hodge.lattice ∧ s₂ ≠ 0 ∧
      secIndex (𝒢P.detLattice (g₁ + g₂)) s =
        secIndex M₁.hodge.lattice s₁ * secIndex M₂.hodge.lattice s₂ ∧
      ∀ (τ : L →+* ℂ) (Φ₁ : (Fin g₁ → ℂ) → M₁.model.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → M₂.model.Pts τ),
        M₁.model.IsAnalyticUniformization τ (M₁.hodge.periods τ) Φ₁ →
        (∀ f, M₁.hodge.coeff τ (M₁.model.wedge f) = M₁.model.jacDet Φ₁ f) →
        M₂.model.IsAnalyticUniformization τ (M₂.hodge.periods τ) Φ₂ →
        (∀ f, M₂.hodge.coeff τ (M₂.model.wedge f) = M₂.model.jacDet Φ₂ f) →
        ∀ c : 𝒢P.hodgeSpace (g₁ + g₂) →ₛₗ[τ] ℂ,
          (∀ f, c (𝒢P.wedge f) = 𝒢P.jacDet (prodPts e Φ₁ Φ₂) f) →
          c s = M₁.hodge.coeff τ s₁ * M₂.hodge.coeff τ s₂

/-- **`ProductMetrizationGeo` from `JacDetDescends`, `ProductUniformization`,
`ProductLatticeFacts` and `ProductHodgeCompat` (proved).** `MP` has lattice `⋀^{g₁+g₂}ω_{𝒢P}`,
periods `Λ₁ × Λ₂` and coefficients from `prodPts e Φ₁ Φ₂`. -/
theorem productMetrizationGeo_of (hJ : JacDetDescends) (hPU : ProductUniformization)
    (hPL : ProductLatticeFacts) (hPC : ProductHodgeCompat) :
    ZInQ.G0HeightAdd.ProductMetrizationGeo := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hP g₁ g₂ M₁ M₂ h₁ h₂
  subst h₁ h₂
  obtain ⟨e, hfst, hsnd, -⟩ := hP
  obtain ⟨hfr, s, s₁, s₂, hs, hs0, hs₁, hs₁0, hs₂, hs₂0, hidx, hcoeff⟩ :=
    hPC K A B C L 𝒢P g₁ g₂ M₁ M₂ e hfst hsnd
  choose Φ₁ hΦ₁ hc₁ using M₁.arch
  choose Φ₂ hΦ₂ hc₂ using M₂.arch
  have hΦP := fun τ => hPU K A B C L 𝒢P M₁.model M₂.model e hfst hsnd τ g₁ g₂ _ _ (Φ₁ τ) (Φ₂ τ)
    (hΦ₁ τ) (hΦ₂ τ)
  choose c hc using fun τ => hJ K C L 𝒢P τ (g₁ + g₂) _ _ (hΦP τ)
  have hlatf : ∀ τ : L →+* ℂ, ∃ (_ : DiscreteTopology
      (prodLattice (M₁.hodge.periods τ) (M₂.hodge.periods τ)))
      (_ : IsZLattice ℝ (prodLattice (M₁.hodge.periods τ) (M₂.hodge.periods τ))),
      ZLattice.covolume (prodLattice (M₁.hodge.periods τ) (M₂.hodge.periods τ)) =
        ZLattice.covolume (M₁.hodge.periods τ) * ZLattice.covolume (M₂.hodge.periods τ) := by
    intro τ
    haveI := M₁.hodge.periods_discrete τ
    haveI := M₂.hodge.periods_discrete τ
    exact hPL g₁ g₂ _ _ (M₁.hodge.periods_isZLattice τ) (M₂.hodge.periods_isZLattice τ)
  choose hdisc hZ hcov using hlatf
  have hcs : ∀ τ, c τ s = M₁.hodge.coeff τ s₁ * M₂.hodge.coeff τ s₂ := fun τ =>
    hcoeff τ (Φ₁ τ) (Φ₂ τ) (hΦ₁ τ) (hc₁ τ) (hΦ₂ τ) (hc₂ τ) (c τ) (hc τ)
  have hc0 : ∀ τ, c τ ≠ 0 := by
    intro τ h0
    have h := hcs τ
    rw [h0, LinearMap.zero_apply] at h
    exact mul_ne_zero (M₁.hodge.coeff_apply_ne_zero τ hs₁0)
      (M₂.hodge.coeff_apply_ne_zero τ hs₂0) h.symm
  have hlat : ∃ t ∈ 𝒢P.detLattice (g₁ + g₂), t ≠ 0 ∧ secIndex (𝒢P.detLattice (g₁ + g₂)) t ≠ 0 :=
    ⟨s, hs, hs0, by
      rw [hidx]
      exact mul_ne_zero (M₁.hodge.hodgeBundle.secIndex_ne_zero hs₁ hs₁0)
        (M₂.hodge.hodgeBundle.secIndex_ne_zero hs₂ hs₂0)⟩
  let MP : MetrizedModel C L (g₁ + g₂) :=
    { model := 𝒢P
      hodge :=
        { lattice := 𝒢P.detLattice (g₁ + g₂)
          finrank_eq_one := hfr
          isLattice := hlat
          periods := fun τ => prodLattice (M₁.hodge.periods τ) (M₂.hodge.periods τ)
          periods_discrete := hdisc
          periods_isZLattice := hZ
          coeff := c
          coeff_ne_zero := hc0 }
      lattice_eq := rfl
      arch := fun τ => ⟨prodPts e (Φ₁ τ) (Φ₂ τ), hΦP τ, hc τ⟩ }
  exact ⟨MP, s, s₁, s₂, rfl, hs, hs0, hs₁, hs₁0, hs₂, hs₂0, hidx, hcs, hcov⟩

end ZInQ.Metrization


/-! ## metrization: `ProductLatticeFacts`, proved (body of ProdLattice.lean, section Proof) -/

namespace ZInQ.Metrization

open MeasureTheory

section Proof

variable {g₁ g₂ : ℕ}

@[simp] theorem leftBlock_apply (z : Fin (g₁ + g₂) → ℂ) (i : Fin g₁) :
    leftBlock g₁ g₂ z i = z (Fin.castAdd g₂ i) := rfl

@[simp] theorem rightBlock_apply (z : Fin (g₁ + g₂) → ℂ) (j : Fin g₂) :
    rightBlock g₁ g₂ z j = z (Fin.natAdd g₁ j) := rfl

theorem mem_prodLattice {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
    {z : Fin (g₁ + g₂) → ℂ} :
    z ∈ prodLattice Λ₁ Λ₂ ↔ leftBlock g₁ g₂ z ∈ Λ₁ ∧ rightBlock g₁ g₂ z ∈ Λ₂ := Iff.rfl

theorem eq_of_blocks {z w : Fin (g₁ + g₂) → ℂ} (h1 : leftBlock g₁ g₂ z = leftBlock g₁ g₂ w)
    (h2 : rightBlock g₁ g₂ z = rightBlock g₁ g₂ w) : z = w := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · exact congrFun h1 i
  · exact congrFun h2 j

@[simp] theorem leftBlock_append (x : Fin g₁ → ℂ) (y : Fin g₂ → ℂ) :
    leftBlock g₁ g₂ (Fin.append x y) = x := by
  funext i; simp

@[simp] theorem rightBlock_append (x : Fin g₁ → ℂ) (y : Fin g₂ → ℂ) :
    rightBlock g₁ g₂ (Fin.append x y) = y := by
  funext j; simp

/-- `ℂ^{g₁+g₂} ≃ ℂ^{g₁} × ℂ^{g₂}` over `ℝ`. -/
noncomputable def blockLinearEquiv (g₁ g₂ : ℕ) :
    (Fin (g₁ + g₂) → ℂ) ≃ₗ[ℝ] (Fin g₁ → ℂ) × (Fin g₂ → ℂ) where
  toFun z := (leftBlock g₁ g₂ z, rightBlock g₁ g₂ z)
  invFun p := Fin.append p.1 p.2
  map_add' z w := by ext <;> simp
  map_smul' c z := by ext <;> simp
  left_inv z := eq_of_blocks (by simp) (by simp)
  right_inv p := by ext <;> simp

/-- `blockLinearEquiv` preserves `volume`. -/
theorem measurePreserving_blockLinearEquiv (g₁ g₂ : ℕ) :
    MeasurePreserving (blockLinearEquiv g₁ g₂) volume volume := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : Fin g₁ ⊕ Fin g₂ => ℂ)
    (finSumFinEquiv (m := g₁) (n := g₂)).symm
  have h2 := (volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin g₁ ⊕ Fin g₂ => ℂ)).symm
  have hc := h2.comp h1
  convert hc using 1
  funext z
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp only [Function.comp_apply, MeasurableEquiv.symm_symm,
      MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply,
      MeasurableEquiv.coe_piCongrLeft]
    rw [show (Sum.inl i : Fin g₁ ⊕ Fin g₂) = finSumFinEquiv.symm (Fin.castAdd g₂ i) by simp,
      Equiv.piCongrLeft_apply_apply]
    rfl
  · simp only [Function.comp_apply, MeasurableEquiv.symm_symm,
      MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply,
      MeasurableEquiv.coe_piCongrLeft]
    rw [show (Sum.inr j : Fin g₁ ⊕ Fin g₂) = finSumFinEquiv.symm (Fin.natAdd g₁ j) by simp,
      Equiv.piCongrLeft_apply_apply]
    rfl

/-- A full lattice has a measurable fundamental domain with unique translates, whose volume is
the covolume. -/
theorem exists_fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ F : Set E, MeasurableSet F ∧ (∀ x, ∃! g : Λ, (g : E) + x ∈ F) ∧
      ZLattice.covolume Λ μ = μ.real F := by
  let b := Module.Free.chooseBasis ℤ Λ
  let b' := b.ofZLatticeBasis ℝ Λ
  have hspan : Submodule.span ℤ (Set.range b') = Λ := b.ofZLatticeBasis_span ℝ Λ
  refine ⟨ZSpan.fundamentalDomain b', ZSpan.fundamentalDomain_measurableSet b', fun x => ?_,
    ZLattice.covolume_eq_measure_fundamentalDomain Λ μ (ZLattice.isAddFundamentalDomain b μ)⟩
  obtain ⟨⟨v, hv⟩, h1, h2⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b' x
  refine ⟨⟨v, hspan ▸ hv⟩, h1, fun w hw => ?_⟩
  have h3 := h2 ⟨w, hspan.symm ▸ w.2⟩ hw
  have h4 : (w : E) = v := congrArg Subtype.val h3
  exact Subtype.ext h4

/-- **`ProductLatticeFacts`, proved.** -/
theorem productLatticeFacts : ProductLatticeFacts := by
  intro g₁ g₂ Λ₁ Λ₂ _ _ hZ₁ hZ₂
  -- discreteness: inject into `Λ₁ × Λ₂`
  have hdisc : DiscreteTopology (prodLattice Λ₁ Λ₂) := by
    let f : prodLattice Λ₁ Λ₂ → Λ₁ × Λ₂ := fun z =>
      (⟨leftBlock g₁ g₂ z, z.2.1⟩, ⟨rightBlock g₁ g₂ z, z.2.2⟩)
    refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
    · refine Continuous.prodMk ?_ ?_
      · exact Continuous.subtype_mk
          ((leftBlock g₁ g₂).continuous_of_finiteDimensional.comp continuous_subtype_val) _
      · exact Continuous.subtype_mk
          ((rightBlock g₁ g₂).continuous_of_finiteDimensional.comp continuous_subtype_val) _
    · intro z w h
      have h1 := congrArg (fun p => (p.1 : Fin g₁ → ℂ)) h
      have h2 := congrArg (fun p => (p.2 : Fin g₂ → ℂ)) h
      exact Subtype.ext (eq_of_blocks h1 h2)
  -- full rank
  have hZ : IsZLattice ℝ (prodLattice Λ₁ Λ₂) := by
    refine ⟨?_⟩
    rw [eq_top_iff]
    rintro z -
    have hz : z = Fin.append (leftBlock g₁ g₂ z) 0 + Fin.append 0 (rightBlock g₁ g₂ z) :=
      eq_of_blocks (by funext i; simp) (by funext j; simp)
    rw [hz]
    refine Submodule.add_mem _ ?_ ?_
    · let ι₁ : (Fin g₁ → ℂ) →ₗ[ℝ] (Fin (g₁ + g₂) → ℂ) :=
        (blockLinearEquiv g₁ g₂).symm.toLinearMap ∘ₗ LinearMap.inl ℝ _ _
      have hι : ∀ x, ι₁ x = Fin.append x 0 := fun x => rfl
      have hle : (Submodule.span ℝ (Λ₁ : Set (Fin g₁ → ℂ))).map ι₁ ≤
          Submodule.span ℝ (prodLattice Λ₁ Λ₂ : Set (Fin (g₁ + g₂) → ℂ)) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨x, hx, rfl⟩
        rw [hι]
        exact ⟨by simpa using hx, by simp [Submodule.zero_mem]⟩
      apply hle
      rw [hZ₁.span_top]
      exact ⟨leftBlock g₁ g₂ z, Submodule.mem_top, hι _⟩
    · let ι₂ : (Fin g₂ → ℂ) →ₗ[ℝ] (Fin (g₁ + g₂) → ℂ) :=
        (blockLinearEquiv g₁ g₂).symm.toLinearMap ∘ₗ LinearMap.inr ℝ _ _
      have hι : ∀ y, ι₂ y = Fin.append 0 y := fun y => rfl
      have hle : (Submodule.span ℝ (Λ₂ : Set (Fin g₂ → ℂ))).map ι₂ ≤
          Submodule.span ℝ (prodLattice Λ₁ Λ₂ : Set (Fin (g₁ + g₂) → ℂ)) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨y, hy, rfl⟩
        rw [hι]
        exact ⟨by simp [Submodule.zero_mem], by simpa using hy⟩
      apply hle
      rw [hZ₂.span_top]
      exact ⟨rightBlock g₁ g₂ z, Submodule.mem_top, hι _⟩
  refine ⟨hdisc, hZ, ?_⟩
  -- covolume
  obtain ⟨F₁, hF₁m, hF₁u, hF₁c⟩ := exists_fd Λ₁ volume
  obtain ⟨F₂, hF₂m, hF₂u, hF₂c⟩ := exists_fd Λ₂ volume
  let φ := blockLinearEquiv g₁ g₂
  have hφm : Measurable φ := (measurePreserving_blockLinearEquiv g₁ g₂).measurable
  let F : Set (Fin (g₁ + g₂) → ℂ) := φ ⁻¹' (F₁ ×ˢ F₂)
  have hFd : IsAddFundamentalDomain (prodLattice Λ₁ Λ₂) F volume := by
    refine IsAddFundamentalDomain.mk' ((hφm (hF₁m.prod hF₂m)).nullMeasurableSet) fun z => ?_
    obtain ⟨a, ha, hau⟩ := hF₁u (leftBlock g₁ g₂ z)
    obtain ⟨b, hb, hbu⟩ := hF₂u (rightBlock g₁ g₂ z)
    refine ⟨⟨Fin.append (a : Fin g₁ → ℂ) (b : Fin g₂ → ℂ),
      mem_prodLattice.mpr ⟨by simpa using a.2, by simpa using b.2⟩⟩, ?_, fun w hw => ?_⟩
    · beta_reduce
      rw [Submodule.vadd_def, vadd_eq_add]
      show (leftBlock g₁ g₂ _, rightBlock g₁ g₂ _) ∈ F₁ ×ˢ F₂
      simpa using ⟨ha, hb⟩
    · beta_reduce at hw
      rw [Submodule.vadd_def, vadd_eq_add] at hw
      have hw' : (leftBlock g₁ g₂ ((w : Fin (g₁ + g₂) → ℂ) + z),
          rightBlock g₁ g₂ ((w : Fin (g₁ + g₂) → ℂ) + z)) ∈ F₁ ×ˢ F₂ := hw
      simp only [map_add, Set.mem_prod] at hw'
      have e1 := hau ⟨leftBlock g₁ g₂ w, w.2.1⟩ hw'.1
      have e2 := hbu ⟨rightBlock g₁ g₂ w, w.2.2⟩ hw'.2
      apply Subtype.ext
      apply eq_of_blocks
      · simpa using congrArg Subtype.val e1
      · simpa using congrArg Subtype.val e2
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume hFd, hF₁c, hF₂c,
    (measurePreserving_blockLinearEquiv g₁ g₂).measureReal_preimage
      (hF₁m.prod hF₂m).nullMeasurableSet,
    Measure.volume_eq_prod, measureReal_def, measureReal_def, measureReal_def,
    Measure.prod_prod, ENNReal.toReal_mul]

end Proof

end ZInQ.Metrization


/-! ## metrization: what remains of `ProductMetrizationGeo` and `HeightAdditivity` -/

namespace ZInQ.Metrization

/-- **`ProductMetrizationGeo` from `JacDetDescends`, `ProductUniformization` and
`ProductHodgeCompat`** (`ProductLatticeFacts` proved). -/
theorem productMetrizationGeo_of' (hJ : JacDetDescends) (hPU : ProductUniformization)
    (hPC : ProductHodgeCompat) : ZInQ.G0HeightAdd.ProductMetrizationGeo :=
  productMetrizationGeo_of hJ hPU productLatticeFacts hPC

end ZInQ.Metrization

namespace HSyn.G0Split

/-- **`HeightAdditivity` after task metrization.** From the leaf N1, the bundle field `h5`,
def-faltings' stated `AnalyticUniformizationUnique` and `HodgeLatticeTheorem`, the leaf
`AnalyticUniformizationOfDim`, and the glue `JacDetDescends`, `JacDetNondegenerate`,
`ProductUniformization`, `ProductHodgeCompat`. (`MetrizationDimUnique` and
`ProductLatticeFacts` are proved.) -/
theorem heightAdditivity_of_metrization (hN1 : ZInQ.H5Neron.NeronModelExists) (h5 : LeafAdopt.H5)
    (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hUD : ZInQ.Metrization.AnalyticUniformizationOfDim) (hJ : ZInQ.Metrization.JacDetDescends)
    (hN : ZInQ.Metrization.JacDetNondegenerate) (hPU : ZInQ.Metrization.ProductUniformization)
    (hPC : ZInQ.Metrization.ProductHodgeCompat) : HeightAdditivity :=
  heightAdditivity_of_geo hN1 h5 hU ZInQ.Metrization.metrizationDimUnique
    (ZInQ.Metrization.metrizationExists_of hH hUD hJ hN)
    (ZInQ.Metrization.productMetrizationGeo_of' hJ hPU hPC)

end HSyn.G0Split


/-! ## metrization: the algebraic half of `ProductUniformization`, proved

`prodPts e Φ₁ Φ₂` is a surjective homomorphism with kernel `Λ₁ × Λ₂` (from `e` and the universal
property of `⊗`); `ProductUniformization` is reduced to `ProductUniformizationAnalytic` (openness
of `dom` and holomorphy). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

section ProdPtsAlg

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ}

theorem prodPts_comp_fst (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ)
    (z : Fin (g₁ + g₂) → ℂ) : prodPts e Φ₁ Φ₂ z ≫ e.hom ≫ fst _ _ = Φ₁ (leftBlock g₁ g₂ z) := by
  simp [prodPts]

theorem prodPts_comp_snd (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ)
    (z : Fin (g₁ + g₂) → ℂ) : prodPts e Φ₁ Φ₂ z ≫ e.hom ≫ snd _ _ = Φ₂ (rightBlock g₁ g₂ z) := by
  simp [prodPts]

theorem pts_ext {p q : 𝒢P.Pts τ} (h1 : p ≫ e.hom ≫ fst _ _ = q ≫ e.hom ≫ fst _ _)
    (h2 : p ≫ e.hom ≫ snd _ _ = q ≫ e.hom ≫ snd _ _) : p = q := by
  rw [← cancel_mono e.hom]
  apply CartesianMonoidalCategory.hom_ext
  · simpa using h1
  · simpa using h2

/-- **The algebraic clauses of `IsAnalyticUniformization` for `prodPts` (proved).** -/
theorem prodPts_alg (hfst : IsMonHom (e.hom ≫ fst _ _)) (hsnd : IsMonHom (e.hom ≫ snd _ _))
    {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
    {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}
    (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁) (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) :
    (∀ z w, prodPts e Φ₁ Φ₂ (z + w) = prodPts e Φ₁ Φ₂ z * prodPts e Φ₁ Φ₂ w) ∧
    (∀ z, prodPts e Φ₁ Φ₂ z = 1 ↔ z ∈ prodLattice Λ₁ Λ₂) ∧
    Function.Surjective (prodPts e Φ₁ Φ₂) := by
  refine ⟨fun z w => ?_, fun z => ?_, fun p => ?_⟩
  · apply pts_ext e
    · rw [MonObj.mul_comp, prodPts_comp_fst, prodPts_comp_fst, prodPts_comp_fst, map_add,
        h₁.1]
    · rw [MonObj.mul_comp, prodPts_comp_snd, prodPts_comp_snd, prodPts_comp_snd, map_add,
        h₂.1]
  · constructor
    · intro h
      have e1 : Φ₁ (leftBlock g₁ g₂ z) = 1 := by
        rw [← prodPts_comp_fst e Φ₁ Φ₂ z, h, MonObj.one_comp]
      have e2 : Φ₂ (rightBlock g₁ g₂ z) = 1 := by
        rw [← prodPts_comp_snd e Φ₁ Φ₂ z, h, MonObj.one_comp]
      exact mem_prodLattice.mpr ⟨(h₁.2.1 _).mp e1, (h₂.2.1 _).mp e2⟩
    · intro hz
      obtain ⟨hz1, hz2⟩ := mem_prodLattice.mp hz
      apply pts_ext e
      · rw [prodPts_comp_fst, MonObj.one_comp, (h₁.2.1 _).mpr hz1]
      · rw [prodPts_comp_snd, MonObj.one_comp, (h₂.2.1 _).mpr hz2]
  · obtain ⟨x, hx⟩ := h₁.2.2.1 (p ≫ e.hom ≫ fst _ _)
    obtain ⟨y, hy⟩ := h₂.2.2.1 (p ≫ e.hom ≫ snd _ _)
    refine ⟨Fin.append x y, pts_ext e ?_ ?_⟩
    · rw [prodPts_comp_fst, leftBlock_append, hx]
    · rw [prodPts_comp_snd, rightBlock_append, hy]

end ProdPtsAlg

/-- **Glue (the analytic half of the product uniformization).** With the hypotheses of
`ProductUniformization`: each `dom (prodPts e Φ₁ Φ₂) U` is open and each regular function on `U`
is holomorphic along `prodPts e Φ₁ Φ₂` there. Why true: as in `ProductUniformization` (basic opens
`D(h)` of products of affine opens; regular functions `a/hⁿ`, `a, h ∈ R₁ ⊗_{𝓞_L} R₂`). STANDARD,
unproved. -/
def ProductUniformizationAnalytic : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G), IsMonHom (e.hom ≫ fst _ _) → IsMonHom (e.hom ≫ snd _ _) →
    ∀ (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
      (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
      𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
      (∀ U, IsOpen (𝒢P.dom (prodPts e Φ₁ Φ₂) U)) ∧
      (∀ U (s : Γ(𝒢P.G.left, U)), DifferentiableOn ℂ
        (fun z => 𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s) (𝒢P.dom (prodPts e Φ₁ Φ₂) U))

/-- **`ProductUniformization` from `ProductUniformizationAnalytic` (proved).** -/
theorem productUniformization_of (h : ProductUniformizationAnalytic) : ProductUniformization := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  obtain ⟨hhom, hker, hsurj⟩ := prodPts_alg e hfst hsnd h₁ h₂
  obtain ⟨hopen, hdiff⟩ := h K A B C L 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  exact ⟨hhom, hker, hsurj, hopen, hdiff⟩

end ZInQ.Metrization

namespace HSyn.G0Split

/-- **`HeightAdditivity` after task metrization, with `ProductUniformization` reduced to its
analytic half.** -/
theorem heightAdditivity_of_metrization' (hN1 : ZInQ.H5Neron.NeronModelExists) (h5 : LeafAdopt.H5)
    (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hUD : ZInQ.Metrization.AnalyticUniformizationOfDim) (hJ : ZInQ.Metrization.JacDetDescends)
    (hN : ZInQ.Metrization.JacDetNondegenerate)
    (hPA : ZInQ.Metrization.ProductUniformizationAnalytic)
    (hPC : ZInQ.Metrization.ProductHodgeCompat) : HeightAdditivity :=
  heightAdditivity_of_metrization hN1 h5 hU hH hUD hJ hN
    (ZInQ.Metrization.productUniformization_of hPA) hPC

end HSyn.G0Split


/-! ## metrization: `JacDetDescends` reduced to four calculus properties of `jacDet`

The algebra (universal property of `⋀^g`, extension of scalars `L ⊗_{𝓞_L} -` along `τ`) is
proved; what remains (`JacDetMultilinear`) are four statements about the derivative at `0` of
germs composed with `Φ`. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- **Glue (calculus of `jacDet`).** For an analytic uniformization `Φ` of `𝒢(ℂ)_τ`, the map
`f ↦ jacDet Φ f = det(∂(f_i ∘ Φ)/∂z_j(0))` on `g`-tuples of germs in `𝔪_ξ`
(i) depends only on the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`;
(ii) is additive in each slot;
(iii) scales by `τ(a)` when slot `i` is multiplied by the image of `a ∈ 𝓞_L`;
(iv) vanishes when two slots are equal.
Why true: `Φ 0 = 1` lies over `ξ`, and `dom Φ U` is open, so the germ at `0` of `f ∘ Φ` does not
depend on the representative of `f`, and `(f + f') ∘ Φ = f ∘ Φ + f' ∘ Φ`, `(ff') ∘ Φ = (f ∘ Φ)(f' ∘ Φ)`
and `a ∘ Φ = τ(a)` near `0` (evaluation at a complex point is a ring map); for `f, f' ∈ 𝔪_ξ`,
`f ∘ Φ` and `f' ∘ Φ` vanish at `0`, so `d((ff') ∘ Φ)(0) = 0` (Leibniz), which gives (i); (ii)-(iv)
are row operations on the determinant. Elementary, unproved (needs the compatibility of
`evalAt` with restriction, sums, products and stalks in Mathlib's scheme API). -/
def JacDetMultilinear : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    (∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f') ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g)
      (x y : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (x + y)) =
        𝒢.jacDet Φ (Function.update f i x) + 𝒢.jacDet Φ (Function.update f i y)) ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
      (x : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
        τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x)) ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i j : Fin g), f i = f j → i ≠ j →
      𝒢.jacDet Φ f = 0)

/-- **`JacDetDescends` from `JacDetMultilinear` (proved).** -/
theorem jacDetDescends_of (h : JacDetMultilinear) : JacDetDescends := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  obtain ⟨hcls, hadd, hsmul, halt⟩ := h K A L 𝒢 τ g Λ Φ hΦ
  classical
  letI : Module (𝓞 L) ℂ := Module.compHom ℂ (τ.comp (algebraMap (𝓞 L) L))
  have hsm : ∀ (a : 𝓞 L) (z : ℂ), a • z = τ (algebraMap (𝓞 L) L a) * z := fun _ _ => rfl
  let lift : 𝒢.cotangent → IsLocalRing.maximalIdeal 𝒢.genStalk :=
    Function.surjInv (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective
  have hlift : ∀ v, 𝒢.dCls (lift v) = v := fun v =>
    Function.surjInv_eq (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective v
  have hdadd : ∀ x y, 𝒢.dCls (x + y) = 𝒢.dCls x + 𝒢.dCls y := fun x y =>
    map_add (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent x y
  have hdsmul : ∀ (a : 𝓞 L) x, 𝒢.dCls (𝒢.structMap a • x) = a • 𝒢.dCls x := fun a x =>
    map_smul (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent (𝒢.structMap a) x
  let ψ : 𝒢.cotangent [⋀^Fin g]→ₗ[𝓞 L] ℂ :=
    { toFun := fun v => 𝒢.jacDet Φ (fun i => lift (v i))
      map_update_add' := by
        intro _ v i x y
        have e0 : 𝒢.jacDet Φ (fun j => lift (Function.update v i (x + y) j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x + lift y)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp [hlift, hdadd]
          · simp [Function.update_apply, hj]
        have e1 : 𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        have e2 : 𝒢.jacDet Φ (fun j => lift (Function.update v i y j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift y)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        show 𝒢.jacDet Φ (fun j => lift (Function.update v i (x + y) j)) =
          𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) +
            𝒢.jacDet Φ (fun j => lift (Function.update v i y j))
        rw [e0, e1, e2]
        convert hadd (fun j => lift (v j)) i (lift x) (lift y)
      map_update_smul' := by
        intro _ v i a x
        have e0 : 𝒢.jacDet Φ (fun j => lift (Function.update v i (a • x) j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (𝒢.structMap a • lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp [hlift, hdsmul]
          · simp [Function.update_apply, hj]
        have e1 : 𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        show 𝒢.jacDet Φ (fun j => lift (Function.update v i (a • x) j)) =
          a • 𝒢.jacDet Φ (fun j => lift (Function.update v i x j))
        rw [e0, e1, hsm]
        convert hsmul (fun j => lift (v j)) i a (lift x)
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        exact halt (fun k => lift (v k)) i j (by simp only [hv]) hij }
  let Ψ : ⋀[𝓞 L]^g 𝒢.cotangent →ₗ[𝓞 L] ℂ := exteriorPower.alternatingMapLinearEquiv ψ
  let B : L →ₗ[𝓞 L] ⋀[𝓞 L]^g 𝒢.cotangent →ₗ[𝓞 L] ℂ :=
    LinearMap.mk₂ (𝓞 L) (fun x w => τ x * Ψ w)
      (fun x y w => by rw [map_add, add_mul])
      (fun a x w => by
        rw [hsm, Algebra.smul_def, map_mul, _root_.mul_assoc])
      (fun x w w' => by rw [map_add, mul_add])
      (fun a x w => by
        rw [map_smul, hsm, hsm, mul_left_comm])
  let T : 𝒢.hodgeSpace g →ₗ[𝓞 L] ℂ := TensorProduct.lift B
  have hT : ∀ x w, T (x ⊗ₜ[𝓞 L] w) = τ x * Ψ w := fun x w => rfl
  let c : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := by
        intro y t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul x w =>
          rw [TensorProduct.smul_tmul', hT, hT, smul_eq_mul, map_mul, _root_.mul_assoc]
          rfl
        | add t t' ht ht' => rw [smul_add, map_add, ht, ht', map_add, smul_eq_mul, smul_eq_mul,
            smul_eq_mul, mul_add] }
  refine ⟨c, fun f => ?_⟩
  show T ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => 𝒢.dCls (f i))) = 𝒢.jacDet Φ f
  rw [hT, map_one, _root_.one_mul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact hcls _ _ fun i => hlift _

end ZInQ.Metrization

namespace HSyn.G0Split

/-- **`HeightAdditivity` after task metrization, final form.** -/
theorem heightAdditivity_of_metrization'' (hN1 : ZInQ.H5Neron.NeronModelExists)
    (h5 : LeafAdopt.H5) (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hUD : ZInQ.Metrization.AnalyticUniformizationOfDim)
    (hJ : ZInQ.Metrization.JacDetMultilinear) (hN : ZInQ.Metrization.JacDetNondegenerate)
    (hPA : ZInQ.Metrization.ProductUniformizationAnalytic)
    (hPC : ZInQ.Metrization.ProductHodgeCompat) : HeightAdditivity :=
  heightAdditivity_of_metrization' hN1 h5 hU hH hUD (ZInQ.Metrization.jacDetDescends_of hJ) hN
    hPA hPC

end HSyn.G0Split


/-! ## metrization: `ProductHodgeCompat` split into an algebraic and an analytic Prop

`pullGerm φ : 𝒪_{ℋ,ξ} → 𝒪_{𝒢,ξ}` (pull-back of germs along a homomorphism of group models; it
needs `φ(ξ_𝒢) = ξ_ℋ`, proved from `IsMonHom`). `ProductHodgeLattice` (algebra: `s = p₁*s₁ ∧ p₂*s₂`
lies in the lattice with multiplicative index) and `ProductJacobian` (analysis: block-diagonal
Jacobian) give `ProductHodgeCompat` (with `ProductUniformization`). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

section Pull

variable {K : Type} [Field K] {A C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A homomorphism of group models maps the identity `ξ` of the generic fibre to `ξ` (proved). -/
theorem map_genericUnit_of_isMonHom {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G)
    [IsMonHom φ] : φ.left 𝒢.genericUnit = ℋ.genericUnit := by
  have h1 : η[𝒢.G] ≫ φ = η[ℋ.G] := IsMonHom.one_hom φ
  have h2 : (η[𝒢.G]).left ≫ φ.left = (η[ℋ.G]).left := by rw [← Over.comp_left, h1]
  show φ.left ((η[𝒢.G]).left (genericPt L)) = (η[ℋ.G]).left (genericPt L)
  rw [← h2]
  rfl

/-- Pull-back of germs at `ξ` along a homomorphism of group models: `𝒪_{ℋ,ξ} → 𝒪_{𝒢,ξ}`. -/
noncomputable def pullGerm {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G)
    [IsMonHom φ] : ℋ.genStalk ⟶ 𝒢.genStalk :=
  ℋ.G.left.presheaf.stalkSpecializes
      ((congrArg (fun x => x ⤳ ℋ.genericUnit) (map_genericUnit_of_isMonHom φ)).mpr
        specializes_rfl) ≫
    φ.left.stalkMap 𝒢.genericUnit

end Pull

/-- **Glue (algebra: the Hodge lattice of a product).** For `e : 𝒢P ≅ M₁.model × M₂.model` with
homomorphic components: `hodgeSpace (g₁+g₂)` of `𝒢P` is a line, and there are germ tuples
`f₁, f₂` and their pull-backs `f = (p₁*f₁, p₂*f₂)`, and `a₁, a₂ ∈ L`, such that `sᵢ = aᵢ · 1⊗dfᵢ`
are nonzero elements of `⋀ω_{𝒢ᵢ}`, `s = a₁a₂ · 1⊗df` is a nonzero element of `⋀ω_{𝒢P}`, and
`[⋀ω_{𝒢P} : 𝓞s] = [⋀ω₁ : 𝓞s₁]·[⋀ω₂ : 𝓞s₂]`. Why true (STANDARD): `ω_{𝒢P} = p₁*ω₁ ⊕ p₂*ω₂` and
`𝔪_ξ/𝔪_ξ² = p₁*C₁ ⊕ p₂*C₂` for a product of smooth group schemes (EGA IV 17.2.3, UNVERIFIED
locator), so `⋀^{g₁+g₂}` is the tensor product of the two lines; for invertible `𝓞_L`-modules
indices multiply (norms of ideals). Unproved (stalks and differentials of fibre products are
not in Mathlib). -/
def ProductHodgeLattice : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂)
    (e : 𝒢P.G ≅ M₁.model.G ⊗ M₂.model.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _)),
    Module.finrank L (𝒢P.hodgeSpace (g₁ + g₂)) = 1 ∧
    ∃ (f₁ : Fin g₁ → IsLocalRing.maximalIdeal M₁.model.genStalk)
      (f₂ : Fin g₂ → IsLocalRing.maximalIdeal M₂.model.genStalk)
      (f : Fin (g₁ + g₂) → IsLocalRing.maximalIdeal 𝒢P.genStalk) (a₁ a₂ : L),
      (∀ i, (f (Fin.castAdd g₂ i) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ fst _ _)).hom (f₁ i)) ∧
      (∀ j, (f (Fin.natAdd g₁ j) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ snd _ _)).hom (f₂ j)) ∧
      a₁ • M₁.model.wedge f₁ ∈ M₁.hodge.lattice ∧ a₁ • M₁.model.wedge f₁ ≠ 0 ∧
      a₂ • M₂.model.wedge f₂ ∈ M₂.hodge.lattice ∧ a₂ • M₂.model.wedge f₂ ≠ 0 ∧
      (a₁ * a₂) • 𝒢P.wedge f ∈ 𝒢P.detLattice (g₁ + g₂) ∧ (a₁ * a₂) • 𝒢P.wedge f ≠ 0 ∧
      secIndex (𝒢P.detLattice (g₁ + g₂)) ((a₁ * a₂) • 𝒢P.wedge f) =
        secIndex M₁.hodge.lattice (a₁ • M₁.model.wedge f₁) *
          secIndex M₂.hodge.lattice (a₂ • M₂.model.wedge f₂)

/-- **Glue (analysis: the Jacobian of the product uniformization is block diagonal).** If
`prodPts e Φ₁ Φ₂` is an analytic uniformization and `f = (p₁*f₁, p₂*f₂)`, then
`jacDet (prodPts e Φ₁ Φ₂) f = jacDet Φ₁ f₁ · jacDet Φ₂ f₂`. Why true: `p₁ ∘ prodPts = Φ₁ ∘ leftBlock`
(`prodPts_comp_fst`), so near `0` the germ `(p₁*f₁ᵢ) ∘ prodPts` is `f₁ᵢ ∘ Φ₁ ∘ leftBlock` (the
representatives agree on an open `V ∋ ξ` and `dom (prodPts) V` is open), whose derivative
vanishes on the last `g₂` coordinates; the matrix is block diagonal (`Matrix.det_fromBlocks_zero₂₁`
after `finSumFinEquiv`). Elementary, unproved (needs the `evalAt`/stalk compatibilities of
`JacDetMultilinear` and functoriality of `evalAt` along morphisms). -/
def ProductJacobian : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _))
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
    (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
    𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂) →
    ∀ (f₁ : Fin g₁ → IsLocalRing.maximalIdeal 𝒢₁.genStalk)
      (f₂ : Fin g₂ → IsLocalRing.maximalIdeal 𝒢₂.genStalk)
      (f : Fin (g₁ + g₂) → IsLocalRing.maximalIdeal 𝒢P.genStalk),
      (∀ i, (f (Fin.castAdd g₂ i) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ fst _ _)).hom (f₁ i)) →
      (∀ j, (f (Fin.natAdd g₁ j) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ snd _ _)).hom (f₂ j)) →
      𝒢P.jacDet (prodPts e Φ₁ Φ₂) f = 𝒢₁.jacDet Φ₁ f₁ * 𝒢₂.jacDet Φ₂ f₂

/-- **`ProductHodgeCompat` from `ProductUniformization`, `ProductHodgeLattice` and
`ProductJacobian` (proved).** -/
theorem productHodgeCompat_of (hPU : ProductUniformization) (hL : ProductHodgeLattice)
    (hJ : ProductJacobian) : ProductHodgeCompat := by
  intro K _ A B C L _ _ _ 𝒢P g₁ g₂ M₁ M₂ e hfst hsnd
  obtain ⟨hfr, f₁, f₂, f, a₁, a₂, hf1, hf2, hs₁, hs₁0, hs₂, hs₂0, hs, hs0, hidx⟩ :=
    hL K A B C L 𝒢P g₁ g₂ M₁ M₂ e hfst hsnd
  refine ⟨hfr, (a₁ * a₂) • 𝒢P.wedge f, a₁ • M₁.model.wedge f₁, a₂ • M₂.model.wedge f₂, hs, hs0,
    hs₁, hs₁0, hs₂, hs₂0, hidx, ?_⟩
  intro τ Φ₁ Φ₂ h₁ hc₁ h₂ hc₂ c hc
  have hΦP := hPU K A B C L 𝒢P M₁.model M₂.model e hfst hsnd τ g₁ g₂ _ _ Φ₁ Φ₂ h₁ h₂
  have hjac := hJ K A B C L 𝒢P M₁.model M₂.model e hfst hsnd τ g₁ g₂ _ _ Φ₁ Φ₂ h₁ h₂ hΦP
    f₁ f₂ f hf1 hf2
  rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, hc, hc₁, hc₂, hjac, map_mul]
  simp only [smul_eq_mul]
  ring

end ZInQ.Metrization

namespace HSyn.G0Split

/-- **`HeightAdditivity` after task metrization, with `ProductHodgeCompat` split.** -/
theorem heightAdditivity_of_metrization''' (hN1 : ZInQ.H5Neron.NeronModelExists)
    (h5 : LeafAdopt.H5) (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hUD : ZInQ.Metrization.AnalyticUniformizationOfDim)
    (hJ : ZInQ.Metrization.JacDetMultilinear) (hN : ZInQ.Metrization.JacDetNondegenerate)
    (hPA : ZInQ.Metrization.ProductUniformizationAnalytic)
    (hPL : ZInQ.Metrization.ProductHodgeLattice) (hPJ : ZInQ.Metrization.ProductJacobian) :
    HeightAdditivity :=
  heightAdditivity_of_metrization'' hN1 h5 hU hH hUD hJ hN hPA
    (ZInQ.Metrization.productHodgeCompat_of (ZInQ.Metrization.productUniformization_of hPA)
      hPL hPJ)

end HSyn.G0Split


/-! ## metrization: two of the four clauses of `JacDetMultilinear`, proved

`Φ 0 = 1` lies over `ξ` (`zero_mem_dom`); `germAlong Φ t` agrees near `0` with `z ↦ evalAt (Φ z) U s`
for every representative `(U, s)` of `t` (`germAlong_eventuallyEq`); hence slot additivity
(`jacDet_update_add`). Vanishing on equal slots is immediate (`jacDet_eq_zero_of_eq`). What
remains is `JacDetClassScalar` (clauses (i) and (iii)). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section Germ

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `Spec ℂ → Spec 𝓞_L` (via `τ`) hits the generic point. -/
theorem ptC_hom_apply (τ : L →+* ℂ) (x : Spec (CommRingCat.of ℂ)) :
    (GroupModel.ptC (L := L) τ).hom x = genericPt L := by
  haveI : x.asIdeal.IsPrime := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime x.asIdeal
  apply PrimeSpectrum.ext
  show Ideal.comap (τ.comp (algebraMap (𝓞 L) L)) x.asIdeal = ⊥
  rw [hx]
  exact Ideal.comap_bot_of_injective _
    (τ.injective.comp (IsFractionRing.injective (𝓞 L) L))

/-- The identity complex point lies over `ξ`. -/
theorem one_left_apply (τ : L →+* ℂ) (x : Spec (CommRingCat.of ℂ)) :
    (1 : 𝒢.Pts τ).left x = 𝒢.genericUnit := by
  have hw : (toUnit (GroupModel.ptC (L := L) τ)).left = (GroupModel.ptC (L := L) τ).hom :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (GroupModel.ptC (L := L) τ)))
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left x = 𝒢.unitSection (genericPt L)
  rw [Over.comp_left]
  change (η[𝒢.G]).left ((toUnit (GroupModel.ptC (L := L) τ)).left x) = _
  rw [hw, ptC_hom_apply]
  rfl

/-- For an analytic uniformization, `0 ∈ dom Φ U` whenever `ξ ∈ U`. -/
theorem zero_mem_dom {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U) : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := by
  have h1 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  show ⊤ ≤ (Φ 0).left ⁻¹ᵁ U
  rw [h1]
  intro x _
  show (1 : 𝒢.Pts τ).left x ∈ U
  erw [one_left_apply]
  exact m

/-- `evalAt` is compatible with restriction. -/
theorem evalAt_res {τ : L →+* ℂ} (p : 𝒢.Pts τ) {U W : 𝒢.G.left.Opens} (i : W ⟶ U)
    (hW : ⊤ ≤ p.left ⁻¹ᵁ W) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p W (𝒢.G.left.presheaf.map i.op s) = 𝒢.evalAt p U s := by
  have hU : ⊤ ≤ p.left ⁻¹ᵁ U := hW.trans ((TopologicalSpace.Opens.map p.left.base).map i).le
  unfold GroupModel.evalAt
  rw [dif_pos hW, dif_pos hU, ← Scheme.Hom.map_appLE p.left hW i.op]
  rfl

/-- `evalAt` is additive in the section. -/
theorem evalAt_add {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s + s') = 𝒢.evalAt p U s + 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_add]
    exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

/-- **`germAlong Φ t` is, near `0`, the function of any representative of `t`.** -/
theorem germAlong_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U) (s : Γ(𝒢.G.left, U)) :
    𝒢.germAlong Φ (𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s) =ᶠ[𝓝 0]
      fun z => 𝒢.evalAt (Φ z) U s := by
  unfold GroupModel.germAlong
  obtain ⟨W, mW, i₁, i₂, hW⟩ := TopCat.Presheaf.germ_eq _ 𝒢.genericUnit _ m _ s
    (𝒢.exists_rep (𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s)).choose_spec.choose_spec.choose_spec
  filter_upwards [(hΦ.2.2.2.1 W).mem_nhds (zero_mem_dom 𝒢 hΦ W mW)] with z hz
  rw [← evalAt_res 𝒢 (Φ z) i₁ hz, ← evalAt_res 𝒢 (Φ z) i₂ hz s, hW]

/-- `germAlong Φ t` is differentiable at `0`. -/
theorem germAlong_differentiableAt {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk) :
    DifferentiableAt ℂ (𝒢.germAlong Φ t) 0 := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep t
  have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) U s) 0 :=
    (hΦ.2.2.2.2 U s).differentiableAt ((hΦ.2.2.2.1 U).mem_nhds (zero_mem_dom 𝒢 hΦ U m))
  exact hd.congr_of_eventuallyEq (germAlong_eventuallyEq 𝒢 hΦ U m s)

/-- `germAlong Φ (x + y) = germAlong Φ x + germAlong Φ y` near `0`. -/
theorem germAlong_add_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x y : 𝒢.genStalk) :
    𝒢.germAlong Φ (x + y) =ᶠ[𝓝 0] 𝒢.germAlong Φ x + 𝒢.germAlong Φ y := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep y
  have mm : 𝒢.genericUnit ∈ U ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hsum : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s +
      𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' =
      𝒢.G.left.presheaf.germ (U ⊓ U') 𝒢.genericUnit mm
        (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s +
          𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') := by
    simp only [map_add, TopCat.Presheaf.germ_res_apply]
  rw [hsum]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ (U ⊓ U') mm _,
    germAlong_eventuallyEq 𝒢 hΦ U m s, germAlong_eventuallyEq 𝒢 hΦ U' m' s',
    (hΦ.2.2.2.1 (U ⊓ U')).mem_nhds (zero_mem_dom 𝒢 hΦ (U ⊓ U') mm)] with z h1 h2 h3 hz
  rw [Pi.add_apply, h1, h2, h3, evalAt_add, evalAt_res 𝒢 (Φ z) _ hz,
    evalAt_res 𝒢 (Φ z) _ hz]

/-- **Clause (ii) of `JacDetMultilinear`, proved: slot additivity.** -/
theorem jacDet_update_add {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g)
    (x y : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet Φ (Function.update f i (x + y)) =
      𝒢.jacDet Φ (Function.update f i x) + 𝒢.jacDet Φ (Function.update f i y) := by
  let row : 𝒢.genStalk → Fin g → ℂ := fun t j => fderiv ℂ (𝒢.germAlong Φ t) 0 (Pi.single j 1)
  have hrow : row ((x + y : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.genStalk) =
      row (x : 𝒢.genStalk) + row (y : 𝒢.genStalk) := by
    funext j
    simp only [row, Submodule.coe_add, Pi.add_apply]
    rw [(germAlong_add_eventuallyEq 𝒢 hΦ _ _).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ _) (germAlong_differentiableAt 𝒢 hΦ _)]
    rfl
  let M : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k j => row (f k : 𝒢.genStalk) j
  have e : ∀ z : IsLocalRing.maximalIdeal 𝒢.genStalk,
      𝒢.jacDet Φ (Function.update f i z) = (M.updateRow i (row (z : 𝒢.genStalk))).det := by
    intro z
    unfold GroupModel.jacDet
    congr 1
    ext k j
    by_cases hk : k = i
    · subst hk; simp [M, row]
    · simp [M, row, hk]
  rw [e, e, e, hrow, Matrix.det_updateRow_add]

/-- **Clause (iv) of `JacDetMultilinear`, proved: equal slots give `0`.** -/
theorem jacDet_eq_zero_of_eq {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i j : Fin g) (h : f i = f j)
    (hij : i ≠ j) : 𝒢.jacDet Φ f = 0 := by
  unfold GroupModel.jacDet
  apply Matrix.det_zero_of_row_eq hij
  funext k
  simp [h]

end Germ

/-- **Glue (the two remaining clauses of `JacDetMultilinear`).** (i) `jacDet Φ f` depends only on
the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`; (iii) multiplying slot `i` by the image of `a ∈ 𝓞_L` multiplies
`jacDet` by `τ(a)`. Why true: by `germAlong_eventuallyEq` it suffices that for `f ∈ 𝔪_ξ²` the
function `evalAt (Φ z) U s` of a representative has derivative `0` at `0` (it is a sum of products
of functions vanishing at `0`, as evaluation at a complex point over `ξ` kills `𝔪_ξ`: the induced
map `𝒪_{𝒢,ξ} → 𝒪_{Spec ℂ} = ℂ` is local), and that the image of `a` evaluates to `τ(a)` (the point
lies over `Spec 𝓞_L` through `τ`). Unproved: needs `evalAt` through `Scheme.Hom.stalkMap` and
`ΓSpecIso`. -/
def JacDetClassScalar : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    (∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f') ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
      (x : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
        τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x))

/-- **`JacDetMultilinear` from `JacDetClassScalar` (proved).** -/
theorem jacDetMultilinear_of (h : JacDetClassScalar) : JacDetMultilinear := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  obtain ⟨h1, h3⟩ := h K A L 𝒢 τ g Λ Φ hΦ
  exact ⟨h1, fun f i x y => jacDet_update_add 𝒢 hΦ f i x y, h3,
    fun f i j hij hne => jacDet_eq_zero_of_eq 𝒢 Φ f i j hij hne⟩

end ZInQ.Metrization


/-! ## metrization: clause (iii) of `JacDetMultilinear` (scaling by `τ(a)`), proved -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section Scalar

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `evalAt` is multiplicative in the section. -/
theorem evalAt_mul {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s * s') = 𝒢.evalAt p U s * 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_mul]
    exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

/-- A function from `𝓞_L` evaluates to `τ(a)` at every complex point. -/
theorem evalAt_structSection {τ : L →+* ℂ} (p : 𝒢.Pts τ) (a : 𝓞 L) :
    𝒢.evalAt p ⊤ (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) =
      τ (algebraMap (𝓞 L) L a) := by
  have htop : ⊤ ≤ p.left ⁻¹ᵁ (⊤ : 𝒢.G.left.Opens) := fun x _ => trivial
  unfold GroupModel.evalAt
  rw [dif_pos htop]
  have hw : p.left ≫ 𝒢.G.hom = (GroupModel.ptC τ).hom := Over.w p
  have h1 : p.left.appLE ⊤ ⊤ htop = p.left.appTop := Scheme.Hom.appLE_eq_app p.left
  have h2 : (p.left.appTop) (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) =
      ((p.left ≫ 𝒢.G.hom).appTop) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a) := by
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [h1, h2, hw]
  have h3 := congrArg (fun f => f ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))))
  simp only [ConcreteCategory.comp_apply] at h3
  refine h3.trans ?_
  simp

/-- `germAlong Φ (structMap a * x) = τ(a) · germAlong Φ x` near `0`. -/
theorem germAlong_structMap_mul_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (a : 𝓞 L)
    (x : 𝒢.genStalk) :
    𝒢.germAlong Φ (𝒢.structMap a * x) =ᶠ[𝓝 0]
      fun z => τ (algebraMap (𝓞 L) L a) * 𝒢.germAlong Φ x z := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  set σa : Γ(𝒢.G.left, ⊤) :=
    𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a) with hσa
  have hprod : 𝒢.structMap a * 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s =
      𝒢.G.left.presheaf.germ U 𝒢.genericUnit m
        (𝒢.G.left.presheaf.map (homOfLE le_top).op σa * s) := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply]
    rfl
  rw [hprod]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ U m _, germAlong_eventuallyEq 𝒢 hΦ U m s,
    (hΦ.2.2.2.1 U).mem_nhds (zero_mem_dom 𝒢 hΦ U m)] with z h1 h2 hz
  rw [h1, h2, evalAt_mul, evalAt_res 𝒢 (Φ z) _ hz, hσa, evalAt_structSection]

/-- **Clause (iii) of `JacDetMultilinear`, proved: scaling by `τ(a)`.** -/
theorem jacDet_update_smul {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
    (x : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
      τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x) := by
  let row : 𝒢.genStalk → Fin g → ℂ := fun t j => fderiv ℂ (𝒢.germAlong Φ t) 0 (Pi.single j 1)
  have hrow : row ((𝒢.structMap a • x : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.genStalk) =
      τ (algebraMap (𝓞 L) L a) • row (x : 𝒢.genStalk) := by
    funext j
    simp only [row, Submodule.coe_smul, smul_eq_mul, Pi.smul_apply]
    rw [(germAlong_structMap_mul_eventuallyEq 𝒢 hΦ a _).fderiv_eq,
      fderiv_const_mul (germAlong_differentiableAt 𝒢 hΦ _)]
    rfl
  let M : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k j => row (f k : 𝒢.genStalk) j
  have e : ∀ z : IsLocalRing.maximalIdeal 𝒢.genStalk,
      𝒢.jacDet Φ (Function.update f i z) = (M.updateRow i (row (z : 𝒢.genStalk))).det := by
    intro z
    unfold GroupModel.jacDet
    congr 1
    ext k j
    by_cases hk : k = i
    · subst hk; simp [M, row]
    · simp [M, row, hk]
  rw [e, e, hrow, Matrix.det_updateRow_smul]

end Scalar

/-- **Glue (the last clause of `JacDetMultilinear`: class invariance).** `jacDet Φ f` depends
only on the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`. Why true: by `germAlong_eventuallyEq` and
`germAlong_add_eventuallyEq` it suffices that `d(germAlong Φ t)(0) = 0` for `t ∈ 𝔪_ξ²`, a sum of
products `uv` with `u, v ∈ 𝔪_ξ`; `germAlong Φ (uv) = (germAlong Φ u)(germAlong Φ v)` near `0` (as
for sums, with `evalAt_mul`), and `germAlong Φ u` vanishes at `0` because the identity point
`Spec ℂ → 𝒢` lies over `ξ` (`one_left_apply`) and induces a local map `𝒪_{𝒢,ξ} → 𝒪_{Spec ℂ} = ℂ`,
which kills `𝔪_ξ`; then Leibniz. Unproved (needs `evalAt` through `Scheme.Hom.stalkMap` at the
identity point). -/
def JacDetClassInvariant : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f'

/-- **`JacDetClassScalar` from `JacDetClassInvariant` (proved).** -/
theorem jacDetClassScalar_of (h : JacDetClassInvariant) : JacDetClassScalar := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  exact ⟨h K A L 𝒢 τ g Λ Φ hΦ, fun f i a x => jacDet_update_smul 𝒢 hΦ f i a x⟩

end ZInQ.Metrization


/-! ## metrization: clause (i) of `JacDetMultilinear` (class invariance), proved

So `JacDetMultilinear`, hence `JacDetDescends`, is a theorem. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section ClassInv

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- A section whose germ at `ξ` lies in `𝔪_ξ` vanishes at the identity complex point. -/
theorem evalAt_one_eq_zero {τ : L →+* ℂ} (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U)
    (s : Γ(𝒢.G.left, U))
    (hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.evalAt (1 : 𝒢.Pts τ) U s = 0 := by
  set q := (1 : 𝒢.Pts τ).left with hqdef
  have hq : ∀ x, q x = 𝒢.genericUnit := fun x => by
    rw [hqdef]
    erw [one_left_apply]
  have h : ⊤ ≤ q ⁻¹ᵁ U := by
    intro x _
    show q x ∈ U
    rw [hq]
    exact m
  unfold GroupModel.evalAt
  rw [dif_pos h]
  let q' : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left := q
  have h' : ⊤ ≤ q' ⁻¹ᵁ U := h
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q'.appLE U ⊤ h' s) = 0
  let x : Spec (CommRingCat.of ℂ) := genericPoint (Spec (CommRingCat.of ℂ))
  have hxt : x ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) := by simp
  have hx : q' x ∈ U := h' hxt
  have key : q'.appLE U ⊤ h' ≫ (Spec (CommRingCat.of ℂ)).presheaf.germ ⊤ x hxt =
      𝒢.G.left.presheaf.germ U (q' x) hx ≫ q'.stalkMap x := by
    simp only [Scheme.Hom.appLE, Category.assoc, Scheme.Hom.germ_stalkMap]
    rw [TopCat.Presheaf.germ_res]
  have hmem : ∀ (y : 𝒢.G.left) (hy : y ∈ U), y = 𝒢.genericUnit →
      𝒢.G.left.presheaf.germ U y hy s ∈
        IsLocalRing.maximalIdeal (𝒢.G.left.presheaf.stalk y) := by
    rintro y hy rfl
    exact hs
  have h1 := hmem (q' x) hx (hq x)
  have h2 : (q'.stalkMap x).hom (𝒢.G.left.presheaf.germ U (q' x) hx s) ∈
      IsLocalRing.maximalIdeal ((Spec (CommRingCat.of ℂ)).presheaf.stalk x) :=
    map_nonunit _ _ ((IsLocalRing.mem_maximalIdeal _).mp h1)
  have hfield : IsField ((Spec (CommRingCat.of ℂ)).presheaf.stalk x) := Field.toIsField _
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield] at h2
  have h4 : ((Spec (CommRingCat.of ℂ)).presheaf.germ ⊤ x hxt) (q'.appLE U ⊤ h' s) =
      (q'.stalkMap x) (𝒢.G.left.presheaf.germ U (q' x) hx s) := by
    rw [← ConcreteCategory.comp_apply, key, ConcreteCategory.comp_apply]
  have h5 : q'.appLE U ⊤ h' s = 0 := by
    apply germ_injective_of_isIntegral (U := ⊤) _ x hxt
    rw [map_zero]
    exact h4.trans h2
  rw [h5, map_zero]

/-- `germAlong Φ u` vanishes at `0` for `u ∈ 𝔪_ξ`. -/
theorem germAlong_zero_of_mem {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (u : 𝒢.genStalk)
    (hu : u ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.germAlong Φ u 0 = 0 := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep u
  have h1 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  rw [(germAlong_eventuallyEq 𝒢 hΦ U m s).eq_of_nhds, h1]
  exact evalAt_one_eq_zero 𝒢 U m s hu

/-- `germAlong Φ (x * y) = germAlong Φ x * germAlong Φ y` near `0`. -/
theorem germAlong_mul_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x y : 𝒢.genStalk) :
    𝒢.germAlong Φ (x * y) =ᶠ[𝓝 0] 𝒢.germAlong Φ x * 𝒢.germAlong Φ y := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep y
  have mm : 𝒢.genericUnit ∈ U ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hprod : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s *
      𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' =
      𝒢.G.left.presheaf.germ (U ⊓ U') 𝒢.genericUnit mm
        (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s *
          𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') := by
    simp only [map_mul, TopCat.Presheaf.germ_res_apply]
  rw [hprod]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ (U ⊓ U') mm _,
    germAlong_eventuallyEq 𝒢 hΦ U m s, germAlong_eventuallyEq 𝒢 hΦ U' m' s',
    (hΦ.2.2.2.1 (U ⊓ U')).mem_nhds (zero_mem_dom 𝒢 hΦ (U ⊓ U') mm)] with z h1 h2 h3 hz
  rw [Pi.mul_apply, h1, h2, h3, evalAt_mul, evalAt_res 𝒢 (Φ z) _ hz,
    evalAt_res 𝒢 (Φ z) _ hz]

/-- `d(germAlong Φ t)(0) = 0` for `t ∈ 𝔪_ξ²`. -/
theorem fderiv_germAlong_eq_zero_of_mem_sq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk)
    (ht : t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ^ 2) :
    fderiv ℂ (𝒢.germAlong Φ t) 0 = 0 := by
  rw [pow_two] at ht
  refine Submodule.mul_induction_on ht (fun u hu v hv => ?_) (fun a b ha hb => ?_)
  · rw [(germAlong_mul_eventuallyEq 𝒢 hΦ u v).fderiv_eq,
      fderiv_mul (germAlong_differentiableAt 𝒢 hΦ u) (germAlong_differentiableAt 𝒢 hΦ v),
      germAlong_zero_of_mem 𝒢 hΦ u hu, germAlong_zero_of_mem 𝒢 hΦ v hv]
    ext v
    simp
  · rw [(germAlong_add_eventuallyEq 𝒢 hΦ a b).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ a) (germAlong_differentiableAt 𝒢 hΦ b), ha, hb,
      add_zero]

/-- **Clause (i) of `JacDetMultilinear`, proved: `jacDet` depends only on the classes `df_i`.** -/
theorem jacDet_congr_dCls {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk)
    (h : ∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) : 𝒢.jacDet Φ f = 𝒢.jacDet Φ f' := by
  have hrow : ∀ i, fderiv ℂ (𝒢.germAlong Φ (f i : 𝒢.genStalk)) 0 =
      fderiv ℂ (𝒢.germAlong Φ (f' i : 𝒢.genStalk)) 0 := by
    intro i
    have hsq : ((f i : 𝒢.genStalk) - f' i) ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ^ 2 :=
      (Ideal.toCotangent_eq (IsLocalRing.maximalIdeal 𝒢.genStalk)).mp (h i)
    have hdecomp : (f i : 𝒢.genStalk) = f' i + ((f i : 𝒢.genStalk) - f' i) := by ring
    rw [hdecomp, (germAlong_add_eventuallyEq 𝒢 hΦ _ _).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ _) (germAlong_differentiableAt 𝒢 hΦ _),
      fderiv_germAlong_eq_zero_of_mem_sq 𝒢 hΦ _ hsq, add_zero]
  unfold GroupModel.jacDet
  congr 1
  ext i j
  simp only [Matrix.of_apply, hrow i]

end ClassInv

/-- **`JacDetClassInvariant`, proved.** -/
theorem jacDetClassInvariant : JacDetClassInvariant := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ f f' h
  exact jacDet_congr_dCls 𝒢 hΦ f f' h

/-- **`JacDetDescends`, proved** (no hypotheses). -/
theorem jacDetDescends : JacDetDescends :=
  jacDetDescends_of (jacDetMultilinear_of (jacDetClassScalar_of jacDetClassInvariant))

/-- **`MetrizationExists` from `HodgeLatticeTheorem`, the leaf `AnalyticUniformizationOfDim` and
the glue `JacDetNondegenerate`.** -/
theorem metrizationExists_of' (hH : HodgeLatticeTheorem) (hU : AnalyticUniformizationOfDim)
    (hN : JacDetNondegenerate) : ZInQ.G0HeightAdd.MetrizationExists :=
  metrizationExists_of hH hU jacDetDescends hN

/-- **`ProductMetrizationGeo` from `ProductUniformizationAnalytic`, `ProductHodgeLattice` and
`ProductJacobian`.** -/
theorem productMetrizationGeo_of'' (hPA : ProductUniformizationAnalytic)
    (hPL : ProductHodgeLattice) (hPJ : ProductJacobian) :
    ZInQ.G0HeightAdd.ProductMetrizationGeo :=
  productMetrizationGeo_of' jacDetDescends (productUniformization_of hPA)
    (productHodgeCompat_of (productUniformization_of hPA) hPL hPJ)

end ZInQ.Metrization

namespace HSyn.G0Split

/-- **`HeightAdditivity` after task metrization (final).** -/
theorem heightAdditivity_of_metrization_final (hN1 : ZInQ.H5Neron.NeronModelExists)
    (h5 : LeafAdopt.H5) (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hUD : ZInQ.Metrization.AnalyticUniformizationOfDim)
    (hN : ZInQ.Metrization.JacDetNondegenerate)
    (hPA : ZInQ.Metrization.ProductUniformizationAnalytic)
    (hPL : ZInQ.Metrization.ProductHodgeLattice) (hPJ : ZInQ.Metrization.ProductJacobian) :
    HeightAdditivity :=
  heightAdditivity_of_geo hN1 h5 hU ZInQ.Metrization.metrizationDimUnique
    (ZInQ.Metrization.metrizationExists_of' hH hUD hN)
    (ZInQ.Metrization.productMetrizationGeo_of'' hPA hPL hPJ)

end HSyn.G0Split


/-! ## metrization: `ProductJacobian`, proved (block-diagonal Jacobian of `prodPts`) -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section ProdJac

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- Pull-back of a germ is the germ of the pulled-back section. -/
theorem pullGerm_germ {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G) [IsMonHom φ]
    (U : ℋ.G.left.Opens) (m : ℋ.genericUnit ∈ U) (s : Γ(ℋ.G.left, U)) :
    (pullGerm φ).hom (ℋ.G.left.presheaf.germ U ℋ.genericUnit m s) =
      𝒢.G.left.presheaf.germ (φ.left ⁻¹ᵁ U) 𝒢.genericUnit
        (by show φ.left 𝒢.genericUnit ∈ U; rw [map_genericUnit_of_isMonHom φ]; exact m)
        (φ.left.app U s) := by
  unfold pullGerm
  rw [ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

/-- `evalAt` along a morphism of models. -/
theorem evalAt_comp {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G) {τ : L →+* ℂ}
    (p : 𝒢.Pts τ) (U : ℋ.G.left.Opens) (s : Γ(ℋ.G.left, U))
    (hp : ⊤ ≤ p.left ⁻¹ᵁ (φ.left ⁻¹ᵁ U)) :
    𝒢.evalAt p (φ.left ⁻¹ᵁ U) (φ.left.app U s) = ℋ.evalAt (p ≫ φ) U s := by
  have hp' : ⊤ ≤ (p ≫ φ).left ⁻¹ᵁ U := hp
  unfold GroupModel.evalAt
  rw [dif_pos hp, dif_pos hp']
  rw [show (p ≫ φ).left.appLE U ⊤ hp' = φ.left.app U ≫ p.left.appLE (φ.left ⁻¹ᵁ U) ⊤ hp from
    Scheme.Hom.comp_appLE p.left φ.left U ⊤ hp']
  rfl

variable {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
  {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
  {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}

theorem germAlong_pull_fst_eventuallyEq (hΦ₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (hΦP : 𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂))
    (t : 𝒢₁.genStalk) :
    𝒢P.germAlong (prodPts e Φ₁ Φ₂) ((pullGerm (e.hom ≫ fst _ _)).hom t) =ᶠ[𝓝 0]
      fun z => 𝒢₁.germAlong Φ₁ t (leftBlock g₁ g₂ z) := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢₁.exists_rep t
  rw [pullGerm_germ]
  have ht : Filter.Tendsto (leftBlock g₁ g₂) (𝓝 0) (𝓝 0) :=
    (leftBlock g₁ g₂).continuous_of_finiteDimensional.tendsto' 0 0 (map_zero _)
  filter_upwards [germAlong_eventuallyEq 𝒢P hΦP _ _ _,
    (germAlong_eventuallyEq 𝒢₁ hΦ₁ U m s).comp_tendsto ht,
    (hΦP.2.2.2.1 _).mem_nhds (zero_mem_dom 𝒢P hΦP ((e.hom ≫ fst _ _).left ⁻¹ᵁ U)
      (by show (e.hom ≫ fst _ _).left 𝒢P.genericUnit ∈ U
          rw [map_genericUnit_of_isMonHom]; exact m))] with z h1 h2 hz
  have h2' : 𝒢₁.germAlong Φ₁ (𝒢₁.G.left.presheaf.germ U 𝒢₁.genericUnit m s) (leftBlock g₁ g₂ z) =
      𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) U s := h2
  rw [h1, h2', evalAt_comp _ _ _ _ hz, prodPts_comp_fst]

theorem germAlong_pull_snd_eventuallyEq (hΦ₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂)
    (hΦP : 𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂))
    (t : 𝒢₂.genStalk) :
    𝒢P.germAlong (prodPts e Φ₁ Φ₂) ((pullGerm (e.hom ≫ snd _ _)).hom t) =ᶠ[𝓝 0]
      fun z => 𝒢₂.germAlong Φ₂ t (rightBlock g₁ g₂ z) := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢₂.exists_rep t
  rw [pullGerm_germ]
  have ht : Filter.Tendsto (rightBlock g₁ g₂) (𝓝 0) (𝓝 0) :=
    (rightBlock g₁ g₂).continuous_of_finiteDimensional.tendsto' 0 0 (map_zero _)
  filter_upwards [germAlong_eventuallyEq 𝒢P hΦP _ _ _,
    (germAlong_eventuallyEq 𝒢₂ hΦ₂ U m s).comp_tendsto ht,
    (hΦP.2.2.2.1 _).mem_nhds (zero_mem_dom 𝒢P hΦP ((e.hom ≫ snd _ _).left ⁻¹ᵁ U)
      (by show (e.hom ≫ snd _ _).left 𝒢P.genericUnit ∈ U
          rw [map_genericUnit_of_isMonHom]; exact m))] with z h1 h2 hz
  have h2' : 𝒢₂.germAlong Φ₂ (𝒢₂.G.left.presheaf.germ U 𝒢₂.genericUnit m s) (rightBlock g₁ g₂ z) =
      𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) U s := h2
  rw [h1, h2', evalAt_comp _ _ _ _ hz, prodPts_comp_snd]

/-- Derivative of `F ∘ ℓ` for a linear `ℓ` on `ℂ^{g₁+g₂}` (chain rule). -/
theorem fderiv_comp_linear {n : ℕ} (ℓ : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (F : (Fin n → ℂ) → ℂ) (hF : DifferentiableAt ℂ F 0) (w : Fin (g₁ + g₂) → ℂ) :
    fderiv ℂ (fun z => F (ℓ z)) 0 w = fderiv ℂ F 0 (ℓ w) := by
  let ℓc := LinearMap.toContinuousLinearMap ℓ
  have hfun : (fun z => F (ℓ z)) = F ∘ ℓc := by
    funext z; simp [ℓc]
  have hF' : DifferentiableAt ℂ F (ℓc 0) := by rw [map_zero]; exact hF
  rw [hfun, fderiv_comp _ hF' ℓc.differentiableAt, ContinuousLinearMap.fderiv, map_zero]
  simp [ℓc]

end ProdJac

/-- **`ProductJacobian`, proved.** -/
theorem productJacobian : ProductJacobian := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ hΦ₁ hΦ₂ hΦP f₁ f₂ f hf1 hf2
  have hl : ∀ (i : Fin g₁) (w : Fin (g₁ + g₂) → ℂ),
      fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f (Fin.castAdd g₂ i) : 𝒢P.genStalk)) 0 w =
        fderiv ℂ (𝒢₁.germAlong Φ₁ (f₁ i : 𝒢₁.genStalk)) 0 (leftBlock g₁ g₂ w) := by
    intro i w
    rw [hf1 i, (germAlong_pull_fst_eventuallyEq e hΦ₁ hΦP _).fderiv_eq]
    exact fderiv_comp_linear (leftBlock g₁ g₂) _ (germAlong_differentiableAt 𝒢₁ hΦ₁ _) w
  have hr : ∀ (j : Fin g₂) (w : Fin (g₁ + g₂) → ℂ),
      fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f (Fin.natAdd g₁ j) : 𝒢P.genStalk)) 0 w =
        fderiv ℂ (𝒢₂.germAlong Φ₂ (f₂ j : 𝒢₂.genStalk)) 0 (rightBlock g₁ g₂ w) := by
    intro j w
    rw [hf2 j, (germAlong_pull_snd_eventuallyEq e hΦ₂ hΦP _).fderiv_eq]
    exact fderiv_comp_linear (rightBlock g₁ g₂) _ (germAlong_differentiableAt 𝒢₂ hΦ₂ _) w
  have hL1 : ∀ j : Fin g₁, leftBlock g₁ g₂ (Pi.single (Fin.castAdd g₂ j) 1) = Pi.single j 1 := by
    intro j; funext k; simp [Pi.single_apply]
  have hL2 : ∀ j : Fin g₂, leftBlock g₁ g₂ (Pi.single (Fin.natAdd g₁ j) 1) = 0 := by
    intro j; funext k; simp [Pi.single_apply, Fin.ext_iff]; omega
  have hR1 : ∀ j : Fin g₁, rightBlock g₁ g₂ (Pi.single (Fin.castAdd g₂ j) 1) = 0 := by
    intro j; funext k; simp [Pi.single_apply, Fin.ext_iff]; omega
  have hR2 : ∀ j : Fin g₂, rightBlock g₁ g₂ (Pi.single (Fin.natAdd g₁ j) 1) = Pi.single j 1 := by
    intro j; funext k; simp [Pi.single_apply]
  let J₁ : Matrix (Fin g₁) (Fin g₁) ℂ :=
    Matrix.of fun i j => fderiv ℂ (𝒢₁.germAlong Φ₁ (f₁ i : 𝒢₁.genStalk)) 0 (Pi.single j 1)
  let J₂ : Matrix (Fin g₂) (Fin g₂) ℂ :=
    Matrix.of fun i j => fderiv ℂ (𝒢₂.germAlong Φ₂ (f₂ i : 𝒢₂.genStalk)) 0 (Pi.single j 1)
  have hblock : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      (Matrix.of fun i j : Fin (g₁ + g₂) =>
        fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f i : 𝒢P.genStalk)) 0 (Pi.single j 1)) =
      Matrix.fromBlocks J₁ 0 0 J₂ := by
    ext (i | i) (j | j)
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, J₁]
      rw [hl, hL1 j]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.of_apply,
        Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      rw [hl, hL2, map_zero]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.of_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [hr, hR1, map_zero]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_right, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, J₂]
      rw [hr, hR2]
  unfold GroupModel.jacDet
  rw [← Matrix.det_reindex_self finSumFinEquiv.symm, hblock, Matrix.det_fromBlocks_zero₂₁]

/-- **`ProductMetrizationGeo` from `ProductUniformizationAnalytic` and `ProductHodgeLattice`.** -/
theorem productMetrizationGeo_of''' (hPA : ProductUniformizationAnalytic)
    (hPL : ProductHodgeLattice) : ZInQ.G0HeightAdd.ProductMetrizationGeo :=
  productMetrizationGeo_of'' hPA hPL productJacobian

end ZInQ.Metrization

namespace HSyn.G0Split

/-- **`HeightAdditivity` after task metrization (final form).** -/
theorem heightAdditivity_of_metrization_v2 (hN1 : ZInQ.H5Neron.NeronModelExists)
    (h5 : LeafAdopt.H5) (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hUD : ZInQ.Metrization.AnalyticUniformizationOfDim)
    (hN : ZInQ.Metrization.JacDetNondegenerate)
    (hPA : ZInQ.Metrization.ProductUniformizationAnalytic)
    (hPL : ZInQ.Metrization.ProductHodgeLattice) : HeightAdditivity :=
  heightAdditivity_of_geo hN1 h5 hU ZInQ.Metrization.metrizationDimUnique
    (ZInQ.Metrization.metrizationExists_of' hH hUD hN)
    (ZInQ.Metrization.productMetrizationGeo_of''' hPA hPL)

end HSyn.G0Split


/-! ## metrization: `ProductUniformizationAnalytic` reduced to a statement about complex points

`ProductLocalStructure` (pure algebraic geometry, no analysis): near a complex point of
`𝒢₁ × 𝒢₂`, membership in a Zariski open `U` and a regular function on `U` are given, on
`V₁(ℂ) × V₂(ℂ)`, by sums of products of regular functions on opens `V₁ ⊂ 𝒢₁`, `V₂ ⊂ 𝒢₂`. The
analytic consequences (openness of `dom`, holomorphy) are proved. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

/-- **Glue (local product structure of `𝒢₁ ×_{𝓞_L} 𝒢₂` at complex points).** For
`e : 𝒢P ≅ 𝒢₁ × 𝒢₂`, an open `U ⊂ 𝒢P`, `s ∈ Γ(U)` and complex points `p₁`, `p₂` with
`e⁻¹(p₁, p₂) ∈ U(ℂ)`, there are opens `V₁ ∋ p₁`, `V₂ ∋ p₂` and regular functions
`a_k, c_k` on `V₁`, `b_k, d_k` on `V₂` such that `H = Σ c_k ⊗ d_k` does not vanish at `(p₁, p₂)`,
and at every `(p₁', p₂') ∈ V₁(ℂ) × V₂(ℂ)` with `H(p₁', p₂') ≠ 0`: `e⁻¹(p₁', p₂') ∈ U(ℂ)` and
`s(e⁻¹(p₁', p₂')) · H(p₁', p₂') = Σ a_k(p₁') b_k(p₂')`. Why true (STANDARD): take affine
`V₁ = Spec R₁`, `V₂ = Spec R₂` (over the affine `Spec 𝓞_L`), so `V₁ ×_{𝓞_L} V₂ = Spec(R₁ ⊗ R₂)`
is open in the product; choose a basic open `D(h)` of it with `(p₁, p₂) ∈ D(h) ⊆ e(U)`,
`h ∈ R₁ ⊗ R₂`; on `D(h)`, `s = a/h^m` with `a ∈ R₁ ⊗ R₂`; take `H = h^m` and expand `H` and `a`
as sums of pure tensors; a pure tensor `c ⊗ d` evaluates at `(p₁', p₂')` to `c(p₁') d(p₂')`.
Unproved (needs Mathlib's affine opens of pullbacks and sections on basic opens). -/
def ProductLocalStructure : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (τ : L →+* ℂ) (U : 𝒢P.G.left.Opens) (s : Γ(𝒢P.G.left, U))
    (p₁ : 𝒢₁.Pts τ) (p₂ : 𝒢₂.Pts τ), ⊤ ≤ (lift p₁ p₂ ≫ e.inv).left ⁻¹ᵁ U →
    ∃ (V₁ : 𝒢₁.G.left.Opens) (V₂ : 𝒢₂.G.left.Opens) (n : ℕ)
      (a c : Fin n → Γ(𝒢₁.G.left, V₁)) (b d : Fin n → Γ(𝒢₂.G.left, V₂)),
      ⊤ ≤ p₁.left ⁻¹ᵁ V₁ ∧ ⊤ ≤ p₂.left ⁻¹ᵁ V₂ ∧
      (∑ k, 𝒢₁.evalAt p₁ V₁ (c k) * 𝒢₂.evalAt p₂ V₂ (d k)) ≠ 0 ∧
      ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), ⊤ ≤ p₁'.left ⁻¹ᵁ V₁ → ⊤ ≤ p₂'.left ⁻¹ᵁ V₂ →
        (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) ≠ 0 →
        ⊤ ≤ (lift p₁' p₂' ≫ e.inv).left ⁻¹ᵁ U ∧
        𝒢P.evalAt (lift p₁' p₂' ≫ e.inv) U s *
            (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) =
          ∑ k, 𝒢₁.evalAt p₁' V₁ (a k) * 𝒢₂.evalAt p₂' V₂ (b k)

section Local

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)}
  {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)} {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}

theorem leftBlock_differentiable : Differentiable ℂ (leftBlock g₁ g₂) := by
  have h := (LinearMap.toContinuousLinearMap (leftBlock g₁ g₂)).differentiable
  simpa using h

theorem rightBlock_differentiable : Differentiable ℂ (rightBlock g₁ g₂) := by
  have h := (LinearMap.toContinuousLinearMap (rightBlock g₁ g₂)).differentiable
  simpa using h

/-- The local statement: every point of `dom (prodPts) U` has an open neighbourhood inside
`dom (prodPts) U` on which `z ↦ s(prodPts z)` is holomorphic. -/
theorem prodPts_local (hLS : ProductLocalStructure) (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) (U : 𝒢P.G.left.Opens) (s : Γ(𝒢P.G.left, U))
    (z₀ : Fin (g₁ + g₂) → ℂ) (hz₀ : z₀ ∈ 𝒢P.dom (prodPts e Φ₁ Φ₂) U) :
    ∃ N : Set (Fin (g₁ + g₂) → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ 𝒢P.dom (prodPts e Φ₁ Φ₂) U ∧
      DifferentiableOn ℂ (fun z => 𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s) N := by
  obtain ⟨V₁, V₂, n, a, c, b, d, hV₁, hV₂, hne, hall⟩ :=
    hLS K A B C L 𝒢P 𝒢₁ 𝒢₂ e τ U s (Φ₁ (leftBlock g₁ g₂ z₀)) (Φ₂ (rightBlock g₁ g₂ z₀)) hz₀
  let O : Set (Fin (g₁ + g₂) → ℂ) :=
    leftBlock g₁ g₂ ⁻¹' 𝒢₁.dom Φ₁ V₁ ∩ rightBlock g₁ g₂ ⁻¹' 𝒢₂.dom Φ₂ V₂
  have hO : IsOpen O :=
    ((h₁.2.2.2.1 V₁).preimage (leftBlock_differentiable).continuous).inter
      ((h₂.2.2.2.1 V₂).preimage (rightBlock_differentiable).continuous)
  have hd1 : ∀ σ : Γ(𝒢₁.G.left, V₁),
      DifferentiableOn ℂ (fun z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ σ) O := fun σ =>
    (h₁.2.2.2.2 V₁ σ).comp (leftBlock_differentiable).differentiableOn (fun z hz => hz.1)
  have hd2 : ∀ σ : Γ(𝒢₂.G.left, V₂),
      DifferentiableOn ℂ (fun z => 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ σ) O := fun σ =>
    (h₂.2.2.2.2 V₂ σ).comp (rightBlock_differentiable).differentiableOn (fun z hz => hz.2)
  let H : (Fin (g₁ + g₂) → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (c k) * 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (d k)
  let Afun : (Fin (g₁ + g₂) → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (a k) * 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (b k)
  have hH : DifferentiableOn ℂ H O := by
    have := DifferentiableOn.sum (u := Finset.univ)
      (A := fun k z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (c k) *
        𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (d k))
      (fun k _ => (hd1 (c k)).mul (hd2 (d k)))
    convert this using 1
    funext z
    simp [H, Finset.sum_apply]
  have hA : DifferentiableOn ℂ Afun O := by
    have := DifferentiableOn.sum (u := Finset.univ)
      (A := fun k z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (a k) *
        𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (b k))
      (fun k _ => (hd1 (a k)).mul (hd2 (b k)))
    convert this using 1
    funext z
    simp [Afun, Finset.sum_apply]
  let N := O ∩ H ⁻¹' {0}ᶜ
  have hN : IsOpen N := hH.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  have hsub : ∀ z ∈ N, z ∈ 𝒢P.dom (prodPts e Φ₁ Φ₂) U ∧
      𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s = Afun z / H z := by
    intro z hz
    obtain ⟨hmem, heq⟩ := hall _ _ hz.1.1 hz.1.2 hz.2
    refine ⟨hmem, ?_⟩
    rw [eq_div_iff hz.2]
    exact heq
  refine ⟨N, hN, ⟨⟨hV₁, hV₂⟩, hne⟩, fun z hz => (hsub z hz).1, ?_⟩
  have hdiv : DifferentiableOn ℂ (fun z => Afun z * (H z)⁻¹) N :=
    (hA.mono Set.inter_subset_left).mul
      ((hH.mono Set.inter_subset_left).inv (fun z hz => hz.2))
  refine hdiv.congr fun z hz => ?_
  rw [(hsub z hz).2, div_eq_mul_inv]

end Local

/-- **`ProductUniformizationAnalytic` from `ProductLocalStructure` (proved).** -/
theorem productUniformizationAnalytic_of (hLS : ProductLocalStructure) :
    ProductUniformizationAnalytic := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  refine ⟨fun U => ?_, fun U s => ?_⟩
  · rw [isOpen_iff_forall_mem_open]
    intro z₀ hz₀
    obtain ⟨N, hN, hz₀N, hsub, -⟩ := prodPts_local e hLS h₁ h₂ U 0 z₀ hz₀
    exact ⟨N, hsub, hN, hz₀N⟩
  · intro z₀ hz₀
    obtain ⟨N, hN, hz₀N, -, hd⟩ := prodPts_local e hLS h₁ h₂ U s z₀ hz₀
    exact ((hd z₀ hz₀N).differentiableAt (hN.mem_nhds hz₀N)).differentiableWithinAt

/-- **`ProductMetrizationGeo` from `ProductLocalStructure` and `ProductHodgeLattice`.** -/
theorem productMetrizationGeo_of_local (hLS : ProductLocalStructure)
    (hPL : ProductHodgeLattice) : ZInQ.G0HeightAdd.ProductMetrizationGeo :=
  productMetrizationGeo_of''' (productUniformizationAnalytic_of hLS) hPL

end ZInQ.Metrization

namespace HSyn.G0Split

/-- **`HeightAdditivity` after task metrization (final form, v3).** -/
theorem heightAdditivity_of_metrization_v3 (hN1 : ZInQ.H5Neron.NeronModelExists)
    (h5 : LeafAdopt.H5) (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hUD : ZInQ.Metrization.AnalyticUniformizationOfDim)
    (hN : ZInQ.Metrization.JacDetNondegenerate)
    (hLS : ZInQ.Metrization.ProductLocalStructure)
    (hPL : ZInQ.Metrization.ProductHodgeLattice) : HeightAdditivity :=
  heightAdditivity_of_metrization_v2 hN1 h5 hU hH hUD hN
    (ZInQ.Metrization.productUniformizationAnalytic_of hLS) hPL

end HSyn.G0Split

/-! ## metrization2: `JacDetNondegenerate` from the local structure of morphisms out of a product

Step 1 (linear algebra): if every `jacDet Φ f` vanishes, some `v ≠ 0` is killed by
`d(germAlong Φ t)(0)` for every `t ∈ 𝔪_ξ`. Step 2: then by every regular function near `ξ`
(subtract the pull-back along `𝒢 → Spec 𝓞_L` of its restriction to the unit section). -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology

/-- Step 1 (pure linear algebra). If every `g × g` matrix whose rows are taken from a family
`F` of vectors of `ℂ^g` has determinant `0`, a nonzero vector is orthogonal (for the bilinear
pairing `Σ_j x_j y_j`) to every member of the family. -/
theorem exists_null_of_det_eq_zero {J : Type*} {g : ℕ} (F : J → (Fin g → ℂ))
    (h : ∀ f : Fin g → J, (Matrix.of fun i j => F (f i) j).det = 0) :
    ∃ v : Fin g → ℂ, v ≠ 0 ∧ ∀ i, ∑ j, F i j * v j = 0 := by
  by_cases hW : Submodule.span ℂ (Set.range F) = ⊤
  · exfalso
    obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ F
    rw [hW] at hspan
    have : Finite κ := hli.finite
    haveI := Fintype.ofFinite κ
    have hcard : Fintype.card κ = g := by
      rw [linearIndependent_iff_card_eq_finrank_span.mp hli, Set.finrank, hspan, finrank_top,
        Module.finrank_fin_fun]
    let eqv : Fin g ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    have hli' : LinearIndependent ℂ ((F ∘ a) ∘ eqv) := hli.comp eqv eqv.injective
    have hU : IsUnit (Matrix.of fun i j => F (a (eqv i)) j) :=
      Matrix.linearIndependent_row_iff_isUnit.mp hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero (h (a ∘ eqv))
  · obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hW)
    refine ⟨fun j => φ (fun k => if j = k then 1 else 0), ?_, ?_⟩
    · intro hv
      apply hφ0
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      simp only [LinearMap.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := congrFun hv j
      simp only [Pi.zero_apply] at this
      rw [this, smul_zero]
    · intro i
      have h1 := hle (Submodule.subset_span ⟨i, rfl⟩)
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at h1
      simpa [smul_eq_mul] using h1

section Eval

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- The value at the complex point `Spec ℂ → Spec 𝓞_L` (via `τ`) of a function on an open of
`Spec 𝓞_L` (`0` off the open). -/
noncomputable def baseVal (τ : L →+* ℂ) (O : (Spec (CommRingCat.of (𝓞 L))).Opens)
    (x : Γ(Spec (CommRingCat.of (𝓞 L)), O)) : ℂ := by
  classical
  exact if h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O then
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((GroupModel.ptC (L := L) τ).hom.appLE O ⊤ h x)
  else 0

/-- A function pulled back from `Spec 𝓞_L` takes the same value at every complex point. -/
theorem evalAt_pullback_base {τ : L →+* ℂ} (p : 𝒢.Pts τ) (O : (Spec (CommRingCat.of (𝓞 L))).Opens)
    (x : Γ(Spec (CommRingCat.of (𝓞 L)), O)) :
    𝒢.evalAt p (𝒢.G.hom ⁻¹ᵁ O) (𝒢.G.hom.app O x) = baseVal τ O x := by
  have hw : p.left ≫ 𝒢.G.hom = (GroupModel.ptC τ).hom := Over.w p
  have hpre : p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) = (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O := by
    rw [← hw]; rfl
  unfold GroupModel.evalAt baseVal
  by_cases h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O
  · have h' : ⊤ ≤ p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) := hpre ▸ h
    rw [dif_pos h', dif_pos h]
    congr 1
    have key : ∀ (f : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (𝓞 L)))
        (hf : f = (GroupModel.ptC (L := L) τ).hom) (e : ⊤ ≤ f ⁻¹ᵁ O),
        f.appLE O ⊤ e x = (GroupModel.ptC (L := L) τ).hom.appLE O ⊤ h x := by
      rintro f rfl e; rfl
    have h'' : ⊤ ≤ (p.left ≫ 𝒢.G.hom) ⁻¹ᵁ O := h'
    refine Eq.trans ?_ (key _ hw h'')
    have hc := Scheme.Hom.comp_appLE p.left 𝒢.G.hom O ⊤ h''
    exact congrArg (fun φ => (ConcreteCategory.hom φ) x) hc.symm
  · have h' : ¬ ⊤ ≤ p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) := fun h' => h (hpre ▸ h')
    rw [dif_neg h', dif_neg h]

/-- A complex point factoring as `Spec ℂ → Spec 𝓞_L → 𝒢` evaluates through the section. -/
theorem evalAt_of_left_eq {τ : L →+* ℂ} (p : 𝒢.Pts τ)
    (f : Spec (CommRingCat.of (𝓞 L)) ⟶ 𝒢.G.left) (hp : p.left = (GroupModel.ptC τ).hom ≫ f)
    (V : 𝒢.G.left.Opens) (b : Γ(𝒢.G.left, V)) :
    𝒢.evalAt p V b = baseVal τ (f ⁻¹ᵁ V) (f.app V b) := by
  have hpre : p.left ⁻¹ᵁ V = (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [hp]; rfl
  unfold GroupModel.evalAt baseVal
  by_cases h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ (f ⁻¹ᵁ V)
  · have h' : ⊤ ≤ p.left ⁻¹ᵁ V := hpre ▸ h
    rw [dif_pos h', dif_pos h]
    congr 1
    have key : ∀ (q : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left)
        (hq : q = (GroupModel.ptC (L := L) τ).hom ≫ f) (e : ⊤ ≤ q ⁻¹ᵁ V),
        q.appLE V ⊤ e b = ((GroupModel.ptC (L := L) τ).hom ≫ f).appLE V ⊤ h b := by
      rintro q rfl e; rfl
    refine (key _ hp h').trans ?_
    have hc := Scheme.Hom.comp_appLE (GroupModel.ptC (L := L) τ).hom f V ⊤ h
    exact congrArg (fun φ => (ConcreteCategory.hom φ) b) hc
  · have h' : ¬ ⊤ ≤ p.left ⁻¹ᵁ V := fun h' => h (hpre ▸ h')
    rw [dif_neg h', dif_neg h]

/-- `(1 : 𝒢(ℂ)_τ)` is `Spec ℂ → Spec 𝓞_L → 𝒢` through the unit section. -/
theorem one_left_eq (τ : L →+* ℂ) :
    (1 : 𝒢.Pts τ).left = (GroupModel.ptC τ).hom ≫ 𝒢.unitSection := by
  have hw : (toUnit (GroupModel.ptC (L := L) τ)).left = (GroupModel.ptC (L := L) τ).hom :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (GroupModel.ptC (L := L) τ)))
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left = _
  rw [Over.comp_left, hw]
  rfl

/-- The unit section is a section of the structure map. -/
theorem unitSection_comp_hom : 𝒢.unitSection ≫ 𝒢.G.hom = 𝟙 _ := by
  show (η[𝒢.G] : 𝟙_ (Over (Spec (CommRingCat.of (𝓞 L)))) ⟶ 𝒢.G).left ≫ 𝒢.G.hom = 𝟙 _
  rw [Over.w]
  rfl

theorem one_mem_dom (τ : L →+* ℂ) (W : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ W) :
    ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ W := by
  intro x _
  show (1 : 𝒢.Pts τ).left x ∈ W
  erw [one_left_apply]
  exact m

theorem evalAt_sub {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s - s') = 𝒢.evalAt p U s - 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_sub]
    exact map_sub (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem evalAt_one_sec {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (h : ⊤ ≤ p.left ⁻¹ᵁ U) :
    𝒢.evalAt p U 1 = 1 := by
  unfold GroupModel.evalAt
  rw [dif_pos h, map_one]
  exact map_one (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)

/-- A section vanishing at the identity complex point has its germ at `ξ` in `𝔪_ξ`. -/
theorem germ_mem_of_evalAt_one {τ : L →+* ℂ} (W : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ W)
    (s : Γ(𝒢.G.left, W)) (h : 𝒢.evalAt (1 : 𝒢.Pts τ) W s = 0) :
    𝒢.G.left.presheaf.germ W 𝒢.genericUnit m s ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
  by_contra hn
  obtain ⟨u, hu⟩ := (IsLocalRing.notMem_maximalIdeal.mp hn).exists_right_inv
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep u
  have mm : 𝒢.genericUnit ∈ W ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hg : 𝒢.G.left.presheaf.germ (W ⊓ U') 𝒢.genericUnit mm
      (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s *
        𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') =
      𝒢.G.left.presheaf.germ (W ⊓ U') 𝒢.genericUnit mm 1 := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hu, map_one]
  obtain ⟨W'', m'', i₁, i₂, hW⟩ := TopCat.Presheaf.germ_eq _ 𝒢.genericUnit mm mm _ _ hg
  have hd := one_mem_dom 𝒢 τ W'' m''
  have e1 := congrArg (𝒢.evalAt (1 : 𝒢.Pts τ) W'') hW
  rw [map_mul, map_one, evalAt_mul, evalAt_one_sec 𝒢 _ _ hd, evalAt_res 𝒢 _ _ hd,
    evalAt_res 𝒢 _ _ hd] at e1
  rw [evalAt_res 𝒢 (1 : 𝒢.Pts τ) (homOfLE inf_le_left)
    ((one_mem_dom 𝒢 τ _ mm)) s, h, zero_mul] at e1
  exact zero_ne_one e1

end Eval

end ZInQ.Metrization2
/-! ## metrization2: the glue Prop, step 2 (all regular functions) and step 3 (translation) -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology

/-- **Glue (local structure of a morphism out of a fibre product, at complex points).** For group
models `𝒢₁`, `𝒢₂`, `ℋ` over `𝓞_L`, a morphism `m : 𝒢₁ ×_{𝓞_L} 𝒢₂ → ℋ` of `𝓞_L`-schemes, an open
`U ⊆ ℋ`, `s ∈ Γ(U, 𝒪_ℋ)` and complex points `p₁`, `p₂` with `m(p₁, p₂) ∈ U(ℂ)`: there are opens
`Vᵢ ∋ pᵢ` and regular functions `a_k, c_k` on `V₁`, `b_k, d_k` on `V₂` such that
`H = Σ c_k(·) d_k(·)` is nonzero at `(p₁, p₂)` and, wherever `H(p₁', p₂') ≠ 0` on
`V₁(ℂ) × V₂(ℂ)`, `m(p₁', p₂') ∈ U(ℂ)` and `s(m(p₁', p₂')) · H(p₁', p₂') = Σ a_k(p₁') b_k(p₂')`.
Why true (STANDARD; pure scheme theory, no analysis): take affine opens `Vᵢ = Spec Rᵢ ∋ pᵢ`;
`V₁ ×_{𝓞_L} V₂ = Spec (R₁ ⊗_{𝓞_L} R₂)` is an open of the product (Mathlib: `pullbackSpecIso`);
choose a basic open `D(h) ∋ (p₁, p₂)` inside `m⁻¹(U) ∩ (V₁ × V₂)`; on it `m^*s = a / h^N`; write
`h^N = Σ c_k ⊗ d_k`, `a = Σ a_k ⊗ b_k`; a complex point `(p₁', p₂')` of `V₁ × V₂` is the ring map
`r₁ ⊗ r₂ ↦ r₁(p₁') r₂(p₂')`, and it lies in `D(h)` iff `h^N(p₁', p₂') ≠ 0`.
Special cases: `m = e.inv` for `e : 𝒢P ≅ 𝒢₁ × 𝒢₂` is metrization's `ProductLocalStructure`
(`productLocalStructure_of`); `m = μ` (the group law) gives `JacDetNondegenerate`
(`jacDetNondegenerate_of`). -/
def ProductMapLocalStructure : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (ℋ : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (m : 𝒢₁.G ⊗ 𝒢₂.G ⟶ ℋ.G) (τ : L →+* ℂ) (U : ℋ.G.left.Opens) (s : Γ(ℋ.G.left, U))
    (p₁ : 𝒢₁.Pts τ) (p₂ : 𝒢₂.Pts τ), ⊤ ≤ (lift p₁ p₂ ≫ m).left ⁻¹ᵁ U →
    ∃ (V₁ : 𝒢₁.G.left.Opens) (V₂ : 𝒢₂.G.left.Opens) (n : ℕ)
      (a c : Fin n → Γ(𝒢₁.G.left, V₁)) (b d : Fin n → Γ(𝒢₂.G.left, V₂)),
      ⊤ ≤ p₁.left ⁻¹ᵁ V₁ ∧ ⊤ ≤ p₂.left ⁻¹ᵁ V₂ ∧
      (∑ k, 𝒢₁.evalAt p₁ V₁ (c k) * 𝒢₂.evalAt p₂ V₂ (d k)) ≠ 0 ∧
      ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), ⊤ ≤ p₁'.left ⁻¹ᵁ V₁ → ⊤ ≤ p₂'.left ⁻¹ᵁ V₂ →
        (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) ≠ 0 →
        ⊤ ≤ (lift p₁' p₂' ≫ m).left ⁻¹ᵁ U ∧
        ℋ.evalAt (lift p₁' p₂' ≫ m) U s *
            (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) =
          ∑ k, 𝒢₁.evalAt p₁' V₁ (a k) * 𝒢₂.evalAt p₂' V₂ (b k)

/-- `ProductMapLocalStructure` contains metrization's `ProductLocalStructure` (`m = e.inv`). -/
theorem productLocalStructure_of (h : ProductMapLocalStructure) :
    ZInQ.Metrization.ProductLocalStructure := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e τ U s p₁ p₂ hp
  exact h K A B C L 𝒢P 𝒢₁ 𝒢₂ e.inv τ U s p₁ p₂ hp

section Steps

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

theorem hom_genericUnit : 𝒢.G.hom 𝒢.genericUnit = genericPt L := by
  show 𝒢.G.hom (𝒢.unitSection (genericPt L)) = genericPt L
  rw [← Scheme.Hom.comp_apply, unitSection_comp_hom]
  rfl

/-- Step 2. If `d(germAlong Φ t)(0)` kills `v` for every `t ∈ 𝔪_ξ`, then the differential at `0`
of `z ↦ b(Φ z)` kills `v` for every regular function `b` near `ξ`. -/
theorem fderiv_evalAt_apply_eq_zero {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (v : Fin g → ℂ)
    (hv : ∀ t : IsLocalRing.maximalIdeal 𝒢.genStalk,
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 v = 0)
    (V : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ V) (b : Γ(𝒢.G.left, V)) :
    fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V b) 0 v = 0 := by
  set O := 𝒢.unitSection ⁻¹ᵁ V with hO
  set c : Γ(𝒢.G.left, 𝒢.G.hom ⁻¹ᵁ O) := 𝒢.G.hom.app O (𝒢.unitSection.app V b) with hc
  have mO : 𝒢.genericUnit ∈ 𝒢.G.hom ⁻¹ᵁ O := by
    show 𝒢.unitSection (𝒢.G.hom 𝒢.genericUnit) ∈ V
    rw [hom_genericUnit]
    exact m
  set W := V ⊓ 𝒢.G.hom ⁻¹ᵁ O with hW
  have mW : 𝒢.genericUnit ∈ W := TopologicalSpace.Opens.mem_inf.mpr ⟨m, mO⟩
  set b' : Γ(𝒢.G.left, W) := 𝒢.G.left.presheaf.map (homOfLE inf_le_left).op b -
    𝒢.G.left.presheaf.map (homOfLE inf_le_right).op c with hb'
  have h1 : 𝒢.evalAt (1 : 𝒢.Pts τ) W b' = 0 := by
    have hd := one_mem_dom 𝒢 τ W mW
    rw [hb', evalAt_sub, evalAt_res 𝒢 _ _ hd, evalAt_res 𝒢 _ _ hd,
      evalAt_of_left_eq 𝒢 1 𝒢.unitSection (one_left_eq 𝒢 τ) V b, hc, evalAt_pullback_base,
      sub_self]
  have hgerm := germ_mem_of_evalAt_one 𝒢 W mW b' h1
  have hv' := hv ⟨_, hgerm⟩
  have heq : 𝒢.germAlong Φ (𝒢.G.left.presheaf.germ W 𝒢.genericUnit mW b') =ᶠ[𝓝 0]
      fun z => 𝒢.evalAt (Φ z) V b - baseVal τ O (𝒢.unitSection.app V b) := by
    filter_upwards [germAlong_eventuallyEq 𝒢 hΦ W mW b',
      (hΦ.2.2.2.1 W).mem_nhds (zero_mem_dom 𝒢 hΦ W mW)] with z hz1 hz
    rw [hz1, hb', evalAt_sub, evalAt_res 𝒢 _ _ hz, evalAt_res 𝒢 _ _ hz, hc,
      evalAt_pullback_base]
  simp only at hv'
  rw [heq.fderiv_eq, fderiv_sub_const] at hv'
  exact hv'

/-- Step 3 (translation). If every regular function near `ξ` has `d(b ∘ Φ)(0) v = 0`, then for
every regular function `s` on `U` and every `w ∈ Φ⁻¹(U(ℂ))`, `t ↦ s(Φ(w + t v))` has derivative
`0` at `t = 0`: near `0`, `s(Φ w · Φ z) = N(z)/D(z)` with `N`, `D` combinations of regular
functions near `ξ` along `Φ` (`ProductMapLocalStructure` for the group law `μ`). -/
theorem hasDerivAt_line_zero (hML : ProductMapLocalStructure) {τ : L →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (v : Fin g → ℂ)
    (hv2 : ∀ (V : 𝒢.G.left.Opens) (_ : 𝒢.genericUnit ∈ V) (b : Γ(𝒢.G.left, V)),
      fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V b) 0 v = 0)
    (U : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, U)) (w : Fin g → ℂ) (hw : w ∈ 𝒢.dom Φ U) :
    HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (w + t • v)) U s) 0 0 := by
  have h0 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  have hmul : ∀ z, lift (Φ w) (Φ z) ≫ μ[𝒢.G] = Φ (w + z) := fun z => (hΦ.1 w z).symm
  have hU' : ⊤ ≤ (lift (Φ w) (Φ 0) ≫ μ[𝒢.G]).left ⁻¹ᵁ U := by
    rw [hmul, add_zero]; exact hw
  obtain ⟨V₁, V₂, n, a, c, b, d, hV₁, hV₂, hne, hall⟩ :=
    hML K A A A L 𝒢 𝒢 𝒢 μ[𝒢.G] τ U s (Φ w) (Φ 0) hU'
  have mV₂ : 𝒢.genericUnit ∈ V₂ := by
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of ℂ)) := inferInstance
    have hx := hV₂ (show x ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) from trivial)
    change (Φ 0).left x ∈ V₂ at hx
    rw [h0] at hx
    erw [one_left_apply] at hx
    exact hx
  set Nf : (Fin g → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢.evalAt (Φ w) V₁ (a k) * 𝒢.evalAt (Φ z) V₂ (b k) with hNf
  set Df : (Fin g → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢.evalAt (Φ w) V₁ (c k) * 𝒢.evalAt (Φ z) V₂ (d k) with hDf
  have hdom2 : IsOpen (𝒢.dom Φ V₂) := hΦ.2.2.2.1 V₂
  have h0dom : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ V₂ := hV₂
  have hDcont : ContinuousOn Df (𝒢.dom Φ V₂) := by
    have : DifferentiableOn ℂ Df (𝒢.dom Φ V₂) := by
      simp only [hDf]
      exact DifferentiableOn.fun_sum fun k _ =>
        (hΦ.2.2.2.2 V₂ (d k)).const_mul _
    exact this.continuousOn
  set O := 𝒢.dom Φ V₂ ∩ Df ⁻¹' {0}ᶜ with hO
  have hOopen : IsOpen O := hDcont.isOpen_inter_preimage hdom2 isOpen_compl_singleton
  have hD0 : Df 0 ≠ 0 := hne
  have h0O : (0 : Fin g → ℂ) ∈ O := ⟨h0dom, hD0⟩
  -- derivative along the line of each regular function near `ξ`
  have hline : ∀ (bb : Γ(𝒢.G.left, V₂)),
      HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t • v)) V₂ bb) 0 0 := by
    intro bb
    have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) V₂ bb) 0 :=
      (hΦ.2.2.2.2 V₂ bb).differentiableAt (hdom2.mem_nhds h0dom)
    have hF : HasFDerivAt (fun z => 𝒢.evalAt (Φ z) V₂ bb)
        (fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V₂ bb) 0) ((0 : ℂ) • v) := by
      rw [zero_smul]; exact hd.hasFDerivAt
    have := hF.comp_hasDerivAt (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).smul_const v)
    simp only [one_smul, hv2 V₂ mV₂ bb] at this
    exact this
  have hN : HasDerivAt (fun t : ℂ => Nf (t • v)) 0 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hline (b k)).const_mul (𝒢.evalAt (Φ w) V₁ (a k))
    simpa [hNf] using this
  have hD : HasDerivAt (fun t : ℂ => Df (t • v)) 0 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hline (d k)).const_mul (𝒢.evalAt (Φ w) V₁ (c k))
    simpa [hDf] using this
  have hD0' : Df ((0 : ℂ) • v) ≠ 0 := by rw [zero_smul]; exact hD0
  have hq := hN.div hD hD0'
  simp only [zero_mul, mul_zero, sub_zero, zero_div] at hq
  refine hq.congr_of_eventuallyEq ?_
  have hcont : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), t • v ∈ O :=
    hcont.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hOopen.mem_nhds h0O)
  filter_upwards [hev] with t ht
  obtain ⟨-, heq⟩ := hall (Φ w) (Φ (t • v)) hV₁ ht.1 ht.2
  rw [hmul] at heq
  exact eq_div_of_mul_eq ht.2 heq

end Steps

end ZInQ.Metrization2
/-! ## metrization2: points are determined by their values on an affine open; the assembly -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology

section Final

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- Two complex points in `U(ℂ)`, `U` affine, with the same values on `Γ(U, 𝒪)` are equal. -/
theorem pts_eq_of_evalAt {τ : L →+* ℂ} (U : 𝒢.G.left.Opens) (hU : IsAffineOpen U)
    (p q : 𝒢.Pts τ) (hp : ⊤ ≤ p.left ⁻¹ᵁ U) (hq : ⊤ ≤ q.left ⁻¹ᵁ U)
    (h : ∀ s : Γ(𝒢.G.left, U), 𝒢.evalAt p U s = 𝒢.evalAt q U s) : p = q := by
  have hTop : IsAffineOpen (⊤ : (Spec (CommRingCat.of ℂ)).Opens) :=
    isAffineOpen_top (Spec (CommRingCat.of ℂ))
  have happ : p.left.appLE U ⊤ hp = q.left.appLE U ⊤ hq := by
    ext s
    have hs := h s
    unfold GroupModel.evalAt at hs
    rw [dif_pos hp, dif_pos hq] at hs
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective hs
  have e1 := IsAffineOpen.SpecMap_appLE_fromSpec p.left hU hTop hp
  have e2 := IsAffineOpen.SpecMap_appLE_fromSpec q.left hU hTop hq
  have e3 : hTop.fromSpec ≫ p.left = hTop.fromSpec ≫ q.left :=
    e1.symm.trans ((congrArg (fun φ => Spec.map φ ≫ hU.fromSpec) happ).trans e2)
  have hiso : IsIso hTop.fromSpec := by
    rw [IsAffineOpen.fromSpec_top]; infer_instance
  apply Over.OverMorphism.ext
  exact (cancel_epi hTop.fromSpec).mp e3

end Final

/-- **`JacDetNondegenerate` from `ProductMapLocalStructure` (proved).** If every `jacDet Φ f`
vanished, some `v ≠ 0` would be killed by the differential at `0` of every regular function near
`ξ` along `Φ` (steps 1 and 2), hence, by translation, by the differential at every point
(step 3); so on an affine `U ∋ ξ` every regular function is constant along `t ↦ Φ(t v)` for small
`t`, so `Φ(t v) = Φ 0 = 1` (points of an affine scheme are determined by their values), so
`t v ∈ Λ` for all small `t`, contradicting the discreteness of `Λ`. Neither `A.dim = g` nor
`IsZLattice ℝ Λ` is used. -/
theorem jacDetNondegenerate_of (hML : ProductMapLocalStructure) :
    ZInQ.Metrization.JacDetNondegenerate := by
  intro K _ A L _ _ _ 𝒢 τ g _ Λ hdisc Φ _ hΦ
  by_contra hcon
  push_neg at hcon
  -- step 1
  obtain ⟨v, hv0, hv⟩ := exists_null_of_det_eq_zero
    (fun t : IsLocalRing.maximalIdeal 𝒢.genStalk => fun j =>
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 (Pi.single j 1)) (fun f => hcon f)
  have hsingle : ∀ j : Fin g, (fun k => if j = k then (1 : ℂ) else 0) = Pi.single j 1 := by
    intro j; ext k; simp [Pi.single_apply, eq_comm]
  have hv1 : ∀ t : IsLocalRing.maximalIdeal 𝒢.genStalk,
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 v = 0 := by
    intro t
    rw [pi_eq_sum_univ v, map_sum]
    simp only [hsingle, map_smul, smul_eq_mul]
    rw [← hv t]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- step 2
  have hv2 := fderiv_evalAt_apply_eq_zero 𝒢 hΦ v hv1
  -- an affine open around `ξ`
  obtain ⟨U, hU, mU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show 𝒢.genericUnit ∈ (⊤ : 𝒢.G.left.Opens) from trivial)
  have hdomU : IsOpen (𝒢.dom Φ U) := hΦ.2.2.2.1 U
  have h0U : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := zero_mem_dom 𝒢 hΦ U mU
  have hcont : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
  have hBopen : IsOpen {t : ℂ | t • v ∈ 𝒢.dom Φ U} := hdomU.preimage hcont
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hBopen 0 (by simp [h0U])
  -- steps 3-4: every regular function on `U` is constant along the line on the ball
  have hconst : ∀ t ∈ Metric.ball (0 : ℂ) r, Φ (t • v) = Φ 0 := by
    intro t ht
    have hderiv : ∀ (s : Γ(𝒢.G.left, U)), ∀ t₀ ∈ Metric.ball (0 : ℂ) r,
        HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t • v)) U s) 0 t₀ := by
      intro s t₀ ht₀
      have h3 := hasDerivAt_line_zero 𝒢 hML hΦ v hv2 U s (t₀ • v) (hball ht₀)
      have h4 : HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t₀ • v + (t - t₀) • v)) U s) 0 t₀ := by
        have h3' : HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t₀ • v + t • v)) U s) 0 (t₀ - t₀) := by
          rw [sub_self]; exact h3
        exact h3'.comp_sub_const t₀ t₀
      refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [← add_smul, add_sub_cancel]
    apply pts_eq_of_evalAt 𝒢 U hU _ _ (hball ht) h0U
    intro s
    have := (Metric.isOpen_ball).is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
      (fun t₀ ht₀ => (hderiv s t₀ ht₀).differentiableAt.differentiableWithinAt)
      (fun t₀ ht₀ => (hderiv s t₀ ht₀).deriv) ht (Metric.mem_ball_self hr)
    simpa using this
  -- step 5: discreteness of `Λ`
  have h0 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  have hmem : ∀ t ∈ Metric.ball (0 : ℂ) r, t • v ∈ Λ := fun t ht =>
    (hΦ.2.1 _).mp ((hconst t ht).trans h0)
  obtain ⟨u, hu, hpre⟩ := isOpen_induced_iff.mp (isOpen_discrete ({0} : Set Λ))
  have hu0 : (0 : Fin g → ℂ) ∈ u := by
    have : (0 : Λ) ∈ ({0} : Set Λ) := rfl
    rw [← hpre] at this
    exact this
  have hev1 : ∀ᶠ t in 𝓝 (0 : ℂ), t • v ∈ u :=
    hcont.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hu.mem_nhds hu0)
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ Metric.ball (0 : ℂ) r := Metric.ball_mem_nhds 0 hr
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t • v ∈ u ∧ t ∈ Metric.ball (0 : ℂ) r :=
    nhdsWithin_le_nhds (hev1.and hev2)
  obtain ⟨t, ⟨htu, htb⟩, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hin : (⟨t • v, hmem t htb⟩ : Λ) ∈ Subtype.val ⁻¹' u := htu
  rw [hpre] at hin
  have : t • v = 0 := congrArg Subtype.val hin
  rcases smul_eq_zero.mp this with h | h
  · exact ht0 h
  · exact hv0 h

/-- `MetrizationExists` with `JacDetNondegenerate` replaced by `ProductMapLocalStructure`. -/
theorem metrizationExists_of_productMap (hH : HodgeLatticeTheorem)
    (hU : AnalyticUniformizationOfDim) (hML : ProductMapLocalStructure) :
    ZInQ.G0HeightAdd.MetrizationExists :=
  metrizationExists_of' hH hU (jacDetNondegenerate_of hML)

end ZInQ.Metrization2

/-! ## metrization2: `AnalyticUniformizationOfDim` from leaf-push2's `UniformizationExists` (T35)

Verbatim copies (with `AbVar` resolving to the `ZInQ.DefFaltings.AbVar` of `Base.lean`, a copy of
`PkgI3.AbVar`) of leaf-push2's `cptObj`, `CPts`, `cEvalAt`, `cDom`, `IsUniformization`
(`ZInQKernel/HDecomp/LeafPush2/R22.lean`, lines 22-56) and `UniformizationExists`
(`ZInQKernel/HDecomp/LeafPush2/T.lean`, lines 26-37). -/

namespace ZInQ.LeafPush2

open NumberField MeasureTheory
open ZInQ.DefFaltings

section R22Sec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open Complex


variable {K : Type} [Field K]

/-- `Spec ℂ` as a `K`-scheme via `σ : K → ℂ`. -/
noncomputable def cptObj (σ : K →+* ℂ) : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom σ))

/-- The complex points `A(ℂ)_σ` of an abelian variety over `K` at `σ : K → ℂ`, a group
(Mathlib's group structure on morphisms into a group object). -/
abbrev CPts (A : AbVar K) (σ : K →+* ℂ) : Type := cptObj σ ⟶ A.X

noncomputable example (A : AbVar K) (σ : K →+* ℂ) : Group (CPts A σ) := inferInstance

/-- The value `s(p) ∈ ℂ` of a regular function `s ∈ Γ(U, 𝒪_A)` at a complex point `p ∈ U(ℂ)`
(`0` if `p ∉ U(ℂ)`); adapted from `GroupModel.evalAt` of def-faltings §17. -/
noncomputable def cEvalAt {A : AbVar K} {σ : K →+* ℂ} (p : CPts A σ) (U : A.X.left.Opens)
    (s : Γ(A.X.left, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ p.left ⁻¹ᵁ U then
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.left.appLE U ⊤ h s) else 0

/-- `Φ⁻¹(U(ℂ)) ⊆ ℂ^g`. -/
def cDom {A : AbVar K} {σ : K →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → CPts A σ) (U : A.X.left.Opens) :
    Set (Fin g → ℂ) := {z | ⊤ ≤ (Φ z).left ⁻¹ᵁ U}

/-- **Analytic uniformization of `A(ℂ)_σ`** (def-faltings' `IsAnalyticUniformization`, with the
abelian variety in place of a group model): `Φ : ℂ^g → A(ℂ)_σ` a surjective homomorphism with
kernel `Λ`, with open preimages of affine-chart points and holomorphic regular functions. -/
def IsUniformization {A : AbVar K} (σ : K →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ) : Prop :=
  (∀ z w, Φ (z + w) = Φ z * Φ w) ∧
  (∀ z, Φ z = 1 ↔ z ∈ Λ) ∧
  Function.Surjective Φ ∧
  (∀ U, IsOpen (cDom Φ U)) ∧
  (∀ U (s : Γ(A.X.left, U)), DifferentiableOn ℂ (fun z => cEvalAt (Φ z) U s) (cDom Φ U))

end R22Sec

section TSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj


/-- **AN3 for abelian varieties (textbook leaf; the analytic half of T11/T12).** Every abelian
variety over a field `K` and every `σ : K → ℂ`: `A(ℂ)_σ` has an analytic uniformization by
`ℂ^g`, `g = dim A`, with kernel a full lattice (Mumford, *Abelian varieties*, §1, with GAGA,
Serre 1956, for the complex Lie group structure; UNVERIFIED numbers). The `AbVar` analogue of
def-faltings' `AnalyticUniformizationExists`. -/
def UniformizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (σ : K →+* ℂ) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → CPts A σ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ IsUniformization σ Λ Φ


end TSec

end ZInQ.LeafPush2
/-! ## metrization2: complex points of a group model are complex points of `A_L`

For a group model `𝒢` of `A_L` and `τ : L → ℂ`, `θ : A_L(ℂ)_τ → 𝒢(ℂ)_τ`,
`q ↦ (Spec ℂ → A_L ≅ 𝒢_L → 𝒢)`, is a group isomorphism (inverse `χ`, built from the monoidal
functor `Over.pullback (Spec L → Spec 𝓞_L)`), and evaluation of `s ∈ Γ(U, 𝒪_𝒢)` at `θ q` is
evaluation of the pulled-back section at `q`. So a uniformization of `A_L(ℂ)_τ` in leaf-push2's
sense gives one of `𝒢(ℂ)_τ` in def-faltings' sense. -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.LeafPush2
open scoped Obj

section Transport

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev jO (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

theorem cpt_comp_jO (τ : L →+* ℂ) :
    (cptObj τ).hom ≫ jO L = (GroupModel.ptC (L := L) τ).hom := by
  show Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) =
    Spec.map (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L)))
  rw [← Spec.map_comp]
  rfl

/-- The projection `𝒢_L → 𝒢`. -/
noncomputable def fstG : (genericFibre L 𝒢.G).left ⟶ 𝒢.G.left := pullback.fst 𝒢.G.hom (jO L)

theorem fstG_comp_hom : fstG 𝒢 ≫ 𝒢.G.hom = (genericFibre L 𝒢.G).hom ≫ jO L :=
  pullback.condition

/-- The morphism `A_L → 𝒢` (through `gen⁻¹ : A_L ≅ 𝒢_L` and the projection `𝒢_L → 𝒢`). -/
noncomputable def toModel : (A.baseChange L).X.left ⟶ 𝒢.G.left := 𝒢.gen.inv.left ≫ fstG 𝒢

theorem toModel_comp_hom :
    (toModel 𝒢) ≫ 𝒢.G.hom = (A.baseChange L).X.hom ≫ jO L := by
  unfold toModel
  rw [Category.assoc, fstG_comp_hom, ← Category.assoc, Over.w 𝒢.gen.inv]

/-- `θ : A_L(ℂ)_τ → 𝒢(ℂ)_τ`. -/
noncomputable def theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) : 𝒢.Pts τ :=
  Over.homMk (q.left ≫ (toModel 𝒢))
    ((Category.assoc _ _ _).trans ((congrArg (q.left ≫ ·) (toModel_comp_hom 𝒢)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jO L) (Over.w q)).trans
        (cpt_comp_jO τ)))))

theorem theta_left {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) :
    ((theta 𝒢) q).left = q.left ≫ (toModel 𝒢) := rfl

/-- The base change `(Spec ℂ)_L` of `ptC τ`. -/
noncomputable abbrev ptCL (τ : L →+* ℂ) : Over (Spec (CommRingCat.of L)) :=
  (Over.pullback (jO L)).obj (GroupModel.ptC (L := L) τ)

/-- Its projection to `Spec ℂ` (`ptC τ`'s underlying scheme). -/
noncomputable def fstC (τ : L →+* ℂ) : (ptCL τ).left ⟶ (GroupModel.ptC (L := L) τ).left :=
  pullback.fst (GroupModel.ptC (L := L) τ).hom (jO L)

/-- The section `Spec ℂ → (Spec ℂ)_L` of the base change of `ptC τ`. -/
noncomputable def secC (τ : L →+* ℂ) : cptObj τ ⟶ ptCL τ :=
  Over.homMk (pullback.lift (𝟙 (Spec (CommRingCat.of ℂ))) (cptObj τ).hom
    ((Category.id_comp _).trans (cpt_comp_jO τ).symm))
    (pullback.lift_snd _ _ _)

theorem secC_fstC (τ : L →+* ℂ) : (secC τ).left ≫ fstC τ = 𝟙 _ :=
  pullback.lift_fst _ _ _

theorem secC_snd (τ : L →+* ℂ) : (secC τ).left ≫ (ptCL τ).hom = (cptObj τ).hom :=
  pullback.lift_snd _ _ _

/-- The base change of a complex point `p` of `𝒢`, as a map to `𝒢_L`. -/
noncomputable def mapG {τ : L →+* ℂ} (p : 𝒢.Pts τ) : ptCL τ ⟶ genericFibre L 𝒢.G :=
  (Over.pullback (jO L)).map p

theorem mapG_fstG {τ : L →+* ℂ} (p : 𝒢.Pts τ) : (mapG 𝒢 p).left ≫ fstG 𝒢 = fstC τ ≫ p.left :=
  pullback.lift_fst _ _ _

theorem mapG_snd {τ : L →+* ℂ} (p : 𝒢.Pts τ) :
    (mapG 𝒢 p).left ≫ (genericFibre L 𝒢.G).hom = (ptCL τ).hom :=
  pullback.lift_snd _ _ _

/-- `χ : 𝒢(ℂ)_τ → A_L(ℂ)_τ`. -/
noncomputable def chi {τ : L →+* ℂ} (p : 𝒢.Pts τ) : CPts (A.baseChange L) τ :=
  secC τ ≫ mapG 𝒢 p ≫ 𝒢.gen.hom

theorem chi_mul {τ : L →+* ℂ} (p₁ p₂ : 𝒢.Pts τ) : (chi 𝒢) (p₁ * p₂) = (chi 𝒢) p₁ * (chi 𝒢) p₂ := by
  letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  haveI : IsMonHom 𝒢.gen.hom := 𝒢.gen_hom
  have hm : mapG 𝒢 (p₁ * p₂) = mapG 𝒢 p₁ * mapG 𝒢 p₂ := Functor.map_mul _ _ _
  unfold chi
  rw [hm, MonObj.mul_comp, MonObj.comp_mul]

theorem gen_hom_inv_left : 𝒢.gen.hom.left ≫ 𝒢.gen.inv.left = 𝟙 _ := by
  rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]

theorem gen_inv_hom_left : 𝒢.gen.inv.left ≫ 𝒢.gen.hom.left = 𝟙 _ := by
  rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]

theorem theta_chi {τ : L →+* ℂ} (p : 𝒢.Pts τ) : (theta 𝒢) ((chi 𝒢) p) = p := by
  apply Over.OverMorphism.ext
  rw [theta_left]
  unfold chi toModel
  simp only [Over.comp_left, Category.assoc]
  rw [← Category.assoc 𝒢.gen.hom.left, gen_hom_inv_left, Category.id_comp, mapG_fstG]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p.left) (secC_fstC τ)).trans
    (Category.id_comp _))

theorem chi_theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) : (chi 𝒢) ((theta 𝒢) q) = q := by
  apply Over.OverMorphism.ext
  have key : (secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left = q.left ≫ 𝒢.gen.inv.left := by
    apply pullback.hom_ext
    · change ((secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left) ≫ fstG 𝒢 =
        (q.left ≫ 𝒢.gen.inv.left) ≫ fstG 𝒢
      rw [Category.assoc, mapG_fstG]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ((theta 𝒢) q).left)
        (secC_fstC τ)).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm))
    · change ((secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left) ≫ (genericFibre L 𝒢.G).hom =
        (q.left ≫ 𝒢.gen.inv.left) ≫ (genericFibre L 𝒢.G).hom
      rw [Category.assoc, mapG_snd, secC_snd, Category.assoc, Over.w 𝒢.gen.inv, Over.w q]
  unfold chi
  simp only [Over.comp_left]
  rw [← Category.assoc, key, Category.assoc, gen_inv_hom_left, Category.comp_id]

theorem theta_mul {τ : L →+* ℂ} (q₁ q₂ : CPts (A.baseChange L) τ) :
    (theta 𝒢) (q₁ * q₂) = (theta 𝒢) q₁ * (theta 𝒢) q₂ := by
  conv_lhs => rw [← (chi_theta 𝒢) q₁, ← (chi_theta 𝒢) q₂, ← chi_mul, theta_chi]

theorem theta_injective {τ : L →+* ℂ} : Function.Injective (theta 𝒢 (τ := τ)) := fun a b h => by
  rw [← (chi_theta 𝒢) a, ← (chi_theta 𝒢) b, h]

theorem theta_surjective {τ : L →+* ℂ} : Function.Surjective (theta 𝒢 (τ := τ)) :=
  fun p => ⟨(chi 𝒢) p, (theta_chi 𝒢) p⟩

theorem theta_one {τ : L →+* ℂ} : (theta 𝒢) (1 : CPts (A.baseChange L) τ) = 1 := by
  have h := theta_mul 𝒢 (τ := τ) 1 1
  rw [_root_.mul_one] at h
  exact mul_left_cancel (a := (theta 𝒢) 1) (by rw [_root_.mul_one]; exact h.symm)

theorem evalAt_theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) (U : 𝒢.G.left.Opens)
    (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt ((theta 𝒢) q) U s = cEvalAt q ((toModel 𝒢) ⁻¹ᵁ U) ((toModel 𝒢).app U s) := by
  unfold GroupModel.evalAt cEvalAt
  by_cases h : ⊤ ≤ q.left ⁻¹ᵁ ((toModel 𝒢) ⁻¹ᵁ U)
  · have h' : ⊤ ≤ ((theta 𝒢) q).left ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ ((theta 𝒢) q).left ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

end Transport

/-- **`AnalyticUniformizationOfDim` follows from leaf-push2's leaf `UniformizationExists`
(T35), proved.** Apply T35 to `A_L` over `L` at `σ = τ` (`dim A_L = dim A` by g0-dim's
`G0Dim.dim_baseChange`) and transport along `θ`. -/
theorem analyticUniformizationOfDim_of_uniformizationExists
    (hT : ZInQ.LeafPush2.UniformizationExists) : ZInQ.Metrization.AnalyticUniformizationOfDim := by
  intro K _ A L _ _ _ 𝒢 τ g hg
  have hgL : (A.baseChange L).dim = (g : WithBot ℕ∞) := by
    rw [← hg]
    exact G0Dim.dim_baseChange L A.X.left A.X.hom
  obtain ⟨Λ, Φ₀, hd, hZ, hmul, hker, hsurj, hopen, hdiff⟩ := hT L (A.baseChange L) τ g hgL
  refine ⟨Λ, fun z => (theta 𝒢) (Φ₀ z), hd, hZ, fun z w => ?_, fun z => ?_, ?_, fun U => ?_,
    fun U s => ?_⟩
  · simp only [hmul, theta_mul]
  · rw [← hker z, ← theta_one 𝒢 (τ := τ)]
    exact (theta_injective 𝒢).eq_iff
  · exact (theta_surjective 𝒢).comp hsurj
  · exact hopen ((toModel 𝒢) ⁻¹ᵁ U)
  · have := hdiff ((toModel 𝒢) ⁻¹ᵁ U) ((toModel 𝒢).app U s)
    refine this.congr fun z _ => ?_
    exact (evalAt_theta 𝒢) (Φ₀ z) U s

end ZInQ.Metrization2

/-! ## metrization2: g0-heightadd's `HeightAdditivity` with the smaller hypotheses

Compared with metrization's `heightAdditivity_of_metrization_v3`: the leaf
`AnalyticUniformizationOfDim` is replaced by leaf-push2's T35 `UniformizationExists` (already a
field `t35` of `HSyn.TextbookLeaves`), and the two glue Props `JacDetNondegenerate` and
`ProductLocalStructure` by the one glue Prop `ProductMapLocalStructure`. -/

namespace HSyn.G0Split

theorem heightAdditivity_of_metrization_v4 (hN1 : ZInQ.H5Neron.NeronModelExists)
    (h5 : LeafAdopt.H5) (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hML : ZInQ.Metrization2.ProductMapLocalStructure)
    (hPL : ZInQ.Metrization.ProductHodgeLattice) : HeightAdditivity :=
  heightAdditivity_of_metrization_v3 hN1 h5 hU hH
    (ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT35)
    (ZInQ.Metrization2.jacDetNondegenerate_of hML)
    (ZInQ.Metrization2.productLocalStructure_of hML) hPL

end HSyn.G0Split

#print axioms ZInQ.Metrization2.jacDetNondegenerate_of
#print axioms ZInQ.Metrization2.productLocalStructure_of
#print axioms ZInQ.Metrization2.metrizationExists_of_productMap
#print axioms ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists
#print axioms HSyn.G0Split.heightAdditivity_of_metrization_v4
