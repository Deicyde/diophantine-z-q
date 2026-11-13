import ZInQKernel.HDecomp.Objects
import Mathlib

/-!
# leaf-push2: concrete statements of R18, R22, R3 over the new definitions

Task leaf-push2 (2026-11-12). One file. Contents:

* Part I (copied from `scratch/def-faltings/Faltings.lean` §§1-18 and the H5 section, namespace
  renamed to `ZInQ.LeafPush2`; the local copy of `AbVar` is **replaced by the kernel's
  `PkgI3.AbVar`** (`ZInQKernel/HDecomp/Objects.lean`), so the stable Faltings height is defined on
  the same abelian varieties as the Jacobians of leaf-modcurves). Nothing in Part I is new.
* Part II (copied from `scratch/leaf-modcurves/ModCurveLeaves.lean` §D, §E, §G): curves, the
  Albanese predicate `IsJacobian`, the leaf `JacobianExists`, `IsBelyiFunction`.
* Part III (new): R18 (Javanpeykar), R22 (Pazuki), R3 (Lin–Yang), sanity theorems.
-/


namespace ZInQ.LeafPush2

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
theorem _root_.ZInQ.LeafPush2.exists_smul_eq (hV : Module.finrank K V = 1)
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
open PkgI3

/-! `AbVar`, `AbVar.baseChange`, `AbVar.dim` are the kernel's `PkgI3.AbVar`,
`PkgI3.AbVar.baseChange`, `PkgI3.AbVar.dim` (identical definitions to the copies in
`scratch/def-faltings/Faltings.lean` §15). -/

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

end ModelsSec

/-! # Part II. Curves, Jacobians, Belyi functions (copied from
`scratch/leaf-modcurves/ModCurveLeaves.lean` §D, §E, §G; definitions unchanged) -/

section CurvesSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-- (copied) A smooth proper geometrically connected curve over `K` (proper curves are
projective). -/
class IsCurve {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K))) : Prop where
  proper : IsProper X.hom
  smooth : SmoothOfRelativeDimension 1 X.hom
  geomConnected : GeometricallyConnected X.hom

/-- (copied) **`J` is the Jacobian of the pointed curve `(X, P₀)`, with Abel–Jacobi map `aj`**
(the Albanese property; Milne, *Jacobian varieties*, in Arithmetic Geometry (1986), Prop. 6.1,
UNVERIFIED number). Every pointed `K`-morphism to an abelian variety factors uniquely through a
homomorphism `J → A`. -/
structure IsJacobian {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K)))
    (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) (J : AbVar K) (aj : X ⟶ J.X) : Prop where
  base : P₀ ≫ aj = η[J.X]
  univ : ∀ (A : AbVar K) (f : X ⟶ A.X), P₀ ≫ f = η[A.X] →
    ∃! φ : J.X ⟶ A.X, IsMonHom φ ∧ aj ≫ φ = f

/-- (copied) **Leaf MC6' (existence of the Jacobian)** of leaf-modcurves: Weil 1948; Milne 1986,
Thm 1.1 with Prop. 6.1 (UNVERIFIED numbers). -/
def JacobianExists (K : Type) [Field K] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of K))) (_ : IsCurve X)
    (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X),
    ∃ (J : AbVar K) (aj : X ⟶ J.X), IsJacobian X P₀ J aj

/-- (copied) **Belyi function over `k`** (function-field form): `t` transcendental over `k`, and
`k(t) ⊆ F` unramified (ramification index 1) at every place `w ⊇ k` of `F` over a finite place of
`k(t)` other than `t = 0`, `t = 1`. -/
def IsBelyiFunction (k F : Type) [Field k] [Field F] [Algebra k F] (t : F) : Prop :=
  Transcendental k t ∧
  ∀ w : ValuationSubring F, (∀ c : k, algebraMap k F c ∈ w) → t ∈ w →
    ∀ q : Polynomial k, q.Monic → Irreducible q → q ≠ Polynomial.X → q ≠ Polynomial.X - 1 →
      Polynomial.aeval t q ∈ w.nonunits →
      ∀ x ∈ w.nonunits, ∃ y ∈ w, x = Polynomial.aeval t q * y

/-! ### New: the function field of a curve as a `K`-algebra -/

variable {K : Type} [Field K]

/-- The structure map `K → K(X)` of an integral `K`-scheme: `K = Γ(Spec K) → Γ(X) → K(X)`. -/
noncomputable def ffStructMap (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left] :
    K →+* X.left.functionField :=
  haveI : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ X.hom.appTop ≫
    X.left.germToFunctionField ⊤).hom

/-- `K(X)` as a `K`-algebra (a local instance-free definition; used through `letI`). -/
@[instance_reducible] noncomputable def ffAlgebra (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left] :
    Algebra K X.left.functionField :=
  (ffStructMap X).toAlgebra

end CurvesSec

/-! # Part III. The leaves R18, R22, R3 -/

section R18Sec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-- **The bound of R18**: `13·10⁶ · g · d⁵`. -/
noncomputable def javanpeykarBound (g d : ℕ) : ℝ := 13 * 10 ^ 6 * g * d ^ 5

/-- **R18. Javanpeykar** (Algebra Number Theory 8 (2014), Thm 1.1.1, p. 90; arXiv:1403.6404v1
p. 1; height identification p. 98 / arXiv §2.3 p. 9; read by the locator audit,
docs/research/locators.md). Printed: for a smooth projective connected curve `X/ℚ̄` of genus
`g ≥ 1`, `h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`, where `h_Fal(X)` is the stable Faltings height of
`Jac X` and `deg_B(X)` the least degree of a Belyi map `X → ℙ¹_ℚ̄`.

**Stated form (a consequence).** `X` is a smooth proper geometrically connected integral curve over
a number field `K` with a `K`-point `P₀`; `J` is its Jacobian (Albanese predicate, over the
kernel's `PkgI3.AbVar`); `g = dim J` (= genus `X`, Milne 1986 Prop. 2.1/Thm 1.1, UNVERIFIED
numbers; rv-blueprints §2 recommendation 5: state with `g := dim J`); `t ∈ K(X)` is a Belyi
function over `K` with `d = [K(X) : K(t)]`. Then `h_F^st(J) ≤ 13·10⁶ · g · d⁵`.

Why it is a consequence of the printed theorem:
* `X_ℚ̄` (any embedding `K ↪ ℚ̄`) is smooth projective connected of genus `g`; `J_ℚ̄ = Jac(X_ℚ̄)`
  (the Albanese property is stable under field extension; STANDARD, Milne 1986).
* A Belyi function over `K` is one over `ℚ̄` of the same degree (characteristic 0, `K`
  algebraically closed in `K(X)`), so `deg_B(X_ℚ̄) ≤ d`, and the bound is monotone in `d`.
* The stable height does not depend on the field of definition, and in either of the two
  normalizations in question (Faltings' `(i/2)^g`, Deligne's `(i/2π)^g`) the bound holds for
  `h_F`, since `h_D = h_F + (g/2) log π ≥ h_F` (rv-blueprints §1.2). A normalization without the
  `2^{-g}` factor would give `h = h_F − (g/2) log 2` and make this form stronger; the locator audit
  read Javanpeykar's height as the stable Faltings height (leaf-push2 review: RISK, low).
* **H5** (rv-blueprints F2): `stableFaltingsHeight` (an infimum over metrized smooth group
  models, `EReal`) equals the published height. Only the half "the Néron model over a semistable
  field is a metrized model with the published height" is used here (an upper bound on an
  infimum). The statement asserts in particular `stableFaltingsHeight J < ⊤`, which is part of
  that half (the published height is a real number). -/
def R18_Javanpeykar : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : Over (Spec (CommRingCat.of K))) [IsCurve X]
    [IsIntegral X.left] (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) (J : AbVar K)
    (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ g : ℕ, J.dim = (g : WithBot ℕ∞) → 1 ≤ g →
    ∀ t : X.left.functionField,
      letI := ffAlgebra X
      IsBelyiFunction K X.left.functionField t →
      ∀ d : ℕ, Module.finrank (IntermediateField.adjoin K {t}) X.left.functionField = d → 0 < d →
        stableFaltingsHeight J ≤ ((javanpeykarBound g d : ℝ) : EReal)

/-- The real-valued form: if the stable height is a real number `x`, then `x ≤ 13·10⁶ g d⁵`. -/
theorem R18_real (h : R18_Javanpeykar) (K : Type) [Field K] [NumberField K]
    (X : Over (Spec (CommRingCat.of K))) [IsCurve X] [IsIntegral X.left]
    (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) (J : AbVar K) (aj : X ⟶ J.X)
    (hJ : IsJacobian X P₀ J aj) (g : ℕ) (hg : J.dim = (g : WithBot ℕ∞)) (hg1 : 1 ≤ g)
    (t : X.left.functionField)
    (ht : letI := ffAlgebra X; IsBelyiFunction K X.left.functionField t) (d : ℕ)
    (hd : letI := ffAlgebra X
      Module.finrank (IntermediateField.adjoin K {t}) X.left.functionField = d) (hd0 : 0 < d)
    (x : ℝ) (hx : stableFaltingsHeight J = x) : x ≤ javanpeykarBound g d := by
  have := h K X P₀ J aj hJ g hg hg1 t ht d hd hd0
  rw [hx] at this
  exact_mod_cast this

/-- Sanity: the bound is positive for `g, d ≥ 1` (so the leaf is not of the form `h ≤ 0`). -/
theorem javanpeykarBound_pos {g d : ℕ} (hg : 1 ≤ g) (hd : 0 < d) : 0 < javanpeykarBound g d := by
  unfold javanpeykarBound
  have : (0 : ℝ) < g := by exact_mod_cast hg
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

/-- Monotonicity in the Belyi degree (the step "any Belyi map bounds the minimal Belyi degree"). -/
theorem javanpeykarBound_mono {g d d' : ℕ} (hdd : d ≤ d') :
    javanpeykarBound g d ≤ javanpeykarBound g d' := by
  unfold javanpeykarBound
  have : (d : ℝ) ≤ d' := by exact_mod_cast hdd
  have : (d : ℝ) ^ 5 ≤ (d' : ℝ) ^ 5 := pow_le_pow_left₀ (by positivity) this 5
  have h0 : (0 : ℝ) ≤ 13 * 10 ^ 6 * g := by positivity
  nlinarith

end R18Sec

/-! ## R22 (Pazuki): complex points, analytic uniformization, Siegel space, theta constants -/

section R22Sec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 Complex

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

/-- **Siegel upper half space** `𝔥₂`: symmetric `Ω` with `Im Ω` positive definite. -/
def IsSiegel (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  Ω.transpose = Ω ∧ (Ω.map Complex.im).PosDef

/-- **`Ω` is a period matrix of the lattice `Λ`**: a `ℂ`-linear automorphism `T` of `ℂ²` maps
`Λ` onto `Ωℤ² + ℤ²`. For `Ω ∈ 𝔥₂`, `ℂ²/(Ωℤ² + ℤ²)` carries the principal polarization with
Hermitian form `(Im Ω)⁻¹` (Birkenhake–Lange, *Complex abelian varieties*, §8.1, UNVERIFIED
number), and every principal polarization of `ℂ²/Λ` with every symplectic basis arises this way.
So "for all `Ω ∈ 𝔥₂` with `IsPeriodMatrix Λ Ω`" = "for all principal polarizations of `ℂ²/Λ`
and all symplectic bases". No polarization object is needed. -/
def IsPeriodMatrix (Λ : Submodule ℤ (Fin 2 → ℂ)) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ T : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ), ∀ z, z ∈ Λ ↔
    ∃ m n : Fin 2 → ℤ, T z = Ω.mulVec (fun i => (m i : ℂ)) + fun i => (n i : ℂ)

/-- Theta characteristics of level 2: `m = (a, b)`, `a, b ∈ {0, 1}²` standing for `a/2, b/2`. -/
abbrev Char2 : Type := (Fin 2 → Fin 2) × (Fin 2 → Fin 2)

/-- **The theta constant** `θ[a;b](0, Ω) = ∑_{n ∈ ℤ²} exp(πi (n+a/2)ᵀΩ(n+a/2) + 2πi (n+a/2)ᵀ b/2)`
(Mumford, *Tata Lectures on Theta I*, II §1, UNVERIFIED number). Absolutely convergent for
`Ω ∈ 𝔥₂`; the `tsum` junk value `0` occurs only outside `𝔥₂`. The six odd characteristics give
`0`, so the point has the same height as the ten even theta constants used by the project. -/
noncomputable def thetaConst (Ω : Matrix (Fin 2) (Fin 2) ℂ) (m : Char2) : ℂ :=
  ∑' n : Fin 2 → ℤ,
    Complex.exp (Real.pi * I *
        ((fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ
          Ω.mulVec (fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2)) +
      2 * Real.pi * I *
        ((fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ (fun i => ((m.2 i : ℕ) : ℂ) / 2)))

/-- (copied from scratch/rv-loc-leaves/PazukiR22.lean) Absolute logarithmic Weil height (sup
norms) of a point of projective space over a number field: Mathlib's `Height.logHeight` divided by
`[K : ℚ]`. -/
noncomputable def absLogHeight {L : Type*} [Field L] [NumberField L] {J : Type*} [Finite J]
    (z : J → L) : ℝ :=
  Height.logHeight z / Module.finrank ℚ L

/-- (copied) Pazuki's constant `C₂(2, 2) = 1000 · 2⁴ · (log 2⁴)⁵`. -/
noncomputable def pazukiC2 : ℝ := 1000 * 2 ^ 4 * (Real.log (2 ^ 4)) ^ 5

/-- **R22. Pazuki** (Bull. SMF 140 (2012), Cor. 1.3(2), pp. 21-22 (`g = r = 2`), metric p. 26,
theta height p. 30; arXiv:0907.1458v2 Cor. 1.3(2) p. 3, Def. 2.1 pp. 6-7, Def. 2.6 p. 9; read by
the locator audit, docs/research/locators.md item 5). Printed (literal): for a principally
polarized abelian surface over `ℚ̄`, `|max(1,h_Θ) − max(1,h_D)/2| ≤ C₂ log(min(max(1,h_Θ),
max(1,h_D)) + 2)`, `h_D` in Deligne's metric, `h_Θ` the theta height with Euclidean norms at the
infinite places.

**Stated form (a consequence; the audit's upper half, rv-loc-leaves (c)).** For an abelian
surface `A` over a number field `K` whose stable Faltings height (Faltings' normalization) is the
real number `x`, and any `X ≥ max(1, x + log π)`; for every complex embedding `σ`, every analytic
uniformization `Φ` of `A(ℂ)_σ` with kernel `Λ`, every `Ω ∈ 𝔥₂` that is a period matrix of `Λ`
(= every principal polarization of `A(ℂ)_σ` with a symplectic basis), and every algebraic
representative `z ∈ L¹⁶` (`L` a number field, `emb : L → ℂ`) of the theta-null point
`[θ_m(0, Ω)]_m`: `h(z) ≤ X/2 + C₂ log(X + 2)`.

Why it is a consequence (each step is a citation-chain fact, not a Lean leaf):
* `h_D = h_F + log π` for surfaces (audit; `stableFaltingsHeightDeligne_eq`), so the hypothesis
  on `X` gives `X ≥ max(1, h_D)`; the three algebraic steps from the literal corollary are proved
  (`pazuki_upper_of_literal` in scratch/rv-loc-leaves, recompiled in §R22-glue below).
* The sup-norm height `absLogHeight` is `≤` the Euclidean-norm height of the paper (each
  archimedean factor `max |z_m| ≤ (∑|z_m|²)^{1/2}`); so an upper bound on Pazuki's `h_Θ` bounds it.
* Every analytic principal polarization of `A(ℂ)_σ` is algebraic and defined over `ℚ̄` (Riemann's
  theorem / GAGA, Mumford §§1-3 (T11-type input); rigidity of `NS`); its theta-null point is
  Pazuki's (Def. 2.6, level `r = 2`; the identification of his coordinates with the classical
  `θ[a;b](0, Ω)`, `a, b ∈ {0,½}²`, follows the project's reading (h-decomposition R22, pkg-I5),
  UNVERIFIED here). A change of symplectic basis permutes the `θ_m` up to eighth roots of unity
  and one common factor (theta transformation formula), so the height does not depend on it.
* **H5** identifies `stableFaltingsHeight` with the published height (rv-blueprints F2); taking
  the height through a real `x` (not `EReal.toReal`) keeps the statement no stronger.

Non-vacuity rests on standard facts not proved here: uniformizations exist (the `AbVar` analogue
of def-faltings' `AnalyticUniformizationExists`), principally polarizable abelian surfaces exist
over number fields (Jacobians of genus-2 curves), the theta-null point is algebraic up to a
common factor; and `𝔥₂ ≠ ∅` (`isSiegel_I`, proved below). -/
def R22_Pazuki : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K), A.dim = (2 : WithBot ℕ∞) →
    ∀ x : ℝ, stableFaltingsHeight A = x →
    ∀ X : ℝ, max 1 (x + Real.log Real.pi) ≤ X →
    ∀ (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φ : (Fin 2 → ℂ) → CPts A σ),
      IsUniformization σ Λ Φ →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsPeriodMatrix Λ Ω →
    ∀ (L : Type) [Field L] [NumberField L] (emb : L →+* ℂ) (z : Char2 → L) (c : ℂ), c ≠ 0 →
      (∀ m, emb (z m) = c * thetaConst Ω m) →
      absLogHeight z ≤ X / 2 + pazukiC2 * Real.log (X + 2)

/-- The hardened form used by the glue (`X = max(1, h_F + 3)`, rv-leaves-a §3.3). -/
theorem R22_plus3 (h : R22_Pazuki) (K : Type) [Field K] [NumberField K] (A : AbVar K)
    (hA : A.dim = (2 : WithBot ℕ∞)) (x : ℝ) (hx : stableFaltingsHeight A = x)
    (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φ : (Fin 2 → ℂ) → CPts A σ)
    (hΦ : IsUniformization σ Λ Φ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : IsSiegel Ω)
    (hP : IsPeriodMatrix Λ Ω) (L : Type) [Field L] [NumberField L] (emb : L →+* ℂ)
    (z : Char2 → L) (c : ℂ) (hc : c ≠ 0) (hz : ∀ m, emb (z m) = c * thetaConst Ω m) :
    absLogHeight z ≤ max 1 (x + 3) / 2 + pazukiC2 * Real.log (max 1 (x + 3) + 2) := by
  have hpi : Real.log Real.pi ≤ 3 := by
    have h4 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_four])
    have h42 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  exact h K A hA x hx (max 1 (x + 3)) (max_le_max le_rfl (by linarith)) σ Λ Φ hΦ Ω hΩ hP
    L emb z c hc hz

/-- Sanity: `i · 1 ∈ 𝔥₂` (the `Ω`-quantifier of R22 is not empty). -/
theorem isSiegel_I : IsSiegel (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  refine ⟨by simp, ?_⟩
  have : ((Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)).map Complex.im) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [this]
  exact Matrix.PosDef.one

end R22Sec

/-! ## R3 (Lin–Yang): the QM surfaces of discriminant 6 are Jacobians on the Lin–Yang family -/

section R3Sec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-! ### The order `𝒪` and QM structures (copied from `scratch/leaf-qm-fp/QMLeaves.lean` §0-§1) -/

/-- (copied) `B = (2, −3)_ℚ` (`i² = 2`, `j² = −3`). -/
abbrev B := QuaternionAlgebra ℚ 2 0 (-3)

/-- (copied) -/
def ofInt (n : Fin 4 → ℤ) : B :=
  ⟨n 0 + (n 2 : ℚ) / 2, n 1 + (n 3 : ℚ) / 2, (n 2 : ℚ) / 2, (n 3 : ℚ) / 2⟩

/-- (copied) -/
def InO (x : B) : Prop := ∃ n : Fin 4 → ℤ, x = ofInt n

/-- (copied) -/
def mulCoord (n m : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

theorem ofInt_mul (n m : Fin 4 → ℤ) : ofInt n * ofInt m = ofInt (mulCoord n m) := by
  ext <;> simp [ofInt, mulCoord] <;> ring

theorem ofInt_add (n m : Fin 4 → ℤ) : ofInt n + ofInt m = ofInt (n + m) := by
  ext <;> simp [ofInt] <;> ring

theorem ofInt_neg (n : Fin 4 → ℤ) : -ofInt n = ofInt (-n) := by
  ext <;> simp [ofInt] <;> ring

theorem ofInt_zero : ofInt 0 = 0 := by ext <;> simp [ofInt]

theorem ofInt_one : ofInt ![1, 0, 0, 0] = 1 := by ext <;> simp [ofInt]

/-- (copied) The maximal order `𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩` of `B = (2,−3)`. -/
def O : Subring B where
  carrier := {x | InO x}
  mul_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨mulCoord n m, ofInt_mul n m⟩
  one_mem' := ⟨![1, 0, 0, 0], ofInt_one.symm⟩
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨n + m, ofInt_add n m⟩
  zero_mem' := ⟨0, ofInt_zero.symm⟩
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    exact ⟨-n, ofInt_neg n⟩

/-- (copied) **A QM structure by `𝒪` on `A`**: an injective unital ring homomorphism
`ι : 𝒪 → End_K(A)`. No polarization (see the R3 docstring). -/
structure QMStr {K : Type} [Field K] (A : AbVar K) where
  iota : O →+* AbVar.End A
  injective : Function.Injective iota

/-! ### Igusa–Clebsch and Igusa invariants of a sextic (copied from
`scratch/hdec-elementary/Leaves.lean` §1; Igusa's `J`'s new here) -/

variable {k : Type*} [Field k]

/-- (copied) `(rᵢ - rⱼ)²`. -/
def dsq (r : Fin 6 → k) (i j : Fin 6) : k := (r i - r j) ^ 2

/-- (copied) Igusa–Clebsch `I₂` of `a ∏ (X - rᵢ)`. -/
def IC2 (a : k) (r : Fin 6 → k) : k :=
  a ^ 2 * (∑ σ : Equiv.Perm (Fin 6),
    dsq r (σ 0) (σ 1) * dsq r (σ 2) (σ 3) * dsq r (σ 4) (σ 5)) / 48

/-- (copied) Igusa–Clebsch `I₄`. -/
def IC4 (a : k) (r : Fin 6 → k) : k :=
  a ^ 4 * (∑ σ : Equiv.Perm (Fin 6),
    dsq r (σ 0) (σ 1) * dsq r (σ 1) (σ 2) * dsq r (σ 2) (σ 0) *
    dsq r (σ 3) (σ 4) * dsq r (σ 4) (σ 5) * dsq r (σ 5) (σ 3)) / 72

/-- (copied) Igusa–Clebsch `I₆`. -/
def IC6 (a : k) (r : Fin 6 → k) : k :=
  a ^ 6 * (∑ σ : Equiv.Perm (Fin 6),
    dsq r (σ 0) (σ 1) * dsq r (σ 1) (σ 2) * dsq r (σ 2) (σ 0) *
    dsq r (σ 3) (σ 4) * dsq r (σ 4) (σ 5) * dsq r (σ 5) (σ 3) *
    dsq r (σ 0) (σ 3) * dsq r (σ 1) (σ 4) * dsq r (σ 2) (σ 5)) / 12

/-- (copied) Igusa–Clebsch `I₁₀`: the discriminant `a¹⁰ ∏_{i<j} (rᵢ - rⱼ)²`. -/
def IC10 (a : k) (r : Fin 6 → k) : k :=
  a ^ 10 * ∏ i : Fin 6, ∏ j : Fin 6, if i < j then dsq r i j else 1

/-- (copied) `y² = a ∏ (X - rᵢ)` is a genus-2 curve: `a ≠ 0` and distinct roots. -/
def IsGenus2 (a : k) (r : Fin 6 → k) : Prop := a ≠ 0 ∧ Function.Injective r

/-- (copied) The QM locus in Igusa–Clebsch coordinates (hdec-elementary). -/
def OnQMLocus (a : k) (r : Fin 6 → k) (j : k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ IC2 a r = c ^ 2 * (96 * (j + 1)) ∧ IC4 a r = c ^ 4 * (576 * j) ∧
    IC6 a r = c ^ 6 * (4608 * j * (5 * j + 4)) ∧ IC10 a r = c ^ 10 * (4096 * j ^ 3)

/-- Igusa's `J₂ = I₂/8`. -/
def IgJ2 (a : k) (r : Fin 6 → k) : k := IC2 a r / 8
/-- Igusa's `J₄ = (4J₂² − I₄)/96`. -/
def IgJ4 (a : k) (r : Fin 6 → k) : k := (4 * IgJ2 a r ^ 2 - IC4 a r) / 96
/-- Igusa's `J₆ = (8J₂³ − 160J₂J₄ − I₆)/576`. -/
def IgJ6 (a : k) (r : Fin 6 → k) : k :=
  (8 * IgJ2 a r ^ 3 - 160 * IgJ2 a r * IgJ4 a r - IC6 a r) / 576
/-- Igusa's `J₁₀ = I₁₀/4096`. -/
def IgJ10 (a : k) (r : Fin 6 → k) : k := IC10 a r / 4096

/-- **Lin–Yang's tuple** (arXiv:1807.00466v1 Example 29, eqs. (13)-(14)): the weighted-projective
point `[J₂ : J₄ : J₆ : J₁₀]` (weights `1, 2, 3, 5`) of `a ∏ (X - rᵢ)` is
`[12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]`. The `J`/Igusa–Clebsch convention is Igusa's
(`I₂ = 8J₂`, `I₄ = 4J₂² − 96J₄`, `I₆ = 8J₂³ − 160J₂J₄ − 576J₆`, `I₁₀ = 4096J₁₀`; the convention of
hdec-elementary's `igusa_thomae_check.py`); locators.md asks to fix it before use: the check
`linYangTuple_onQMLocus` below ties it to hdec-elementary's `OnQMLocus`. -/
def LinYangTuple (a : k) (r : Fin 6 → k) (j : k) : Prop :=
  ∃ t : k, t ≠ 0 ∧ IgJ2 a r = t * (12 * (j + 1)) ∧ IgJ4 a r = t ^ 2 * (6 * (j ^ 2 + j + 1)) ∧
    IgJ6 a r = t ^ 3 * (4 * (j ^ 3 - 2 * j ^ 2 + 1)) ∧ IgJ10 a r = t ^ 5 * j ^ 3

/-- **Convention check (proved).** Lin–Yang's `J`-tuple with scaling `t = c²` is
hdec-elementary's Igusa–Clebsch locus `OnQMLocus` (the input of the proved F1 glue
`HDec.j_eq_of_onQMLocus`). Over an algebraically closed field every `t` is a square. -/
theorem linYangTuple_onQMLocus [CharZero k] {a : k} {r : Fin 6 → k} {j c : k} (hc : c ≠ 0)
    (h2 : IgJ2 a r = c ^ 2 * (12 * (j + 1)))
    (h4 : IgJ4 a r = (c ^ 2) ^ 2 * (6 * (j ^ 2 + j + 1)))
    (h6 : IgJ6 a r = (c ^ 2) ^ 3 * (4 * (j ^ 3 - 2 * j ^ 2 + 1)))
    (h10 : IgJ10 a r = (c ^ 2) ^ 5 * j ^ 3) : OnQMLocus a r j := by
  have e2 : IC2 a r = 8 * IgJ2 a r := by unfold IgJ2; field_simp
  have e4 : IC4 a r = 4 * IgJ2 a r ^ 2 - 96 * IgJ4 a r := by
    rw [show IgJ4 a r = (4 * IgJ2 a r ^ 2 - IC4 a r) / 96 from rfl]; field_simp; ring
  have e6 : IC6 a r = 8 * IgJ2 a r ^ 3 - 160 * IgJ2 a r * IgJ4 a r - 576 * IgJ6 a r := by
    rw [show IgJ6 a r = (8 * IgJ2 a r ^ 3 - 160 * IgJ2 a r * IgJ4 a r - IC6 a r) / 576 from rfl]
    field_simp; ring
  have e10 : IC10 a r = 4096 * IgJ10 a r := by unfold IgJ10; field_simp
  refine ⟨c, hc, ?_, ?_, ?_, ?_⟩
  · rw [e2, h2]; ring
  · rw [e4, h2, h4]; ring
  · rw [e6, h2, h4, h6]; ring
  · rw [e10, h10]; ring

/-- `LinYangTuple` gives `OnQMLocus` when the scaling is a square (e.g. `k` algebraically
closed), hence, by hdec-elementary's proved glue, `j = 3779136 · I₁₀² / I₄⁵`. -/
theorem onQMLocus_of_linYangTuple [CharZero k] [IsAlgClosed k] {a : k} {r : Fin 6 → k} {j : k}
    (h : LinYangTuple a r j) : OnQMLocus a r j := by
  obtain ⟨t, ht, h2, h4, h6, h10⟩ := h
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq t (by norm_num : 0 < 2)
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact ht hc.symm
  rw [← hc] at h2 h4 h6 h10
  exact linYangTuple_onQMLocus hc0 h2 h4 h6 h10

/-! ### The curve `y² = a ∏ (X − rᵢ)` as a scheme -/

/-- The sextic `a ∏ (X − rᵢ)`. -/
noncomputable def sextic (a : k) (r : Fin 6 → k) : Polynomial k :=
  Polynomial.C a * ∏ i, (Polynomial.X - Polynomial.C (r i))

/-- **`C` has the affine model `y² = a ∏ (X − rᵢ)`**: its function field is generated over `k`
by `x` transcendental and `y` with `y² = a ∏ (x − rᵢ)` (so it is `k(x)[y]/(y² − f(x))`, `f`
squarefree of degree 6 under `IsGenus2`). For a smooth proper geometrically connected curve this
determines `C` up to `k`-isomorphism (Hartshorne I.6.12 with II.6.7, UNVERIFIED numbers). -/
def HasSexticModel {K : Type} [Field K] (C : Over (Spec (CommRingCat.of K))) [IsIntegral C.left]
    (a : K) (r : Fin 6 → K) : Prop :=
  letI := ffAlgebra C
  ∃ x y : C.left.functionField, Transcendental K x ∧ y ^ 2 = Polynomial.aeval x (sextic a r) ∧
    IntermediateField.adjoin K {x, y} = ⊤

/-- **R3. Lin–Yang** (Math. Z. 295 (2020), 775-819; arXiv:1807.00466v1 **Example 29**, pp. 20-21,
discriminant 6, eqs. (13)-(14); read in arXiv v1 by the locator audit, journal numbering
UNVERIFIED; alternative supplier of the tuple and of the finite-nonzero-`j` Jacobian assertion:
Baba–Granath, Canad. J. Math. 60 (2008), Prop. 3.6, p. 742, read by the audit). Printed: on the
finite nonzero `j`-locus, the principally polarized QM surface of discriminant 6 over `j` is the
Jacobian of a genus-2 curve with `[J₂:J₄:J₆:J₁₀] = [12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]`.

**Stated form (a consequence; polarization-free and coordinate-free).** Every abelian surface `A`
over `ℂ` with an embedding `𝒪 ↪ End(A)` is either `≅ Jac(C)` (as group schemes) for a curve `C`
with an affine model `y² = a ∏ (x − rᵢ)` (six distinct roots) on the Lin–Yang family at some
`j ≠ 0`, or `≅ E₁ × E₂` for elliptic curves `E₁, E₂`.

Why it is a consequence (citation chain, not Lean leaves):
* `(A, ι)` carries a principal polarization of the fixed type, so it is a point of `X₆` with a
  value `j ∈ ℙ¹` of the Hauptmodul of `X₆/W` (bp-qmmoduli §2.2, existence of the polarization:
  SPECULATIVE in the repository, under review in rv-qm-polar; Baba–Granath Thm 2.1 for `X₆/W`).
* `j ≠ 0, ∞`: Lin–Yang's assertion, forgetting the polarization (`≅` of group schemes).
* `j ∈ {0, ∞}`: the tuple has `J₁₀ = 0` there (in weighted-projective coordinates), so the
  principally polarized surface is not the Jacobian of a smooth curve, hence a product of elliptic
  curves (Weil's dichotomy for principally polarized abelian surfaces; Weil 1957, UNVERIFIED).
  The second disjunct is weaker than "product with its product polarization".

**Polarization (rv-qm-polar).** The statement is existential in `C` and does not mention a
polarization, so it stays a consequence if a QM surface carries several principal polarizations
(each gives a curve; Lin–Yang's is one of them). What would change: a form "for **every** genus-2
`C` with `Jac C ≅ A`, `C` lies on the family" (not stated here; false in general if `A` carries a
principal polarization whose Rosati involution is not of the fixed type), and the
coordinate-linked form "`j` = the value `π₆(x)` of the moduli point" (needs leaf-qm-fp's `X₆`
package and the polarization type; not stated here).

**Over `ℂ`** (Lin–Yang's setting). The `ℚ̄`-form used at A7/F1 follows by the Lefschetz principle
(the Shimura curve, the family and the Igusa invariants are defined over `ℚ`): glue target
`R03_LinYang_algClosed` below, not a leaf. -/
def R03_LinYang : Prop :=
  ∀ (A : AbVar ℂ) (_ : QMStr A), A.dim = (2 : WithBot ℕ∞) →
    (∃ (j a : ℂ) (r : Fin 6 → ℂ), j ≠ 0 ∧ IsGenus2 a r ∧ LinYangTuple a r j ∧
      ∃ (C : Over (Spec (CommRingCat.of ℂ))) (_ : IsCurve C) (_ : IsIntegral C.left),
        HasSexticModel C a r ∧
        ∃ (P₀ : 𝟙_ (Over (Spec (CommRingCat.of ℂ))) ⟶ C) (J : AbVar ℂ) (aj : C ⟶ J.X),
          IsJacobian C P₀ J aj ∧ ∃ e : J.X ≅ A.X, IsMonHom e.hom) ∨
    (∃ E₁ E₂ : AbVar ℂ, E₁.dim = (1 : WithBot ℕ∞) ∧ E₂.dim = (1 : WithBot ℕ∞) ∧
      Nonempty (A.X ≅ E₁.X ⊗ E₂.X))

/-- **Glue target (Lefschetz principle), not a leaf**: `R03_LinYang` over every algebraically
closed field of characteristic 0 (the case `k = ℚ̄` is the one A7/F1 use). -/
def R03_LinYang_algClosed : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : AbVar k) (_ : QMStr A),
    A.dim = (2 : WithBot ℕ∞) →
    (∃ (j a : k) (r : Fin 6 → k), j ≠ 0 ∧ IsGenus2 a r ∧ LinYangTuple a r j ∧
      ∃ (C : Over (Spec (CommRingCat.of k))) (_ : IsCurve C) (_ : IsIntegral C.left),
        HasSexticModel C a r ∧
        ∃ (P₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (J : AbVar k) (aj : C ⟶ J.X),
          IsJacobian C P₀ J aj ∧ ∃ e : J.X ≅ A.X, IsMonHom e.hom) ∨
    (∃ E₁ E₂ : AbVar k, E₁.dim = (1 : WithBot ℕ∞) ∧ E₂.dim = (1 : WithBot ℕ∞) ∧
      Nonempty (A.X ≅ E₁.X ⊗ E₂.X))

/-- The algebraically closed form contains the leaf (`k = ℂ`). -/
theorem R03_of_algClosed (h : R03_LinYang_algClosed) : R03_LinYang :=
  fun A q hA => h ℂ A q hA

/-- Consumer form (F1): on the first branch, Lin–Yang's `j` is the weight-0 Igusa invariant
`3779136 · I₁₀² / I₄⁵` of the curve (from `onQMLocus_of_linYangTuple` and hdec-elementary's
`j_eq_of_onQMLocus`, whose two-line proof is repeated here). -/
theorem linYang_j_eq [CharZero k] [IsAlgClosed k] {a : k} {r : Fin 6 → k} {j : k} (hj : j ≠ 0)
    (h : LinYangTuple a r j) : j = 3779136 * IC10 a r ^ 2 / IC4 a r ^ 5 := by
  obtain ⟨c, hc, -, h4, -, h10⟩ := onQMLocus_of_linYangTuple h
  rw [h4, h10]
  field_simp
  ring

end R3Sec

/-! ## T10-T12: what a concrete statement needs (only the parts statable over the definitions
above; no étale cohomology is built). See docs/research/leaf-push2.md §5. -/

section TSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-- **AN3 for abelian varieties (textbook leaf; the analytic half of T11/T12).** Every abelian
variety over a field `K` and every `σ : K → ℂ`: `A(ℂ)_σ` has an analytic uniformization by
`ℂ^g`, `g = dim A`, with kernel a full lattice (Mumford, *Abelian varieties*, §1, with GAGA,
Serre 1956, for the complex Lie group structure; UNVERIFIED numbers). The `AbVar` analogue of
def-faltings' `AnalyticUniformizationExists`. -/
def UniformizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (σ : K →+* ℂ) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → CPts A σ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ IsUniformization σ Λ Φ

/-- **T11(a), Riemann/GAGA for endomorphisms (textbook leaf).** For an abelian variety over `ℂ`
with a uniformization `Φ` (kernel `Λ`) at `σ = id`, the endomorphisms of `A` are exactly the
`ℂ`-linear maps of `ℂ^g` preserving `Λ`: each such `M` is induced by a unique endomorphism `f`
(`Φ(Mz) = f ∘ Φ(z)`), and each `f` is induced by some `M`. (Mumford §1 and §2, Birkenhake–Lange
Prop. 1.2.1 for complex tori; GAGA, Serre 1956, for "holomorphic ⇒ algebraic"; UNVERIFIED
numbers.) With `ℚ ⊗`, this is `End⁰(A_ℂ) = End(H₁(A(ℂ),ℚ))` ∩ (Hodge endomorphisms), the form of
T11 used at G5/G10. -/
def T11a_RiemannEnd : Prop :=
  ∀ (A : AbVar ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → IsUniformization (RingHom.id ℂ) Λ Φ →
    (∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z ∈ Λ, M z ∈ Λ) →
      ∃! f : AbVar.End A, ∀ z, Φ (M z) = Φ z ≫ f.hom) ∧
    (∀ f : AbVar.End A, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, Φ (M z) = Φ z ≫ f.hom)

/-- **T11(b), rigidity (textbook leaf).** For abelian varieties over an algebraically closed field
`k` of characteristic 0 and an extension `k → L`, every homomorphism `A_L → B_L` descends uniquely
to a homomorphism `A → B` (Conrad 2006, §3; Milne 1986 §20; UNVERIFIED numbers). With `k = ℚ̄`,
`L = ℂ` this is `Hom_ℚ̄ = Hom_ℂ`. -/
def T11b_Rigidity : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (L : Type) [Field L] [Algebra k L]
    (A B : AbVar k) (ψ : (A.baseChange L).X ⟶ (B.baseChange L).X), IsMonHom ψ →
    ∃! φ : A.X ⟶ B.X, IsMonHom φ ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map φ = ψ

/-- Complex conjugation in `G_ℚ`: `c` restricts complex conjugation along some embedding
`ℚ̄ ↪ ℂ`. (Duplicates `PkgI4.IsComplexConj` of Leaves.lean; to be identified at integration.) -/
def IsComplexConj (c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : Prop :=
  ∃ emb : AlgebraicClosure ℚ →ₐ[ℚ] ℂ, ∀ x, emb (c x) = starRingEnd ℂ (emb x)

/-- **T12, in the form used at G10 (oddness).** For an abelian variety `A/ℚ` of dimension `g`,
complex conjugation acts on `V_ℓ(A)` with `+1`- and `−1`-eigenspaces of dimension `g` each.
Not a single published statement: Artin's comparison `V_ℓ(A) ≅ H₁(A(ℂ),ℚ) ⊗ ℚ_ℓ` compatibly with
complex conjugation (SGA 4 XI 4.4; for abelian varieties elementary through `ℂ^g/Λ`: the
`ℓⁿ`-torsion of `A(ℂ)` is `Φ(ℓ⁻ⁿΛ)`, and `A(ℚ̄)[ℓⁿ] → A(ℂ)[ℓⁿ]` is bijective by T5), plus the
computation that an antiholomorphic involution of `ℂ^g/Λ` acts on `Λ ⊗ ℝ = ℂ^g` with eigenspaces
of real dimension `g` (`ℂ^g = W ⊕ iW`). A **glue target** from `UniformizationExists`, T5, T26
(`V_ℓ` finite of rank `2g`) and the antiholomorphy of complex conjugation on `A(ℂ)` for `A/ℚ`. -/
def T12_ComplexConjEigen : Prop :=
  ∀ (A : AbVar ℚ) (g : ℕ), A.dim = (g : WithBot ℕ∞) → ∀ (ℓ : ℕ) [Fact ℓ.Prime]
    (c : Field.absoluteGaloisGroup ℚ), IsComplexConj c →
    Module.finrank ℚ_[ℓ] (LinearMap.ker (AbVar.galRep ℓ A c - 1)) = g ∧
      Module.finrank ℚ_[ℓ] (LinearMap.ker (AbVar.galRep ℓ A c + 1)) = g

/-- Sanity: complex conjugations exist in `G_ℚ` (so T12's quantifier over `c` is not empty). -/
theorem exists_isComplexConj : ∃ c : Field.absoluteGaloisGroup ℚ, IsComplexConj c := by
  obtain ⟨emb⟩ : Nonempty (AlgebraicClosure ℚ →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  let _ : Algebra (AlgebraicClosure ℚ) ℂ := emb.toRingHom.toAlgebra
  have : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ :=
    IsScalarTower.of_algebraMap_eq (fun x => (emb.commutes x).symm)
  let χ : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ
  refine ⟨χ.restrictNormal (AlgebraicClosure ℚ), emb, fun x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes χ (AlgebraicClosure ℚ) x

/-- **T10, the part statable in Mathlib v4.35 (not the form used).** Mathlib has `ℓ`-adic
cohomology as pro-étale cohomology, `Scheme.EllAdicCohomology X ℓ n` (Bhatt–Scholze 2015,
Def. 6.8.1; `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean`), but only as an abelian group:
no `ℤ_ℓ`-module structure and no pullback maps, hence no Galois action. `ℓ ≠ char K` as in
Milne's theorem. What is statable is the
underlying group isomorphism `H¹(A_K̄, ℤ_ℓ) ≅ Hom_{ℤ_ℓ}(T_ℓ A, ℤ_ℓ)`: a consequence of Milne 1986,
Thm 15.1(a) (UNVERIFIED number) together with the comparison of pro-étale and classical `ℓ`-adic
cohomology for qcqs schemes (Bhatt–Scholze 2015 §5.6, UNVERIFIED number; Mathlib's docstring
announces this comparison as future work). The form used (derive R10's Tate-module form) needs
the Galois-equivariant version: `ℤ_ℓ`-linearity and functoriality of `EllAdicCohomology` in `X`. -/
def T10_groupIso : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    Nonempty ((A.baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1 ≃+
      Module.Dual ℤ_[ℓ] (A.T ℓ))

end TSec

end ZInQ.LeafPush2

#print axioms ZInQ.LeafPush2.stableFaltingsHeight
#print axioms ZInQ.LeafPush2.R18_real
#print axioms ZInQ.LeafPush2.javanpeykarBound_pos
#print axioms ZInQ.LeafPush2.javanpeykarBound_mono
#print axioms ZInQ.LeafPush2.R22_plus3
#print axioms ZInQ.LeafPush2.isSiegel_I
#print axioms ZInQ.LeafPush2.linYangTuple_onQMLocus
#print axioms ZInQ.LeafPush2.onQMLocus_of_linYangTuple
#print axioms ZInQ.LeafPush2.linYang_j_eq
#print axioms ZInQ.LeafPush2.R03_of_algClosed
#print axioms ZInQ.LeafPush2.exists_isComplexConj
#print axioms ZInQ.LeafPush2.T10_groupIso
#print axioms ZInQ.LeafPush2.R03_LinYang
#print axioms ZInQ.LeafPush2.R22_Pazuki
#print axioms ZInQ.LeafPush2.R18_Javanpeykar
