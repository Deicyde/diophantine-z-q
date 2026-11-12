import Mathlib

/-!
# bp-faltings: the first concrete layer of the stable Faltings height

Draft for `docs/research/bp-faltings.md`. Mathlib-only (no project imports).

The layer that does not depend on Néron models:

* `HermitianLattice K V`: a Hermitian line bundle on `Spec 𝓞_K` in generic-fibre form, i.e. a
  rank-one `𝓞_K`-lattice `M` in a one-dimensional `K`-vector space `V`, with a norm on
  `V ⊗_{K,σ} ℂ` for every complex embedding `σ`.
* `HermitianLattice.degreeAt`: the Arakelov degree computed with a nonzero section,
  `log #(M / 𝓞_K s) − ∑_σ log ‖s‖_σ`, and `arakelovDegree`; theorem `degreeAt_eq_arakelovDegree`:
  it does not depend on the section (product formula).
* `torusMetricSq Λ c`: the archimedean Faltings metric on the top form `c · dz₁ ∧ ⋯ ∧ dz_g` of the
  complex torus `ℂ^g / Λ`, `(i/2)^g ∫_{ℂ^g/Λ} η ∧ η̄` (sign convention: the positive value),
  computed as an integral over any fundamental domain (`torusMetricSq_eq_setIntegral`), and its
  independence of the linear coordinates (`torusMetricSq_comap`).
* `HodgeData K g V`: an abelian variety over `K` "given with a model": the determinant of the
  invariant differentials of a model as a lattice in `det H⁰(A, Ω¹)`, and for every `σ` the period
  lattice of `A_σ(ℂ)` in linear coordinates. `HodgeData.modelHeight` is Faltings' model height;
  proved: section independence, coordinate independence, monotonicity in the lattice (which is
  why the infimum over models is the Néron-model value).
-/

namespace ZInQ.BPFaltings

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
theorem _root_.ZInQ.BPFaltings.exists_smul_eq (hV : Module.finrank K V = 1)
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

end ZInQ.BPFaltings

#print axioms ZInQ.BPFaltings.HermitianLattice.degreeAt_eq_arakelovDegree
#print axioms ZInQ.BPFaltings.torusMetricSq_comap
#print axioms ZInQ.BPFaltings.torusMetricSq_eq_setIntegral
#print axioms ZInQ.BPFaltings.HodgeData.modelHeight_eq
#print axioms ZInQ.BPFaltings.HodgeData.modelHeight_recoord
#print axioms ZInQ.BPFaltings.HodgeData.modelHeight_eq_add_of_le
#print axioms ZInQ.BPFaltings.HodgeData.modelHeight_le_of_le
#print axioms ZInQ.BPFaltings.modelHeight_eq_faltingsHeightEC
#print axioms ZInQ.BPFaltings.HermitianLattice.arakelovDegree_rescale
#print axioms ZInQ.BPFaltings.exampleHodge_modelHeight
