import ZInQKernel.Contrib.OneProof.DSThm965Weak

noncomputable section

set_option linter.unusedSectionVars false

namespace DSCoeffExt

open Polynomial NumberField IsDedekindDomain
open ZInQ.Contrib.G9.PkgI4 (Qbar GQ GaloisRep)

/-! ## 1. Algebraic elements of `ℂ` come from `ℚ̄` -/

theorem mem_fieldRange_of_isIntegral (ιC : Qbar →ₐ[ℚ] ℂ) {x : ℂ} (hx : IsIntegral ℚ x) :
    x ∈ ιC.fieldRange := by
  set P := minpoly ℚ x
  have hP0 : P.map (algebraMap ℚ ℂ) ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hx)
  have hroot : x ∈ (P.map (algebraMap ℚ ℂ)).roots := by
    rw [mem_roots hP0, IsRoot, eval_map_algebraMap]
    exact minpoly.aeval ℚ x
  have hmap : P.map (algebraMap ℚ ℂ) = (P.map (algebraMap ℚ Qbar)).map ιC.toRingHom := by
    rw [Polynomial.map_map]
    congr 1
    exact (ιC.comp_algebraMap).symm
  rw [hmap, ← roots_map_of_injective_of_card_eq_natDegree ιC.toRingHom.injective
    IsAlgClosed.card_roots_eq_natDegree] at hroot
  obtain ⟨r, -, hr⟩ := Multiset.mem_map.1 hroot
  exact ⟨r, hr⟩

/-! ## 2. Norms on `ℚ̄_ℓ` -/

section Norm

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- Copy of `SwanBridge.isIntegral_iff_norm_le_one` (forward direction). -/
theorem norm_le_one_of_isIntegral (y : PadicAlgCl ℓ) (hy : IsIntegral ℤ_[ℓ] y) : ‖y‖ ≤ 1 := by
  have hyQ : IsIntegral ℚ_[ℓ] y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hyQ)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[ℓ] hy, coeff_map]
  exact PadicInt.norm_le_one _

theorem norm_le_one_of_isIntegral_int (y : PadicAlgCl ℓ) (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 :=
  norm_le_one_of_isIntegral y (hy.tower_top)

theorem norm_natCast_prime : ‖(ℓ : PadicAlgCl ℓ)‖ < 1 := by
  have : (ℓ : PadicAlgCl ℓ) = algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) (ℓ : ℚ_[ℓ]) := by simp
  rw [this, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

end Norm

/-! ## 3. The place of a number field cut out by an embedding into `ℚ̄_ℓ` -/

section Place

variable {ℓ : ℕ} [Fact ℓ.Prime] {K : Type*} [Field K] [NumberField K] (τ : K →+* PadicAlgCl ℓ)

theorem norm_le_one_int (a : 𝓞 K) : ‖τ (a : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral_int _ ((a.isIntegral_coe).map τ.toIntAlgHom)

/-- The prime ideal `{a ∈ 𝓞_K : ‖τ a‖ < 1}`. -/
def placeIdeal : Ideal (𝓞 K) where
  carrier := {a | ‖τ (a : K)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at *
    calc ‖τ (c : K)‖ * ‖τ (a : K)‖ ≤ 1 * ‖τ (a : K)‖ :=
          mul_le_mul_of_nonneg_right (norm_le_one_int τ c) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact ha

theorem mem_placeIdeal {a : 𝓞 K} : a ∈ placeIdeal τ ↔ ‖τ (a : K)‖ < 1 := Iff.rfl

theorem natCast_mem_placeIdeal : (ℓ : 𝓞 K) ∈ placeIdeal τ := by
  rw [mem_placeIdeal]
  simpa using (norm_natCast_prime (ℓ := ℓ))

/-- The place `λ_τ` of `K` above `ℓ` cut out by `τ : K → ℚ̄_ℓ`. -/
def place : HeightOneSpectrum (𝓞 K) where
  asIdeal := placeIdeal τ
  isPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, mem_placeIdeal]
      simp
    · intro a b hab
      rw [mem_placeIdeal] at hab
      simp only [map_mul, norm_mul] at hab
      by_contra h
      push Not at h
      rw [mem_placeIdeal, mem_placeIdeal, not_lt, not_lt] at h
      have ha : ‖τ (a : K)‖ = 1 := le_antisymm (norm_le_one_int τ a) h.1
      have hb : ‖τ (b : K)‖ = 1 := le_antisymm (norm_le_one_int τ b) h.2
      rw [ha, hb, one_mul] at hab
      exact lt_irrefl _ hab
  ne_bot := by
    intro h
    have h1 := natCast_mem_placeIdeal (K := K) τ
    rw [h, Ideal.mem_bot] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero) h1

theorem norm_eq_one_of_not_mem {d : 𝓞 K} (hd : d ∉ (place τ).asIdeal) : ‖τ (d : K)‖ = 1 :=
  le_antisymm (norm_le_one_int τ d) (not_lt.1 hd)

/-- Valuation comparison: `v_λ(x) ≤ v_λ(y)` gives `‖τ x‖ ≤ ‖τ y‖`. -/
theorem norm_le_of_valuation_le {x y : K} (hy : y ≠ 0)
    (h : (place τ).valuation K x ≤ (place τ).valuation K y) : ‖τ x‖ ≤ ‖τ y‖ := by
  have hv : (place τ).valuation K (x / y) ≤ 1 := by
    rw [map_div₀]
    have : (place τ).valuation K y ≠ 0 := by simpa using hy
    exact (div_le_one₀ (zero_lt_iff.2 this)).2 h
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (place τ) _ hv
  have hd : ‖τ (d : 𝓞 K)‖ = 1 := norm_eq_one_of_not_mem τ d.2
  have hn := norm_le_one_int τ n
  have e := congrArg (fun z => ‖τ z‖) hnd
  simp only [map_mul, norm_mul, map_div₀, norm_div] at e
  have hd' : ‖τ (algebraMap (𝓞 K) K (d : 𝓞 K))‖ = 1 := hd
  rw [hd', mul_one] at e
  have hyn : 0 < ‖τ y‖ := norm_pos_iff.2 ((map_ne_zero τ).2 hy)
  have : ‖τ x‖ / ‖τ y‖ ≤ 1 := e ▸ hn
  exact (div_le_one₀ hyn).1 this

end Place

/-! ## 4. Extension to the completion `K_λ` -/

section Completion

variable {ℓ : ℕ} [Fact ℓ.Prime] {K : Type*} [Field K] [NumberField K] (τ : K →+* PadicAlgCl ℓ)

/-- `τ` as a ring hom on `WithVal v_λ`. -/
def τW : WithVal ((place τ).valuation K) →+* PadicAlgCl ℓ :=
  τ.comp (WithVal.equiv ((place τ).valuation K)).toRingHom

theorem continuous_τW : Continuous (τW τ) := by
  refine continuous_of_continuousAt_zero (τW τ).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (norm_natCast_prime (ℓ := ℓ))
  set y : K := (ℓ : K) ^ m
  have hy : y ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)
  set yW : WithVal ((place τ).valuation K) := WithVal.toVal _ y
  have hyv : (Valued.v : Valuation (WithVal ((place τ).valuation K)) _) yW ≠ 0 := by
    rw [← WithVal.apply_ofVal]
    simpa [yW] using hy
  have hres : (Valued.v : Valuation (WithVal ((place τ).valuation K)) _).restrict yW ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  rw [Filter.mem_map, Valued.mem_nhds_zero]
  refine ⟨Units.mk0 _ hres, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  show (τW τ) x ∈ s
  apply hball
  rw [Metric.mem_ball, dist_zero_right]
  have hle : (place τ).valuation K (WithVal.ofVal x) ≤ (place τ).valuation K y := by
    rw [WithVal.apply_ofVal, WithVal.apply_ofVal]
    exact hx.le
  calc ‖τW τ x‖ = ‖τ (WithVal.ofVal x)‖ := rfl
    _ ≤ ‖τ y‖ := norm_le_of_valuation_le τ hy hle
    _ = ‖(ℓ : PadicAlgCl ℓ)‖ ^ m := by simp [y]
    _ < ε := hm

/-- A finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` containing `τ(K)`. -/
def tgt : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) :=
  IntermediateField.adjoin ℚ_[ℓ] (Set.range (fun i => τ (Module.finBasis ℚ K i)))

instance : FiniteDimensional ℚ_[ℓ] (tgt τ) :=
  IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsIntegral.isIntegral x))

theorem mem_tgt (x : K) : τ x ∈ tgt τ := by
  rw [← (Module.finBasis ℚ K).sum_repr x, map_sum]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def, map_mul, eq_ratCast, map_ratCast]
  exact mul_mem (SubfieldClass.ratCast_mem _ _)
    (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

instance : CompleteSpace (tgt τ) := by
  have : FiniteDimensional ℚ_[ℓ] ((tgt τ).toSubalgebra.toSubmodule) :=
    (inferInstance : FiniteDimensional ℚ_[ℓ] (tgt τ))
  exact (Submodule.complete_of_finiteDimensional ((tgt τ).toSubalgebra.toSubmodule)).completeSpace_coe

/-- `τ` into the complete field `tgt τ`. -/
def τE : WithVal ((place τ).valuation K) →+* tgt τ :=
  (τW τ).codRestrict (tgt τ) (fun _ => mem_tgt τ _)

theorem continuous_τE : Continuous (τE τ) :=
  Continuous.subtype_mk (continuous_τW τ) _

/-- The continuous extension `K_λ → ℚ̄_ℓ` of `τ`. -/
def τhat : (place τ).adicCompletion K →+* PadicAlgCl ℓ :=
  ((tgt τ).val.toRingHom.comp (UniformSpace.Completion.extensionHom (τE τ) (continuous_τE τ))).comp
    (HeightOneSpectrum.adicCompletion.equiv K (place τ)).toRingHom

theorem continuous_τhat : Continuous (τhat τ) :=
  continuous_subtype_val.comp ((UniformSpace.Completion.continuous_extension).comp
    (HeightOneSpectrum.adicCompletion.continuous_toCompletion K (place τ)))

theorem τhat_algebraMap (x : K) : τhat τ (algebraMap K ((place τ).adicCompletion K) x) = τ x := by
  simp only [τhat, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  have : (HeightOneSpectrum.adicCompletion.equiv K (place τ))
      (algebraMap K ((place τ).adicCompletion K) x) =
      ((WithVal.toVal ((place τ).valuation K) x : WithVal _) :
        ((place τ).valuation K).Completion) := rfl
  rw [this, UniformSpace.Completion.extensionHom_coe]
  rfl

end Completion

end DSCoeffExt
