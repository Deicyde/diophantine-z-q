import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Textbook.Different

/-! Development file for `LadicDVRModelZp` (merged into `G15Ram.lean` §2f when done). -/

noncomputable section

namespace G15RamDev

open LadicCond
open PkgI4 (GQp)
open IsLocalRing Polynomial

variable {p : ℕ} [Fact p.Prime]

section Model

variable (F : Fld p)

/-- `ℤ_p → ℚ_p → F`. -/
@[reducible] def algZpF : Algebra ℤ_[p] F :=
  ((algebraMap ℚ_[p] F).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

attribute [local instance] algZpF

instance towerZpF : IsScalarTower ℤ_[p] ℚ_[p] F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The ring of integers `𝓞_F = integralClosure ℤ_p F`. -/
abbrev OF := integralClosure ℤ_[p] F

theorem norm_eq_spectral (x : F) : ‖(x : Kbar p)‖ = spectralNorm ℚ_[p] F x := by
  rw [spectralNorm.eq_of_tower (L := Kbar p) x, PadicAlgCl.spectralNorm_eq]
  rfl

variable [FiniteDimensional ℚ_[p] F]

/-- `y ∈ F` is integral over `ℤ_p` iff `‖y‖ ≤ 1` (copied from glue-sqrt-local's
`isIntegral_iff_spectralNorm_le_one`, with the norm of `ℚ̄_p`). -/
theorem isIntegral_iff_norm_le_one (y : F) :
    IsIntegral ℤ_[p] y ↔ ‖(y : Kbar p)‖ ≤ 1 := by
  rw [norm_eq_spectral]
  have hyQ : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyQ)]
  constructor
  · intro hy n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hy, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl : minpoly ℚ_[p] y ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyQ)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[p], hq, minpoly.aeval]

theorem mem_OF (y : F) : y ∈ OF F ↔ ‖(y : Kbar p)‖ ≤ 1 := isIntegral_iff_norm_le_one F y

theorem norm_le_one (b : OF F) : ‖((b : F) : Kbar p)‖ ≤ 1 := (mem_OF F b).mp b.2

theorem isUnit_iff_norm (b : OF F) : IsUnit b ↔ ‖((b : F) : Kbar p)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ‖(((u : OF F) : F) : Kbar p)‖ * ‖((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p)‖ = 1 := by
      rw [← norm_mul]
      have : ((u : OF F) : F) * (((u⁻¹ : (OF F)ˣ) : OF F) : F) = 1 := by
        rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
      have h2 : (((u : OF F) : F) : Kbar p) * ((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p) = 1 := by
        rw [← IntermediateField.coe_mul, this, IntermediateField.coe_one]
      rw [h2, norm_one]
    have a1 := norm_le_one F u
    have a2 := norm_le_one F (u⁻¹ : (OF F)ˣ)
    have b1 := norm_nonneg ((((u : OF F) : F) : Kbar p))
    have b2 := norm_nonneg (((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p))
    nlinarith
  · intro h
    have hx0 : (b : F) ≠ 0 := by
      intro h0
      rw [h0, IntermediateField.coe_zero, norm_zero] at h
      exact zero_ne_one h
    have hinv : ‖(((b : F)⁻¹ : F) : Kbar p)‖ = 1 := by
      rw [IntermediateField.coe_inv, norm_inv, h, inv_one]
    have hint : ((b : F)⁻¹) ∈ OF F := (mem_OF F _).mpr hinv.le
    refine IsUnit.of_mul_eq_one (⟨_, hint⟩ : OF F) ?_
    apply Subtype.ext
    simp [hx0]

theorem isLocalRing_OF : IsLocalRing (OF F) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, isUnit_iff_norm] at ha hb ⊢
  have ha' : ‖((a : F) : Kbar p)‖ < 1 := lt_of_le_of_ne (norm_le_one F a) ha
  have hb' : ‖((b : F) : Kbar p)‖ < 1 := lt_of_le_of_ne (norm_le_one F b) hb
  have := IsUltrametricDist.norm_add_le_max ((a : F) : Kbar p) ((b : F) : Kbar p)
  intro hab
  rw [Subalgebra.coe_add, IntermediateField.coe_add] at hab
  rw [hab] at this
  exact absurd this (not_le.mpr (max_lt ha' hb'))

end Model

section Model2

variable (F : Fld p) [FiniteDimensional ℚ_[p] F]

attribute [local instance] algZpF

theorem finite_OF : Module.Finite ℤ_[p] (OF F) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] F (OF F)

theorem noeth_OF : IsNoetherianRing (OF F) :=
  IsIntegralClosure.isNoetherianRing ℤ_[p] ℚ_[p] F (OF F)

theorem dedekind_OF : IsDedekindDomain (OF F) :=
  IsIntegralClosure.isDedekindDomain ℤ_[p] ℚ_[p] F (OF F)

omit [FiniteDimensional ℚ_[p] F] in
theorem coe_natCast_F (n : ℕ) : ((n : F) : Kbar p) = n := map_natCast (algebraMap F (Kbar p)) n

theorem p_mem : ((p : ℕ) : F) ∈ OF F := by
  rw [mem_OF, coe_natCast_F, norm_p_kbar]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)

theorem not_isField_OF : ¬ IsField (OF F) := by
  intro h
  have hp0 : (⟨((p : ℕ) : F), p_mem F⟩ : OF F) ≠ 0 := by
    intro h0
    have := congrArg (fun x : OF F => ((x : F) : Kbar p)) h0
    simp only [ZeroMemClass.coe_zero] at this
    rw [coe_natCast_F] at this
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) this
  obtain ⟨b, hb⟩ := h.mul_inv_cancel hp0
  have hu : IsUnit (⟨((p : ℕ) : F), p_mem F⟩ : OF F) := IsUnit.of_mul_eq_one _ hb
  rw [isUnit_iff_norm] at hu
  change ‖(((p : ℕ) : F) : Kbar p)‖ = 1 at hu
  rw [coe_natCast_F, norm_p_kbar, inv_eq_one] at hu
  have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

theorem dvr_OF : IsDiscreteValuationRing (OF F) := by
  haveI := isLocalRing_OF F
  haveI := noeth_OF F
  haveI := dedekind_OF F
  have h := (IsDiscreteValuationRing.TFAE (OF F) (not_isField_OF F)).out 1 3
  exact h.mpr (dedekind_OF F)

theorem torsionFree_OF : Module.IsTorsionFree ℤ_[p] (OF F) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  have hinj : Function.Injective (algebraMap ℤ_[p] F) :=
    (algebraMap ℚ_[p] F).injective.comp (FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p])
  intro a b h
  apply hinj
  have := congrArg (fun x : OF F => (x : F)) h
  exact this

variable {F}

/-- The uniformizer `ϖ` as an element of `𝓞_F`. -/
def unifB {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : OF F :=
  ⟨⟨ϖ, hϖ.1⟩, (mem_OF F _).mpr hϖ.2.1.le⟩

theorem coe_unifB {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : (((unifB hϖ : OF F) : F) : Kbar p) = ϖ := rfl

theorem norm_unif_pos {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : 0 < ‖ϖ‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpF : (p : Kbar p) ∈ F := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have hpn : ‖(p : Kbar p)‖ < 1 := by rw [norm_p_kbar]; exact inv_lt_one_of_one_lt₀ hp1
  have hp := hϖ.2.2 _ hpF hpn
  exact lt_of_lt_of_le (by rw [norm_p_kbar]; positivity) hp

theorem mem_span_pow_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (k : ℕ) (b : OF F) :
    b ∈ Ideal.span {unifB hϖ ^ k} ↔ ‖((b : F) : Kbar p)‖ ≤ ‖ϖ‖ ^ k := by
  have hϖ0 := norm_unif_pos hϖ
  have hϖne : ϖ ≠ 0 := norm_pos_iff.mp hϖ0
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    have : (((c * unifB hϖ ^ k : OF F) : F) : Kbar p) = ((c : F) : Kbar p) * ϖ ^ k := by
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, IntermediateField.coe_mul,
        IntermediateField.coe_pow, coe_unifB]
    rw [this, norm_mul, norm_pow]
    calc ‖((c : F) : Kbar p)‖ * ‖ϖ‖ ^ k ≤ 1 * ‖ϖ‖ ^ k :=
          mul_le_mul_of_nonneg_right (norm_le_one F c) (by positivity)
      _ = ‖ϖ‖ ^ k := one_mul _
  · intro h
    set ϖF : F := ⟨ϖ, hϖ.1⟩
    have hϖF : ϖF ≠ 0 := by
      intro h0
      exact hϖne (congrArg (fun x : F => (x : Kbar p)) h0)
    set c : F := (b : F) * (ϖF ^ k)⁻¹ with hc
    have hcn : ‖(c : Kbar p)‖ ≤ 1 := by
      rw [hc, IntermediateField.coe_mul, IntermediateField.coe_inv, IntermediateField.coe_pow,
        norm_mul, norm_inv, norm_pow]
      have : ‖((ϖF : F) : Kbar p)‖ = ‖ϖ‖ := rfl
      rw [this]
      rw [mul_inv_le_iff₀ (by positivity), one_mul]
      exact h
    refine ⟨⟨c, (mem_OF F c).mpr hcn⟩, ?_⟩
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow]
    change c * ϖF ^ k = (b : F)
    rw [hc, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hϖF), mul_one]

theorem maximalIdeal_eq {ϖ : Kbar p} (hϖ : IsUnif F ϖ) :
    haveI := isLocalRing_OF F
    maximalIdeal (OF F) = Ideal.span {unifB hϖ} := by
  haveI := isLocalRing_OF F
  ext b
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm, ← pow_one (unifB hϖ),
    mem_span_pow_iff, pow_one]
  constructor
  · intro h
    exact hϖ.2.2 _ (b : F).2 (lt_of_le_of_ne (norm_le_one F b) h)
  · intro h h1
    rw [h1] at h
    exact absurd hϖ.2.1 (not_lt.mpr h)

theorem mem_maximalIdeal_pow_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (k : ℕ) (b : OF F) :
    haveI := isLocalRing_OF F
    b ∈ maximalIdeal (OF F) ^ k ↔ ‖((b : F) : Kbar p)‖ ≤ ‖ϖ‖ ^ k := by
  haveI := isLocalRing_OF F
  rw [maximalIdeal_eq hϖ, Ideal.span_singleton_pow, mem_span_pow_iff]

end Model2

end G15RamDev
