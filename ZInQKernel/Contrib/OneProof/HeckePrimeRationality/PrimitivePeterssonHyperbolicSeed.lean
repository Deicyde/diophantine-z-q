import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitivePeterssonStripIntegral

/-!
# The cuspidal strip seed for the genuine invariant measure

The coordinate measure comparison identifies the proved Lebesgue seed with
conjugate(f(τ)) Im(τ)^k against the actual measure dx dy / y². Both absolute
integrability and zero integral are transported, without a new measure
convention or an Eisenstein orthogonality hypothesis.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set UpperHalfPlane Complex
open scoped Topology MatrixGroups ModularForm ComplexConjugate NNReal

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson

/-- Real coordinates on the actual upper half plane. -/
def coordinates (τ : ℍ) : ℝ × ℝ := (τ.re,τ.im)

/-- Pullback of ordinary complex Lebesgue measure, before the hyperbolic density. -/
def flatVolume : Measure ℍ := Measure.comap UpperHalfPlane.coe (volume : Measure ℂ)

lemma coordinates_measurableEmbedding : MeasurableEmbedding coordinates :=
  Complex.measurableEquivRealProd.measurableEmbedding.comp UpperHalfPlane.measurableEmbedding_coe

lemma coordinates_measurePreserving : MeasurePreserving coordinates flatVolume
    ((volume : Measure (ℝ × ℝ)).restrict {p | 0 < p.2}) := by
  have hc : MeasurePreserving UpperHalfPlane.coe flatVolume
      ((volume : Measure ℂ).restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe,UpperHalfPlane.measurableEmbedding_coe.map_comap volume⟩
  have hp := Complex.volume_preserving_equiv_real_prod.restrict_image_emb
    Complex.measurableEquivRealProd.measurableEmbedding (range UpperHalfPlane.coe)
  have hs : Complex.measurableEquivRealProd '' range UpperHalfPlane.coe = {p : ℝ × ℝ | 0 < p.2} := by
    ext p
    constructor
    · rintro ⟨z,⟨τ,rfl⟩,rfl⟩
      exact τ.im_pos
    · intro hp
      let τ : ℍ := ⟨(p.1 : ℂ)+p.2*Complex.I,by simpa using hp⟩
      exact ⟨τ,⟨τ,rfl⟩,by simp [Complex.measurableEquivRealProd_apply,τ]⟩
  rw [hs] at hp
  exact hp.comp hc

/-- The actual positive strip; positivity of the height is built into ℍ. -/
def strip (h : ℝ) : Set ℍ := {τ | τ.re ∈ Icc 0 h}

lemma strip_measurable (h : ℝ) : MeasurableSet (strip h) := by
  exact measurableSet_Icc.preimage (by fun_prop : Measurable UpperHalfPlane.re)

lemma coordinates_preimage_strip (h : ℝ) :
    coordinates ⁻¹' (Icc 0 h ×ˢ Ioi (0 : ℝ)) = strip h := by
  ext τ
  simp [coordinates,strip,τ.im_pos]

/-- The true invariant-measure seed, with weight k before density is applied. -/
def hyperSeed {Γ : Subgroup (GL (Fin 2) ℝ)} (k : ℕ) (f : CuspForm Γ (k : ℤ)) (τ : ℍ) : ℂ :=
  conj (f τ)*(τ.im : ℂ)^k

lemma density_smul_hyperSeed {Γ : Subgroup (GL (Fin 2) ℝ)} (k : ℕ) (hk : 3 ≤ k)
    (f : CuspForm Γ (k : ℤ)) (τ : ℍ) :
    ((1 / NNReal.mk τ.im τ.im_pos.le : ℝ≥0)^2) • hyperSeed k f τ = planeSeed k f (coordinates τ) := by
  have hτ : (τ.re : ℂ)+τ.im*Complex.I = τ := by
    apply Complex.ext <;> simp
  simp only [planeSeed,coordinates,hτ,UpperHalfPlane.ofComplex_apply,hyperSeed,
    NNReal.smul_def,real_smul]
  simp only [NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_mk,
    Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one]
  have he : k = (k-2)+2 := (Nat.sub_add_cancel (by omega : 2 ≤ k)).symm
  have hpow : (τ.im : ℂ)^k = (τ.im : ℂ)^(k-2)*(τ.im : ℂ)^2 := by
    conv_lhs => rw [he,pow_add]
  rw [hpow]
  field_simp [Complex.ofReal_ne_zero.mpr τ.im_ne_zero]

lemma flatSeed_integrable_strip {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (k : ℕ) (hk : 3 ≤ k) (f : CuspForm Γ (k : ℤ))
    (h : ℝ) (hh : 0 < h) (hp : h ∈ Γ.strictPeriods) :
    IntegrableOn (fun τ => planeSeed k f (coordinates τ)) (strip h) flatVolume := by
  have hi := planeSeed_integrable_strip k hk f h hh hp
  have hs : (Icc 0 h ×ˢ Ioi (0 : ℝ)) ⊆ {p : ℝ × ℝ | 0 < p.2} := fun p hp => hp.2
  have hr : IntegrableOn (planeSeed k f) (Icc 0 h ×ˢ Ioi (0 : ℝ))
      ((volume : Measure (ℝ × ℝ)).restrict {p | 0 < p.2}) := by
    change Integrable (planeSeed k f)
      (((volume : Measure (ℝ × ℝ)).restrict {p | 0 < p.2}).restrict (Icc 0 h ×ˢ Ioi (0 : ℝ)))
    rw [Measure.restrict_restrict_of_subset hs]
    exact hi
  rw [← coordinates_preimage_strip]
  exact (coordinates_measurePreserving.integrableOn_comp_preimage coordinates_measurableEmbedding).mpr hr

/-- Absolute integrability of the actual invariant-measure cusp seed. -/
theorem hyperSeed_integrable_strip {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (k : ℕ) (hk : 3 ≤ k) (f : CuspForm Γ (k : ℤ))
    (h : ℝ) (hh : 0 < h) (hp : h ∈ Γ.strictPeriods) :
    IntegrableOn (hyperSeed k f) (strip h) (volume : Measure ℍ) := by
  rw [IntegrableOn,UpperHalfPlane.volume_def,restrict_withDensity (strip_measurable h)]
  apply (integrable_withDensity_iff_integrable_smul (by fun_prop)).mpr
  simp only [density_smul_hyperSeed k hk f]
  exact flatSeed_integrable_strip k hk f h hh hp

/-- The actual invariant-measure strip seed has zero integral. -/
theorem hyperSeed_strip_integral_zero {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (k : ℕ) (hk : 3 ≤ k) (f : CuspForm Γ (k : ℤ))
    (h : ℝ) (hh : 0 < h) (hp : h ∈ Γ.strictPeriods) :
    ∫ τ in strip h, hyperSeed k f τ = 0 := by
  rw [UpperHalfPlane.volume_def,setIntegral_withDensity_eq_setIntegral_smul (by fun_prop)
    (hyperSeed k f) (strip_measurable h)]
  simp only [density_smul_hyperSeed k hk f]
  have he := coordinates_measurePreserving.setIntegral_preimage_emb
    coordinates_measurableEmbedding (planeSeed k f) (Icc 0 h ×ˢ Ioi (0 : ℝ))
  rw [coordinates_preimage_strip] at he
  have hs : (Icc 0 h ×ˢ Ioi (0 : ℝ)) ⊆ {p : ℝ × ℝ | 0 < p.2} := fun p hp => hp.2
  rw [Measure.restrict_restrict_of_subset hs] at he
  change (∫ τ in strip h, planeSeed k f (coordinates τ) ∂flatVolume) = 0
  rw [he]
  exact planeSeed_strip_integral_zero k hk f h hh hp

end ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson
