import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.LocalFrobenius
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.ResidueDegree

/-! A finite prime and the absolute prime give compatible local rings and
residue fields (the on-the-spot restriction calculation (c)). -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing TauCeti
open ZInQ.Contrib.ChebFD.C10 (Zbar Qbar GQ)
open scoped NumberField

namespace ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace

variable {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p)
variable {L : Type*} [Field L] [NumberField L] (e : L →ₐ[ℚ] Qbar)

local notation "u" => (restrictHeightOne v e)
local notation "S" => (valuationSubringAtPrime L u)
local notation "Sₚ" => (LocalSubring.toSubring (localRing v))
local notation "wₚ" => (ValuationSubring.valuation (valuationRing v))
local notation "Rₚ" => (Valuation.valuationSubring wₚ)
local notation "wL" => (IsDedekindDomain.HeightOneSpectrum.valuation L u)
local notation "RL" => (Valuation.valuationSubring wL)

/-- The contracted prime has the same underlying rational prime. -/
theorem rationalPrimeBelow_restrict : rationalPrimeBelow u = p := by
  rw [rationalPrimeBelow_def]
  change Ideal.absNorm ((v.restrictPrime e).under ℤ) = p
  rw [v.restrictPrime_under e]
  exact ZInQ.Contrib.ChebFD.C10.card_quot p

instance localRingMap_isLocal : IsLocalHom (v.localRingMap e) := by
  constructor
  intro a ha
  obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq (HeightOneSpectrum.asIdeal u).primeCompl a
  simp only [localRingMap, IsLocalization.map_mk'] at ha
  exact (IsLocalization.AtPrime.isUnit_mk'_iff S (HeightOneSpectrum.asIdeal u) x y).mpr
    ((IsLocalization.AtPrime.isUnit_mk'_iff Sₚ v.prime _ _).mp ha)

private def finiteValuationEquiv : RL ≃+* S :=
  RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
    (valuationSubringAtPrime_eq_valuationSubring (K := L) u).symm)

/-- The inclusion of valuation rings associated to a finite subfield. -/
def valuationRingMap : RL →+* Rₚ :=
  v.localValuationEquiv.toRingHom.comp ((v.localRingMap e).comp
    (finiteValuationEquiv v e).toRingHom)

instance valuationRingMap_isLocal : IsLocalHom (v.valuationRingMap e) := by
  constructor
  intro a ha
  change IsUnit (v.localValuationEquiv (v.localRingMap e (finiteValuationEquiv v e a))) at ha
  have h₁ : IsUnit (v.localRingMap e (finiteValuationEquiv v e a)) := by
    simpa only [RingEquiv.symm_apply_apply] using ha.map v.localValuationEquiv.symm
  simpa only [RingEquiv.symm_apply_apply] using
    (isUnit_of_map_unit (v.localRingMap e) _ h₁).map (finiteValuationEquiv v e).symm

/-- The map of valuation rings restricts the original embedding. -/
theorem coe_valuationRingMap (x : RL) : (v.valuationRingMap e x : Qbar) = e (x : L) :=
  v.coe_localRingMap e (finiteValuationEquiv v e x)

/-- Integrality in the absolute place is equivalent to integrality at its contraction. -/
theorem valuation_le_one_restrict (x : L) : wₚ (e x) ≤ 1 ↔ wL x ≤ 1 := by
  constructor
  · intro hx
    by_contra hn
    have hlt : wL x⁻¹ < 1 := by
      rw [map_inv₀, inv_lt_one₀ (zero_lt_one.trans (lt_of_not_ge hn))]
      exact lt_of_not_ge hn
    let a : RL := ⟨x⁻¹, hlt.le⟩
    have hnu : ¬ IsUnit a := fun hu => (residue_ne_zero_iff_isUnit a).mpr hu
      ((residue_eq_zero_iff a).mpr ((Valuation.mem_maximalIdeal_iff (v := wL)).mpr hlt))
    apply hnu
    apply isUnit_of_map_unit (v.valuationRingMap e) a
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨e x, hx⟩, Subtype.ext ?_⟩
    change (v.valuationRingMap e a : Qbar) * e x = 1
    rw [v.coe_valuationRingMap e, ← map_mul, inv_mul_cancel₀, map_one]
    exact fun he => hn (by simp [he])
  · intro hx
    let a : RL := ⟨x, hx⟩
    rw [← v.coe_valuationRingMap e a]
    exact (v.valuationRingMap e a).property

/-- The embedding of finite residue fields induced by the exact place. -/
def valuationResidueMap : ResidueField RL →+* ResidueField Rₚ :=
  ResidueField.map (v.valuationRingMap e)

/-- Coordinate reduction commutes with the embedding of a finite subfield. -/
theorem valuationResidueMap_residue (x : L) (hx : wL x ≤ 1) :
    v.valuationResidueMap e (residue RL ⟨x, hx⟩) =
      residue Rₚ ⟨e x, (v.valuation_le_one_restrict e x).mpr hx⟩ := by
  rw [valuationResidueMap, ResidueField.map_residue]
  exact congrArg (residue Rₚ) (Subtype.ext (v.coe_valuationRingMap e ⟨x, hx⟩))

/-- The residue field of the finite valuation is the quotient by the contracted prime. -/
def finiteValuationResidueEquiv : (𝓞 L ⧸ v.restrictPrime e) ≃+* ResidueField RL :=
  (IsLocalization.AtPrime.equivQuotMaximalIdeal (HeightOneSpectrum.asIdeal u) S).toRingEquiv.trans
    (ResidueField.mapEquiv (finiteValuationEquiv v e).symm)

#print axioms rationalPrimeBelow_restrict
#print axioms localRingMap_isLocal
#print axioms finiteValuationEquiv
#print axioms valuationRingMap
#print axioms valuationRingMap_isLocal
#print axioms coe_valuationRingMap
#print axioms valuation_le_one_restrict
#print axioms valuationResidueMap
#print axioms valuationResidueMap_residue
#print axioms finiteValuationResidueEquiv

end ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace
