import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Residue
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic
import Mathlib.RingTheory.Valuation.LocalSubring

/-! The valuation attached to the chosen prime of the algebraic integers.
The local ring is a valuation ring because each element lies in a finite
number field, where the restricted prime already gives a valuation (c). -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open ZInQ.Contrib.ChebFD.C10 (Zbar Qbar GQ)
open scoped NumberField IntermediateField

namespace ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace

variable {g : GQ} {p : ℕ} (v : FrobeniusPlace g p)
variable {L : Type*} [Field L] [NumberField L]

/-- Contraction to a finite field gives the height-one prime for point reduction. -/
def restrictHeightOne [Fact p.Prime] (e : L →ₐ[ℚ] Qbar) : HeightOneSpectrum (𝓞 L) := by
  refine ⟨v.restrictPrime e, inferInstance, ?_⟩
  intro h
  have hm : (p : ℤ) ∈ (v.restrictPrime e).under ℤ := by
    rw [restrictPrime_under]
    exact Ideal.subset_span rfl
  change algebraMap ℤ (𝓞 L) (p : ℤ) ∈ v.restrictPrime e at hm
  rw [h, Ideal.mem_bot] at hm
  have hz : (p : 𝓞 L) = 0 := by simpa only [eq_intCast, Int.cast_natCast] using hm
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hz

local notation "Z" => (Subalgebra.toSubring (integralClosure ℤ Qbar))

/-- Localization of the absolute integers at the chosen prime. -/
abbrev localRing (v : FrobeniusPlace g p) := @LocalSubring.ofPrime _ _ Z v.prime v.isPrime

local notation "Sₚ" => (LocalSubring.toSubring (localRing v))

instance localRingIntAlgebra : Algebra Zbar Sₚ :=
  inferInstanceAs (Algebra (↥Z) Sₚ)

instance localRingLocalization : IsLocalization.AtPrime Sₚ v.prime :=
  IsLocalization.isLocalization_of_algEquiv _ (@LocalSubring.ofPrimeEquiv _ _ Z v.prime v.isPrime)

/-- The localized rings of integers of finite subfields map into this local ring. -/
def localRingMap [Fact p.Prime] (e : L →ₐ[ℚ] Qbar) :
    valuationSubringAtPrime L (v.restrictHeightOne e) →+* Sₚ :=
  IsLocalization.map Sₚ (integersMap e)
    (show (v.restrictHeightOne e).asIdeal.primeCompl ≤
      v.prime.primeCompl.comap (integersMap e) from fun _ ha => ha)

/-- The map of local rings uses the original field embedding on their elements. -/
theorem coe_localRingMap [Fact p.Prime] (e : L →ₐ[ℚ] Qbar)
    (x : valuationSubringAtPrime L (v.restrictHeightOne e)) :
    ((v.localRingMap e x : Sₚ) : Qbar) = e (x : L) := by
  have hh : (Subring.subtype Sₚ).comp (v.localRingMap e) =
      e.toRingHom.comp (Subring.subtype (ValuationSubring.toSubring (valuationSubringAtPrime L (v.restrictHeightOne e)))) := by
    apply IsLocalization.ringHom_ext (v.restrictHeightOne e).asIdeal.primeCompl
    ext y
    change ((v.localRingMap e (algebraMap (𝓞 L) _ y) : Sₚ) : Qbar) =
      e ((algebraMap (𝓞 L) (valuationSubringAtPrime L (v.restrictHeightOne e)) y : _) : L)
    simp only [localRingMap, IsLocalization.map_eq]
    change algebraMap Zbar Qbar (integersMap e y) = e (algebraMap (𝓞 L) L y)
    exact algebraMap_galRestrict'_apply ℤ (𝓞 L) Zbar e y
  exact RingHom.congr_fun hh x

/-- The localization of the algebraic integers at the exact Chebotarev prime
is a valuation subring of the algebraic closure. -/
def valuationRing [Fact p.Prime] : ValuationSubring Qbar :=
  .ofSubring Sₚ (fun x => by
    let L₀ := ℚ⟮x⟯
    let : FiniteDimensional ℚ L₀ := IntermediateField.adjoin.finiteDimensional (IsAlgebraic.isIntegral
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x))
    let : NumberField L₀ := ⟨⟩
    let x₀ : L₀ := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
    let e : L₀ →ₐ[ℚ] Qbar := L₀.val
    let A := valuationSubringAtPrime L₀ (v.restrictHeightOne e)
    rcases A.mem_or_inv_mem x₀ with hx | hx
    · left
      change e x₀ ∈ Sₚ
      exact v.coe_localRingMap e ⟨x₀, hx⟩ ▸ (v.localRingMap e ⟨x₀, hx⟩).property
    · right
      have he : e (x₀⁻¹) = x⁻¹ := by rw [map_inv₀]; rfl
      rw [← he]
      exact v.coe_localRingMap e ⟨x₀⁻¹, hx⟩ ▸ (v.localRingMap e ⟨x₀⁻¹, hx⟩).property)

#print axioms restrictHeightOne
#print axioms localRing
#print axioms localRingIntAlgebra
#print axioms localRingLocalization
#print axioms localRingMap
#print axioms coe_localRingMap
#print axioms valuationRing

end ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace
