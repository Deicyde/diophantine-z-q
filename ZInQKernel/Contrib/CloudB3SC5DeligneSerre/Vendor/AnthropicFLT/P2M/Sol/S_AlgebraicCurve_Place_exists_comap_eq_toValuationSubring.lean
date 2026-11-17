/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring (git blob 42c56e545b0563a858264c3bd0bd214d92210608, sha256 d9763b7de38a7309f52b18bc71c97c694f01583265b3789b6730fbbeba14bc50).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve.Place
end AlgebraicCurve.Place
namespace AlgebraicCurve
end AlgebraicCurve

namespace P2MW.S_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring

set_option autoImplicit false

open IsDedekindDomain

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Place.coe_algebraMap Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring)
namespace Place
export _root_.AlgebraicCurve.Place (ext coe_algebraMap ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring toValuationSubring)
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

theorem rowMain (v : Place K F) :
    ∃ w : Place K F', w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring := by
  classical

  let A : Type _ := v.toValuationSubring
  letI : Algebra A F' := ((algebraMap F F').comp (algebraMap A F)).toAlgebra
  haveI : IsScalarTower A F F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  let C : Type _ := integralClosure A F'
  haveI : IsDedekindDomain C := integralClosure.isDedekindDomain A F F'
  haveI : IsFractionRing C F' := integralClosure.isFractionRing_of_finite_extension F F'
  letI : Algebra K C := ((algebraMap A C).comp (algebraMap K A)).toAlgebra
  have hAC : ∀ a : A, algebraMap C F' (algebraMap A C a) = algebraMap F F' (a : F) := fun a => rfl
  haveI : IsScalarTower K C F' := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap K F' a = algebraMap C F' (algebraMap A C (algebraMap K A a))
    rw [hAC, Place.coe_algebraMap, ← IsScalarTower.algebraMap_apply])

  have hinj : Function.Injective (algebraMap A C) := by
    intro a b h
    have h' := congrArg (algebraMap C F') h
    rw [hAC, hAC] at h'
    exact Subtype.ext ((algebraMap F F').injective h')
  obtain ⟨P, hPmax, hP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C)
    (IsLocalRing.maximalIdeal A) (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _))
  have hPne : P ≠ ⊥ := by
    intro hbot
    apply IsDiscreteValuationRing.not_a_field A
    rw [← hP, hbot]; exact Ideal.comap_bot_of_injective _ hinj -- [port]
  let w₀ : HeightOneSpectrum C := ⟨P, hPmax.isPrime, hPne⟩
  refine ⟨Place.ofHeightOneSpectrum (K := K) w₀, ?_⟩
  ext f
  rw [ValuationSubring.mem_comap, Place.ofHeightOneSpectrum_toValuationSubring,
    Valuation.mem_valuationSubring_iff]
  constructor
  · intro hle
    by_contra hfA
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hfA (zero_mem _)
    have hinvA : f⁻¹ ∈ v.toValuationSubring :=
      (v.toValuationSubring.mem_or_inv_mem f).resolve_left hfA

    have hnu : (⟨f⁻¹, hinvA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
      have hb' : f⁻¹ * (b : F) = 1 := by simpa [Subtype.ext_iff] using hb
      have hbf : (b : F) = f := by
        have := congrArg (fun z => f * z) hb'
        simpa [← mul_assoc, mul_inv_cancel₀ hf0] using this
      exact hfA (hbf ▸ b.2)
    have hP' : algebraMap A C ⟨f⁻¹, hinvA⟩ ∈ P := by
      rw [← Ideal.mem_comap, ← Ideal.under_def, hP] -- [port]
      exact hnu
    have hlt : w₀.valuation F' (algebraMap F F' f⁻¹) < 1 := by
      rw [show algebraMap F F' f⁻¹ = algebraMap C F' (algebraMap A C ⟨f⁻¹, hinvA⟩) from
        (hAC ⟨f⁻¹, hinvA⟩).symm]
      exact (w₀.valuation_lt_one_iff_mem _).mpr hP'
    rw [map_inv₀, map_inv₀] at hlt
    have hx0 : w₀.valuation F' (algebraMap F F' f) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr hf0)
    have : 1 < w₀.valuation F' (algebraMap F F' f) := (inv_lt_one₀ (zero_lt_iff.mpr hx0)).mp hlt
    exact absurd hle (not_le.mpr this)
  · intro hfA
    rw [show algebraMap F F' f = algebraMap C F' (algebraMap A C ⟨f, hfA⟩) from (hAC ⟨f, hfA⟩).symm]
    exact w₀.valuation_le_one _

end AlgebraicCurve.Place

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring.AlgebraicCurve in
theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F) :
    ∃ w : Place K F', w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring :=
  AlgebraicCurve.Place.rowMain v
