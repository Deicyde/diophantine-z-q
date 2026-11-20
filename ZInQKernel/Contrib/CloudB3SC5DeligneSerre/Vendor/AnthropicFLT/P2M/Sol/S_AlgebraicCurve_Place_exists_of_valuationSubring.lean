/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_exists_of_valuationSubring (git blob 3dd546599a8e91f6db293012d902c875660f42e9, sha256 1b96bcc03022a9d1863fb829bd5bed910dc6e640fa5f2879f791c3919724e717).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_Place_exists_of_valuationSubring.AlgebraicCurve
end P2MW.S_AlgebraicCurve_Place_exists_of_valuationSubring.AlgebraicCurve
namespace IsDedekindDomain
end IsDedekindDomain
namespace AlgebraicCurve.Place
end AlgebraicCurve.Place

namespace P2MW.S_AlgebraicCurve_Place_exists_of_valuationSubring

set_option autoImplicit false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_Place_exists_of_valuationSubring.AlgebraicCurve
open _root_.IsDedekindDomain
open scoped IntermediateField.algebraAdjoinAdjoin

section Crux

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
variable (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
variable (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hA : A ≠ ⊤)
variable (hx : Transcendental K x) (hxA : x ∈ A)




omit [CharZero K] [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] in
include hx in
private theorem isDedekindDomain_Kx : IsDedekindDomain ((Algebra.adjoin K ({x} : Set F))) := by
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hrange : (Polynomial.aeval x : Polynomial K →ₐ[K] F).range = (Algebra.adjoin K ({x} : Set F)) :=
    (Algebra.adjoin_singleton_eq_range_aeval K x).symm
  let e : Polynomial K ≃ₐ[K] (Algebra.adjoin K ({x} : Set F)) :=
    (AlgEquiv.ofInjective _ hinj).trans (Subalgebra.equivOfEq _ _ hrange)
  haveI : IsPrincipalIdealRing ((Algebra.adjoin K ({x} : Set F))) :=
    IsPrincipalIdealRing.of_surjective (e : Polynomial K →+* (Algebra.adjoin K ({x} : Set F))) e.surjective
  infer_instance

include hx in
private theorem isDedekindDomain_integralClosure :
    IsDedekindDomain (integralClosure ((Algebra.adjoin K ({x} : Set F))) F) := by
  haveI := isDedekindDomain_Kx x hx
  haveI : Algebra.IsSeparable ((IntermediateField.adjoin K ({x} : Set F))) F := Algebra.IsSeparable.of_integral _ _
  exact integralClosure.isDedekindDomain ((Algebra.adjoin K ({x} : Set F))) ((IntermediateField.adjoin K ({x} : Set F))) F

omit [CharZero K] in
private theorem isFractionRing_integralClosure :
    IsFractionRing (integralClosure ((Algebra.adjoin K ({x} : Set F))) F) F :=
  integralClosure.isFractionRing_of_finite_extension (A := (Algebra.adjoin K ({x} : Set F))) ((IntermediateField.adjoin K ({x} : Set F))) F

omit [CharZero K] [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] in
include hxA hAK in
private theorem Kx_le_A : ((Algebra.adjoin K ({x} : Set F))).toSubring ≤ A.toSubring := by
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem z hz => obtain rfl : z = x := hz; exact hxA
  | algebraMap a => exact hAK a
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

private scoped instance : IsFractionRing (A : ValuationSubring F).toSubring F := by
  rw [← A.integer_valuation]; infer_instance

private scoped instance : IsFractionRing (A : ValuationSubring F) F :=
  inferInstanceAs (IsFractionRing A.toSubring F)

omit [CharZero K] [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] in
include hxA hAK in
private theorem integralClosure_Kx_le_A :
    (integralClosure ((Algebra.adjoin K ({x} : Set F))) F).toSubring ≤ A.toSubring := by
  intro y hy
  have hyI : IsIntegral ((Algebra.adjoin K ({x} : Set F))) y := hy
  letI : Algebra ((Algebra.adjoin K ({x} : Set F))) A :=
    (Subring.inclusion (Kx_le_A x A hAK hxA)).toAlgebra
  haveI : IsScalarTower ((Algebra.adjoin K ({x} : Set F))) A F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hyA : IsIntegral A y := hyI.tower_top
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff F).mp inferInstance hyA
  exact hz ▸ z.2

omit [CharZero K] [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] in
include hxA hAK in
private theorem inv_mem_of_notMem_maximalIdeal {b : integralClosure ((Algebra.adjoin K ({x} : Set F))) F}
    (hb : Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA) b
        ∉ IsLocalRing.maximalIdeal A) :
    ((b : F))⁻¹ ∈ A := by
  have hbA : (b : F) ∈ A := integralClosure_Kx_le_A x A hAK hxA b.2
  have hbU : IsUnit (⟨(b : F), hbA⟩ : A) := IsLocalRing.notMem_maximalIdeal.mp hb
  obtain ⟨u, hu⟩ := hbU
  have hcoe : (((u⁻¹ : Aˣ) : A) : F) * (b : F) = 1 := by
    have h1 : ((u⁻¹ : Aˣ) : A) * ⟨(b : F), hbA⟩ = 1 := by rw [← hu]; exact u.inv_mul
    have := congrArg (Subtype.val : A → F) h1; simpa using this
  exact (eq_inv_of_mul_eq_one_left hcoe) ▸ ((u⁻¹ : Aˣ) : A).2

omit [CharZero K] in
include hxA hAK hA in
private theorem idealOfA_ne_bot :
    (IsLocalRing.maximalIdeal A).comap
        (Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA)) ≠ ⊥ := by
  haveI : IsFractionRing (integralClosure ((Algebra.adjoin K ({x} : Set F))) F) F := isFractionRing_integralClosure x
  intro hP
  apply hA
  rw [eq_top_iff]
  intro y _
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := integralClosure ((Algebra.adjoin K ({x} : Set F))) F) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have haA : (a : F) ∈ A := integralClosure_Kx_le_A x A hAK hxA a.2
  have hbm : Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA) b
      ∉ IsLocalRing.maximalIdeal A := by
    intro hbm
    have hmem : b ∈ (IsLocalRing.maximalIdeal A).comap
        (Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA)) := hbm
    rw [hP, Ideal.mem_bot] at hmem
    exact hb0 hmem
  rw [← hab, div_eq_mul_inv]
  exact mul_mem haA (inv_mem_of_notMem_maximalIdeal x A hAK hxA hbm)

omit [CharZero K] [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] in
include hxA hAK in
private theorem place_of_idealOfA_le (P : HeightOneSpectrum (integralClosure ((Algebra.adjoin K ({x} : Set F))) F))
    [IsDedekindDomain (integralClosure ((Algebra.adjoin K ({x} : Set F))) F)] [IsFractionRing (integralClosure ((Algebra.adjoin K ({x} : Set F))) F) F]
    (hP : P.asIdeal = (IsLocalRing.maximalIdeal A).comap
        (Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA))) :
    (Place.ofHeightOneSpectrum (K := K) (F := F) P).toValuationSubring ≤ A := by
  rw [Place.ofHeightOneSpectrum_toValuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rintro y ⟨a, s, hs, rfl⟩
  have haA : (a : F) ∈ A := integralClosure_Kx_le_A x A hAK hxA a.2
  have hsm : Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA) s
      ∉ IsLocalRing.maximalIdeal A := by
    intro h
    exact hs (hP ▸ h : s ∈ P.asIdeal)
  exact mul_mem haA (inv_mem_of_notMem_maximalIdeal x A hAK hxA hsm)

include hx hxA hAK hA in
private theorem exists_place_of_mem :
    ∃ v : Place K F, v.toValuationSubring = A := by
  haveI := isDedekindDomain_integralClosure x hx
  haveI : IsFractionRing (integralClosure ((Algebra.adjoin K ({x} : Set F))) F) F := isFractionRing_integralClosure x
  let P : HeightOneSpectrum (integralClosure ((Algebra.adjoin K ({x} : Set F))) F) :=
    ⟨(IsLocalRing.maximalIdeal A).comap
        (Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA)),
      inferInstance, idealOfA_ne_bot x A hAK hA hxA⟩
  let V : Place K F := Place.ofHeightOneSpectrum P
  have hVA : V.toValuationSubring ≤ A := place_of_idealOfA_le x A hAK hxA P rfl
  exact ⟨V, ValuationSubring.eq_of_le_of_ne_top _ hVA hA⟩

end Crux

section Roots

namespace AlgebraicCurve export _root_.AlgebraicCurve (Place Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring) namespace Place export _root_.AlgebraicCurve.Place (ord ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring toValuationSubring) end AlgebraicCurve.Place
open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in

private theorem AlgebraicCurve.Place.exists_of_valuationSubring {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hA : A ≠ ⊤) : ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = A := by
  by_cases hx : Transcendental K x
  · rcases A.mem_or_inv_mem x with hxA | hxiA
    · exact exists_place_of_mem x A hAK hA hx hxA
    · have hx0 : x ≠ 0 := by
        rintro rfl; exact hx (isAlgebraic_zero (R := K))
      have hxinv : Transcendental K x⁻¹ := by
        rw [Transcendental, IsAlgebraic.inv_iff]; exact hx
      have hadj : IntermediateField.adjoin K ({x⁻¹} : Set F) =
          IntermediateField.adjoin K ({x} : Set F) := by
        refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
          (IntermediateField.adjoin_le_iff.mpr ?_)
        · intro z hz; rw [show z = x⁻¹ from hz]
          exact inv_mem (IntermediateField.mem_adjoin_simple_self K x)
        · intro z hz; rw [show z = x from hz]
          have h : x⁻¹⁻¹ ∈ IntermediateField.adjoin K ({x⁻¹} : Set F) :=
            inv_mem (IntermediateField.mem_adjoin_simple_self K x⁻¹)
          rwa [inv_inv] at h
      haveI : FiniteDimensional (IntermediateField.adjoin K ({x⁻¹} : Set F)) F := by
        rw [hadj]; infer_instance
      exact exists_place_of_mem x⁻¹ A hAK hA hxinv hxiA
  · rw [Transcendental, not_not] at hx
    refine absurd ?_ hA
    rw [eq_top_iff]
    intro y _
    haveI : FiniteDimensional K (IntermediateField.adjoin K ({x} : Set F)) :=
      IntermediateField.adjoin.finiteDimensional hx.isIntegral
    haveI : FiniteDimensional K F :=
      FiniteDimensional.trans K (IntermediateField.adjoin K ({x} : Set F)) F
    haveI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
    have hyI : IsIntegral K y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
    letI : Algebra K A :=
      ((algebraMap K F).codRestrict A.toSubring hAK).toAlgebra
    haveI : IsScalarTower K A F := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hyA : IsIntegral A y := hyI.tower_top
    obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff F).mp inferInstance hyA
    exact hz ▸ z.2

open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in

private theorem AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [CharZero K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (φ : F →+* F') (w : ValuationSubring F') (hwK : ∀ a : K, φ (algebraMap K F a) ∈ w) (hwx : ∃ y : F, φ y ∉ w) : ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = w.comap φ := by
  refine AlgebraicCurve.Place.exists_of_valuationSubring x (w.comap φ)
    (fun a => hwK a) ?_
  intro h
  obtain ⟨y, hy⟩ := hwx
  exact hy (h ▸ ValuationSubring.mem_top y : y ∈ w.comap φ)

end Roots

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hA : A ≠ ⊤) : ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = A :=
  AlgebraicCurve.Place.exists_of_valuationSubring x A hAK hA

#print axioms solution
