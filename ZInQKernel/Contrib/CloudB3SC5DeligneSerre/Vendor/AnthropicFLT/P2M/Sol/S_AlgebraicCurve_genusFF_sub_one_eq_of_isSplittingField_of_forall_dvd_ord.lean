/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord (git blob 572fd126be97fc34582a286a3ae94c1568d44f5e, sha256 3e868bf7ebc6cdb7cff406466ebf44949393965e04034fdf462c6416cfdb4359).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RiemannRochRows
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_map_ne_zero_of_tame
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord.AlgebraicCurve
end P2MW.S_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord.AlgebraicCurve
namespace Polynomial
end Polynomial
namespace IntermediateField
end IntermediateField

namespace P2MW.S_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord

noncomputable section

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord.AlgebraicCurve
open _root_.Polynomial
open _root_.IntermediateField

namespace AlgebraicCurve
export _root_.AlgebraicCurve (genusFF Place Divisor Divisor.degree IsCurveOver IsCurveOver.finiteResidue HasCanonicalDivisor canonicalDivisorOf genus WeilDualityAdelic FunctionFieldRiemannRoch ConstantsAreBase StichtenothGenusExists isCurveOver_of_transcendental_of_isSeparable isCurveOver_ratFunc hasCanonicalDivisor_of_isCurveOver dCoordGenerates_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver constantsAreBase_of_isAlgClosed stichtenothGenusExists_of_isCurveOver weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists genus_eq_genusFF degree_canonicalDivisor_eq_of_riemannRoch localUnitDerivativeRegular_of_isCurveOver map_ne_zero_of_tame two_mul_genus_sub_two_eq_of_degree_canonical Place.ramificationIndex_eq_one_of_forall_dvd_ord)
open _root_.AlgebraicCurve

namespace KummerGenusReduction

universe u v w

section Package

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

theorem charZero_of_charZero [CharZero L] : CharZero F :=
  charZero_of_injective_algebraMap (algebraMap L F).injective

variable [CharZero L]
  (x : F) (hx : Transcendental L x) (hfin : FiniteDimensional L⟮x⟯ F)

include hx hfin

theorem isCurveOver_pkg : IsCurveOver L F := by
  haveI := hfin
  haveI : CharZero L⟮x⟯ :=
    charZero_of_injective_algebraMap (algebraMap L L⟮x⟯).injective
  haveI : Algebra.IsSeparable L⟮x⟯ F := inferInstance
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable L F x hx hfin this

omit [CharZero L] in
theorem essFiniteType_pkg : Algebra.EssFiniteType L F :=
  AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfin

theorem hasCanonicalDivisor_pkg : HasCanonicalDivisor (K := L) (F := F) := by
  haveI := isCurveOver_pkg x hx hfin
  haveI := essFiniteType_pkg x hx hfin
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

theorem dCoordGenerates_pkg : ∀ v : Place L F, v.DCoordGenerates := by
  haveI := isCurveOver_pkg x hx hfin
  haveI := essFiniteType_pkg x hx hfin
  exact AlgebraicCurve.dCoordGenerates_of_isCurveOver

theorem localUnitDerivativeRegular_pkg :
    ∀ (w : Place L F) (u : F), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D L F u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D L F u)) := by
  haveI := isCurveOver_pkg x hx hfin
  haveI := essFiniteType_pkg x hx hfin
  haveI := dCoordGenerates_pkg x hx hfin
  exact AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver

variable [IsAlgClosed L]

theorem isRational_pkg (v : Place L F) : v.IsRational := by
  haveI := isCurveOver_pkg x hx hfin
  haveI : Module.Finite L v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral L v.ResidueField := Algebra.IsIntegral.of_finite L _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := v.ResidueField)).surjective

theorem riemannRoch_and_constantsAreBase_pkg :
    FunctionFieldRiemannRoch L F ∧ ConstantsAreBase L F := by
  classical
  haveI := hfin
  haveI := isCurveOver_pkg x hx hfin
  haveI := hasCanonicalDivisor_pkg x hx hfin
  haveI := dCoordGenerates_pkg x hx hfin

  haveI : IsCurveOver L (RatFunc L) := AlgebraicCurve.isCurveOver_ratFunc L
  haveI : Algebra.EssFiniteType L[X] (RatFunc L) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors L[X])
  haveI : Algebra.EssFiniteType L (RatFunc L) := Algebra.EssFiniteType.comp L L[X] (RatFunc L)
  haveI : ∀ v : Place L (RatFunc L), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver

  let e : RatFunc L ≃ₐ[L] L⟮x⟯ := RatFunc.algEquivOfTranscendental x hx
  letI : Algebra (RatFunc L) F := ((algebraMap L⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc L) F) (e.symm.toRingEquiv : L⟮x⟯ →+* RatFunc L)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap L⟮x⟯ F) := by
    ext y
    show algebraMap L⟮x⟯ F (e (e.symm y)) = algebraMap L⟮x⟯ F y
    rw [e.apply_symm_apply]
  haveI : IsScalarTower L (RatFunc L) F := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap L F a = algebraMap L⟮x⟯ F (e (algebraMap L (RatFunc L) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI hfd : FiniteDimensional (RatFunc L) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsIntegral (RatFunc L) F := Algebra.IsIntegral.of_finite _ _
  haveI : CharZero (RatFunc L) :=
    charZero_of_injective_algebraMap (algebraMap L (RatFunc L)).injective
  haveI : Algebra.IsSeparable (RatFunc L) F := inferInstance
  exact ⟨AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver,
    AlgebraicCurve.constantsAreBase_of_isAlgClosed L F⟩

theorem stichtenothGenusExists_pkg : StichtenothGenusExists L F := by
  haveI := isCurveOver_pkg x hx hfin
  haveI := essFiniteType_pkg x hx hfin
  exact AlgebraicCurve.stichtenothGenusExists_of_isCurveOver
    (riemannRoch_and_constantsAreBase_pkg x hx hfin).2

theorem weilDualityAdelic_pkg : WeilDualityAdelic L F :=
  AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
    (riemannRoch_and_constantsAreBase_pkg x hx hfin).1 (stichtenothGenusExists_pkg x hx hfin)

theorem genus_eq_genusFF_pkg :
    haveI := hasCanonicalDivisor_pkg x hx hfin
    genus L F = genusFF L F := by
  haveI := isCurveOver_pkg x hx hfin
  haveI := hasCanonicalDivisor_pkg x hx hfin
  haveI := dCoordGenerates_pkg x hx hfin
  exact AlgebraicCurve.genus_eq_genusFF (riemannRoch_and_constantsAreBase_pkg x hx hfin).1
    (weilDualityAdelic_pkg x hx hfin) (riemannRoch_and_constantsAreBase_pkg x hx hfin).2

theorem degree_canonical_pkg :
    haveI := hasCanonicalDivisor_pkg x hx hfin
    ∀ {ω : Ω[F⁄L]} (hω : ω ≠ 0),
      Divisor.degree (canonicalDivisorOf hω) = 2 * (genus L F : ℤ) - 2 := by
  intro ω hω
  haveI := isCurveOver_pkg x hx hfin
  haveI := hasCanonicalDivisor_pkg x hx hfin
  haveI := dCoordGenerates_pkg x hx hfin
  exact AlgebraicCurve.degree_canonicalDivisor_eq_of_riemannRoch
    (riemannRoch_and_constantsAreBase_pkg x hx hfin).1
    (riemannRoch_and_constantsAreBase_pkg x hx hfin).2 hω

end Package

section Cover

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]
  {F' : Type w} [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']

theorem transcendental_algebraMap {x : F} (hx : Transcendental L x) :
    Transcendental L (algebraMap F F' x) :=
  (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx

theorem finiteDimensional_adjoin_algebraMap (x : F) (hfin : FiniteDimensional L⟮x⟯ F)
    [FiniteDimensional F F'] :
    FiniteDimensional L⟮algebraMap F F' x⟯ F' := by
  haveI := hfin
  let φ : F →ₐ[L] F' := IsScalarTower.toAlgHom L F F'
  haveI : Module.Finite L⟮x⟯ F' := Module.Finite.trans F F'
  have hmap : L⟮x⟯.map φ = L⟮algebraMap F F' x⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  let e : L⟮x⟯ ≃ₐ[L] L⟮algebraMap F F' x⟯ :=
    (L⟮x⟯.equivMap φ).trans (IntermediateField.equivOfEq hmap)
  refine Module.Finite.of_equiv_equiv e.toRingEquiv (RingEquiv.refl F') ?_
  ext y
  rfl

end Cover

end KummerGenusReduction

end AlgebraicCurve

open AlgebraicCurve.KummerGenusReduction in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L]
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {q : ℕ} [Fact q.Prime] {f : F} (hf : ∀ g : F, g ^ q ≠ f)
    (hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord f)
    (F' : Type*) [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']
    [IsSplittingField F F' (X ^ q - C f)] :
    (genusFF L F' : ℤ) - 1 = q * ((genusFF L F : ℤ) - 1) := by
  classical
  obtain ⟨x, hx, hfin⟩ := hF
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩

  haveI : CharZero F := charZero_of_charZero (L := L)
  haveI := isCurveOver_pkg x hx hfin
  haveI := essFiniteType_pkg x hx hfin
  haveI := hasCanonicalDivisor_pkg x hx hfin
  haveI := dCoordGenerates_pkg x hx hfin

  haveI : FiniteDimensional F F' := IsSplittingField.finiteDimensional F' (X ^ q - C f)
  haveI : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  haveI : Algebra.IsSeparable F F' := inferInstance
  have hirr : Irreducible (X ^ q - C f) := X_pow_sub_C_irreducible_of_prime hq hf
  have hζ : (primitiveRoots q F).Nonempty := by
    haveI : NeZero (q : L) := ⟨Nat.cast_ne_zero.mpr hq.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L q
    exact ⟨algebraMap L F ζ, (mem_primitiveRoots hq.pos).mpr
      (hζ.map_of_injective (algebraMap L F).injective)⟩
  have hrank : Module.finrank F F' = q := finrank_of_isSplittingField_X_pow_sub_C hζ hirr F'
  set α : F' := rootOfSplitsXPowSubC (NeZero.pos q) f F' with hαdef
  have hα : α ^ q = algebraMap F F' f := rootOfSplitsXPowSubC_pow f F'
  have htop : F⟮α⟯ = ⊤ := IntermediateField.adjoin_root_eq_top_of_isSplittingField hζ hirr hα

  set x' : F' := algebraMap F F' x with hx'def
  have hx' : Transcendental L x' := transcendental_algebraMap hx
  have hfin' : FiniteDimensional L⟮x'⟯ F' := finiteDimensional_adjoin_algebraMap x hfin
  haveI := isCurveOver_pkg x' hx' hfin'
  haveI := essFiniteType_pkg x' hx' hfin'
  haveI := hasCanonicalDivisor_pkg x' hx' hfin'
  haveI := dCoordGenerates_pkg x' hx' hfin'

  have he : ∀ w : Place L F', w.ramificationIndex F = 1 := fun w =>
    AlgebraicCurve.Place.ramificationIndex_eq_one_of_forall_dvd_ord hf hα htop hdvd w
      (isRational_pkg x' hx' hfin' w)
  have htame : ∀ w : Place L F', ((w.ramificationIndex F : ℕ) : F') ≠ 0 := fun w => by
    rw [he w, Nat.cast_one]
    exact one_ne_zero
  have hreg := localUnitDerivativeRegular_pkg x' hx' hfin'

  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄L])
  obtain ⟨w₀⟩ := (stichtenothGenusExists_pkg x' hx' hfin').1
  have hω₀' : KaehlerDifferential.map L L F F' ω₀ ≠ 0 :=
    AlgebraicCurve.map_ne_zero_of_tame hreg htame w₀ hω₀

  have hK := degree_canonical_pkg x hx hfin hω₀
  have hK' := degree_canonical_pkg x' hx' hfin' hω₀'
  have hRH := AlgebraicCurve.two_mul_genus_sub_two_eq_of_degree_canonical
    hreg htame hω₀ hω₀' hK hK'
  have hsum : ∑ᶠ w : Place L F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) = 0 := by
    have : ∀ w : Place L F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) = 0 := fun w => by
      rw [he w]
      simp
    simp_rw [this, finsum_zero]
  rw [hsum, add_zero, hrank] at hRH

  rw [genus_eq_genusFF_pkg x hx hfin, genus_eq_genusFF_pkg x' hx' hfin'] at hRH
  have h2 : (2 : ℤ) * ((genusFF L F' : ℤ) - 1) = 2 * (q * ((genusFF L F : ℤ) - 1)) := by
    linear_combination hRH
  exact mul_left_cancel₀ two_ne_zero h2
