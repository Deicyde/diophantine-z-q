/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_KaehlerDifferential_D_ne_zero_of_transcendental (git blob 20093a4e20534f93205290f629c39f8d67d83c39, sha256 3742fa087ce318085aa50599044e139217fb69f8270e4e38896bd973f9ed8d54).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Polynomial
end Polynomial
namespace KaehlerDifferential
end KaehlerDifferential
namespace P2MW.S_KaehlerDifferential_D_ne_zero_of_transcendental.KaehlerDifferential
end P2MW.S_KaehlerDifferential_D_ne_zero_of_transcendental.KaehlerDifferential

namespace P2MW.S_KaehlerDifferential_D_ne_zero_of_transcendental

noncomputable section
open _root_.Polynomial
open _root_.KaehlerDifferential
open _root_.P2MW.S_KaehlerDifferential_D_ne_zero_of_transcendental.KaehlerDifferential

namespace KaehlerDifferential
export _root_.KaehlerDifferential (tensorKaehlerEquivOfFormallyEtale polynomialEquiv tensorKaehlerEquivOfFormallyEtale_apply mapBaseChange_tmul D map_D map)
namespace FF2
open _root_.KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {x : F} (hx : Transcendental K x)
  [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]

include hx in

private theorem exists_basis : ∃ b : Module.Basis Unit F Ω[F⁄K], b () = D K F x := by

  let e : RatFunc K ≃ₐ[K] IntermediateField.adjoin K ({x} : Set F) := RatFunc.algEquivOfTranscendental x hx
  letI algKx : Algebra K[X] (IntermediateField.adjoin K ({x} : Set F)) := (e.toAlgHom.toRingHom.comp (algebraMap K[X] (RatFunc K))).toAlgebra
  letI algF : Algebra K[X] F := ((algebraMap (IntermediateField.adjoin K ({x} : Set F)) F).comp (algebraMap K[X] (IntermediateField.adjoin K ({x} : Set F)))).toAlgebra
  haveI : IsScalarTower K[X] (IntermediateField.adjoin K ({x} : Set F)) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K K[X] (IntermediateField.adjoin K ({x} : Set F)) := IsScalarTower.of_algebraMap_eq (fun c => by
    change _ = (e.toAlgHom.toRingHom.comp (algebraMap K[X] (RatFunc K))) (C c)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_algHom]
    rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K), AlgEquiv.commutes])
  haveI : IsScalarTower K K[X] F := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply K (IntermediateField.adjoin K ({x} : Set F)) F, IsScalarTower.algebraMap_apply K[X] (IntermediateField.adjoin K ({x} : Set F)) F,
      ← IsScalarTower.algebraMap_apply K K[X] (IntermediateField.adjoin K ({x} : Set F))])

  haveI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])
  haveI : Algebra.FormallyEtale K[X] (IntermediateField.adjoin K ({x} : Set F)) :=
    Algebra.FormallyEtale.of_equiv (R := K[X]) (A := RatFunc K) { e with commutes' := fun _ => rfl }
  haveI : Algebra.FormallyEtale (IntermediateField.adjoin K ({x} : Set F)) F := Algebra.FormallyEtale.of_isSeparable (IntermediateField.adjoin K ({x} : Set F)) F
  haveI : Algebra.FormallyEtale K[X] F := Algebra.FormallyEtale.comp K[X] (IntermediateField.adjoin K ({x} : Set F)) F

  let b₀ : Module.Basis Unit K[X] Ω[K[X]⁄K] :=
    (Module.Basis.singleton Unit K[X]).map (polynomialEquiv K).symm
  have hb₀ : b₀ () = D K K[X] X := by simp [b₀]
  let ψ := tensorKaehlerEquivOfFormallyEtale K K[X] F
  refine ⟨(b₀.baseChange F).map ψ, ?_⟩
  have hX : algebraMap K[X] F X = x := by
    change algebraMap (IntermediateField.adjoin K ({x} : Set F)) F (e (algebraMap K[X] (RatFunc K) X)) = x
    rw [RatFunc.algebraMap_X]
    exact RatFunc.algEquivOfTranscendental_X x hx
  simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb₀, ψ,
    tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, map_D, hX]

end KaehlerDifferential.FF2

theorem solution (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    KaehlerDifferential.D K F x ≠ 0 := by
  obtain ⟨b, hb⟩ := KaehlerDifferential.FF2.exists_basis hx
  simpa [hb] using b.ne_zero ()

end
