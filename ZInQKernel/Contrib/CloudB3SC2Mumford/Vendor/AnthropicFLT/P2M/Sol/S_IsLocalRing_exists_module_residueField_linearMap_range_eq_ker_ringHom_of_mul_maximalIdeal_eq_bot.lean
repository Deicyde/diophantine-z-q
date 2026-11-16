/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_IsLocalRing_exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_IsLocalRing_exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot

set_option autoImplicit false

open IsLocalRing

universe u

namespace E160VP
end E160VP

theorem solution
    {B B₁ : Type u} [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₁] (π : B →+* B₁)
    (hsmall : RingHom.ker π * maximalIdeal B = ⊥) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module (ResidueField B) V) (_ : Module.Finite (ResidueField B) V)
      (_ : Module B V) (_ : IsScalarTower B (ResidueField B) V)
      (_ : Module (ResidueField B)ᵐᵒᵖ V) (_ : IsCentralScalar (ResidueField B) V) (ι : V →ₗ[B] B),
      Function.Injective ι ∧ LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker π) := by
  classical

  let K : Submodule B B := RingHom.ker π
  have hV : Module.IsTorsionBySet B (↥K) (maximalIdeal B : Set B) := by
    rintro x ⟨m, hm⟩
    apply Subtype.ext
    change m • (x : B) = 0
    have : (x : B) * m ∈ RingHom.ker π * maximalIdeal B := Ideal.mul_mem_mul x.2 hm
    rw [hsmall, Ideal.mem_bot] at this
    rw [smul_eq_mul, mul_comm]; exact this
  have hV' : Module.IsTorsionBySet B (↥K) (↑(maximalIdeal B)) := hV
  letI instK : Module (ResidueField B) ↥K := hV'.module
  haveI instT : IsScalarTower B (ResidueField B) ↥K := hV'.isScalarTower
  haveI : Module.Finite B ↥K := Module.Finite.of_fg (IsNoetherian.noetherian K)
  haveI instF : Module.Finite (ResidueField B) ↥K :=
    Module.Finite.of_restrictScalars_finite B (ResidueField B) ↥K
  letI instM : Module (ResidueField B)ᵐᵒᵖ ↥K :=
    Module.compHom ↥K ((RingEquiv.toOpposite (ResidueField B)).symm : (ResidueField B)ᵐᵒᵖ →+* ResidueField B)
  haveI instC : IsCentralScalar (ResidueField B) ↥K := ⟨fun r x => rfl⟩
  refine ⟨↥K, inferInstance, instK, instF, inferInstance, instT, instM, instC, K.subtype,
    Subtype.val_injective, ?_⟩
  rw [Submodule.range_subtype, Submodule.restrictScalars_self]
