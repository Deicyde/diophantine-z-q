/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField (git blob e7ef78a81d7aead56a050f4ee8c0881407f55283, sha256 ff3ab1fc1632c143784d8ed9d0b43a0db8a810102bb058a81d60437b56fc48b3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.AlgebraicCurve
end P2MW.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.AlgebraicCurve
namespace ModularCurve
end ModularCurve
namespace AlgebraicCurve.Place
end AlgebraicCurve.Place

namespace P2MW.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField

set_option autoImplicit false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.AlgebraicCurve
open _root_.ModularCurve

namespace AlgebraicCurve export _root_.AlgebraicCurve (Place Place.deg) namespace Place export _root_.AlgebraicCurve.Place (ResidueField deg) end AlgebraicCurve.Place
open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in

private theorem AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.deg = 1 ↔ Function.Surjective (algebraMap K v.ResidueField) := by
  unfold Place.deg
  rw [show Function.Surjective (algebraMap K v.ResidueField)
        ↔ Function.Bijective (algebraMap K v.ResidueField) from
      ⟨fun h => ⟨(algebraMap K v.ResidueField).injective, h⟩, fun h => h.2⟩]
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.AlgebraicCurve ModularCurve in

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.deg = 1 ↔ Function.Surjective (algebraMap K v.ResidueField) :=
  AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField v

#print axioms solution
