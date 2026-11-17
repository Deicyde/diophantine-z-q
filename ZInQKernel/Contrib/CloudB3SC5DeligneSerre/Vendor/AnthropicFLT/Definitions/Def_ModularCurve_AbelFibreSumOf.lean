/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_AbelFibreSumOf (git blob a57d1ef20df58fe65dce74dc4c1fbc9c6f24b875, sha256 8f9cbc5c92987c6535610b45e338cb04e7eb4b472e234f2a4f6cfff227a75396).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_AbelFibreSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve

variable (Γ : Subgroup SL(2, ℤ))

def orbifoldIndexOf (τ : ℍ) : ℕ :=
  Nat.card (MulAction.stabilizer
    (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) / 2

def abelFibreSumOf (F : ℍ → ℂ) (t : ℂ) : Module.Dual ℂ (CuspForm Γ 2) :=
  ∑ᶠ ξ : Quotient (MulAction.orbitRel Γ ℍ),
    ((valueMultiplicity F t ξ.out : ℂ) / (orbifoldIndexOf Γ ξ.out : ℂ)) •
      periodAlongOf Γ UpperHalfPlane.I ξ.out

theorem orbifoldIndexOf_def (τ : ℍ) :
    orbifoldIndexOf Γ τ =
      Nat.card (MulAction.stabilizer
        (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) / 2 :=
  rfl

theorem abelFibreSumOf_def (F : ℍ → ℂ) (t : ℂ) :
    abelFibreSumOf Γ F t =
      ∑ᶠ ξ : Quotient (MulAction.orbitRel Γ ℍ),
        ((valueMultiplicity F t ξ.out : ℂ) / (orbifoldIndexOf Γ ξ.out : ℂ)) •
          periodAlongOf Γ UpperHalfPlane.I ξ.out :=
  rfl

end ModularCurve

end
