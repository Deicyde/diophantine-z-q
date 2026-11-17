/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_CuspForm_PeterssonOn (git blob 5f653afd2280bc63a8774cb802a42a78fa951775, sha256 eb1197ed69c45401a3eaa4f4b5575ec67e46476e8c6ddd4beb30e1919f1e4570).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Petersson
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace CuspForm

def peterssonOnIntegrand (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) : ℂ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ Γ,
    UpperHalfPlane.petersson k (f ∣[k] (q.out⁻¹ : SL(2, ℤ))) (g ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ

def peterssonOn (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ) : ℂ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
    (peterssonOnIntegrand Γ k f g)

theorem peterssonOn_def (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ) :
    peterssonOn Γ k f g =
      MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
        (peterssonOnIntegrand Γ k f g) := rfl

end CuspForm

end
