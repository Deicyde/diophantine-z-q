/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_lt
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_lt

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function

namespace ProjSpaceCech
-- [port] was: p2m_export "ProjSpaceCech" "Twist.cochain_subsingleton_of_lt Twist.H"
export _root_.ProjSpaceCech (Twist.cochain_subsingleton_of_lt Twist.H)
-- [port] was: p2m_open "ProjSpaceCech"
open _root_.ProjSpaceCech

section Cohomology

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

namespace Twist
-- [port] was: p2m_export "ProjSpaceCech.Twist" "d cochain_subsingleton_of_lt H"
export _root_.ProjSpaceCech.Twist (d cochain_subsingleton_of_lt H)
end Twist
-- [port] was: p2m_open_scoped "ProjSpaceCech.Twist" in
open scoped _root_.ProjSpaceCech.Twist in

theorem Twist.subsingleton_cohomology_of_lt {i : ℕ} (hi : n < i) :
    Subsingleton (Twist.H R n d i) := by
  rcases i with _ | j
  · exact absurd hi (Nat.not_lt_zero n)
  dsimp only [Twist.H]
  have hsub := Twist.cochain_subsingleton_of_lt R n d hi
  exact ⟨fun x y => Quotient.inductionOn₂' x y fun a b =>
    congrArg _ (Subtype.ext (hsub.elim a.1 b.1))⟩

end Cohomology

end ProjSpaceCech

theorem solution (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) {i : ℕ}
    (hi : n < i) : Subsingleton (ProjSpaceCech.Twist.H R n d i) :=
  ProjSpaceCech.Twist.subsingleton_cohomology_of_lt R n d hi

end
