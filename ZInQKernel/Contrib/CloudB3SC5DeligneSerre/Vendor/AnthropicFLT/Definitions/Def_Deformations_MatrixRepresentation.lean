/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_Deformations_MatrixRepresentation (git blob 12e189352f7040108f0fe3c3a0fd391a06500508, sha256 4756b21737d1fdaeef31995474f4a42313167a6d736ec76234fb3c02ad71155b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

namespace Deformation

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G]
variable {k : Type u} [Field k]

noncomputable def matrixRepresentation (ρ : G →* GL n k) : Representation k G (n → k) :=
  (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ)

@[simp]
lemma matrixRepresentation_apply (ρ : G →* GL n k) (g : G) :
    matrixRepresentation ρ g = Matrix.mulVecLin (ρ g).val :=
  Matrix.GeneralLinearGroup.coe_toLin _

end Deformation
