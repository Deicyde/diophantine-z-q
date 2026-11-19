/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_LanglandsTunnell_ExplicitLift (git blob 94fc9108773e527af56a8c86ed16e5be2c60f620, sha256 8f87cb137e74a522aa653a074924f44330b35d1e23661f9424cf5c7eeb102a80).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

namespace FLT.ExplicitLift

open Matrix Zsqrtd

theorem neg_one_sq_eq_neg_two : (-1 : ZMod 3) * (-1) = ((-2 : ℤ) : ZMod 3) := by decide

noncomputable def red : ℤ√(-2) →+* ZMod 3 :=
  Zsqrtd.lift ⟨-1, neg_one_sq_eq_neg_two⟩

def sbar : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![-1, 1; -1, 0]

def tbar : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, -1; 1, 1]

def Slift : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) := !![⟨-1, 0⟩, ⟨1, 0⟩; ⟨-1, 0⟩, ⟨0, 0⟩]

def Tlift : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) := !![⟨1, 0⟩, ⟨-1, 0⟩; ⟨0, -1⟩, ⟨-1, 1⟩]

end FLT.ExplicitLift
