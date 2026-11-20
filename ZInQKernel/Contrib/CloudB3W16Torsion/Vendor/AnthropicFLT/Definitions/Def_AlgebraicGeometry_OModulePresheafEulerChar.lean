/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

def cechFinrank : ℕ → ℕ
  | 0 => Module.finrank R (F.H0 K)
  | i + 1 => Module.finrank R (F.HSucc K i)

theorem cechFinrank_zero : F.cechFinrank K 0 = Module.finrank R (F.H0 K) := rfl

theorem cechFinrank_succ (i : ℕ) : F.cechFinrank K (i + 1) = Module.finrank R (F.HSucc K i) := rfl

def eulerChar : ℤ :=
  ∑ i ∈ Finset.range (Fintype.card K.ι), (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ)

theorem eulerChar_def :
    F.eulerChar K = ∑ i ∈ Finset.range (Fintype.card K.ι), (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ) := rfl

end AlgebraicGeometry.OModulePresheaf

end
