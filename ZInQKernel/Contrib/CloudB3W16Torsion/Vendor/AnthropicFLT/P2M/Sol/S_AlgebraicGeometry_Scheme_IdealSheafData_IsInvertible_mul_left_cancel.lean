/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel

set_option autoImplicit false

universe u

namespace Ideal p2m_export "Ideal" "span mem_span_singleton_mul" end Ideal
open scoped Ideal in
theorem Ideal.span_singleton_mul_right_injective_of_mem_nonZeroDivisors {R : Type*} [CommRing R]
    {a : R} (ha : a ∈ nonZeroDivisors R) :
    Function.Injective fun K : Ideal R ↦ Ideal.span {a} * K := by

  suffices key : ∀ K K' : Ideal R, Ideal.span {a} * K = Ideal.span {a} * K' → K ≤ K' from
    fun K K' h ↦ le_antisymm (key K K' h) (key K' K h.symm)
  intro K K' h x hx
  have hax : a * x ∈ Ideal.span {a} * K' := h ▸ Ideal.mem_span_singleton_mul.mpr ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := Ideal.mem_span_singleton_mul.mp hax
  rwa [← (mul_cancel_left_mem_nonZeroDivisors ha).mp hyx]

open AlgebraicGeometry

theorem solution {X : Scheme.{u}}
    {I J J' : X.IdealSheafData} (hI : I.IsInvertible) (h : I * J = I * J') : J = J' := by
  choose U f hxf g hg hIg using hI
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun x : X ↦ X.affineBasicOpen (f x)) ?_ ?_
  · exact top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxf x⟩
  · intro x
    have hx := congrArg (fun K : X.IdealSheafData ↦ K.ideal (X.affineBasicOpen (f x))) h
    simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hIg] at hx
    exact Ideal.span_singleton_mul_right_injective_of_mem_nonZeroDivisors (hg x) hx
