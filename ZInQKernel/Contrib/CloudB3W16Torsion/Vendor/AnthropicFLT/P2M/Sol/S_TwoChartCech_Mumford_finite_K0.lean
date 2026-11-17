/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_TwoChartCech_Mumford_finite_K0. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_MumfordTruncation
import Mathlib.RingTheory.Noetherian.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_TwoChartCech_Mumford_finite_K0

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

namespace TwoChartCech
export _root_.TwoChartCech (Mumford.K0)
namespace Mumford
export _root_.TwoChartCech.Mumford (rank lift K0 mem_K0_iff dK ι0 dK_apply ι0_apply)
open TwoChartCech.Mumford
open TwoChartCech

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

def kerToK0 : LinearMap.ker d →ₗ[R] K0 d :=
  LinearMap.codRestrict (K0 d)
    ((LinearMap.inl R C0 (Fin (rank d) → R)).comp (LinearMap.ker d).subtype)
    (fun ⟨x, hx⟩ => by
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.inl_apply,
        LinearMap.coprod_apply, map_zero, add_zero]
      exact hx)

def kerEquiv : LinearMap.ker (dK d) ≃ₗ[R] LinearMap.ker d := by
  refine LinearEquiv.ofLinear
    (LinearMap.codRestrict (LinearMap.ker d) ((ι0 d).comp (LinearMap.ker (dK d)).subtype) ?_)
    (LinearMap.codRestrict (LinearMap.ker (dK d)) (kerToK0 d) (fun x => by
      simp only [LinearMap.mem_ker, dK_apply]; rfl))
    ?_ ?_
  · rintro ⟨⟨⟨x, v⟩, hxv⟩, hv⟩
    have hxv' : d x + lift d v = 0 := (mem_K0_iff d _).mp hxv
    have hv' : v = 0 := (LinearMap.mem_ker).mp hv
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, ι0_apply]
    simpa [hv', map_zero, add_zero] using hxv'
  · apply LinearMap.ext; rintro ⟨x, hx⟩; rfl
  · apply LinearMap.ext; rintro ⟨⟨⟨x, v⟩, hxv⟩, hv⟩
    have hv' : v = 0 := (LinearMap.mem_ker).mp hv
    apply Subtype.ext; apply Subtype.ext
    show ((x, 0) : C0 × _) = (x, v)
    rw [hv']

end TwoChartCech.Mumford

open _root_.TwoChartCech.Mumford _root_.P2MW.S_TwoChartCech_Mumford_finite_K0.TwoChartCech.Mumford in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Module.Finite R (TwoChartCech.Mumford.K0 d) := by
  haveI hker : Module.Finite R (LinearMap.ker (dK d)) := Module.Finite.equiv (kerEquiv d).symm
  haveI hquot : Module.Finite R (K0 d ⧸ LinearMap.ker (dK d)) := by
    haveI : Module.Finite R (LinearMap.range (dK d)) := inferInstance
    exact Module.Finite.equiv (dK d).quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker (dK d))

end
