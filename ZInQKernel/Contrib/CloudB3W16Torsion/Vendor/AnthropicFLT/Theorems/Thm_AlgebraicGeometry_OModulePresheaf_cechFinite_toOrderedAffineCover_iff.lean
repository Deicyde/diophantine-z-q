/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.RingTheory.Finiteness.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_toOrderedAffineCover_iff
    {R : Type u} [CommRing R] {X : Scheme.{u}} {c : X ⟶ Spec (.of R)}
    (F : OModulePresheaf c) (𝒱 : X.TwoAffineOpenCover) :
    F.CechFinite 𝒱.toOrderedAffineCover ↔
      Module.Finite R (F.twoChartSections 𝒱).H0 ∧ Module.Finite R (F.twoChartSections 𝒱).H1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff.solution
