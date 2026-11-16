/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes
import Mathlib.Algebra.Module.LocalizedModule.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)
    (hq : F.IsQuasicoherent) (U : V.affineOpens) (f : Γ(V, U.1)) :
    letI := F.moduleRestrict (V.basicOpen_le f)
    IsLocalizedModule (Submonoid.powers f) (F.resₗ (V.basicOpen_le f)) := by
  letI := F.moduleRestrict (V.basicOpen_le f)
  obtain ⟨hsurj, hker⟩ := hq U f
  haveI := U.2.isLocalization_basicOpen f
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units (M := Submonoid.powers f) Γ(V, V.basicOpen f) ⟨f ^ n, n, rfl⟩
    have key : Function.Bijective fun y : F.obj (V.basicOpen f) => (u : Γ(V, V.basicOpen f)) • y :=
      MulAction.bijective u
    refine (Module.End.isUnit_iff _).mpr ?_
    convert key using 1
    funext y
    show ((f ^ n : Γ(V, U.1)) • y) = (u : Γ(V, V.basicOpen f)) • y
    rw [hu]
    rfl
  · intro y
    obtain ⟨n, x, hx⟩ := hsurj y
    exact ⟨(x, ⟨f ^ n, n, rfl⟩), hx.symm⟩
  · intro x₁ x₂ h
    have h0 : F.res (V.basicOpen_le f) (x₁ - x₂) = 0 := by
      rw [map_sub, sub_eq_zero]; exact h
    obtain ⟨n, hn⟩ := hker _ h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    show (f ^ n : Γ(V, U.1)) • x₁ = (f ^ n : Γ(V, U.1)) • x₂
    rwa [smul_sub, sub_eq_zero] at hn
