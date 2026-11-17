/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem solution
    {U H S : Scheme.{u}} [IsIntegral U] (sU : U ⟶ S) (sH : H ⟶ S) [IsSeparated sH]
    (f g : U ⟶ H) (hf : f ≫ sH = sU) (hg : g ≫ sH = sU)
    (h : U.fromSpecStalk (genericPoint U) ≫ f = U.fromSpecStalk (genericPoint U) ≫ g) :
    f = g := by
  haveI : IsDominant (U.fromSpecStalk (genericPoint U)) := by
    constructor
    have hmem : genericPoint U ∈ Set.range (U.fromSpecStalk (genericPoint U)).base :=
      ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
    have hd : Dense ({genericPoint U} : Set U) := by
      rw [dense_iff_closure_eq]
      exact genericPoint_closure U
    exact hd.mono (Set.singleton_subset_iff.mpr hmem)
  exact ext_of_isDominant_of_isSeparated sH (hf.trans hg.symm) (U.fromSpecStalk (genericPoint U)) h
