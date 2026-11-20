/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
attribute [-simp] WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty

open WeierstrassCurve

universe u v w in

theorem WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
    {R : Type u} [CommRing R] (E : WeierstrassCurve R)
    {A : Type v} {B : Type w} [Field A] [DecidableEq A] [IsAlgClosed A] [Field B] [DecidableEq B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (H : AddSubgroup (E.baseChange A).toAffine.Point) (N : ℕ) :
    (E.baseChange B).cyclicQuotientJ (H.map (WeierstrassCurve.Affine.Point.map f)) N =
      f ((E.baseChange A).cyclicQuotientJ H N) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed.solution
