/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π] [IsLocallyNoetherian V] (K : V.OrderedAffineCover) (Y : TopologicalSpace.Closeds V) (F : OModulePresheaf π) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hFs : F.SupportedIn Y) (hStep : ∀ k, (OModulePresheaf.idealPowQuot π (Scheme.IdealSheafData.vanishingIdeal Y) F k).CechFinite K) : F.CechFinite K := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot.solution
