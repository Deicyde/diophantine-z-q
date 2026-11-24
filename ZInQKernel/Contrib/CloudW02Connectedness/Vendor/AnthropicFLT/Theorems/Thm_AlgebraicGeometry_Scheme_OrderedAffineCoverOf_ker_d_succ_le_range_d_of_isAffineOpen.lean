/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Localization.Away.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π] {W : V.Opens} (K : V.OrderedAffineCoverOf W) (hW : IsAffineOpen W) (p : ℕ) : letI := Scheme.OrderedAffineCoverOf.moduleSections π; LinearMap.ker (K.d π (p + 1)) ≤ LinearMap.range (K.d π p) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen.solution
