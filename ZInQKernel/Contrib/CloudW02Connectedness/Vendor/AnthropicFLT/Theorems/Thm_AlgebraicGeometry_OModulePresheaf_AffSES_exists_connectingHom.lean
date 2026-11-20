/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.AffSES.exists_connectingHom {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover) : ∃ (δ₀ : F₃.H0 K →ₗ[R] F₁.HSucc K 0) (δ : ∀ i : ℕ, F₃.HSucc K i →ₗ[R] F₁.HSucc K (i + 1)), LinearMap.ker δ₀ ≤ LinearMap.range (S.proj.H0Map K) ∧ (∀ i, LinearMap.ker (δ i) ≤ LinearMap.range (S.proj.HSuccMap K i)) ∧ LinearMap.ker (S.inc.HSuccMap K 0) ≤ LinearMap.range δ₀ ∧ (∀ i, LinearMap.ker (S.inc.HSuccMap K (i + 1)) ≤ LinearMap.range (δ i)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.solution
