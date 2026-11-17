/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Cover.Open
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_openCover
    {X : Scheme.{u}} (𝒰 : X.OpenCover) (I : ∀ i, (𝒰.X i).IdealSheafData)
    (hI : ∀ ⦃i j : 𝒰.I₀⦄ ⦃V : Scheme.{u}⦄ (a : V ⟶ 𝒰.X i) (b : V ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (I i).comap a = (I j).comap b) :
    ∃ I₀ : X.IdealSheafData, ∀ i, I₀.comap (𝒰.f i) = I i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.solution
