/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_exists_isPullback_fibre_prod_and_slices_of_section
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isPullback_fibre_prod_and_slices_of_section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isPullback_fibre_prod_and_slices_of_section
    {S K : Type u} [CommRing S] [CommRing K] (r : S →+* K)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [IsSeparated f]
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    {AK : Scheme.{u}} (aK : AK ⟶ A) (xK : AK ⟶ Spec (CommRingCat.of K))
    (haK : IsPullback aK xK f (Spec.map (CommRingCat.ofHom r))) :
    ∃ (p₁ p₂ : pullback (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ⟶ AK)
      (eK : Spec (CommRingCat.of K) ⟶ AK)
      (iX iY : AK ⟶ pullback (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r))),
      p₁ ≫ aK = pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ≫ pullback.fst f f ∧
      p₁ ≫ xK = pullback.snd (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ∧
      p₂ ≫ aK = pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ≫ pullback.snd f f ∧
      p₂ ≫ xK = pullback.snd (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ∧
      IsPullback p₁ p₂ xK xK ∧
      eK ≫ aK = Spec.map (CommRingCat.ofHom r) ≫ e ∧ eK ≫ xK = 𝟙 _ ∧
      IsClosedImmersion iX ∧ iX ≫ p₁ = 𝟙 AK ∧ iX ≫ p₂ = xK ≫ eK ∧
      iX ≫ pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r))
        = aK ≫ pullback.lift (𝟙 A) (f ≫ e) (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) ∧
      IsClosedImmersion iY ∧ iY ≫ p₁ = xK ≫ eK ∧ iY ≫ p₂ = 𝟙 AK ∧
      iY ≫ pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r))
        = aK ≫ pullback.lift (f ≫ e) (𝟙 A) (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isPullback_fibre_prod_and_slices_of_section.solution
