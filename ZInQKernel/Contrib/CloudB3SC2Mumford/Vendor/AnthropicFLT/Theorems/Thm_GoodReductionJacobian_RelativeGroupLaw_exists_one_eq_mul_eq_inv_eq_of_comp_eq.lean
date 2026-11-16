/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_mul_eq_inv_eq_of_comp_eq
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_mul_eq_inv_eq_of_comp_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_one_eq_mul_eq_inv_eq_of_comp_eq
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (m : pullback f f ⟶ A) (hm : m ≫ f = pullback.fst f f ≫ f)
    (h_one_mul : pullback.lift (f ≫ e.1) (𝟙 A) (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 A)
    (h_mul_one : pullback.lift (𝟙 A) (f ≫ e.1) (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 A)
    (h_assoc : pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ m) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc, hm]; exact pullback.condition) ≫ m =
        pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f)
          (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
              (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition) ≫ m)
          (by rw [Category.assoc, Category.assoc, hm, pullback.lift_fst_assoc, Category.assoc,
                ← pullback.condition (f := f) (g := f)]) ≫ m)
    (i : A ⟶ A) (hi : i ≫ f = f)
    (h_inv_mul : pullback.lift i (𝟙 A) (by rw [hi, Category.id_comp]) ≫ m = f ≫ e.1) :
    ∃ L : RelativeGroupLaw R f, L.one (𝟙 _) = e ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (L.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f), (L.inv t x).1 = x.1 ≫ i) ∧
      (∀ L' : RelativeGroupLaw R f, L'.one (𝟙 _) = e →
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
          (L'.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) →
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
          L'.one t = L.one t ∧ L'.inv t x = L.inv t x ∧ ∀ y, L'.mul t x y = L.mul t x y) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_mul_eq_inv_eq_of_comp_eq.solution
