/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_section
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian
open NeronModelInfra (SchemeHomOver)

universe u

noncomputable section

namespace H2bFibrePt

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

def secAt (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : SchemeHomOver t f :=
  schemeHomOverComp t (Category.comp_id t) e

theorem secAt_natural (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (secAt e t) = secAt e t' := by
  apply Subtype.ext
  simp only [secAt, GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc, hψ]

theorem secAt_id (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    secAt e (𝟙 (Spec (CommRingCat.of R))) = e :=
  Subtype.ext (Category.id_comp _)

theorem inv_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : L.mul t' (schemeHomOverComp ψ hψ (L.inv t x)) (schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, L.one_natural]
  exact eq_inv_of_mul_eq_one_left h

def recentre (L : RelativeGroupLaw R f) (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    RelativeGroupLaw R f where
  mul t x y := L.mul t (L.mul t x (L.inv t (secAt e t))) y
  one t := secAt e t
  inv t x := L.mul t (L.mul t (secAt e t) (L.inv t x)) (secAt e t)
  mul_assoc t x y z := by
    letI := L.pointGroup t
    show ((x * (secAt e t)⁻¹) * y * (secAt e t)⁻¹) * z = (x * (secAt e t)⁻¹) * ((y * (secAt e t)⁻¹) * z)
    simp only [mul_assoc]
  one_mul t x := by
    letI := L.pointGroup t
    show (secAt e t * (secAt e t)⁻¹) * x = x
    rw [mul_inv_cancel, one_mul]
  mul_one t x := by
    letI := L.pointGroup t
    show (x * (secAt e t)⁻¹) * secAt e t = x
    rw [inv_mul_cancel_right]
  inv_mul_cancel t x := by
    letI := L.pointGroup t
    show ((secAt e t * x⁻¹) * secAt e t) * (secAt e t)⁻¹ * x = secAt e t
    rw [mul_inv_cancel_right, inv_mul_cancel_right]
  mul_natural t t' ψ hψ x y := by
    rw [L.mul_natural, L.mul_natural, inv_natural, secAt_natural]

theorem recentre_one (L : RelativeGroupLaw R f) (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    (recentre L e).one (𝟙 _) = e :=
  secAt_id e

theorem recentre_isCommutative (L : RelativeGroupLaw R f) (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hL : L.IsCommutative) : (recentre L e).IsCommutative := by
  intro T t x y
  letI := L.pointGroup t
  show (x * (secAt e t)⁻¹) * y = (y * (secAt e t)⁻¹) * x
  have hc : ∀ a b : SchemeHomOver t f, a * b = b * a := fun a b => hL.mul_comm t a b
  rw [hc x, mul_assoc, hc x, ← mul_assoc, hc (secAt e t)⁻¹ y]

end H2bFibrePt

end

open H2bFibrePt in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    ∃ L' : RelativeGroupLaw R f, L'.one (𝟙 _) = e ∧ (L.IsCommutative → L'.IsCommutative) :=
  ⟨recentre L e, recentre_one L e, recentre_isCommutative L e⟩
