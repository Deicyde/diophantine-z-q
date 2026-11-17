/-
Adapted from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
file P2M/Sol/S_GoodReductionJacobian_exists_inv_hom_forall_comp_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete.lean (see Vendor/AnthropicFLT/NOTICE, NOTICE.upstream, ATTRIBUTION.upstream.md and LICENSE).
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): the projective-embedding hypotheses are
removed, the projective algebraization step is replaced by `ProperAlgebraization` (proper schemes),
imports are relocated and the namespace is renamed; every other change is marked `-- [port]`; 160 names of constants that are not in this file's import closure are dropped from its `attribute [-instance]`/`[-simp]` lines (they come from the upstream combined environment).
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_AdicThickening
import ZInQKernel.Contrib.CloudB3SC2Mumford.Interfaces

-- [port] the upstream lakefile options, as for the vendored files
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
namespace ZInQ.Contrib.CloudB3SC2Mumford.Pipeline.InvHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace P2mWs49InvAlg

theorem map_inv_of_map_mul {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] {A₁ A₂ T₁ T₂ : Scheme.{u}}
    {f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)} {f₂ : A₂ ⟶ Spec (CommRingCat.of R₂)}
    (G₁ : RelativeGroupLaw R₁ f₁) (G₂ : RelativeGroupLaw R₂ f₂)
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R₁)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R₂)}
    (φ : SchemeHomOver t₁ f₁ → SchemeHomOver t₂ f₂)
    (hφ : ∀ x y, φ (G₁.mul t₁ x y) = G₂.mul t₂ (φ x) (φ y)) (x : SchemeHomOver t₁ f₁) :
    φ (G₁.inv t₁ x) = G₂.inv t₂ (φ x) := by
  letI := G₁.pointGroup t₁
  letI := G₂.pointGroup t₂
  exact map_inv (MonoidHom.mk' φ hφ) x

theorem inv_natural {R : Type u} [CommRing R] {A T T' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) =
      G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) :=
  map_inv_of_map_mul G G (GoodReductionJacobian.schemeHomOverComp ψ hψ) (G.mul_natural t t' ψ hψ) x

section

variable {R : Type u} [CommRing R] (I : Ideal R) {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))

abbrev bmap (n : ℕ) :
    Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))))

def upt (n : ℕ) : SchemeHomOver (adicThickeningToBase f I n) (adicThickeningToBase f I n) :=
  ⟨𝟙 _, Category.id_comp _⟩

def invMor (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n)) (n : ℕ) :
    adicThickening f I n ⟶ adicThickening f I n :=
  ((L n).inv (adicThickeningToBase f I n) (upt I f n)).1

theorem invMor_toBase (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n)) (n : ℕ) :
    invMor I f L n ≫ adicThickeningToBase f I n = adicThickeningToBase f I n :=
  ((L n).inv (adicThickeningToBase f I n) (upt I f n)).2

def push (n : ℕ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))}
    (P : SchemeHomOver t (adicThickeningToBase f I n)) :
    SchemeHomOver (t ≫ bmap I n) (adicThickeningToBase f I (n + 1)) :=
  ⟨P.1 ≫ adicThickeningTransition f I n, by
    rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, P.2]⟩

@[scoped simp] theorem push_coe (n : ℕ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))}
    (P : SchemeHomOver t (adicThickeningToBase f I n)) : (push I f n P).1 = P.1 ≫ adicThickeningTransition f I n := rfl

theorem invMor_transition (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n))
    (hcompat : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
      (P Q : SchemeHomOver t (adicThickeningToBase f I n)),
      ((L n).mul t P Q).1 ≫ adicThickeningTransition f I n =
        ((L (n + 1)).mul (t ≫ bmap I n) (push I f n P) (push I f n Q)).1)
    (n : ℕ) :
    adicThickeningTransition f I n ≫ invMor I f L (n + 1) = invMor I f L n ≫ adicThickeningTransition f I n := by

  have hR : push I f n ((L n).inv _ (upt I f n)) = (L (n + 1)).inv _ (push I f n (upt I f n)) :=
    map_inv_of_map_mul (L n) (L (n + 1)) (push I f n) (fun P Q => Subtype.ext (hcompat n _ P Q)) (upt I f n)

  have hL : GoodReductionJacobian.schemeHomOverComp (adicThickeningTransition f I n)
      (adicThickeningTransition_toBase f I n) ((L (n + 1)).inv _ (upt I f (n + 1))) =
      (L (n + 1)).inv _ (GoodReductionJacobian.schemeHomOverComp (adicThickeningTransition f I n)
        (adicThickeningTransition_toBase f I n) (upt I f (n + 1))) :=
    inv_natural (L (n + 1)) _ _ _ _ _
  have hpt : GoodReductionJacobian.schemeHomOverComp (adicThickeningTransition f I n)
        (adicThickeningTransition_toBase f I n) (upt I f (n + 1)) = push I f n (upt I f n) := by
    apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe, push_coe, upt, upt]
    simp only [Category.comp_id, Category.id_comp]
  rw [hpt] at hL
  have h1 := congrArg Subtype.val hL
  have h2 := congrArg Subtype.val hR
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h1
  rw [push_coe] at h2
  rw [invMor, invMor, h1, ← h2]

theorem comp_invMor (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n)) (n : ℕ)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))}
    (x : SchemeHomOver t (adicThickeningToBase f I n)) :
    x.1 ≫ invMor I f L n = ((L n).inv t x).1 := by
  have h := inv_natural (L n) (adicThickeningToBase f I n) t x.1 x.2 (upt I f n)
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (upt I f n) = x :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, upt]; exact Category.comp_id _)
  rw [hx] at h
  have h' := congrArg Subtype.val h
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h'
  exact h'

end

end P2mWs49InvAlg

end

open P2mWs49InvAlg in
theorem solution (hA : ProperAlgebraization.{u}) -- [port]
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (hp : IsProper f) -- [port] in place of a projective embedding
    (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n))
    (hcompat : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
      (P Q : SchemeHomOver t (adicThickeningToBase f I n)),
      ((L n).mul t P Q).1 ≫ adicThickeningTransition f I n =
        ((L (n + 1)).mul (t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))))
          ⟨P.1 ≫ adicThickeningTransition f I n, by
            rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ adicThickeningTransition f I n, by
            rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, Q.2]⟩).1) :
    ∃ i : A ⟶ A, i ≫ f = f ∧
      ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
        (x : SchemeHomOver t (adicThickeningToBase f I n)),
        x.1 ≫ adicThickeningι f I n ≫ i = ((L n).inv t x).1 ≫ adicThickeningι f I n := by
  obtain ⟨i, ⟨hi, hin⟩, -⟩ :=
    -- [port] proper algebraization in place of the projective one
    hA I f f hp hp (invMor I f L) (invMor_toBase I f L)
      (invMor_transition I f L (fun n _ t P Q => hcompat n t P Q))
  refine ⟨i, hi, ?_⟩
  intro n T t x
  rw [hin n, ← Category.assoc, comp_invMor]
