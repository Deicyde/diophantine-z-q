/-
Adapted from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
file P2M/Sol/S_GoodReductionJacobian_exists_mul_hom_forall_lift_comp_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete.lean (see Vendor/AnthropicFLT/NOTICE, NOTICE.upstream, ATTRIBUTION.upstream.md and LICENSE).
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
namespace ZInQ.Contrib.CloudB3SC2Mumford.Pipeline.MulHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace MulAlgBody

variable {R : Type u} [CommRing R] (I : Ideal R) {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))

abbrev p2 : pullback f f ⟶ Spec (CommRingCat.of R) := pullback.fst f f ≫ f

def pr1 (n : ℕ) : adicThickening (p2 f) I n ⟶ adicThickening f I n :=
  pullback.lift (adicThickeningι (p2 f) I n ≫ pullback.fst f f) (adicThickeningToBase (p2 f) I n)
    (by rw [Category.assoc]; exact adicThickeningι_comp (p2 f) I n)

def pr2 (n : ℕ) : adicThickening (p2 f) I n ⟶ adicThickening f I n :=
  pullback.lift (adicThickeningι (p2 f) I n ≫ pullback.snd f f) (adicThickeningToBase (p2 f) I n)
    (by rw [Category.assoc, ← pullback.condition]; exact adicThickeningι_comp (p2 f) I n)

@[scoped simp] theorem pr1_ι (n : ℕ) : pr1 I f n ≫ adicThickeningι f I n = adicThickeningι (p2 f) I n ≫ pullback.fst f f :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem pr2_ι (n : ℕ) : pr2 I f n ≫ adicThickeningι f I n = adicThickeningι (p2 f) I n ≫ pullback.snd f f :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem pr1_toBase (n : ℕ) : pr1 I f n ≫ adicThickeningToBase f I n = adicThickeningToBase (p2 f) I n :=
  pullback.lift_snd _ _ _
@[scoped simp] theorem pr2_toBase (n : ℕ) : pr2 I f n ≫ adicThickeningToBase f I n = adicThickeningToBase (p2 f) I n :=
  pullback.lift_snd _ _ _

def prPt1 (n : ℕ) : SchemeHomOver (adicThickeningToBase (p2 f) I n) (adicThickeningToBase f I n) := ⟨pr1 I f n, pr1_toBase I f n⟩
def prPt2 (n : ℕ) : SchemeHomOver (adicThickeningToBase (p2 f) I n) (adicThickeningToBase f I n) := ⟨pr2 I f n, pr2_toBase I f n⟩

variable (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n))

def φ (n : ℕ) : adicThickening (p2 f) I n ⟶ adicThickening f I n :=
  ((L n).mul (adicThickeningToBase (p2 f) I n) (prPt1 I f n) (prPt2 I f n)).1

theorem φ_def (n : ℕ) : φ I f L n = ((L n).mul (adicThickeningToBase (p2 f) I n) (prPt1 I f n) (prPt2 I f n)).1 := rfl

theorem φ_toBase (n : ℕ) : φ I f L n ≫ adicThickeningToBase f I n = adicThickeningToBase (p2 f) I n :=
  ((L n).mul _ _ _).2

theorem transition_pr1 (n : ℕ) :
    adicThickeningTransition (p2 f) I n ≫ pr1 I f (n + 1) = pr1 I f n ≫ adicThickeningTransition f I n := by
  apply pullback.hom_ext
  · show (_ ≫ _) ≫ adicThickeningι f I (n + 1) = (_ ≫ _) ≫ adicThickeningι f I (n + 1)
    rw [Category.assoc, pr1_ι, ← Category.assoc, adicThickeningTransition_ι, Category.assoc, adicThickeningTransition_ι, pr1_ι]
  · show (_ ≫ _) ≫ adicThickeningToBase f I (n + 1) = (_ ≫ _) ≫ adicThickeningToBase f I (n + 1)
    rw [Category.assoc, pr1_toBase, adicThickeningTransition_toBase, Category.assoc, adicThickeningTransition_toBase, ← Category.assoc,
      pr1_toBase]

theorem transition_pr2 (n : ℕ) :
    adicThickeningTransition (p2 f) I n ≫ pr2 I f (n + 1) = pr2 I f n ≫ adicThickeningTransition f I n := by
  apply pullback.hom_ext
  · show (_ ≫ _) ≫ adicThickeningι f I (n + 1) = (_ ≫ _) ≫ adicThickeningι f I (n + 1)
    rw [Category.assoc, pr2_ι, ← Category.assoc, adicThickeningTransition_ι, Category.assoc, adicThickeningTransition_ι, pr2_ι]
  · show (_ ≫ _) ≫ adicThickeningToBase f I (n + 1) = (_ ≫ _) ≫ adicThickeningToBase f I (n + 1)
    rw [Category.assoc, pr2_toBase, adicThickeningTransition_toBase, Category.assoc, adicThickeningTransition_toBase, ← Category.assoc,
      pr2_toBase]

end MulAlgBody

open MulAlgBody in
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
    ∃ m : pullback f f ⟶ A, m ≫ f = pullback.fst f f ≫ f ∧
      ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
        (x y : SchemeHomOver t (adicThickeningToBase f I n)),
        pullback.lift (x.1 ≫ adicThickeningι f I n) (y.1 ≫ adicThickeningι f I n)
            (by rw [Category.assoc, Category.assoc, adicThickeningι_comp, ← Category.assoc, ← Category.assoc, x.2, y.2]) ≫ m =
          ((L n).mul t x y).1 ≫ adicThickeningι f I n := by
  haveI := hp

  have hφt : ∀ n : ℕ, adicThickeningTransition (p2 f) I n ≫ φ I f L (n + 1) = φ I f L n ≫ adicThickeningTransition f I n := by
    intro n
    have hψ : adicThickeningTransition (p2 f) I n ≫ adicThickeningToBase (p2 f) I (n + 1) =
        adicThickeningToBase (p2 f) I n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))) :=
      adicThickeningTransition_toBase (p2 f) I n
    have hnat := congrArg Subtype.val ((L (n + 1)).mul_natural _ _ (adicThickeningTransition (p2 f) I n) hψ
      (prPt1 I f (n + 1)) (prPt2 I f (n + 1)))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at hnat
    have e1 : GoodReductionJacobian.schemeHomOverComp (adicThickeningTransition (p2 f) I n) hψ (prPt1 I f (n + 1)) =
        ⟨(prPt1 I f n).1 ≫ adicThickeningTransition f I n, by
          rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, (prPt1 I f n).2]⟩ :=
      Subtype.ext (transition_pr1 I f n)
    have e2 : GoodReductionJacobian.schemeHomOverComp (adicThickeningTransition (p2 f) I n) hψ (prPt2 I f (n + 1)) =
        ⟨(prPt2 I f n).1 ≫ adicThickeningTransition f I n, by
          rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, (prPt2 I f n).2]⟩ :=
      Subtype.ext (transition_pr2 I f n)
    rw [e1, e2] at hnat
    rw [φ_def, hnat, φ_def]
    exact (hcompat n (adicThickeningToBase (p2 f) I n) (prPt1 I f n) (prPt2 I f n)).symm

  obtain ⟨m, ⟨hmf, hmn⟩, -⟩ :=
    -- [port] proper algebraization in place of the projective one
    hA I (p2 f) f inferInstance hp (φ I f L) (φ_toBase I f L) hφt
  refine ⟨m, hmf, fun n T t x y => ?_⟩

  have hw : pullback.lift (x.1 ≫ adicThickeningι f I n) (y.1 ≫ adicThickeningι f I n)
      (by rw [Category.assoc, Category.assoc, adicThickeningι_comp, ← Category.assoc, ← Category.assoc, x.2, y.2]) ≫ p2 f =
      t ≫ adicThickeningBase I n := by
    rw [p2, ← Category.assoc, pullback.lift_fst, Category.assoc, adicThickeningι_comp, ← Category.assoc, x.2]
  obtain ⟨u, hudef⟩ : ∃ u : T ⟶ adicThickening (p2 f) I n, u = pullback.lift _ t hw := ⟨_, rfl⟩
  have hu₁ : u ≫ adicThickeningι (p2 f) I n = pullback.lift (x.1 ≫ adicThickeningι f I n) (y.1 ≫ adicThickeningι f I n)
      (by rw [Category.assoc, Category.assoc, adicThickeningι_comp, ← Category.assoc, ← Category.assoc, x.2, y.2]) := by
    rw [hudef]; exact pullback.lift_fst _ _ _
  have hu₂ : u ≫ adicThickeningToBase (p2 f) I n = t := by rw [hudef]; exact pullback.lift_snd _ _ _
  have hux : GoodReductionJacobian.schemeHomOverComp u hu₂ (prPt1 I f n) = x := by
    apply Subtype.ext; apply pullback.hom_ext
    · show (u ≫ pr1 I f n) ≫ adicThickeningι f I n = x.1 ≫ adicThickeningι f I n
      rw [Category.assoc, pr1_ι, ← Category.assoc, hu₁, pullback.lift_fst]
    · show (u ≫ pr1 I f n) ≫ adicThickeningToBase f I n = x.1 ≫ adicThickeningToBase f I n
      rw [Category.assoc, pr1_toBase, hu₂, x.2]
  have huy : GoodReductionJacobian.schemeHomOverComp u hu₂ (prPt2 I f n) = y := by
    apply Subtype.ext; apply pullback.hom_ext
    · show (u ≫ pr2 I f n) ≫ adicThickeningι f I n = y.1 ≫ adicThickeningι f I n
      rw [Category.assoc, pr2_ι, ← Category.assoc, hu₁, pullback.lift_snd]
    · show (u ≫ pr2 I f n) ≫ adicThickeningToBase f I n = y.1 ≫ adicThickeningToBase f I n
      rw [Category.assoc, pr2_toBase, hu₂, y.2]
  have hnat := congrArg Subtype.val ((L n).mul_natural _ _ u hu₂ (prPt1 I f n) (prPt2 I f n))
  rw [GoodReductionJacobian.schemeHomOverComp_coe, hux, huy] at hnat
  rw [← hu₁, Category.assoc, hmn n, ← Category.assoc, φ_def, hnat]

end
