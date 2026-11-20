import ZInQKernel.Contrib.CloudR2Poincare.L2.QuotientGraph
import ZInQKernel.Contrib.CloudR2Poincare.L2.NativeSquare
import ZInQKernel.Contrib.CloudR2Poincare.L2.VeryAmpleBaseChange
import ZInQKernel.Contrib.CloudR2Poincare.L1.FieldPoints
import ZInQKernel.Contrib.CloudR2Poincare.L3.B2Interface

/-!
# Actual field-point quotient classes and graph existence/uniqueness

Finite surjective q gives actual lifts of algebraically closed field points.
The exact kernelPair and finite-stabilizer point description make descended
polarization classes injective on Q-points. No dual/universal-family Fact.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- A finite surjective morphism has actual lifts of every algebraically
closed field-valued point, not merely surjective underlying scheme points. -/
theorem exists_fieldPoint_lift_of_finite_surjective
    {k Ω : Type u} [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    {B Q : Over (Spec (.of k))} (q : B ⟶ Q) [IsFinite q.left] [Surjective q.left]
    (z : L1.fieldTest k Ω ⟶ Q) : ∃ b : L1.fieldTest k Ω ⟶ B, b ≫ q = z := by
  let zp : Spec (.of Ω) ⟶ Q.left := z.left
  let F := pullback q.left zp
  let p : F ⟶ Spec (.of Ω) := pullback.snd q.left zp
  letI : Nonempty F := ⟨(Surjective.surj (f := p) (IsLocalRing.closedPoint Ω)).choose⟩
  letI : CompactSpace F := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨a, _, ha⟩ := IsClosed.exists_closed_singleton (S := (Set.univ : Set F))
    isClosed_univ Set.univ_nonempty
  let pt : Spec (.of Ω) ⟶ F := pointOfClosedPoint p a ha
  have hp : pt ≫ p = 𝟙 _ := pointOfClosedPoint_comp p a ha
  have hq : (pt ≫ pullback.fst q.left zp) ≫ q.left = zp := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, Category.id_comp]
  let b : L1.fieldTest k Ω ⟶ B := Over.homMk (pt ≫ pullback.fst q.left zp) (by
    rw [← q.w, ← Category.assoc, hq]
    exact Over.w z)
  refine ⟨b, ?_⟩
  apply Over.OverMorphism.ext
  exact hq

/-- Equality of the actual polarization families detects the difference
translation stabilizer. No theorem-of-the-square premise is needed here. -/
theorem polarizationFamily_difference_mem_stabilizer
    {S : Scheme.{u}} (B : Over S) [GrpObj B] (M : B.left.Pic)
    {T : Over S} (b c : T ⟶ B)
    (h : L1.polarizationFamily B M b = L1.polarizationFamily B M c) :
    b * c⁻¹ ∈ L1.stabilizerSubgroup B M T := by
  rw [L1.polarizationFamily_eq_translate_parameter, L1.polarizationFamily_eq_translate_parameter] at h
  have h' := _root_.mul_right_cancel h
  have h'' := congrArg (Scheme.Pic.map (L1.familyTranslate B c⁻¹).left) h'
  rw [← Scheme.Pic.map_comp, ← Scheme.Pic.map_comp, ← Over.comp_left, ← Over.comp_left,
    L1.familyTranslate_comp, L1.familyTranslate_comp, _root_.mul_inv_cancel,
    L1.familyTranslate_one, Over.id_left, Scheme.Pic.map_id] at h''
  exact h''

/-- The exact quotient kernelPair kills its stabilizer inclusion as an ACTUAL
homomorphism, with no group-quotient universality assumption. -/
theorem stabilizer_inclusion_killed_by_quotient
    {k : Type u} [Field k] (B Q : PkgI3.AbVar k) (M : B.X.left.Pic)
    (H : L1.FiniteStabilizerScheme B M) (q : PkgI3.AbVar.Hom B Q)
    (hk : IsPullback ((fst H.K B.X ≫ H.j) * snd H.K B.X) (snd H.K B.X) q.hom q.hom) :
    H.j ≫ q.hom = 1 := by
  let s : H.K ⟶ H.K ⊗ B.X := lift (𝟙 H.K) (1 : H.K ⟶ B.X)
  have hs : s ≫ ((fst H.K B.X ≫ H.j) * snd H.K B.X) = H.j := by
    rw [MonObj.comp_mul]
    simp [s, _root_.mul_one]
  have h := congrArg (fun f => s ≫ f) hk.w
  rw [← Category.assoc, hs] at h
  simpa only [s, lift_snd_assoc, MonObj.one_comp] using h

/-- Actual quotient-bundle specialization along any parameter point. -/
theorem quotientBundle_parameter_class
    {k : Type u} [Field k] (B Q : PkgI3.AbVar k) (M : B.X.left.Pic)
    (q : PkgI3.AbVar.Hom B Q) (P : (pullback B.X.hom Q.X.hom).Pic)
    (hp : Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom q.hom) P =
      L1.normalizedPolarizationFamily B.X M (𝟙 B.X))
    {T : Over (Spec (.of k))} (b : T ⟶ B.X) :
    Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom (b ≫ q.hom)) P =
      L1.normalizedPolarizationFamily B.X M b := by
  rw [JacobianChallenge.baseChangeMap_comp, Scheme.Pic.map_comp, hp,
    L1.normalizedPolarizationFamily_parameter, Category.comp_id]

/-- Descended polarization classes distinguish ACTUAL quotient field points.
The point fibres are precisely stabilizer cosets, not an assumed dual. -/
theorem quotientBundle_fieldPoint_injective
    {k Ω : Type u} [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (B Q : PkgI3.AbVar k) (M : B.X.left.Pic) (H : L1.FiniteStabilizerScheme B M)
    (q : PkgI3.AbVar.Hom B Q) [IsFinite q.hom.left] [Surjective q.hom.left]
    (hk : IsPullback ((fst H.K B.X ≫ H.j) * snd H.K B.X) (snd H.K B.X) q.hom q.hom)
    (P : (pullback B.X.hom Q.X.hom).Pic)
    (hp : Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom q.hom) P =
      L1.normalizedPolarizationFamily B.X M (𝟙 B.X)) :
    Function.Injective (fun z : L1.fieldTest k Ω ⟶ Q.X =>
      Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom z) P) := by
  intro z w h
  change Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom z) P =
    Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom w) P at h
  obtain ⟨b, hb⟩ := exists_fieldPoint_lift_of_finite_surjective q.hom z
  obtain ⟨c, hc⟩ := exists_fieldPoint_lift_of_finite_surjective q.hom w
  letI : Subsingleton (L1.fieldTest k Ω).left.Pic := inferInstanceAs (Subsingleton (Spec (.of Ω)).Pic)
  have hf : L1.polarizationFamily B.X M b = L1.polarizationFamily B.X M c := by
    rw [← hb, ← hc, quotientBundle_parameter_class B Q M q P hp b,
      quotientBundle_parameter_class B Q M q P hp c,
      L1.normalizedPolarizationFamily_eq_of_subsingletonPic B.X M b,
      L1.normalizedPolarizationFamily_eq_of_subsingletonPic B.X M c] at h
    exact h
  have hd := polarizationFamily_difference_mem_stabilizer B.X M b c hf
  have hr : b * c⁻¹ ∈ Set.range (fun a : L1.fieldTest k Ω ⟶ H.K => a ≫ H.j) := by
    rw [H.points Ω]
    exact hd
  obtain ⟨a, ha⟩ := hr
  have hzero : (b * c⁻¹) ≫ q.hom = 1 := by
    rw [← ha, Category.assoc, stabilizer_inclusion_killed_by_quotient B Q M H q hk]
    exact MonObj.comp_one _
  have hzw : z * w⁻¹ = 1 := by
    let f := IsMonHom.monoidHom q.hom (L1.fieldTest k Ω)
    change f (b * c⁻¹) = 1 at hzero
    rw [map_mul, map_inv] at hzero
    change (b ≫ q.hom) * (c ≫ q.hom)⁻¹ = 1 at hzero
    simpa only [hb, hc] using hzero
  exact _root_.mul_inv_eq_one.mp hzw

end ZInQ.Contrib.CloudR2Poincare.L2
