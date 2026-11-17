/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section plan GM10 / interface I4 in the EXACT consumer form fixed by C3 (),
`EulerCharTwistInvariant`. SOURCE ONLY, UNCOMPILED. Native HELD. No admission grade.

Proof: the twist family `E := p₁^*M ⊗ (m^*N ⊗ p₁^*Nᵛ)` on `A ×_K A` over the SECOND factor
(`snd`), whose literal fibre at a `K`-point `z` is identified with `A` by the actual fibre square
of the section `s_z = lift (𝟙 A) (toUnit A ≫ z)`, so the fibre coefficient is `s_z^*E ≅
M ⊗ (t_z^*N ⊗ Nᵛ)` (C3's right-translation convention `t_z = (s_z ≫ μ).left`). The fibre Euler
characteristic is constant over the connected base `A` by GM10 (`EulerCharConstancy.lean`, from
the held W07 `isLocallyConstant_eulerCharFiber`), and at the unit point `t_η = 𝟙` (Mathlib
`MonObj.lift_comp_one_right`) and `N ⊗ Nᵛ ≅ 𝟙` (W07 `tensorObjDualIsoUnit`).

Hypothesis check of the held W07 theorem against this family (none is aliased or assumed):
* proper, locally finitely presented, flat: `snd = pullback.snd A.hom A.hom` is the base change
  of the proper smooth `A.hom` (`PkgI2.IsAbelianVariety` fields);
* coefficient: `E` is invertible (W07 instances), hence finitely presented, quasi-coherent, and
  flat over `snd` (W07 `isFlatOver_of_isInvertible`);
* base: `A.X.left` is integral (Mathlib `GeometricallyIntegral.isIntegral_of_subsingleton`), hence
  preconnected; no Noetherian/reduced/smooth base hypothesis is required by the W07 theorem;
* scalars/fibres: W07 `eulerCharFiber` uses the residue-field fibre; it is converted to the
  `K`-Euler characteristic of the literal fibre by W07 `eulerCharFiber_eq_eulerChar` and
  `eulerCharFiber_pullback_of_isPullback`, and then to `A` itself by W07
  `eulerChar_pullback_of_isIso` along the fibre-square isomorphism.
`IsAlgClosed K` is accepted (C3's form) but not used. Universe `u`, any characteristic, no Facts.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.EulerCharConstancy
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Dual
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.PullbackMonoidal
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Isomorphism
import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry MonObj

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection

variable {K : Type u} [Field K] (A : Grp (Over (Spec (CommRingCat.of K))))

/-- C3's right translation by a `K`-point, exact shared convention (I1/I4/I5). -/
noncomputable def transl (z : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :
    A.X.left ⟶ A.X.left :=
  letI : GrpObj A.X := A.grp
  (lift (𝟙 A.X) (toUnit A.X ≫ z) ≫ μ[A.X]).left

/-- The multiplication of `A` on underlying schemes. -/
noncomputable def mulLeft : (A.X ⊗ A.X).left ⟶ A.X.left :=
  letI : GrpObj A.X := A.grp
  μ[A.X].left

/-- The twist family `p₁^*M ⊗ (m^*N ⊗ p₁^*Nᵛ)` on `A ×_K A` (all operations native W07). -/
noncomputable def twistFamily (M N : A.X.left.Modules) : (A.X ⊗ A.X).left.Modules :=
  (Scheme.Modules.pullback (fst A.X A.X).left).obj M ⊗
    ((Scheme.Modules.pullback (mulLeft A)).obj N ⊗
      (Scheme.Modules.pullback (fst A.X A.X).left).obj (Scheme.Modules.dual N))

/-- The section `a ↦ (a, z)` of the family at the `K`-point `z`. -/
noncomputable def twistSection (z : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :
    A.X.left ⟶ (A.X ⊗ A.X).left :=
  (lift (𝟙 A.X) (toUnit A.X ≫ z)).left

theorem twistSection_fst (z : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :
    twistSection A z ≫ (fst A.X A.X).left = 𝟙 A.X.left := by
  have h := congrArg (fun φ : A.X ⟶ A.X => φ.left) (lift_fst (𝟙 A.X) (toUnit A.X ≫ z))
  simpa [twistSection] using h

theorem twistSection_snd (z : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :
    twistSection A z ≫ (snd A.X A.X).left = A.X.hom ≫ z.left := by
  have h := congrArg (fun φ : A.X ⟶ A.X => φ.left) (lift_snd (𝟙 A.X) (toUnit A.X ≫ z))
  simpa [twistSection] using h

theorem twistSection_mul (z : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :
    twistSection A z ≫ mulLeft A = transl A z :=
  rfl

/-- The literal fibre square: `A` is the fibre of `snd : A ×_K A ⟶ A` over `z`. -/
theorem isPullback_twistSection (z : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :
    IsPullback (twistSection A z) A.X.hom (snd A.X A.X).left z.left := by
  have hz : z.left ≫ A.X.hom = 𝟙 (Spec (CommRingCat.of K)) := Over.w z
  refine IsPullback.of_right (h₁₂ := (fst A.X A.X).left) (h₂₂ := A.X.hom) ?_
    (twistSection_snd A z) ?_
  · rw [twistSection_fst, hz]
    exact IsPullback.id_horiz A.X.hom
  · exact IsPullback.of_hasPullback A.X.hom A.X.hom

/-- The `K`-Euler characteristic of the literal fibre of `snd` at `z`, with the literal fibre
coefficient, equals that of the section pullback `s_z^* F` on `A`. -/
theorem eulerChar_fibre_eq_twistSection (z : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X)
    (F : (A.X ⊗ A.X).left.Modules) :
    (letI : (pullback (snd A.X A.X).left z.left).Over (Spec (CommRingCat.of K)) :=
        ⟨pullback.snd (snd A.X A.X).left z.left⟩
      ((Scheme.Modules.pullback (pullback.fst (snd A.X A.X).left z.left)).obj F).eulerChar K) =
    (letI : A.X.left.Over (Spec (CommRingCat.of K)) := ⟨A.X.hom⟩
      ((Scheme.Modules.pullback (twistSection A z)).obj F).eulerChar K) := by
  let sq := isPullback_twistSection A z
  let e := sq.isoPullback
  have hsnd : e.hom ≫ pullback.snd (snd A.X A.X).left z.left = A.X.hom := sq.isoPullback_hom_snd
  have hfst : e.hom ≫ pullback.fst (snd A.X A.X).left z.left = twistSection A z :=
    sq.isoPullback_hom_fst
  have key : ∀ (g₁ g₂ : A.X.left ⟶ Spec (CommRingCat.of K)), g₁ = g₂ →
      ∀ (P Q : A.X.left.Modules), (P ≅ Q) →
        (letI : A.X.left.Over (Spec (CommRingCat.of K)) := ⟨g₁⟩; P.eulerChar K) =
        (letI : A.X.left.Over (Spec (CommRingCat.of K)) := ⟨g₂⟩; Q.eulerChar K) := by
    rintro g₁ g₂ rfl P Q φ
    letI : A.X.left.Over (Spec (CommRingCat.of K)) := ⟨g₁⟩
    exact Scheme.Modules.eulerChar_congr K φ
  refine (Scheme.Modules.eulerChar_pullback_of_isIso e.hom
      (pullback.snd (snd A.X A.X).left z.left)
      ((Scheme.Modules.pullback (pullback.fst (snd A.X A.X).left z.left)).obj F)).symm.trans ?_
  exact key _ _ hsnd _ _
    (((Scheme.Modules.pullbackComp e.hom (pullback.fst (snd A.X A.X).left z.left)).app F) ≪≫
      (Scheme.Modules.pullbackCongr hfst).app F)

/-- A pullback along `s_z` followed by the first projection is the identity, by actual maps. -/
noncomputable def twistSectionFstIso (z : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X)
    (P : A.X.left.Modules) :
    (Scheme.Modules.pullback (twistSection A z)).obj
      ((Scheme.Modules.pullback (fst A.X A.X).left).obj P) ≅ P :=
  ((Scheme.Modules.pullbackComp (twistSection A z) (fst A.X A.X).left).app P) ≪≫
    (Scheme.Modules.pullbackCongr (twistSection_fst A z)).app P ≪≫
    (Scheme.Modules.pullbackId A.X.left).app P

/-- The fibre coefficient: `s_z^*(twistFamily M N) ≅ M ⊗ (t_z^*N ⊗ Nᵛ)`, by the actual W07
pullback-tensor isomorphisms and the composition isomorphisms. -/
noncomputable def twistSectionPullbackIso (z : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X)
    (M N : A.X.left.Modules) :
    (Scheme.Modules.pullback (twistSection A z)).obj (twistFamily A M N) ≅
      M ⊗ ((Scheme.Modules.pullback (transl A z)).obj N ⊗ Scheme.Modules.dual N) :=
  Scheme.Modules.pullbackTensorObjIso (twistSection A z) _ _ ≪≫
    (twistSectionFstIso A z M ⊗ᵢ
      (Scheme.Modules.pullbackTensorObjIso (twistSection A z) _ _ ≪≫
        ((((Scheme.Modules.pullbackComp (twistSection A z) (mulLeft A)).app N) ≪≫
            (Scheme.Modules.pullbackCongr (twistSection_mul A z)).app N) ⊗ᵢ
          twistSectionFstIso A z (Scheme.Modules.dual N))))

/-- At the unit point the translation is the identity (right unit law, actual map). -/
theorem transl_one : letI : GrpObj A.X := A.grp; transl A η[A.X] = 𝟙 A.X.left := by
  letI : GrpObj A.X := A.grp
  change (lift (𝟙 A.X) (toUnit A.X ≫ η[A.X]) ≫ μ[A.X]).left = 𝟙 A.X.left
  rw [MonObj.lift_comp_one_right]
  rfl

/-- **I4 `EulerCharTwistInvariant`, in C3's exact consumer form.** -/
theorem eulerChar_twist_invariant [IsAlgClosed K] [PkgI2.IsAbelianVariety A]
    (M N : A.X.left.Modules) [M.IsInvertible] [N.IsInvertible]
    (z : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :
    (letI : A.X.left.Over (Spec (CommRingCat.of K)) := ⟨A.X.hom⟩
     (M ⊗ ((Scheme.Modules.pullback (transl A z)).obj N ⊗ Scheme.Modules.dual N)).eulerChar K =
       M.eulerChar K) := by
  letI : GrpObj A.X := A.grp
  letI : A.X.left.Over (Spec (CommRingCat.of K)) := ⟨A.X.hom⟩
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : Smooth A.X.hom := PkgI2.IsAbelianVariety.smooth
  haveI : GeometricallyIntegral A.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  haveI : IsProper (snd A.X A.X).left := by
    show IsProper (pullback.snd A.X.hom A.X.hom)
    infer_instance
  haveI : LocallyOfFinitePresentation (snd A.X A.X).left := by
    show LocallyOfFinitePresentation (pullback.snd A.X.hom A.X.hom)
    infer_instance
  haveI : Flat (snd A.X A.X).left := by
    show Flat (pullback.snd A.X.hom A.X.hom)
    infer_instance
  -- constancy of the literal fibre χ between `z` and the unit point (GM10)
  have hconst := eulerChar_pullback_eq_of_preconnectedSpace (K := K) (snd A.X A.X).left
    (twistFamily A M N) z.left (η[A.X]).left
  have hz := eulerChar_fibre_eq_twistSection A z (twistFamily A M N)
  have hη := eulerChar_fibre_eq_twistSection A η[A.X] (twistFamily A M N)
  -- the two section coefficients
  have hcz : (M ⊗ ((Scheme.Modules.pullback (transl A z)).obj N ⊗
      Scheme.Modules.dual N)).eulerChar K =
      ((Scheme.Modules.pullback (twistSection A z)).obj (twistFamily A M N)).eulerChar K :=
    Scheme.Modules.eulerChar_congr K (twistSectionPullbackIso A z M N).symm
  have hcη : ((Scheme.Modules.pullback (twistSection A η[A.X])).obj
      (twistFamily A M N)).eulerChar K = M.eulerChar K := by
    refine Scheme.Modules.eulerChar_congr K
      (twistSectionPullbackIso A η[A.X] M N ≪≫ ?_)
    exact (Iso.refl M ⊗ᵢ (((Scheme.Modules.pullbackCongr (transl_one A)).app N ≪≫
        (Scheme.Modules.pullbackId A.X.left).app N) ⊗ᵢ Iso.refl _)) ≪≫
      (Iso.refl M ⊗ᵢ Scheme.Modules.tensorObjDualIsoUnit N) ≪≫ ρ_ M
  exact hcz.trans (hz.symm.trans (hconst.trans (hη.trans hcη)))

end ZInQ.Contrib.CloudR2NOS.ClosedSection
