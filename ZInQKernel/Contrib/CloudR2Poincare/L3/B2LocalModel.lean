import ZInQKernel.Contrib.CloudR2Poincare.L3.B2PointModelCoupling
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FiniteFreeComplexPullback
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Restrict

/-!
# Actual local native models on a locally Noetherian base

The Cartesian comparison assembly is adapted from the published W07
FiniteFreeModelBaseChange proof (frenzymath/Jacobian-Challenge,
c4254cce15b3e284a0a3ae1d73936f2ee195d272, Apache-2.0; copyright 2026
Axel Delaval, Jie Xu, and Shitan Xu). Modification: the actual affine chart of
the locally Noetherian base replaces general Noetherian approximation, so no
new approximation tree or assumed model/comparison input is required.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits

namespace ZInQ.Contrib.CloudR2Poincare.L3
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- A genuine universal native finite-free model near every point of an actual
locally Noetherian base, for an invertible coefficient in a proper flat family. -/
theorem exists_local_native_model
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] (F : X.Modules) [F.IsInvertible] (y : Y) :
    ∃ (U : Y.Opens) (P : CochainComplex U.toScheme.Modules ℤ) (bound : ℕ),
      y ∈ U ∧ Scheme.Modules.IsFiniteFreeComplex P bound ∧
        UniversalModelComparison f F U P := by
  obtain ⟨i, v, hv⟩ := Y.affineCover.exists_eq y
  let A : Scheme.{u} := Y.affineCover.X i
  let R := Γ(A, ⊤)
  let a : Spec R ⟶ Y := A.isoSpec.inv ≫ Y.affineCover.f i
  let v' : Spec R := A.isoSpec.hom v
  have hv' : a v' = y := by
    have he : A.isoSpec.inv (A.isoSpec.hom v) = v :=
      congrArg (fun t : A ⟶ A => t v) A.isoSpec.hom_inv_id
    exact (congrArg (Y.affineCover.f i) he).trans hv
  letI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian (Y.affineCover.f i)
  letI : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian (⟨⊤, isAffineOpen_top A⟩ : A.affineOpens)
  let f' := pullback.snd f a
  let F' := (Scheme.Modules.pullback (pullback.fst f a)).obj F
  have hfFlat : F'.IsFlatOver f' := Scheme.Modules.isFlatOver_of_isInvertible f' F'
  obtain ⟨denominator, P, bound, hvU, hP, comparison⟩ :=
    Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage_of_isProper R f' F' hfFlat v'
  let U := (Spec (.of R)).basicOpen denominator
  let j : U.toScheme ⟶ Y := U.ι ≫ a
  let g : j.opensRange.toScheme ⟶ U.toScheme := j.isoOpensRange.inv
  let Q := ((Scheme.Modules.pullback g).mapHomologicalComplex (.up ℤ)).obj P
  have hy : y ∈ j.opensRange := by
    refine ⟨⟨v', hvU⟩, ?_⟩
    exact hv'
  refine ⟨j.opensRange, Q, bound, hy, hP.pullback_complex g, ?_⟩
  intro T X'' b px pf _ square q
  let b' : T ⟶ U.toScheme := b ≫ g
  have hfac : b' ≫ U.ι ≫ a = b ≫ j.opensRange.ι := by
    simpa only [b', g, j, Category.assoc] using
      congrArg (fun t => b ≫ t) j.isoOpensRange_inv_comp
  let px' : X'' ⟶ pullback f a := pullback.lift px (pf ≫ b' ≫ U.ι) (by
    calc
      px ≫ f = pf ≫ (b ≫ j.opensRange.ι) := square.w
      _ = pf ≫ (b' ≫ U.ι ≫ a) := congrArg (fun t => pf ≫ t) hfac.symm
      _ = (pf ≫ b' ≫ U.ι) ≫ a := by simp only [Category.assoc])
  have square' : IsPullback px' pf f' (b' ≫ U.ι) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback f a)
    simpa only [px', pullback.lift_fst, Category.assoc, hfac] using square
  let eF : (Scheme.Modules.pullback px').obj F' ≅ (Scheme.Modules.pullback px).obj F :=
    (Scheme.Modules.pullbackComp px' (pullback.fst f a)).app F ≪≫
      (Scheme.Modules.pullbackCongr (pullback.lift_fst px (pf ≫ b' ≫ U.ι) _)).app F
  let eP : ((Scheme.Modules.pullback b).mapHomologicalComplex (.up ℤ)).obj Q ≅
      ((Scheme.Modules.pullback b').mapHomologicalComplex (.up ℤ)).obj P :=
    (Functor.mapHomologicalComplexCompIso (Scheme.Modules.pullbackComp b g) (.up ℤ)).app P
  obtain ⟨e⟩ := comparison b' px' pf square' q
  exact ⟨(HomologicalComplex.homologyFunctor T.Modules (.up ℤ) (q : ℤ)).mapIso eP ≪≫
    e ≪≫ (Scheme.Modules.higherDirectImage pf q).mapIso eF⟩

/-- Restricting the model retains its exact universal native comparator. -/
theorem UniversalModelComparison.pullback_open
    {X Y : Scheme.{u}} {f : X ⟶ Y} {F : X.Modules}
    {U V : Y.Opens} {P : CochainComplex U.toScheme.Modules ℤ}
    (comparison : UniversalModelComparison f F U P)
    (j : V.toScheme ⟶ U.toScheme) (hj : j ≫ U.ι = V.ι) :
    UniversalModelComparison f F V
      (((Scheme.Modules.pullback j).mapHomologicalComplex (.up ℤ)).obj P) := by
  intro T X' b px pf _ square q
  have square' : IsPullback px pf f ((b ≫ j) ≫ U.ι) := by
    simpa only [Category.assoc, hj] using square
  let eP := (Functor.mapHomologicalComplexCompIso
    (Scheme.Modules.pullbackComp b j) (.up ℤ)).app P
  obtain ⟨e⟩ := comparison (b ≫ j) px pf square' q
  exact ⟨(HomologicalComplex.homologyFunctor T.Modules (.up ℤ) (q : ℤ)).mapIso eP ≪≫ e⟩

/-- The actual restricted higher direct image is the homology of the model;
this uses the proved native open-restriction theorem, not an assumed bridge. -/
theorem nonempty_model_restriction_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsSeparated f]
    (F : X.Modules) [F.IsQuasicoherent]
    {U V : Y.Opens} {P : CochainComplex U.toScheme.Modules ℤ}
    (comparison : UniversalModelComparison f F U P)
    (g : V.toScheme ⟶ U.toScheme) (hg : g ≫ U.ι = V.ι) (q : ℕ) :
    Nonempty (((Scheme.Modules.higherDirectImage f q).obj F).restrict V.ι ≅
      (((Scheme.Modules.pullback g).mapHomologicalComplex (.up ℤ)).obj P).homology q) := by
  have square : IsPullback (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι :=
    (isPullback_morphismRestrict f V).flip
  letI := Scheme.Modules.isGrothendieckAbelian (f ⁻¹ᵁ V).toScheme
  let eR := Scheme.Modules.higherDirectImagePullbackIsoRestrict square F q
  obtain ⟨eP⟩ := comparison g (f ⁻¹ᵁ V).ι (f ∣_ V) (by rw [hg]; exact square) q
  exact ⟨eR.symm ≪≫ eP.symm⟩

end ZInQ.Contrib.CloudR2Poincare.L3
