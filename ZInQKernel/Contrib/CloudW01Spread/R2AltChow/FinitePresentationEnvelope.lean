/-
Copyright (c) 2026 AxiomMath contributors and the H65 proof campaign.
Released under Apache 2.0; see ../LICENSE and ../H65_NOTICE.md.

Adapted from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b:
  StacksFrontier/AlgebraicGeometry/ChowFiniteType/Basic.lean:119-186
  StacksFrontier/AlgebraicGeometry/LimitDescentGlueing/Glueing.lean
  StacksFrontier/AlgebraicGeometry/Limits/ProperImageSystemModels.lean:109-135
  ZInQKernel/Contrib/CloudW01Spread/Smooth.lean:28-37 (frozen native bridge)

Modification notice (2026-11-14): use the proven proper-envelope construction,
not single-projective-space Chow; take finite presentation as actually supplied
by fixed H65. Use the frozen 01ZM model theorem and the native 01ZQ theorem
directly, avoiding ProperLimitStage.SeparatedModel, H65ModelBundle and the
finite-type-to-finite-presentation factorization. No unknown stage properness
or integrality hypothesis enters. All declarations are in R2AltChow.
-/
module

public import ZInQKernel.Contrib.CloudW01Spread.R2AltChow.ProperEnvelope
public import ZInQKernel.Contrib.CloudW01Spread.StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import ZInQKernel.Contrib.CloudW01Spread.ProperVendor.StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Diagonal
public import ZInQKernel.Contrib.CloudW01Spread.ProperVendor.StacksFrontier.AlgebraicGeometry.Limits.AbsoluteNoetherianApproximation
public import ZInQKernel.Contrib.CloudW01Spread.ProperVendor.StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStep

/-!
# Proper envelopes over a qcqs base for the actual finitely presented source

This is the complete envelope supplier for fixed H65. It descends the
finitely presented source to a Noetherian stage, descends separatedness to a
later such stage, applies the non-Segre proper-envelope construction there,
and base changes the whole proper-surjective-immersion diagram back.
-/

set_option linter.style.haveILetI false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace ZInQ.Contrib.CloudW01Spread.R2AltChow

/-- Compare the actual structure map with its morphism to the identity object
in the over category. Copied here on the new module side, so the frozen legacy
Smooth bridge need not be imported or changed. -/
theorem pullback_to_identity_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S T : Scheme.{u}} (g : T ⟶ S) (X : Over S) :
    P ((Over.pullback g).map (Over.homMk X.hom : X ⟶ Over.mk (𝟙 S))).left ↔
      P ((Over.pullback g).obj X).hom := by
  have h : ((Over.pullback g).map (Over.homMk X.hom : X ⟶ Over.mk (𝟙 S))).left ≫
      pullback.snd (𝟙 S) g = ((Over.pullback g).obj X).hom := by
    simp only [Over.pullback_map_left, Over.pullback_obj_hom, Over.homMk_left, Over.mk_hom]
    exact pullback.lift_snd _ _ _
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := P) _ (pullback.snd (𝟙 S) g), h]

/-- Native comparison of the original model's limit pullback with that of the
model moved along a true transition arrow. Source: AxiomMath/Stacks c496,
Limits/ProperImageSystemModels.lean:128-135; no properness is used. -/
noncomputable def overPullbackObj_shiftIso {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) {i j : I} (a : j ⟶ i) (Z : Over (D.obj i)) :
    (Over.pullback (c.π.app i)).obj Z ≅
      (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map a)).obj Z) :=
  (eqToIso (by rw [c.w a]) :
    (Over.pullback (c.π.app i)).obj Z ≅
      (Over.pullback (c.π.app j ≫ D.map a)).obj Z) ≪≫
    (Over.pullbackComp (c.π.app j) (D.map a)).app Z

/-- The left component of an isomorphism in an over category is an isomorphism.
The explicit instance prevents nominal spelling from obscuring the transport. -/
theorem isIso_left_of_overIso {S : Scheme.{u}} {A B : Over S} (e : A ≅ B) :
    IsIso e.hom.left :=
  ⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩

/-- Transport separatedness along an actual isomorphism over the same base. -/
theorem isSeparated_of_overIso {S : Scheme.{u}} {A B : Over S} (e : A ≅ B)
    [IsSeparated B.hom] : IsSeparated A.hom := by
  rw [← Over.w e.hom]
  haveI : IsIso e.hom.left := isIso_left_of_overIso e
  infer_instance

/-- A separated, finitely presented source over a cofiltered limit of
Noetherian schemes has a proper-envelope modification over that limit.
Only separatedness, never properness or integrality, is requested of the
finite-stage model. -/
theorem hasProperEnvelope_of_noetherianLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, IsNoetherian (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (X : Over c.pt) [IsSeparated X.hom] (hX : FinitePresentation X.hom) :
    HasProperEnvelope X.hom := by
  classical
  obtain ⟨i, Xᵢ, hXᵢ, ⟨e⟩⟩ :=
    AlgebraicGeometry.LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall
      D c hc X hX
  haveI : LocallyOfFinitePresentation Xᵢ.hom := hXᵢ.1
  haveI : QuasiCompact Xᵢ.hom := hXᵢ.2.1
  haveI : QuasiSeparated Xᵢ.hom := hXᵢ.2.2
  haveI : CompactSpace Xᵢ.left := QuasiCompact.compactSpace_of_compactSpace Xᵢ.hom
  haveI : QuasiSeparatedSpace Xᵢ.left := quasiSeparatedSpace_of_quasiSeparated Xᵢ.hom
  haveI : IsSeparated ((Over.pullback (c.π.app i)).obj Xᵢ).hom :=
    isSeparated_of_overIso e.symm
  haveI : MorphismProperty.RespectsIso (@IsSeparated : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let Yᵢ : Over (D.obj i) := Over.mk (𝟙 (D.obj i))
  let τ : Xᵢ ⟶ Yᵢ := Over.homMk Xᵢ.hom
  haveI : CompactSpace Yᵢ.left := by change CompactSpace (D.obj i); infer_instance
  haveI : QuasiSeparatedSpace Yᵢ.left := by
    change QuasiSeparatedSpace (D.obj i); infer_instance
  haveI : IsSeparated ((Over.pullback (c.π.app i)).map τ).left :=
    (pullback_to_identity_iff (@IsSeparated) (c.π.app i) Xᵢ).2
      inferInstance
  obtain ⟨j, a, hsep⟩ :=
    AlgebraicGeometry.exists_isSeparated_baseChange_of_isLimit D c i Xᵢ Yᵢ τ hc
  let Xⱼ : Over (D.obj j) := (Over.pullback (D.map a)).obj Xᵢ
  haveI : LocallyOfFinitePresentation Xⱼ.hom := by
    change LocallyOfFinitePresentation (pullback.snd Xᵢ.hom (D.map a))
    infer_instance
  haveI : QuasiCompact Xⱼ.hom := by
    change QuasiCompact (pullback.snd Xᵢ.hom (D.map a))
    infer_instance
  haveI : IsSeparated Xⱼ.hom :=
    (pullback_to_identity_iff (@IsSeparated) (D.map a) Xᵢ).1 hsep
  have hbase : HasProperEnvelope ((Over.pullback (c.π.app j)).obj Xⱼ).hom :=
    HasProperEnvelope.of_isPullback
      (IsPullback.of_hasPullback Xⱼ.hom (c.π.app j))
      (hasProperEnvelope_of_noetherian Xⱼ.hom)
  let eⱼ : X ≅ (Over.pullback (c.π.app j)).obj Xⱼ :=
    e ≪≫ overPullbackObj_shiftIso D c a Xᵢ
  haveI : IsIso eⱼ.hom.left := isIso_left_of_overIso eⱼ
  haveI : IsClosedImmersion eⱼ.hom.left := inferInstance
  exact HasProperEnvelope.of_isClosedImmersion (j := eⱼ.hom.left) (Over.w eⱼ.hom) hbase

/-- **Complete proper-envelope supplier for fixed H65.** A separated morphism
of finite presentation over any quasi-compact quasi-separated scheme has a
proper, surjective modification immersed over the same base into a proper
scheme. No stage properness, integrality, Segre or Chow hypothesis is added. -/
theorem hasProperEnvelope_of_finitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] (hf : FinitePresentation f)
    [CompactSpace S] [QuasiSeparatedSpace S] : HasProperEnvelope f := by
  obtain ⟨J, _, _, _, D, hEq, _⟩ :=
    Scheme.FiniteTypeApproximation.exists_limitNoetherianSituation_of_isOneAffineOpenStep
      Scheme.FiniteTypeApproximation.isOneAffineOpenStep S
  subst hEq
  haveI : ∀ {i j : Jᵒᵖ} (g : i ⟶ j), IsAffineHom (D.system.map g) := D.transition_affine
  haveI : ∀ i : Jᵒᵖ, IsNoetherian (D.system.obj i) := fun i => D.noetherian i.unop
  haveI : IsSeparated (Over.mk f).hom := by
    change IsSeparated f
    infer_instance
  exact hasProperEnvelope_of_noetherianLimit D.system D.limitCone D.isLimit (Over.mk f) hf

/-- Instance-style spelling used by the parent bridge. Its source conditions
are precisely the finite-presentation conjunction already in fixed H65. -/
theorem hasProperEnvelope {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace S] [QuasiSeparatedSpace S] : HasProperEnvelope f :=
  hasProperEnvelope_of_finitePresentation f ⟨inferInstance, inferInstance, inferInstance⟩

end ZInQ.Contrib.CloudW01Spread.R2AltChow

end
