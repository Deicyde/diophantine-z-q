import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectivePoints

/-! On the fixed rational Weierstrass model the group identities can be
checked on field valued points, because the source schemes are reduced
and the target is separated. On the spot (c), tex 1785–1787. -/

noncomputable section

open scoped Classical

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory PkgI3
open WeierstrassCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme

namespace ZInQ.Manuscript.RC.J0Cusps

open PreparedParam

/-- The unit morphism of the Weierstrass model, using the existing section
at infinity. -/
def projectiveUnit (E : WeierstrassCurve ℚ) :
    𝟙_ (Over (Spec (.of ℚ))) ⟶ projectiveTarget E :=
  Over.homMk (weierstrassOrigin E) (maps_to_rat_unique _ _)

theorem projectiveUnit_value (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (F : Type) [Field F] [Algebra ℚ F] :
    projectiveValue
      ((toUnit (AbVar.ptObj (K := ℚ) F) ≫ projectiveUnit E).left) = 0 := by
  apply (projectiveValue_eq_zero_iff _).mpr
  change (Spec.map (CommRingCat.ofHom (algebraMap ℚ F)) ≫ weierstrassOrigin E) default =
    pointO E
  rw [Scheme.Hom.comp_apply,
    Subsingleton.elim (Spec.map _ default) (default : Spec (.of ℚ)), weierstrassOrigin_point]

/-- For reduced sources, restriction to field valued points detects
equality of morphisms to the fixed projective model. -/
theorem projectiveHom_ext (E : WeierstrassCurve ℚ)
    {T : Over (Spec (.of ℚ))} [IsReduced T.left] {f g : T ⟶ projectiveTarget E}
    (h : ∀ (F : Type) [Field F] [Algebra ℚ F] (p : AbVar.ptObj (K := ℚ) F ⟶ T),
      p ≫ f = p ≫ g) : f = g := by
  haveI : IsProper (projectiveTarget E).hom := by
    change IsProper (projectiveOverQ E)
    unfold projectiveOverQ
    have := isProper_proj E
    infer_instance
  apply Over.OverMorphism.ext
  apply ext_of_fromSpecResidueField_eq _ _ (projectiveTarget E).hom Set.univ dense_univ
  · intro x _
    letI : Algebra ℚ (T.left.residueField x) :=
      (Spec.homEquiv (T.left.fromSpecResidueField x ≫ T.hom)).hom.toAlgebra
    let p : AbVar.ptObj (K := ℚ) (T.left.residueField x) ⟶ T :=
      Over.homMk (T.left.fromSpecResidueField x) (maps_to_rat_unique _ _)
    exact congrArg (fun q => q.left) (h _ p)
  · exact f.w.trans g.w.symm

private theorem projectiveHom_ext_value (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {T : Over (Spec (.of ℚ))} [IsReduced T.left] {f g : T ⟶ projectiveTarget E}
    (h : ∀ (F : Type) [Field F] [Algebra ℚ F] (p : AbVar.ptObj (K := ℚ) F ⟶ T),
      projectiveValue (p ≫ f).left = projectiveValue (p ≫ g).left) : f = g := by
  apply projectiveHom_ext E
  intro F _ _ p
  exact Over.OverMorphism.ext ((projectiveValue_bijective E F).1 (h F p))

private theorem projectiveTarget_reduced (E : WeierstrassCurve ℚ) :
    IsReduced (projectiveTarget E).left := isReduced_proj E

private theorem projectiveTarget_product_reduced (E : WeierstrassCurve ℚ)
    (T : Over (Spec (.of ℚ))) [IsReduced T.left] [IsLocallyNoetherian T.left] :
    IsReduced ((projectiveTarget E) ⊗ T).left := by
  haveI := projectiveTarget_reduced E
  haveI : GeometricallyReduced (projectiveTarget E).hom :=
    geometricallyReduced_of_isReduced _
  change IsReduced (Limits.pullback (projectiveTarget E).hom T.hom)
  infer_instance

private theorem projectiveTarget_unit_product_reduced (E : WeierstrassCurve ℚ) :
    IsReduced ((𝟙_ (Over (Spec (.of ℚ)))) ⊗ (projectiveTarget E)).left := by
  letI := projectiveTarget_reduced E
  exact isReduced_of_isOpenImmersion ((λ_ (projectiveTarget E)).hom.left)

private theorem projectiveTarget_product_unit_reduced (E : WeierstrassCurve ℚ) :
    IsReduced ((projectiveTarget E) ⊗ (𝟙_ (Over (Spec (.of ℚ))))).left := by
  letI := projectiveTarget_reduced E
  exact isReduced_of_isOpenImmersion ((ρ_ (projectiveTarget E)).hom.left)

theorem projectiveTarget_square_reduced (E : WeierstrassCurve ℚ) :
    IsReduced ((projectiveTarget E) ⊗ (projectiveTarget E)).left := by
  haveI := projectiveTarget_reduced E
  haveI : IsProper (projectiveTarget E).hom := by
    change IsProper (projectiveOverQ E)
    unfold projectiveOverQ
    have := isProper_proj E
    infer_instance
  haveI : IsLocallyNoetherian (projectiveTarget E).left :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveTarget E).hom
  exact projectiveTarget_product_reduced E (projectiveTarget E)

/-- Field point laws suffice for the group diagrams on the fixed projective
model. The morphisms may be constructed using any coordinate charts. -/
def projectiveGroupOfOperations (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (m : projectiveTarget E ⊗ projectiveTarget E ⟶ projectiveTarget E)
    (n : projectiveTarget E ⟶ projectiveTarget E)
    (hm : ∀ (F : Type) [Field F] [Algebra ℚ F] (p q : AbVar.ptObj (K := ℚ) F ⟶ projectiveTarget E),
      projectiveValue (lift p q ≫ m).left = projectiveValue p.left + projectiveValue q.left)
    (hn : ∀ (F : Type) [Field F] [Algebra ℚ F] (p : AbVar.ptObj (K := ℚ) F ⟶ projectiveTarget E),
      projectiveValue (p ≫ n).left = -projectiveValue p.left) :
    GrpObj (projectiveTarget E) := by
  let X := projectiveTarget E
  haveI : IsReduced X.left := projectiveTarget_reduced E
  haveI : IsProper X.hom := by
    change IsProper (projectiveOverQ E)
    unfold projectiveOverQ
    have := isProper_proj E
    infer_instance
  haveI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  haveI : IsReduced ((𝟙_ (Over (Spec (.of ℚ)))) ⊗ X).left :=
    projectiveTarget_unit_product_reduced E
  haveI : IsReduced (X ⊗ (𝟙_ (Over (Spec (.of ℚ))))).left :=
    projectiveTarget_product_unit_reduced E
  haveI : IsReduced (X ⊗ X).left := projectiveTarget_product_reduced E X
  haveI : IsReduced ((X ⊗ X) ⊗ X).left := by
    change IsReduced (Limits.pullback (X ⊗ X).hom X.hom)
    haveI : LocallyOfFiniteType (X ⊗ X).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    haveI : IsLocallyNoetherian (X ⊗ X).left :=
      LocallyOfFiniteType.isLocallyNoetherian (X ⊗ X).hom
    haveI : GeometricallyReduced X.hom := geometricallyReduced_of_isReduced _
    infer_instance
  refine
    { one := projectiveUnit E
      mul := m
      inv := n
      one_mul := ?_
      mul_one := ?_
      mul_assoc := ?_
      left_inv := ?_
      right_inv := ?_ }
  · apply projectiveHom_ext_value E
    intro F _ _ p
    conv_lhs =>
      rw [← lift_comp_fst_snd p, lift_whiskerRight_assoc]
    rw [hm, leftUnitor_hom]
    rw [show p ≫ fst _ _ = toUnit _ from isTerminalTensorUnit.hom_ext _ _,
      projectiveUnit_value, zero_add]
  · apply projectiveHom_ext_value E
    intro F _ _ p
    conv_lhs =>
      rw [← lift_comp_fst_snd p, lift_whiskerLeft_assoc]
    rw [hm, rightUnitor_hom]
    rw [show p ≫ snd _ _ = toUnit _ from isTerminalTensorUnit.hom_ext _ _,
      projectiveUnit_value, add_zero]
  · apply projectiveHom_ext_value E
    intro F _ _ p
    let t := p ≫ fst _ _
    have hp : p = lift (lift (t ≫ fst _ _) (t ≫ snd _ _)) (p ≫ snd _ _) := by
      simp only [t, lift_comp_fst_snd]
    conv_lhs =>
      rw [hp, lift_whiskerRight_assoc, hm, hm]
    conv_rhs =>
      rw [hp, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hm, hm]
    exact add_assoc _ _ _
  · apply projectiveHom_ext_value E
    intro F _ _ p
    rw [comp_lift_assoc, Category.comp_id, hm, hn, neg_add_cancel, ← Category.assoc, comp_toUnit,
      projectiveUnit_value]
  · apply projectiveHom_ext_value E
    intro F _ _ p
    rw [comp_lift_assoc, Category.comp_id, hm, hn, add_neg_cancel, ← Category.assoc, comp_toUnit,
      projectiveUnit_value]


end ZInQ.Manuscript.RC.J0Cusps
