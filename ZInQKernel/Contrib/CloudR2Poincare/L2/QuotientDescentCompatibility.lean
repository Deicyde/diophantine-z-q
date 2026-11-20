import ZInQKernel.Contrib.CloudR2Poincare.L2.B4Assembly
import ZInQKernel.Contrib.CloudR2Poincare.L2.FieldTrivialityDetection
import ZInQKernel.Contrib.CloudR2Poincare.L3.Cartier

/-!
# Quotient polarization descent compatibility from normalized seesaw

Every ingredient except the explicit ordinary global normalized seesaw input
is proved on the original schemes: commutative translation composition,
Cartier reducedness for the finite stabilizer, actual residue-field tests,
and fpqc detection after algebraic closure. No square, canonical H0 map,
quotient existence, or compatibility Fact is used in these proofs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Translation by a stabilizer point does not change the polarization
family of another point. This uses actual commutativity, not a square input. -/
theorem polarizationFamily_mul_eq_of_stabilizer
    {S : Scheme.{u}} (B : Over S) [GrpObj B] [IsCommMonObj B] (M : B.left.Pic)
    {T : Over S} (h b : T ⟶ B) (hh : h ∈ L1.stabilizerSubgroup B M T) :
    L1.polarizationFamily B M (h * b) = L1.polarizationFamily B M b := by
  have hc : L1.familyTranslate B (h * b) = L1.familyTranslate B b ≫ L1.familyTranslate B h :=
    (L1.familyTranslate_comp B b h).symm
  change Scheme.Pic.map (L1.familyTranslate B h).left (L1.parameterLineClass B M T) =
    L1.parameterLineClass B M T at hh
  rw [L1.polarizationFamily_eq_translate_parameter, L1.polarizationFamily_eq_translate_parameter,
    hc, Over.comp_left, Scheme.Pic.map_comp, hh]

/-- Normalization preserves the preceding genuine equality on any test scheme. -/
theorem normalizedPolarizationFamily_mul_eq_of_stabilizer
    {S : Scheme.{u}} (B : Over S) [GrpObj B] [IsCommMonObj B] (M : B.left.Pic)
    {T : Over S} (h b : T ⟶ B) (hh : h ∈ L1.stabilizerSubgroup B M T) :
    L1.normalizedPolarizationFamily B M (h * b) = L1.normalizedPolarizationFamily B M b := by
  have hr := polarizationFamily_mul_eq_of_stabilizer B M h b hh
  simp only [L1.normalizedPolarizationFamily_formula, hr]

/-- The stabilizer-parameter scheme is smooth by the actual Cartier theorem. -/
theorem stabilizerParameter_smooth
    {k : Type u} [Field k] [CharZero k] (B : PkgI3.AbVar k) (M : B.X.left.Pic)
    (H : L1.FiniteStabilizerScheme B M) : Smooth (H.K ⊗ B.X).hom := by
  letI : Smooth H.K.hom := L3.cartierSmooth_proof k H.K (inferInstance : LocallyOfFiniteType H.K.hom)
  change Smooth (pullback.fst H.K.hom B.X.hom ≫ H.K.hom)
  infer_instance

/-- The actual finite stabilizer is reduced in characteristic zero; pulling
back the proper smooth B over it gives a reduced locally-noetherian parameter. -/
theorem stabilizerParameter_reduced
    {k : Type u} [Field k] [CharZero k] (B : PkgI3.AbVar k) (M : B.X.left.Pic)
    (H : L1.FiniteStabilizerScheme B M) : AlgebraicGeometry.IsReduced (H.K ⊗ B.X).left := by
  have hK : H.K = Over.mk H.K.hom := by cases H.K; rfl
  letI : GrpObj (Over.mk H.K.hom) := hK ▸ (inferInstance : GrpObj H.K)
  letI : AlgebraicGeometry.IsReduced H.K.left :=
    L3.isReduced_groupScheme_charZero k H.K.left H.K.hom
  letI : IsLocallyNoetherian H.K.left := LocallyOfFiniteType.isLocallyNoetherian H.K.hom
  change AlgebraicGeometry.IsReduced (pullback H.K.hom B.X.hom)
  infer_instance

/-- The actual H.K×B structural morphism is proper, hence locally of finite type. -/
theorem stabilizerParameter_proper
    {k : Type u} [Field k] (B : PkgI3.AbVar k) (M : B.X.left.Pic)
    (H : L1.FiniteStabilizerScheme B M) : IsProper (H.K ⊗ B.X).hom := by
  change IsProper (pullback.fst H.K.hom B.X.hom ≫ H.K.hom)
  infer_instance

/-- The actual normalized difference of the two pulled-back Mumford families. -/
def stabilizerDescentDifference
    {k : Type u} [Field k] (B : PkgI3.AbVar k) (M : B.X.left.Pic)
    (H : L1.FiniteStabilizerScheme B M) : (pullback B.X.hom (H.K ⊗ B.X).hom).Pic :=
  L1.normalizedPolarizationFamily B.X M ((fst H.K B.X ≫ H.j) * snd H.K B.X) *
    (L1.normalizedPolarizationFamily B.X M (snd H.K B.X))⁻¹

/-- Genuine unit-section normalization of the actual difference bundle. -/
theorem stabilizerDescentDifference_normalized
    {k : Type u} [Field k] (B : PkgI3.AbVar k) (M : B.X.left.Pic)
    (H : L1.FiniteStabilizerScheme B M) :
    Scheme.Pic.map (sectionBaseChange B.X.hom η[B.X].left (L1.groupUnit_over B.X) (H.K ⊗ B.X))
      (stabilizerDescentDifference B M H) = 1 := by
  rw [stabilizerDescentDifference, Scheme.Pic.map_mul, L1.pic_map_inv,
    L1.normalizedPolarizationFamily_normalized, L1.normalizedPolarizationFamily_normalized,
    inv_one, _root_.mul_one]

/-- On every actual algebraically closed field test, the difference class
is trivial, because H.points supplies a genuine stabilizer point. -/
theorem stabilizerDescentDifference_fieldTest_eq_one
    {k Ω : Type u} [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (B : PkgI3.AbVar k) (M : B.X.left.Pic) (H : L1.FiniteStabilizerScheme B M)
    (x : L1.fieldTest k Ω ⟶ H.K ⊗ B.X) :
    Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom x)
      (stabilizerDescentDifference B M H) = 1 := by
  let h : L1.fieldTest k Ω ⟶ B.X := (x ≫ fst H.K B.X) ≫ H.j
  let b : L1.fieldTest k Ω ⟶ B.X := x ≫ snd H.K B.X
  have hh : h ∈ L1.stabilizerSubgroup B.X M (L1.fieldTest k Ω) := by
    change h ∈ (L1.stabilizerSubgroup B.X M (L1.fieldTest k Ω) : Set (L1.fieldTest k Ω ⟶ B.X))
    rw [← H.points Ω]
    exact ⟨x ≫ fst H.K B.X, rfl⟩
  have heq := normalizedPolarizationFamily_mul_eq_of_stabilizer B.X M h b hh
  have hx : x ≫ ((fst H.K B.X ≫ H.j) * snd H.K B.X) = h * b := by
    simp only [MonObj.comp_mul, Category.assoc, h, b]
  rw [stabilizerDescentDifference, Scheme.Pic.map_mul, L1.pic_map_inv,
    L1.normalizedPolarizationFamily_parameter, L1.normalizedPolarizationFamily_parameter,
    hx, heq, _root_.mul_inv_cancel]

/-- Every actual residue fibre is trivial. Its algebraic closure is an actual
fpqc test; native normalized-class detection descends to the original residue field. -/
theorem stabilizerDescentDifference_residueFibres_eq_one
    {k : Type u} [Field k] (B : PkgI3.AbVar k) (M : B.X.left.Pic)
    (H : L1.FiniteStabilizerScheme B M) (t : (H.K ⊗ B.X).left) :
    Scheme.Pic.map ((pullback.snd B.X.hom (H.K ⊗ B.X).hom).fiberι t)
      (stabilizerDescentDifference B M H) = 1 := by
  let T := H.K ⊗ B.X
  letI : IsProper T.hom := stabilizerParameter_proper B M H
  letI : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  let Ω := AlgebraicClosure (T.left.residueField t)
  let z : Spec (.of Ω) ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) Ω)) ≫ T.left.fromSpecResidueField t
  let c : CommRingCat.of k ⟶ CommRingCat.of Ω := Spec.preimage (z ≫ T.hom)
  letI : Algebra k Ω := c.hom.toAlgebra
  let x : L1.fieldTest k Ω ⟶ T := Over.homMk z (by
    change z ≫ T.hom = Spec.map c
    exact (Spec.map_preimage _).symm)
  have hx : x.left (IsLocalRing.closedPoint Ω) = t := by
    let pt : Spec (.of Ω) := IsLocalRing.closedPoint Ω
    change (Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) Ω)) ≫
      T.left.fromSpecResidueField t) pt = t
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply (X := T.left) t _
  have hm := (fibreTriviality_mem_fieldTest_iff B.X.hom η[B.X].left (L1.groupUnit_over B.X)
    T (stabilizerDescentDifference B M H) (stabilizerDescentDifference_normalized B M H) x).mpr
      (stabilizerDescentDifference_fieldTest_eq_one B M H x)
  change Scheme.Pic.map ((pullback.snd B.X.hom T.hom).fiberι (x.left (IsLocalRing.closedPoint Ω)))
    (stabilizerDescentDifference B M H) = 1 at hm
  rw [hx] at hm
  exact hm

/-- The two original normalized families agree globally on H.K×B by the
EXACT ordinary global seesaw input; no square or compatibility input remains. -/
theorem normalizedPolarizationFamily_stabilizer_action_eq_of_seesaw
    (hA : ReducedGlobalNormalizedSeesaw)
    {k : Type} [Field k] [CharZero k] (B : PkgI3.AbVar k) (M : B.X.left.Pic)
    (H : L1.FiniteStabilizerScheme B M) :
    L1.normalizedPolarizationFamily B.X M ((fst H.K B.X ≫ H.j) * snd H.K B.X) =
      L1.normalizedPolarizationFamily B.X M (snd H.K B.X) := by
  let T := H.K ⊗ B.X
  letI : IsProper T.hom := stabilizerParameter_proper B M H
  letI : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  letI : AlgebraicGeometry.IsReduced T.left := stabilizerParameter_reduced B M H
  have hd : stabilizerDescentDifference B M H = 1 :=
    hA B.X.hom η[B.X].left (L1.groupUnit_over B.X) T (stabilizerDescentDifference B M H)
      (stabilizerDescentDifference_normalized B M H)
      (stabilizerDescentDifference_residueFibres_eq_one B M H)
  exact _root_.mul_inv_eq_one.mp hd

/-- **Compatibility is no longer a supplied input.** It follows from the exact
ordinary normalized seesaw hypothesis and genuine Cartier/fpqc/stabilizer results. -/
theorem nativeQuotientDescentCompatibility_of_seesaw
    (hA : ReducedGlobalNormalizedSeesaw) : NativeQuotientDescentCompatibility := by
  intro k _ _ B M H Q
  let Λ := L1.normalizedPolarizationFamily B.X M (𝟙 B.X)
  let action : H.K ⊗ B.X ⟶ B.X := (fst H.K B.X ≫ H.j) * snd H.K B.X
  let proj : H.K ⊗ B.X ⟶ B.X := snd H.K B.X
  have hc : Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom action) Λ =
      Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom proj) Λ := by
    dsimp only [Λ]
    rw [L1.normalizedPolarizationFamily_parameter, L1.normalizedPolarizationFamily_parameter,
      Category.comp_id, Category.comp_id]
    exact normalizedPolarizationFamily_stabilizer_action_eq_of_seesaw hA B M H
  have hnatA := (toPicardFunctor B.X.hom).naturality_apply action.op Λ
  have hnatP := (toPicardFunctor B.X.hom).naturality_apply proj.op Λ
  change (picardFunctor B.X.hom).obj.map action.op
      ((toPicardFunctor B.X.hom).app (.op B.X) Λ) =
    (picardFunctor B.X.hom).obj.map proj.op ((toPicardFunctor B.X.hom).app (.op B.X) Λ)
  rw [← hnatA, ← hnatP]
  change (toPicardFunctor B.X.hom).app (.op (H.K ⊗ B.X))
      (Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom action) Λ) =
    (toPicardFunctor B.X.hom).app (.op (H.K ⊗ B.X))
      (Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom proj) Λ)
  exact congrArg ((toPicardFunctor B.X.hom).app (.op (H.K ⊗ B.X))) hc

/-- **Reduced-input assembly:** same fixed PolarizationRetract conclusion,
with no hCompatibility. Its actual proof is supplied by the theorem above. -/
theorem polarizationRetract_of_inputs'
    (hA : ReducedGlobalNormalizedSeesaw)
    (hB2 : PicZeroPointSurjectivityFromSquare)
    (hQuotient : L4.FiniteStabilizerQuotientExists)
    (hSquare : NativeTheoremOfTheSquare.{0})
    (hEmbedding : NativeProjectiveEmbeddingExists)
    (hGeometry : NativeNormalGraphProjectionCriterion) :
    ZInQ.Contrib.CloudR2Poincare.PolarizationRetract :=
  polarizationRetract_of_inputs hA hB2 hQuotient hSquare
    (nativeQuotientDescentCompatibility_of_seesaw hA) hEmbedding hGeometry

end ZInQ.Contrib.CloudR2Poincare.L2
