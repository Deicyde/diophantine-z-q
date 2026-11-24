import ZInQKernel.Contrib.OneProof.JDescent3FunctionField
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
import Mathlib.RingTheory.Unramified.LocalRing

/-! Centers of places on the actual abelian curve, and compatibility with étale pullback. -/

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry

noncomputable section

attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra

variable {K : Type} [Field K]

/-- Every place of the actual function field is centered at a closed point, and its
valuation ring is the image of the local ring at that point. -/
theorem abVar_exists_placeCenter (A : PkgI3.AbVar K) (hdim : A.dim = 1)
    (P : TauCeti.Place K (AbVarFunctionField A)) :
    ∃ x : A.X.left, IsClosed ({x} : Set A.X.left) ∧
      (algebraMap (A.X.left.presheaf.stalk x) (AbVarFunctionField A)).range =
        P.integers.toSubring := by
  let := abVar_smoothRelDimOne A hdim
  let v : AlgebraicCurve.Place K (AbVarFunctionField A) :=
    ⟨P.integers, P.algebraMap_mem_integers, P.integers_ne_top, inferInstance⟩
  exact AlgebraicCurve.exists_closedPoint_range_stalk_eq A.X.hom v

/-- Every closed point of the actual abelian curve gives a Tau Ceti place. -/
theorem abVar_exists_placeOf_closedPoint [CharZero K] (A : PkgI3.AbVar K) (hdim : A.dim = 1)
    (x : A.X.left) (hx : IsClosed ({x} : Set A.X.left)) :
    ∃ P : TauCeti.Place K (AbVarFunctionField A),
      (algebraMap (A.X.left.presheaf.stalk x) (AbVarFunctionField A)).range =
        P.integers.toSubring := by
  let := abVar_smoothRelDimOne A hdim
  obtain ⟨v, hv⟩ := AlgebraicCurve.exists_place_range_stalk_eq A.X.hom x hx
  let P := TauCeti.Place.ofValuationSubring (A := v.toValuationSubring)
    (abVar_isFunctionField A hdim) v.algebraMap_mem' v.ne_top'
  exact ⟨P, by simpa [P, TauCeti.Place.integers_ofValuationSubring] using hv⟩

private theorem stalk_functionField_square {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : X) (r : Y.presheaf.stalk (f x)) :
    f.functionFieldMap.hom (algebraMap (Y.presheaf.stalk (f x)) Y.functionField r) =
      algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom r) := by
  let h := (genericPoint_spec X).specializes
    (Set.mem_univ x)
  have H := f.stalkSpecializes_stalkMap (genericPoint X) x h
  have H' := Y.presheaf.stalkSpecializes_comp
    (specializes_of_eq f.genericPoint_eq_of_isDominant)
    ((genericPoint_spec Y).specializes (Set.mem_univ (f x)))
  have hh :
      Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ (f x))) ≫
          f.functionFieldMap =
        f.stalkMap x ≫ X.presheaf.stalkSpecializes h := by
    unfold Scheme.Hom.functionFieldMap
    rw [← Category.assoc, H', H]
  exact congrArg (fun a => CommRingCat.Hom.hom a r) hh

private def stalkEquivIntegers (A : PkgI3.AbVar K) (x : A.X.left)
    (P : TauCeti.Place K (AbVarFunctionField A))
    (hP : (algebraMap (A.X.left.presheaf.stalk x) (AbVarFunctionField A)).range =
      P.integers.toSubring) : A.X.left.presheaf.stalk x ≃+* P.integers := by
  let R := A.X.left.presheaf.stalk x
  let f : R →+* AbVarFunctionField A := algebraMap R _
  exact RingEquiv.ofBijective (f.codRestrict P.integers.toSubring (fun a => hP ▸ ⟨a, rfl⟩))
    ⟨fun _ _ h => IsFractionRing.injective R (AbVarFunctionField A) (congrArg Subtype.val h),
      fun ⟨a, ha⟩ => by
        obtain ⟨b, hb⟩ : a ∈ f.range := hP.symm ▸ ha
        exact ⟨b, Subtype.ext hb⟩⟩

/-- Pullback by a morphism over the ground field fixes the constants in the generic stalk. -/
theorem abVar_functionFieldMap_isScalarTower (A B : PkgI3.AbVar K) (f : A.X.left ⟶ B.X.left)
    [IsDominant f] (hf : f ≫ B.X.hom = A.X.hom) :
    letI : Algebra (AbVarFunctionField B) (AbVarFunctionField A) :=
      f.functionFieldMap.hom.toAlgebra
    IsScalarTower K (AbVarFunctionField B) (AbVarFunctionField A) := by
  let : Algebra (AbVarFunctionField B) (AbVarFunctionField A) := f.functionFieldMap.hom.toAlgebra
  let X := A.X.left
  let Y := B.X.left
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change X.germToFunctionField ⊤ (A.X.hom.appTop ((Scheme.ΓSpecIso (.of K)).inv a)) =
    f.functionFieldMap.hom (Y.germToFunctionField ⊤
      (B.X.hom.appTop ((Scheme.ΓSpecIso (.of K)).inv a)))
  have h : Y.germToFunctionField ⊤ ≫ f.functionFieldMap =
      f.appTop ≫ X.germToFunctionField ⊤ :=
    f.germToFunctionField_functionFieldMap (⊤ : Y.Opens)
  have hh : B.X.hom.appTop ≫ f.appTop = A.X.hom.appTop := by
    rw [← Scheme.Hom.comp_appTop, hf]
  have h' := congrArg (fun g => B.X.hom.appTop ≫ g) h
  have h'' : (B.X.hom.appTop ≫ Y.germToFunctionField ⊤) ≫ f.functionFieldMap =
      A.X.hom.appTop ≫ X.germToFunctionField ⊤ := by
    simpa only [Category.assoc, ← hh] using h'
  exact (congrArg (fun g => CommRingCat.Hom.hom g
    ((Scheme.ΓSpecIso (.of K)).inv a)) h'').symm

/-- At every place, finite unramified pullback over the constants has ramification index one. -/
theorem abVar_ramificationIdx_eq_one_of_finite_unramified [CharZero K]
    (A B : PkgI3.AbVar K) (hA : A.dim = 1) (hB : B.dim = 1)
    (f : A.X.left ⟶ B.X.left) [IsDominant f] [IsFinite f] [FormallyUnramified f]
    (hf : f ≫ B.X.hom = A.X.hom) :
    letI : Algebra (AbVarFunctionField B) (AbVarFunctionField A) :=
      f.functionFieldMap.hom.toAlgebra
    ∀ P : TauCeti.Place K (AbVarFunctionField A),
      P.ramificationIdx (AbVarFunctionField B) = 1 := by
  intro P
  let : Algebra (AbVarFunctionField B) (AbVarFunctionField A) :=
    f.functionFieldMap.hom.toAlgebra
  let : IsScalarTower K (AbVarFunctionField B) (AbVarFunctionField A) :=
    abVar_functionFieldMap_isScalarTower A B f hf
  let : Algebra.IsAlgebraic (AbVarFunctionField B) (AbVarFunctionField A) :=
    (abVar_isFunctionField B hB).isAlgebraic_of_isFunctionField (abVar_isFunctionField A hA)
  obtain ⟨x, hx, hxP⟩ := abVar_exists_placeCenter A hA P
  have hy : IsClosed ({f x} : Set B.X.left) := by
    simpa only [Set.image_singleton] using f.isClosedMap _ hx
  obtain ⟨Q, hyQ⟩ := abVar_exists_placeOf_closedPoint B hB (f x) hy
  let ex := stalkEquivIntegers A x P hxP
  let ey := stalkEquivIntegers B (f x) Q hyQ
  let g := (f.stalkMap x).hom
  let u : Q.integers →+* P.integers := ex.toRingHom.comp (g.comp ey.symm.toRingHom)
  have hu (a : Q.integers) : (u a : AbVarFunctionField A) =
      algebraMap (AbVarFunctionField B) (AbVarFunctionField A) (a : AbVarFunctionField B) := by
    have h := stalk_functionField_square f x (ey.symm a)
    change algebraMap (AbVarFunctionField B) (AbVarFunctionField A)
      ((ey (ey.symm a) : Q.integers) : AbVarFunctionField B) = (u a : AbVarFunctionField A) at h
    rw [ey.apply_symm_apply] at h
    exact h.symm
  have hQ : P.restrict K (AbVarFunctionField B) = Q :=
    (P.restrict_eq_iff_integers_le K (AbVarFunctionField B) Q).2
      fun a ha => hu ⟨a, ha⟩ ▸ (u ⟨a, ha⟩).2
  have hg : g.FormallyUnramified := FormallyUnramified.stalkMap f x
  let := g.toAlgebra
  have : Algebra.FormallyUnramified (B.X.left.presheaf.stalk (f x)) (A.X.left.presheaf.stalk x) := hg
  have : Algebra.EssFiniteType (B.X.left.presheaf.stalk (f x)) (A.X.left.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap f x
  have : IsLocalHom (algebraMap (B.X.left.presheaf.stalk (f x)) (A.X.left.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have hey : (IsLocalRing.maximalIdeal Q.integers).map ey.symm.toRingHom =
      IsLocalRing.maximalIdeal (B.X.left.presheaf.stalk (f x)) :=
    IsLocalRing.map_ringEquiv_maximalIdeal ey.symm
  have hex : (IsLocalRing.maximalIdeal (A.X.left.presheaf.stalk x)).map ex.toRingHom =
      IsLocalRing.maximalIdeal P.integers :=
    IsLocalRing.map_ringEquiv_maximalIdeal ex
  have hmap : (IsLocalRing.maximalIdeal Q.integers).map u = IsLocalRing.maximalIdeal P.integers := by
    dsimp only [u]
    rw [← Ideal.map_map, ← Ideal.map_map, hey,
      show g = algebraMap (B.X.left.presheaf.stalk (f x)) (A.X.left.presheaf.stalk x) from rfl,
      Algebra.FormallyUnramified.map_maximalIdeal, hex]
  obtain ⟨t, ht⟩ := Q.exists_isUniformizer
  let a : Q.integers := ⟨t, Q.mem_integers_iff_ord_nonneg.mpr (by
    rw [Q.isUniformizer_iff_ord_eq_one.mp ht]; norm_num)⟩
  have hs : IsLocalRing.maximalIdeal Q.integers = Ideal.span {a} :=
    Valuation.IsUniformizer.is_generator ht
  have hb : P.valuation.IsUniformizer (u a : AbVarFunctionField A) := by
    apply Valuation.isUniformizer_of_maximalIdeal_eq_span
    change IsLocalRing.maximalIdeal P.integers = Ideal.span {u a}
    rw [← hmap, hs, Ideal.map_span, Set.image_singleton]
  rw [hu, P.isUniformizer_iff_ord_eq_one,
    P.ord_algebraMap_restrict K (AbVarFunctionField B), hQ,
    show (a : AbVarFunctionField B) = t from rfl, Q.isUniformizer_iff_ord_eq_one.mp ht, mul_one] at hb
  exact_mod_cast hb

#print axioms stalk_functionField_square
#print axioms abVar_functionFieldMap_isScalarTower
#print axioms abVar_ramificationIdx_eq_one_of_finite_unramified
#print axioms abVar_exists_placeCenter
#print axioms abVar_exists_placeOf_closedPoint

end

end HDec.CMBranch.CMjBridges
