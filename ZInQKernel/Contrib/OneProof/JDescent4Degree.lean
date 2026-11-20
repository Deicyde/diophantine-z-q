import ZInQKernel.Contrib.OneProof.JDescent3FunctionField
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import ZInQKernel.Contrib.AbVarBC.Dim
import ZInQKernel.Contrib.CloudB3W16Torsion.RelativeBridges
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Unramified.Field

set_option maxHeartbeats 1000000

/-! The generic field degree of doubling, compared with the geometric degree of the isogeny. -/

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry Limits CartesianMonoidalCategory MonObj
open ZInQ.Contrib.CloudB3W16Torsion

noncomputable section

attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra

/-- The spectrum of the generic stalk of the source is the generic fibre of a finite étale
dominant morphism of integral schemes. -/
theorem genericFiber_isPullback {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] [Etale f] :
    IsPullback (X.fromSpecStalk (genericPoint X)) (Spec.map f.functionFieldMap)
      f (Y.fromSpecStalk (genericPoint Y)) := by
  let x := genericPoint X
  let y := genericPoint Y
  let j := Y.fromSpecStalk y
  have eq_closedPoint (z : Spec (Y.presheaf.stalk y)) :
      z = IsLocalRing.closedPoint Y.functionField := by
    let pts : Unique (PrimeSpectrum Y.functionField) := inferInstance
    exact (pts.uniq _).trans (pts.uniq _).symm
  let i := X.fromSpecStalk x
  let s := Spec.map f.functionFieldMap
  have h : i ≫ f = s ≫ j := f.SpecMap_functionFieldMap_fromSpecStalk.symm
  let P := pullback f j
  let p := pullback.snd f j
  let q := pullback.fst f j
  let l : Spec X.functionField ⟶ P := pullback.lift i s h
  have hl : l ≫ q = i := pullback.lift_fst _ _ _
  have : IsPreimmersion q := inferInstanceAs (IsPreimmersion (pullback.fst f j))
  have : IsPreimmersion (l ≫ q) := hl.symm ▸ inferInstanceAs (IsPreimmersion i)
  have : IsPreimmersion l := IsPreimmersion.of_comp l q
  have : Surjective l := ⟨fun z => by
    let z₀ := IsLocalRing.closedPoint X.functionField
    have hx : f x = y := f.genericPoint_eq_of_isDominant
    have hz : f (q z) = y := by
      have he := congrArg (fun a : P ⟶ Y => a z) (pullback.condition (f := f) (g := j))
      change f (q z) = j (p z) at he
      rw [eq_closedPoint (p z)] at he
      exact he.trans Scheme.fromSpecStalk_closedPoint
    have heq : x = q z :=
      (f.isDiscrete_preimage_singleton y).eq_of_specializes
        ((genericPoint_spec X).specializes (Set.mem_univ _)) hx hz
    refine ⟨z₀, q.isEmbedding.injective ?_⟩
    exact (congrArg (fun a => a z₀) hl).trans (Scheme.fromSpecStalk_closedPoint.trans heq)⟩
  let : IsClosedImmersion l := IsClosedImmersion.of_isPreimmersion l (by
    rw [Set.range_eq_univ.mpr l.surjective]; exact isClosed_univ)
  have : IsFinite p := inferInstanceAs (IsFinite (pullback.snd f j))
  have : Etale p := inferInstanceAs (Etale (pullback.snd f j))
  have : IsAffine P := isAffine_of_isAffineHom p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (P.isoSpec.inv ≫ p)
  have hp : FormallyUnramified (Spec.map φ) := hφ.symm ▸ inferInstanceAs (FormallyUnramified (P.isoSpec.inv ≫ p))
  have hφ' : φ.hom.FormallyUnramified :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mp hp
  have hpfin : IsFinite (Spec.map φ) :=
    hφ.symm ▸ inferInstanceAs (IsFinite (P.isoSpec.inv ≫ p))
  let := φ.hom.toAlgebra
  have : Module.Finite Y.functionField Γ(P, ⊤) := (IsFinite.SpecMap_iff φ).mp hpfin
  have : Algebra.FormallyUnramified Y.functionField Γ(P, ⊤) := hφ'
  have : _root_.IsReduced Γ(P, ⊤) :=
    Algebra.FormallyUnramified.isReduced_of_field Y.functionField _
  have : IsReduced P := isReduced_of_isAffine_isReduced P
  have : IsIso l := isIso_of_isClosedImmersion_of_surjective l
  exact IsPullback.of_iso_pullback ⟨h⟩ (asIso l) hl (pullback.lift_snd _ _ _)

/-- The pullback on generic stalks is finite and its field degree is the morphism's rank
at the generic point. -/
theorem genericFiber_finite_finrank {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] [Etale f] :
    letI : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
    Module.Finite Y.functionField X.functionField ∧
      Module.finrank Y.functionField X.functionField = f.finrank (genericPoint Y) := by
  let : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
  have h := genericFiber_isPullback f
  have hfin : IsFinite (Spec.map f.functionFieldMap) :=
    MorphismProperty.of_isPullback h inferInstance
  have : Module.Finite Y.functionField X.functionField :=
    ((IsFinite.SpecMap_iff _).mp hfin)
  refine ⟨inferInstance, ?_⟩
  have hr := Scheme.Hom.finrank_of_isPullback _ _ _ _ h (IsLocalRing.closedPoint Y.functionField)
  rw [Scheme.fromSpecStalk_closedPoint] at hr
  rw [← hr]
  rw [show f.functionFieldMap = CommRingCat.ofHom (algebraMap Y.functionField X.functionField) from rfl,
    Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rfl

variable {K : Type} [Field K]

/-- Multiplication by two on the given abelian variety. -/
abbrev abVarDouble (A : PkgI3.AbVar K) : A.X.left ⟶ A.X.left :=
  ((𝟙 A.X : A.X ⟶ A.X) ^ (2 : ℕ)).left

instance abVarDouble_etale [CharZero K] (A : PkgI3.AbVar K) : Etale (abVarDouble A) :=
  multiplication_etale (ObjBridge.toGrp A) 2 (by norm_num)

instance abVarDouble_finite [CharZero K] (A : PkgI3.AbVar K) : IsFinite (abVarDouble A) :=
  multiplication_finite (ObjBridge.toGrp A) 2 (by norm_num)

instance abVarDouble_dominant [CharZero K] (A : PkgI3.AbVar K) : IsDominant (abVarDouble A) :=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace (abVarDouble A) (abVarDouble A).isOpenMap⟩

theorem abVarDouble_over (A : PkgI3.AbVar K) :
    abVarDouble A ≫ A.X.hom = A.X.hom := Over.w _

private theorem double_baseChange_pullback (A : PkgI3.AbVar K)
    (E : Type) [Field E] [Algebra K E] :
    let j := Spec.map (CommRingCat.ofHom (algebraMap K E))
    IsPullback (pullback.fst A.X.hom j) (abVarDouble (A.baseChange E))
      (abVarDouble A) (pullback.fst A.X.hom j) := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap K E))
  let F := Over.pullback j
  let : GrpObj (F.obj A.X) := Functor.grpObjObj
  have hm :
      (F.map ((𝟙 A.X : A.X ⟶ A.X) ^ (2 : ℕ))).left =
        abVarDouble (A.baseChange E) := by
    change (F.homMonoidHom ((𝟙 A.X : A.X ⟶ A.X) ^ (2 : ℕ))).left =
      abVarDouble (A.baseChange E)
    rw [map_pow]
    change (F.map (𝟙 A.X) ^ (2 : ℕ)).left = _
    exact congrArg (fun u : F.obj A.X ⟶ F.obj A.X => (u ^ (2 : ℕ)).left)
      (CategoryTheory.Functor.map_id F A.X)
  have h₁ : abVarDouble (A.baseChange E) ≫ pullback.fst A.X.hom j =
      pullback.fst A.X.hom j ≫ abVarDouble A := by
    rw [← hm]
    exact pullback.lift_fst _ _ _
  have h₂ : abVarDouble (A.baseChange E) ≫ pullback.snd A.X.hom j =
      pullback.snd A.X.hom j := Over.w
        ((𝟙 ((A.baseChange E).X) : (A.baseChange E).X ⟶ (A.baseChange E).X) ^ (2 : ℕ))
  have hp := IsPullback.of_hasPullback A.X.hom j
  refine (IsPullback.of_right ?_ h₁ hp.flip).flip
  rw [h₂, abVarDouble_over]
  exact hp.flip

/-- On a dimension-one abelian variety over an algebraically closed field, the rank of
doubling at every point is four. -/
private theorem abVarDouble_finrank_of_isAlgClosed [CharZero K] [IsAlgClosed K]
    (A : PkgI3.AbVar K) (hdim : A.dim = 1) (x : A.X.left) :
    (abVarDouble A).finrank x = 4 := by
  let G := ObjBridge.toGrp A
  let L := relativeLaw G
  let β := L.nsmul A.X.hom 2 GoodReductionJacobian.RelativeGroupLaw.idPoint
  have hb : β.1 = abVarDouble A := by
    have h (n : ℕ) : pointOverEquiv G A.X.hom ((𝟙 A.X : A.X ⟶ A.X) ^ n) =
        L.nsmul A.X.hom n GoodReductionJacobian.RelativeGroupLaw.idPoint := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ, GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, ← ih]
        simp only [L, relativeLaw, Equiv.symm_apply_apply]
        rfl
    exact (congrArg Subtype.val (h 2)).symm
  let := abVar_smoothRelDimOne A hdim
  have : IsFinite β.1 := hb.symm ▸ abVarDouble_finite A
  have : Flat β.1 := hb.symm ▸ inferInstanceAs (Flat (abVarDouble A))
  have h := L.endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero K A.X.hom
    (relativeLaw_commutative G) (abelianSchemePropertyBundle G) 1 2 (by norm_num)
  have h' := (L.surjective_and_endDegree_eq_finrank_of_isFinite_of_flat K A.X.hom β).2.2 x
  rw [hb] at h'
  exact h'.symm.trans (by simpa [β] using h)

/-- The self-extension of the actual function field induced by doubling is finite of
degree four. -/
theorem abVarDouble_functionField_degree [CharZero K] (A : PkgI3.AbVar K) (hdim : A.dim = 1) :
    letI : Algebra (AbVarFunctionField A) (AbVarFunctionField A) :=
      (abVarDouble A).functionFieldMap.hom.toAlgebra
    letI : Module (AbVarFunctionField A) (AbVarFunctionField A) := Algebra.toModule
    Module.Finite (AbVarFunctionField A) (AbVarFunctionField A) ∧
      Module.finrank (AbVarFunctionField A) (AbVarFunctionField A) = 4 := by
  let : Algebra (AbVarFunctionField A) (AbVarFunctionField A) :=
    (abVarDouble A).functionFieldMap.hom.toAlgebra
  let : Module (AbVarFunctionField A) (AbVarFunctionField A) := Algebra.toModule
  obtain ⟨hfin, hr⟩ := genericFiber_finite_finrank (abVarDouble A)
  refine ⟨hfin, hr.trans ?_⟩
  let E := AlgebraicClosure K
  let B := A.baseChange E
  have hB : B.dim = 1 := (A.dim_baseChange E).trans hdim
  let j := Spec.map (CommRingCat.ofHom (algebraMap K E))
  let p := pullback.fst A.X.hom j
  let x := abVarIdentity B
  have hcompare := Scheme.Hom.finrank_of_isPullback _ _ _ _
    (double_baseChange_pullback A E) x
  calc
    (abVarDouble A).finrank (genericPoint A.X.left) = (abVarDouble A).finrank (p x) :=
      (abVarDouble A).isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _
    _ = (abVarDouble B).finrank x := hcompare.symm
    _ = 4 := abVarDouble_finrank_of_isAlgClosed B hB x

#print axioms genericFiber_isPullback
#print axioms genericFiber_finite_finrank
#print axioms abVarDouble_etale
#print axioms abVarDouble_finite
#print axioms abVarDouble_dominant
#print axioms abVarDouble_over
#print axioms double_baseChange_pullback
#print axioms abVarDouble_finrank_of_isAlgClosed
#print axioms abVarDouble_functionField_degree

end

end HDec.CMBranch.CMjBridges
