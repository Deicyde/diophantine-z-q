/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.Interfaces

/-!
# W13 dictionary D3/D4, part 1: the action ring homomorphism and the level map

For a fake elliptic curve `E` (`N = 1`) over a field `K` with `h : AbVarProps E`, with kernel
abelian variety `A := abVarOfFakeEC E h` (group object `E.L.grpObjOverMk` on `Over.mk E.f`):

* `actHom E x : Over.mk E.f ⟶ Over.mk E.f` is the FLT action, a group-object homomorphism
  (`isMonHom_actHom`, from `act_hom`);
* `iota E h : 𝒪 →+* End A` uses `act_one`, `act_mul` (whose orientation `act (x*y) = act y ≫ act x`
  matches `End`'s `f * g = g.hom ≫ f.hom`) and `act_add`;
* `ptHom u a : ptObj K ⟶ Over.mk E.f` is `a · P` (`fltLevelPoint`). Its additivity comes from
  `act_add`, `𝒪`-linearity from `act_mul`, and `3 · P = 0` from `FullLevel.torsion`. If `a · P = 0`
  over `K`, then `a ∈ 3𝒪` by `FullLevel.annihilator` at the geometric point `K → K̄`.

No hypothesis beyond the data of `u` and `h` is used.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D34

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped Quaternion CategoryTheory.MonObj
open ZInQ.Contrib.CloudW03NeronSurj ZInQ.Contrib.CloudW03NeronSurj.FLT
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open ZInQ.Contrib.CloudB2Shimura.Dictionary

section Action

variable {K : Type} [Field K] (E : FakeEC K)

/-- The FLT action of `x ∈ Λ` as an endomorphism of `Over.mk E.f`. -/
def actHom (x : ↥Λ) : Over.mk E.f ⟶ Over.mk E.f := Over.homMk (E.act x) (E.act_over x)

@[simp] lemma actHom_left (x : ↥Λ) : (actHom E x).left = E.act x := rfl

lemma equiv_comp_actHom (x : ↥Λ) {T : Over (Spec (CommRingCat.of K))} (c : T ⟶ Over.mk E.f) :
    GoodReductionJacobian.overHomEquivSchemeHomOver T E.f (c ≫ actHom E x) =
      CerednikDrinfeld.QM.pushPt (E.act x) (E.act_over x)
        (GoodReductionJacobian.overHomEquivSchemeHomOver T E.f c) :=
  Subtype.ext rfl

/-- The action preserves the pointwise group law (`act_hom`). -/
lemma actHom_comp_mul (x : ↥Λ) {T : Over (Spec (CommRingCat.of K))} (a b : T ⟶ Over.mk E.f) :
    letI := E.L.grpObjOverMk
    (a * b) ≫ actHom E x = (a ≫ actHom E x) * (b ≫ actHom E x) := by
  letI := E.L.grpObjOverMk
  apply (GoodReductionJacobian.overHomEquivSchemeHomOver T E.f).injective
  rw [equiv_comp_actHom, E.L.overHomEquivSchemeHomOver_mul, E.L.overHomEquivSchemeHomOver_mul,
    equiv_comp_actHom, equiv_comp_actHom]
  exact E.act_hom x T.hom _ _

/-- The action is a homomorphism of group objects. -/
lemma isMonHom_actHom (x : ↥Λ) :
    letI := E.L.grpObjOverMk
    IsMonHom (actHom E x) := by
  letI := E.L.grpObjOverMk
  have hone : (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Over.mk E.f) ≫ actHom E x = 1 := by
    have h := actHom_comp_mul E x (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Over.mk E.f) 1
    rw [one_mul] at h
    exact mul_eq_left.mp h.symm
  constructor
  · rw [MonObj.one_eq_one]
    exact hone
  · rw [MonObj.mul_eq_mul, actHom_comp_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]

lemma actHom_add (x y : ↥Λ) :
    letI := E.L.grpObjOverMk
    actHom E (x + y) = actHom E x * actHom E y := by
  letI := E.L.grpObjOverMk
  apply (GoodReductionJacobian.overHomEquivSchemeHomOver (Over.mk E.f) E.f).injective
  rw [E.L.overHomEquivSchemeHomOver_mul]
  have hid : ∀ z : ↥Λ, GoodReductionJacobian.overHomEquivSchemeHomOver (Over.mk E.f) E.f
      (actHom E z) = CerednikDrinfeld.QM.pushPt (E.act z) (E.act_over z)
        (⟨𝟙 E.A, Category.id_comp _⟩ : SchemeHomOver E.f E.f) :=
    fun z => Subtype.ext (Category.id_comp _).symm
  rw [hid, hid, hid]
  exact E.act_add x y E.f _

lemma toΛ_one : toΛ 1 = ⟨1, (toΛ 1).2⟩ := rfl
lemma toΛ_add (a b : LeafQM.O) : toΛ (a + b) = toΛ a + toΛ b := Subtype.ext rfl

end Action

section Iota

variable {K : Type} [Field K] (E : FakeEC K) (h : AbVarProps E)

/-- `a ↦ act a` as an element of the kernel's `End A`. -/
def iotaEnd (a : LeafQM.O) : PkgI3.AbVar.End (abVarOfFakeEC E h) :=
  @PkgI3.AbVar.Hom.mk' _ _ (abVarOfFakeEC E h) (abVarOfFakeEC E h) (actHom E (toΛ a))
    (isMonHom_actHom E (toΛ a))

@[simp] lemma iotaEnd_hom (a : LeafQM.O) : (iotaEnd E h a).hom = actHom E (toΛ a) := rfl

lemma iotaEnd_add (a b : LeafQM.O) : iotaEnd E h (a + b) = iotaEnd E h a + iotaEnd E h b := by
  apply PkgI3.AbVar.Hom.ext'
  rw [PkgI3.AbVar.Hom.hom_add, iotaEnd_hom, iotaEnd_hom, iotaEnd_hom, toΛ_add]
  exact actHom_add E (toΛ a) (toΛ b)

/-- **The kernel ring homomorphism `𝒪 → End_K(A)`** given by the FLT action. -/
def iota : LeafQM.O →+* PkgI3.AbVar.End (abVarOfFakeEC E h) :=
  RingHom.mk'
    { toFun := iotaEnd E h
      map_one' := PkgI3.AbVar.Hom.ext' (Over.OverMorphism.ext (E.act_one _))
      map_mul' := fun a b =>
        PkgI3.AbVar.Hom.ext' (Over.OverMorphism.ext (E.act_mul (toΛ a) (toΛ b) _)) }
    (fun a b => iotaEnd_add E h a b)

@[simp] lemma iota_hom_left (a : LeafQM.O) : (iota E h a).hom.left = E.act (toΛ a) := rfl

end Iota

section Level

variable {K : Type} [Field K]

lemma ptObj_hom : (PkgI3.AbVar.ptObj (K := K) K).hom = 𝟙 (Spec (CommRingCat.of K)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap K K)) = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

variable (u : FLTL3 K)

/-- The level point `P` over the base of `ptObj K`. -/
def P' : SchemeHomOver (PkgI3.AbVar.ptObj (K := K) K).hom u.1.f :=
  ⟨u.2.P.1, u.2.P.2.trans ptObj_hom.symm⟩

lemma fltLevelPoint_over (a : LeafQM.O) :
    fltLevelPoint u a ≫ u.1.f = (PkgI3.AbVar.ptObj (K := K) K).hom := by
  change (u.2.P.1 ≫ u.1.act (toΛ a)) ≫ u.1.f = _
  rw [Category.assoc, u.1.act_over, u.2.P.2, ptObj_hom]

/-- `a · P` as a morphism `ptObj K ⟶ Over.mk E.f` (a `K`-point of the kernel abelian variety). -/
def ptHom (a : LeafQM.O) : PkgI3.AbVar.ptObj (K := K) K ⟶ Over.mk u.1.f :=
  Over.homMk (fltLevelPoint u a) (fltLevelPoint_over u a)

@[simp] lemma ptHom_left (a : LeafQM.O) : (ptHom u a).left = fltLevelPoint u a := rfl

lemma equiv_ptHom (a : LeafQM.O) :
    GoodReductionJacobian.overHomEquivSchemeHomOver _ u.1.f (ptHom u a) =
      CerednikDrinfeld.QM.pushPt (u.1.act (toΛ a)) (u.1.act_over (toΛ a)) (P' u) :=
  Subtype.ext rfl

lemma ptHom_add (a b : LeafQM.O) :
    letI := u.1.L.grpObjOverMk
    ptHom u (a + b) = ptHom u a * ptHom u b := by
  letI := u.1.L.grpObjOverMk
  apply (GoodReductionJacobian.overHomEquivSchemeHomOver _ u.1.f).injective
  rw [u.1.L.overHomEquivSchemeHomOver_mul, equiv_ptHom, equiv_ptHom, equiv_ptHom]
  simp only [toΛ_add]
  exact u.1.act_add (toΛ a) (toΛ b) _ (P' u)

lemma ptHom_mul (a b : LeafQM.O) : ptHom u (a * b) = ptHom u b ≫ actHom u.1 (toΛ a) :=
  Over.OverMorphism.ext (by
    change u.2.P.1 ≫ u.1.act (toΛ (a * b)) = (u.2.P.1 ≫ u.1.act (toΛ b)) ≫ u.1.act (toΛ a)
    rw [Category.assoc, ← u.1.act_mul (toΛ a) (toΛ b) (toΛ (a * b)).2]
    rfl)

lemma ptHom_one : ptHom u 1 = Over.homMk (P' u).1 (P' u).2 :=
  Over.OverMorphism.ext (by
    change u.2.P.1 ≫ u.1.act (toΛ 1) = u.2.P.1
    rw [show u.1.act (toΛ 1) = 𝟙 _ from u.1.act_one _, Category.comp_id])

/-- Powers of a point in the kernel group are FLT's `nsmulPt`. -/
lemma equiv_pow {T : Over (Spec (CommRingCat.of K))} (c : T ⟶ Over.mk u.1.f) (n : ℕ) :
    letI := u.1.L.grpObjOverMk
    GoodReductionJacobian.overHomEquivSchemeHomOver T u.1.f (c ^ n) =
      CerednikDrinfeld.QM.nsmulPt u.1.L T.hom n
        (GoodReductionJacobian.overHomEquivSchemeHomOver T u.1.f c) := by
  letI := u.1.L.grpObjOverMk
  induction n with
  | zero => rw [pow_zero, u.1.L.overHomEquivSchemeHomOver_one]; rfl
  | succ n ih => rw [pow_succ, u.1.L.overHomEquivSchemeHomOver_mul, ih]; rfl

lemma nsmulPt_three_of_eq {t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)}
    (ht : t = 𝟙 _) (Q : SchemeHomOver t u.1.f) (hQ : Q.1 = u.2.P.1) :
    CerednikDrinfeld.QM.nsmulPt u.1.L t 3 Q = u.1.L.one t := by
  subst ht
  have : Q = u.2.P := Subtype.ext hQ
  rw [this]
  exact u.2.torsion

/-- `3 · P = 0` in `A(K)`. -/
lemma ptHom_three : letI := u.1.L.grpObjOverMk
    ptHom u 3 = 1 := by
  letI := u.1.L.grpObjOverMk
  have h3 : (3 : LeafQM.O) = 1 + 1 + 1 := by norm_num
  rw [h3, ptHom_add, ptHom_add, ← pow_three']
  apply (GoodReductionJacobian.overHomEquivSchemeHomOver _ u.1.f).injective
  rw [equiv_pow, u.1.L.overHomEquivSchemeHomOver_one]
  apply nsmulPt_three_of_eq u ptObj_hom
  change u.2.P.1 ≫ u.1.act (toΛ 1) = u.2.P.1
  rw [show u.1.act (toΛ 1) = 𝟙 _ from u.1.act_one _, Category.comp_id]

/-- If `a · P = 0` in `A(K)` then `a ∈ 3𝒪` (`FullLevel.annihilator` at `K → K̄`). -/
lemma mem_three_of_ptHom_eq_one (a : LeafQM.O)
    (ha : letI := u.1.L.grpObjOverMk; ptHom u a = 1) : ∃ b : LeafQM.O, a = 3 * b := by
  letI := u.1.L.grpObjOverMk
  have h1 := congrArg (GoodReductionJacobian.overHomEquivSchemeHomOver _ u.1.f) ha
  rw [equiv_ptHom, u.1.L.overHomEquivSchemeHomOver_one] at h1
  have hv : u.2.P.1 ≫ u.1.act (toΛ a) =
      (u.1.L.one (PkgI3.AbVar.ptObj (K := K) K).hom).1 := congrArg Subtype.val h1
  let k := AlgebraicClosure K
  let sk : K →+* k := algebraMap K k
  have hψ : CerednikDrinfeld.QM.geomPoint k sk ≫ (PkgI3.AbVar.ptObj (K := K) K).hom =
      CerednikDrinfeld.QM.geomPoint k sk := by rw [ptObj_hom, Category.comp_id]
  have hgeo : CerednikDrinfeld.QM.pushPt (u.1.act (toΛ a)) (u.1.act_over (toΛ a))
      (CerednikDrinfeld.QM.FakeEllipticCurve.sectionAt u.2.P k sk) =
        u.1.L.one (CerednikDrinfeld.QM.geomPoint k sk) := by
    rw [← u.1.L.one_natural _ _ _ hψ]
    apply Subtype.ext
    change (CerednikDrinfeld.QM.geomPoint k sk ≫ u.2.P.1) ≫ u.1.act (toΛ a) =
      CerednikDrinfeld.QM.geomPoint k sk ≫ (u.1.L.one _).1
    rw [Category.assoc, hv]
    rfl
  obtain ⟨y, hy⟩ := (u.2.annihilator k sk (toΛ a)).1 hgeo
  refine ⟨⟨(y : ℍ[ℚ, 2, -3]), (order_bridge.2.2 _).mp y.2⟩, Subtype.ext ?_⟩
  change (a : ℍ[ℚ, 2, -3]) = ((3 : LeafQM.O) : ℍ[ℚ, 2, -3]) * (y : ℍ[ℚ, 2, -3])
  have hy' : (a : ℍ[ℚ, 2, -3]) = ((3 : ℕ) : ℚ) • (y : ℍ[ℚ, 2, -3]) := hy
  rw [hy', Algebra.smul_def, show ((3 : LeafQM.O) : ℍ[ℚ, 2, -3]) = 3 from map_ofNat LeafQM.O.subtype 3]
  simp

end Level

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D34
