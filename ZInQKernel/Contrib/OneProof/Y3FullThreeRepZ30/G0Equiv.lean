import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.G0Dictionary
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FibreTransfer
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
open Y3Fix.G0Dictionary
namespace Y3Buzzard

/-!
# Level-three families and false elliptic curves with a level-three generator (draft)

A level-three family is the same thing as a false elliptic curve together with a section
`P` generating its full level-three structure, with `eta a = P ≫ ι a`. Base change of
families is base change of the curve carrying the section `eta 1`.
Source: Buzzard 1997, §1, Def. 1.1 (a full level structure is determined by the image of 1
by `O`-linearity).
-/

attribute [local instance] FEC.grp
attribute [local instance] Y3Fix.QMAbSchemeNL.grp

/-! ## 1. Section algebra on a false elliptic curve -/

section Sections

variable {S : Scheme.{0}} (A : FEC S) (P : S ⟶ A.F.left) (hP : P ≫ A.F.hom = 𝟙 S)

include hP in
theorem sec_comp_iota_sec (a : O) : (P ≫ A.iota a) ≫ A.F.hom = 𝟙 S := by
  rw [Category.assoc, A.iota_over, hP]

/-- The section `P ≫ ι a` as a point of `A` over the unit of `Over S`. -/
abbrev secPt (a : O) : 𝟙_ (Over S) ⟶ A.F :=
  Over.homMk (U := 𝟙_ (Over S)) (P ≫ A.iota a) (sec_comp_iota_sec A P hP a)

/-- The section `P` itself as a point over the unit of `Over S`. -/
abbrev basePt : 𝟙_ (Over S) ⟶ A.F := Over.homMk (U := 𝟙_ (Over S)) P hP

theorem secPt_eq_comp (a : O) :
    secPt A P hP a = basePt A P hP ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) :=
  Over.OverMorphism.ext rfl

theorem secPt_add (a b : O) : secPt A P hP (a + b) = secPt A P hP a * secPt A P hP b := by
  rw [secPt_eq_comp, secPt_eq_comp, secPt_eq_comp]
  exact comp_iota_add A (basePt A P hP) a b

theorem secPt_zero : secPt A P hP 0 = 1 := by
  rw [secPt_eq_comp, iotaHom_zero, MonObj.comp_one]

/-- The unit of the hom-monoid `𝟙_ (Over S) ⟶ A.F` is the unit section. -/
theorem one_unit_eq : (1 : 𝟙_ (Over S) ⟶ A.F) = MonObj.one := by
  have hu : toUnit (𝟙_ (Over S)) = 𝟙 (𝟙_ (Over S)) := by
    first
      | exact toUnit_unique _ _
      | exact SemiCartesianMonoidalCategory.toUnit_unique _ _
      | exact CartesianMonoidalCategory.toUnit_unique _ _
  show toUnit (𝟙_ (Over S)) ≫ MonObj.one = MonObj.one
  rw [hu, Category.id_comp]

include hP in
theorem sec_zero_left : P ≫ A.iota 0 = (MonObj.one : 𝟙_ (Over S) ⟶ A.F).left := by
  have h : P ≫ A.iota 0 = (1 : 𝟙_ (Over S) ⟶ A.F).left :=
    congrArg (fun f : 𝟙_ (Over S) ⟶ A.F => f.left) (secPt_zero A P hP)
  rw [h, one_unit_eq]

include hP in
theorem sec_zero_left_one : P ≫ A.iota 0 = (1 : 𝟙_ (Over S) ⟶ A.F).left :=
  congrArg (fun f : 𝟙_ (Over S) ⟶ A.F => f.left) (secPt_zero A P hP)

theorem sec_mul (a b : O) : P ≫ A.iota (a * b) = (P ≫ A.iota b) ≫ A.iota a := by
  rw [A.iota_mul, Category.assoc]

/-- Clause 1 of `IsGen` read on the unit of `Over S`. -/
theorem basePt_pow_of_isGen (hgen : IsGen 3 A P) : basePt A P hP ^ 3 = 1 := by
  have h := hgen
  dsimp only [IsGen] at h
  obtain ⟨h1, -⟩ := h
  have e : basePt A P hP = (unitIso A P hP).hom ≫
      (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) :=
    unit_homMk_eq A P hP P hP rfl
  rw [e, ← MonObj.comp_pow, h1, MonObj.comp_one]

include hP in
theorem sec_natThree_mul (hgen : IsGen 3 A P) (b : O) :
    P ≫ A.iota (((3 : ℕ) : O) * b) = P ≫ A.iota 0 := by
  have hx : basePt A P hP ≫ (Over.homMk (A.iota ((3 : ℕ) : O)) (A.iota_over _) : A.F ⟶ A.F)
      = 1 := by
    rw [comp_iotaHom_natCast, basePt_pow_of_isGen A P hP hgen]
  have h1 := comp_iota_natCast_mul_eq_one A 3 (basePt A P hP) hx b
  have h0 : basePt A P hP ≫ (Over.homMk (A.iota 0) (A.iota_over 0) : A.F ⟶ A.F) = 1 := by
    rw [iotaHom_zero, MonObj.comp_one]
  exact congrArg (fun f : 𝟙_ (Over S) ⟶ A.F => f.left) (h1.trans h0.symm)

include hP in
theorem sec_three_mul (hgen : IsGen 3 A P) (b : O) :
    P ≫ A.iota (3 * b) = P ≫ A.iota 0 := by
  rw [← Nat.cast_ofNat (R := O) (n := 3)]
  exact sec_natThree_mul A P hP hgen b

end Sections

/-! ## 2. From a generator to a level-three family -/

section OfGen

variable {S : Scheme.{0}} (A : FEC S) (P : S ⟶ A.F.left) (hP : P ≫ A.F.hom = 𝟙 S)
  (hgen : IsGen 3 A P)

/-- The family without the printed level clause, with `eta a := P ≫ ι a`. -/
def ofFECGenNL : Y3Fix.QMAbSchemeNL S where
  F := A.F
  proper := A.proper
  smooth := A.smooth
  iota := A.iota
  iota_over := A.iota_over
  grp := A.grp
  geomConn := A.geomConn
  iota_hom := A.iota_hom
  iota_one := A.iota_one
  iota_mul := A.iota_mul
  iota_add := A.iota_add
  eta a := P ≫ A.iota a
  eta_sec a := sec_comp_iota_sec A P hP a
  one_eq := by
    first
    | exact secPt_zero A P hP
    | exact (secPt_zero A P hP).symm
    | exact sec_zero_left A P hP
    | exact (sec_zero_left A P hP).symm
    | exact sec_zero_left_one A P hP
    | exact (sec_zero_left_one A P hP).symm
  eta_add := by
    intro a b
    first
    | exact secPt_add A P hP a b
    | exact (secPt_add A P hP a b).symm
  eta_linear := by
    intro a b
    first
    | exact sec_mul A P a b
    | exact sec_mul A P b a
    | exact (sec_mul A P a b).symm
    | exact (sec_mul A P b a).symm
  eta_three := by
    first
    | (intro b
       first
       | exact sec_natThree_mul A P hP hgen b
       | exact sec_three_mul A P hP hgen b
       | exact (sec_natThree_mul A P hP hgen b).symm
       | exact (sec_three_mul A P hP hgen b).symm)
    | exact (by simpa only [_root_.mul_one] using sec_three_mul A P hP hgen 1)

theorem ofFECGenNL_eta (a : O) : (ofFECGenNL A P hP hgen).eta a = P ≫ A.iota a := rfl

theorem ofFECGenNL_toFEC : (ofFECGenNL A P hP hgen).toFEC = A := rfl

/-- A false elliptic curve with a section generating its full level-three structure gives a
level-three family. -/
def ofFECGen : Y3Fix.QMAbSchemeP S where
  toQMAbSchemeNL := ofFECGenNL A P hP hgen
  level := by
    refine (levelPrint_iff_isGenAt (ofFECGenNL A P hP hgen)).2 ?_
    intro k _ _ s
    have e : s ≫ P ≫ A.F.hom = s := by rw [hP, Category.comp_id]
    have hs : (s ≫ P) ≫ A.F.hom = s := by rw [Category.assoc, e]
    have hg := hgen
    dsimp only [IsGen] at hg
    have h1 := (isGenAt_congr A e (s ≫ P) (Category.assoc _ _ _) hs).1 (hg.2 k s)
    have hpt : s ≫ P ≫ A.iota 1 = s ≫ P := by rw [A.iota_one, Category.comp_id]
    have hs' : (s ≫ P ≫ A.iota 1) ≫ A.F.hom = s := by rw [hpt]; exact hs
    have h2 : IsGenAt 3 A s (Over.homMk (U := Over.mk s) (s ≫ P ≫ A.iota 1) hs') :=
      IsGenAt.of_eq (Over.OverMorphism.ext hpt.symm) h1
    exact h2

theorem ofFECGen_eta (a : O) : (ofFECGen A P hP hgen).eta a = P ≫ A.iota a := rfl

end OfGen

/-! ## 3. From a level-three family to a generator -/

/-- A false elliptic curve with a section generating its full level-three structure. -/
structure FECGen (S : Scheme.{0}) where
  A : FEC S
  P : S ⟶ A.F.left
  sec : P ≫ A.F.hom = 𝟙 S
  gen : IsGen 3 A P

theorem FECGen.mk_congr {S : Scheme.{0}} {A : FEC S} {P P' : S ⟶ A.F.left} (h : P = P')
    (hs : P ≫ A.F.hom = 𝟙 S) (hs' : P' ≫ A.F.hom = 𝟙 S) (hg : IsGen 3 A P)
    (hg' : IsGen 3 A P') : FECGen.mk A P hs hg = FECGen.mk A P' hs' hg' := by
  subst h
  rfl

section ToGen

variable {S : Scheme.{0}} (𝒜 : Y3Fix.QMAbSchemeNL S)

/-- `eta (a * b) = ι a (eta b)`, in the order used below. -/
theorem eta_mul_eq (a b : O) : 𝒜.eta (a * b) = 𝒜.eta b ≫ 𝒜.iota a := by
  first
  | exact 𝒜.eta_linear a b
  | exact 𝒜.eta_linear b a
  | exact (𝒜.eta_linear a b).symm
  | exact (𝒜.eta_linear b a).symm

theorem eta_eq_one_comp (a : O) : 𝒜.eta a = 𝒜.eta 1 ≫ 𝒜.iota a := by
  simpa only [_root_.mul_one] using eta_mul_eq 𝒜 a 1

theorem eta_natThree : 𝒜.eta ((3 : ℕ) : O) = 𝒜.eta 0 := by
  first
  | (have h := 𝒜.eta_three 1
     rw [_root_.mul_one] at h
     first
     | exact h
     | (rw [Nat.cast_ofNat]; exact h)
     | simpa using h)
  | exact 𝒜.eta_three
  | (rw [Nat.cast_ofNat]; exact 𝒜.eta_three)

/-- The section `eta a` as a point over the unit of `Over S`. -/
abbrev etaPt (a : O) : 𝟙_ (Over S) ⟶ 𝒜.toFEC.F :=
  Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta a) (𝒜.eta_sec a)

theorem etaPt_eq_comp (a : O) :
    etaPt 𝒜 a = etaPt 𝒜 1 ≫
      (Over.homMk (𝒜.toFEC.iota a) (𝒜.toFEC.iota_over a) : 𝒜.toFEC.F ⟶ 𝒜.toFEC.F) :=
  Over.OverMorphism.ext (eta_eq_one_comp 𝒜 a)

theorem etaPt_zero : etaPt 𝒜 0 = 1 := by
  rw [etaPt_eq_comp, iotaHom_zero, MonObj.comp_one]

theorem etaPt_natThree : etaPt 𝒜 ((3 : ℕ) : O) = etaPt 𝒜 0 :=
  Over.OverMorphism.ext (eta_natThree 𝒜)

theorem etaPt_one_pow_three : etaPt 𝒜 1 ^ 3 = 1 := by
  rw [← comp_iotaHom_natCast 𝒜.toFEC (etaPt 𝒜 1) 3, ← etaPt_eq_comp, etaPt_natThree,
    etaPt_zero]

theorem isGen_eta_one (hlev : Y3Fix.LevelPrint 𝒜) : IsGen 3 𝒜.toFEC (𝒜.eta 1) := by
  dsimp only [IsGen]
  refine ⟨?_, ?_⟩
  · have hτ : (Over.homMk (U := Over.mk (𝒜.eta 1 ≫ 𝒜.toFEC.F.hom)) (𝒜.eta 1) rfl :
          Over.mk (𝒜.eta 1 ≫ 𝒜.toFEC.F.hom) ⟶ 𝒜.toFEC.F) =
        (unitIso 𝒜.toFEC (𝒜.eta 1) (𝒜.eta_sec 1)).inv ≫ etaPt 𝒜 1 :=
      Over.OverMorphism.ext (Category.id_comp (𝒜.eta 1)).symm
    exact (congrArg (fun z => z ^ 3) hτ).trans
      ((MonObj.comp_pow _ _ _).symm.trans
        ((congrArg (fun z => (unitIso 𝒜.toFEC (𝒜.eta 1) (𝒜.eta_sec 1)).inv ≫ z)
          (etaPt_one_pow_three 𝒜)).trans (MonObj.comp_one _)))
  · intro k _ _ s
    have e : s ≫ 𝒜.eta 1 ≫ 𝒜.toFEC.F.hom = s :=
      (congrArg (fun z => s ≫ z) (𝒜.eta_sec 1)).trans (Category.comp_id s)
    have hs : (s ≫ 𝒜.eta 1) ≫ 𝒜.toFEC.F.hom = s := (Category.assoc _ _ _).trans e
    exact (isGenAt_congr 𝒜.toFEC e (s ≫ 𝒜.eta 1) (Category.assoc _ _ _) hs).2
      ((levelPrint_iff_isGenAt 𝒜).1 hlev k s)

end ToGen

/-- The false elliptic curve of a level-three family with the generator `eta 1`. -/
def toFECGen {S : Scheme.{0}} (𝒜 : Y3Fix.QMAbSchemeP S) : FECGen S :=
  ⟨𝒜.toQMAbSchemeNL.toFEC, 𝒜.eta 1, 𝒜.eta_sec 1,
    isGen_eta_one 𝒜.toQMAbSchemeNL 𝒜.level⟩

/-! ## 4. Round trips -/

section RoundTrip

variable {S : Scheme.{0}}

theorem toFECGen_ofFECGen_A (A : FEC S) (P : S ⟶ A.F.left) (hP : P ≫ A.F.hom = 𝟙 S)
    (hgen : IsGen 3 A P) : (toFECGen (ofFECGen A P hP hgen)).A = A := rfl

theorem toFECGen_ofFECGen_P (A : FEC S) (P : S ⟶ A.F.left) (hP : P ≫ A.F.hom = 𝟙 S)
    (hgen : IsGen 3 A P) : (toFECGen (ofFECGen A P hP hgen)).P = P := by
  show P ≫ A.iota 1 = P
  rw [A.iota_one, Category.comp_id]

theorem toFECGen_ofFECGen (A : FEC S) (P : S ⟶ A.F.left) (hP : P ≫ A.F.hom = 𝟙 S)
    (hgen : IsGen 3 A P) : toFECGen (ofFECGen A P hP hgen) = ⟨A, P, hP, hgen⟩ := by
  have h : P ≫ A.iota 1 = P := by rw [A.iota_one, Category.comp_id]
  show FECGen.mk A (P ≫ A.iota 1) (sec_comp_iota_sec A P hP 1) _ = FECGen.mk A P hP hgen
  exact FECGen.mk_congr h _ hP _ hgen

/-- The family rebuilt from a generator triple. -/
def ofFECGen' (G : FECGen S) : Y3Fix.QMAbSchemeP S := ofFECGen G.A G.P G.sec G.gen

theorem ofFECGen_toFECGen_F (𝒜 : Y3Fix.QMAbSchemeP S) : (ofFECGen' (toFECGen 𝒜)).F = 𝒜.F :=
  rfl

theorem ofFECGen_toFECGen_iota (𝒜 : Y3Fix.QMAbSchemeP S) :
    (ofFECGen' (toFECGen 𝒜)).iota = 𝒜.iota := rfl

theorem ofFECGen_toFECGen_eta (𝒜 : Y3Fix.QMAbSchemeP S) (a : O) :
    (ofFECGen' (toFECGen 𝒜)).eta a = 𝒜.eta a := by
  show 𝒜.eta 1 ≫ 𝒜.iota a = 𝒜.eta a
  exact (eta_eq_one_comp 𝒜.toQMAbSchemeNL a).symm

end RoundTrip

/-! ## 5. Base change is determined by the section `eta 1` -/

open Y3Fix SGRSplit in
theorem qmFamFibre_iff {T S : Scheme.{0}} (𝒜 : Y3Fix.QMAbSchemeP T) (g : S ⟶ T)
    (𝒜' : Y3Fix.QMAbSchemeP S) :
    SGRSplit.QMFamFibre 𝒜.toQMFamily g 𝒜'.toQMFamily ↔
      ∃ h : 𝒜'.F.left ⟶ 𝒜.F.left, IsPullback h 𝒜'.F.hom 𝒜.F.hom g ∧
        (∀ a, 𝒜'.iota a ≫ h = h ≫ 𝒜.iota a) ∧ 𝒜'.eta 1 ≫ h = g ≫ 𝒜.eta 1 := by
  unfold SGRSplit.QMFamFibre
  constructor
  · rintro ⟨h, hpb, hι, hη⟩
    exact ⟨h, hpb, hι, hη 1⟩
  · rintro ⟨h, hpb, hι, h1⟩
    refine ⟨h, hpb, hι, fun a => ?_⟩
    rw [eta_eq_one_comp 𝒜'.toQMAbSchemeNL a, eta_eq_one_comp 𝒜.toQMAbSchemeNL a]
    simp only [Category.assoc]
    rw [hι a, ← Category.assoc, h1, Category.assoc]

end Y3Buzzard
