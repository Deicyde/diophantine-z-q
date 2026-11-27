import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.BuzzardLeaves
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FibreTransfer
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FECPullback
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.QuotientDescent
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.GrpObjDescent
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.BuzzardLeaves2
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# Descent of a false elliptic curve with a level-three generator (draft)

Input: a false elliptic curve `A` over `X`, a finite flat surjective `qX : X ⟶ Y` with the
kernel pair of a free action of `G`, the quotient `qA : A ⟶ B` with its kernel pair, a cartesian
square `qA, A.F.hom, b, qX`, the kernel pair of the fibre-power map, and a `G`-invariant
section `P3` generating the 3-torsion.

Output: `descFEC : FEC Y` with `F := Over.mk b`, the descended section `descP3`, the fibre
square `FECFibre descFEC qX A`, and `IsGen 3 descFEC descP3`.

The action of `G` enters only through the kernel pairs: each kernel pair `R` comes with maps
`inc g` (the graph of `g`), jointly epimorphic, with `inc g ≫ act = act g` and
`inc g ≫ pr = 𝟙`. For `R = G × X` (a coproduct of copies of `X`) these are the coproduct
inclusions. Compatibility of a map with a kernel pair is then checked on each `g`.

Leaves (statements taken as hypotheses): `ProperLocalOnBase`, `GeomConnLocalOnBase`,
`IsGenDescent`. Smoothness of relative dimension 2 of `b` is a hypothesis of `descFEC`.
-/

attribute [local instance] FEC.grp

/-! ## 0. Leaves -/

/-- Properness is fpqc local on the base, stated for one cartesian square along a flat,
surjective, quasi-compact map.
Source: Stacks Project, Remark 02WH, item 17; Descent, Lemma 35.23.16. -/
def ProperLocalOnBase : Prop :=
  ∀ ⦃P B X Y : Scheme.{0}⦄ (fst : P ⟶ B) (snd : P ⟶ X) (f : B ⟶ Y) (q : X ⟶ Y),
    IsPullback fst snd f q → Flat q → Surjective q → QuasiCompact q → IsProper snd →
      IsProper f

/-- Smoothness of relative dimension `n` is fpqc local on the base, stated for one cartesian
square along a flat, surjective, quasi-compact map.
Source: Stacks Project, Remark 02WH, item 20; Descent, Lemma 35.23.29 (smooth) and
Lemma 35.23.27 (relative dimension). -/
def SmoothRelDimLocalOnBase (n : ℕ) : Prop :=
  ∀ ⦃P B X Y : Scheme.{0}⦄ (fst : P ⟶ B) (snd : P ⟶ X) (f : B ⟶ Y) (q : X ⟶ Y),
    IsPullback fst snd f q → Flat q → Surjective q → QuasiCompact q →
      SmoothOfRelativeDimension n snd → SmoothOfRelativeDimension n f

/-- Geometric connectedness descends along a surjective base change. Argument: for a field `K`
and `y : Spec K ⟶ Y`, surjectivity of `q` gives a field extension `L` of `K` and a point
`Spec L ⟶ X` over `y`; the fibre of `f` over `Spec L` is the fibre of `snd` over that point,
hence connected, and it maps onto the fibre of `f` over `Spec K` (a base change of the
surjection `Spec L ⟶ Spec K`), which is therefore connected.
Source: Stacks Project, Varieties, Section 33.7 (geometrically connected schemes and field
extensions); precise lemma number to be verified. -/
def GeomConnLocalOnBase : Prop :=
  ∀ ⦃P B X Y : Scheme.{0}⦄ (fst : P ⟶ B) (snd : P ⟶ X) (f : B ⟶ Y) (q : X ⟶ Y),
    IsPullback fst snd f q → Surjective q → GeometricallyConnected snd →
      GeometricallyConnected f

/-- Generators descend along fpqc maps of the parameter scheme: if `f ≫ P` is a generator of
a full level-`M` structure and `f` is flat, surjective and quasi-compact, so is `P`.
Argument: the torsion identity descends because `f` is an effective epimorphism; every
geometric point of `T` lifts, after an extension of algebraically closed fields, to a
geometric point of `T'`, and the `M`-torsion points of a fibre do not change under such an
extension because the `M`-torsion is finite over the base.
Source: Buzzard 1997, §1, Def. 1.1 (the condition is fibrewise at geometric points);
the invariance under extension of algebraically closed fields is to be cited. -/
def IsGenDescent : Prop :=
  ∀ (M : ℕ) (S : Scheme.{0}) (A : FEC S) (T T' : Scheme.{0}) (f : T' ⟶ T)
    (P : T ⟶ A.F.left), Flat f → Surjective f → QuasiCompact f → IsGen M A (f ≫ P) →
      IsGen M A P

/-! ## 1. Effective epimorphisms from cartesian squares -/

/-- A base change of a finite, flat, surjective morphism is an effective epimorphism. -/
theorem effectiveEpi_of_isPullback {P B X Y : Scheme.{0}} {fst : P ⟶ B} {snd : P ⟶ X}
    {f : B ⟶ Y} {q : X ⟶ Y} [IsFinite q] [Flat q] [Surjective q]
    (h : IsPullback fst snd f q) : EffectiveEpi fst := by
  haveI : Flat fst := MorphismProperty.of_isPullback (P := @Flat) h.flip ‹Flat q›
  haveI : Surjective fst := MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹Surjective q›
  haveI : IsFinite fst := MorphismProperty.of_isPullback (P := @IsFinite) h.flip ‹IsFinite q›
  haveI : QuasiCompact fst := inferInstance
  first
    | exact inferInstance
    | exact Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat fst

/-- The first component of `Over.pullback q` applied to a map. -/
theorem map_left_fst {X Y : Scheme.{0}} (q : X ⟶ Y) {U V : Over Y} (u : U ⟶ V) :
    ((Over.pullback q).map u).left ≫ pullback.fst V.hom q = pullback.fst U.hom q ≫ u.left := by
  first
    | exact pullback.lift_fst _ _ _
    | exact SGRSplit.map_left_fst u
    | (rw [Over.pullback_map_left]; exact pullback.lift_fst _ _ _)
    | simp

/-! ## 2. The square and the fibre-power map -/

section Square

variable {X Y B : Scheme.{0}} (A : FEC X) (qX : X ⟶ Y) (qA : A.F.left ⟶ B) (b : B ⟶ Y)
  (hpb : IsPullback qA A.F.hom b qX)

/-- The unit section of `A`. -/
abbrev oneL : X ⟶ A.F.left := (MonObj.one : 𝟙_ (Over X) ⟶ A.F).left

/-- The multiplication of `A` on the fibre square `A ×_X A`. -/
abbrev mulL : (A.F ⊗ A.F).left ⟶ A.F.left := (MonObj.mul : A.F ⊗ A.F ⟶ A.F).left

/-- The inverse of `A`. -/
abbrev invL : A.F.left ⟶ A.F.left := (GrpObj.inv : A.F ⟶ A.F).left

/-- `A` is the pullback of `Over.mk b` along `qX`, as objects of `Over X`. -/
def sqIsoOf : A.F ≅ (Over.pullback qX).obj (Over.mk b) :=
  Over.isoMk hpb.isoPullback (by first | exact hpb.isoPullback_hom_snd | simp)

/-- `A ×_X A` is the pullback of `Over.mk b ⊗ Over.mk b` along `qX`. -/
def sqTensorIsoOf : (Over.pullback qX).obj (Over.mk b ⊗ Over.mk b) ≅ A.F ⊗ A.F :=
  (Functor.Monoidal.μIso (Over.pullback qX) (Over.mk b) (Over.mk b)).symm ≪≫
    tensorIso (sqIsoOf A qX qA b hpb).symm (sqIsoOf A qX qA b hpb).symm

/-- The fibre-power map `A ×_X A ⟶ B ×_Y B`. -/
def fibrePowerMap : (A.F ⊗ A.F).left ⟶ (Over.mk b ⊗ Over.mk b).left :=
  (sqTensorIsoOf A qX qA b hpb).inv.left ≫ pullback.fst (Over.mk b ⊗ Over.mk b).hom qX

end Square

/-! ## 3. The descent input -/

/-- The data of a free finite quotient square.
* `actX`, `actA`: the action of `G` on `X` and on `A`, covering each other (`act_over`), by
  group automorphisms (`act_one`, `act_inv`, `act_mul`, with `actAA` the diagonal action on
  `A ×_X A`), commuting with `ι` (`act_iota`);
* `qX`: finite, flat, surjective, with kernel pair `aX, prX`;
* `qA`: with kernel pair `aA, prA`; `b`: with `IsPullback qA A.F.hom b qX`;
* the kernel pair `aAA, prAA` of the fibre-power map;
* each kernel pair is generated by the graphs `inc g` of the action;
* `P3`: an invariant section generating the 3-torsion. -/
structure DescentInput (X Y : Scheme.{0}) where
  A : FEC X
  G : Type
  actX : G → (X ⟶ X)
  actA : G → (A.F.left ⟶ A.F.left)
  act_over : ∀ g, actA g ≫ A.F.hom = A.F.hom ≫ actX g
  act_iota : ∀ (g : G) (a : O), actA g ≫ A.iota a = A.iota a ≫ actA g
  act_one : ∀ g, actX g ≫ oneL A = oneL A ≫ actA g
  act_inv : ∀ g, actA g ≫ invL A = invL A ≫ actA g
  actAA : G → ((A.F ⊗ A.F).left ⟶ (A.F ⊗ A.F).left)
  act_mul : ∀ g, actAA g ≫ mulL A = mulL A ≫ actA g
  qX : X ⟶ Y
  [finite : IsFinite qX]
  [flat : Flat qX]
  [surj : Surjective qX]
  RX : Scheme.{0}
  aX : RX ⟶ X
  prX : RX ⟶ X
  hKX : IsPullback aX prX qX qX
  incX : G → (X ⟶ RX)
  incX_a : ∀ g, incX g ≫ aX = actX g
  incX_pr : ∀ g, incX g ≫ prX = 𝟙 X
  incX_jointlyEpi : ∀ {W : Scheme.{0}} (u v : RX ⟶ W), (∀ g, incX g ≫ u = incX g ≫ v) → u = v
  B : Scheme.{0}
  qA : A.F.left ⟶ B
  RA : Scheme.{0}
  aA : RA ⟶ A.F.left
  prA : RA ⟶ A.F.left
  hKA : IsPullback aA prA qA qA
  incA : G → (A.F.left ⟶ RA)
  incA_a : ∀ g, incA g ≫ aA = actA g
  incA_pr : ∀ g, incA g ≫ prA = 𝟙 A.F.left
  incA_jointlyEpi : ∀ {W : Scheme.{0}} (u v : RA ⟶ W),
    (∀ g, incA g ≫ u = incA g ≫ v) → u = v
  b : B ⟶ Y
  hpb : IsPullback qA A.F.hom b qX
  RAA : Scheme.{0}
  aAA : RAA ⟶ (A.F ⊗ A.F).left
  prAA : RAA ⟶ (A.F ⊗ A.F).left
  hKAA : IsPullback aAA prAA (fibrePowerMap A qX qA b hpb) (fibrePowerMap A qX qA b hpb)
  incAA : G → ((A.F ⊗ A.F).left ⟶ RAA)
  incAA_a : ∀ g, incAA g ≫ aAA = actAA g
  incAA_pr : ∀ g, incAA g ≫ prAA = 𝟙 (A.F ⊗ A.F).left
  incAA_jointlyEpi : ∀ {W : Scheme.{0}} (u v : RAA ⟶ W),
    (∀ g, incAA g ≫ u = incAA g ≫ v) → u = v
  P3 : X ⟶ A.F.left
  P3_sec : P3 ≫ A.F.hom = 𝟙 X
  P3_gen : IsGen 3 A P3
  P3_inv : ∀ g, actX g ≫ P3 = P3 ≫ actA g

attribute [instance] DescentInput.finite DescentInput.flat DescentInput.surj

namespace DescentInput

variable {X Y : Scheme.{0}} (D : DescentInput X Y)

abbrev sqIso : D.A.F ≅ (Over.pullback D.qX).obj (Over.mk D.b) :=
  sqIsoOf D.A D.qX D.qA D.b D.hpb

abbrev PhiIso : (Over.pullback D.qX).obj (Over.mk D.b ⊗ Over.mk D.b) ≅ D.A.F ⊗ D.A.F :=
  sqTensorIsoOf D.A D.qX D.qA D.b D.hpb

abbrev qAA : (D.A.F ⊗ D.A.F).left ⟶ (Over.mk D.b ⊗ Over.mk D.b).left :=
  fibrePowerMap D.A D.qX D.qA D.b D.hpb

/-! ### Effective epimorphisms -/

instance effectiveEpi_qX : EffectiveEpi D.qX := by
  haveI : QuasiCompact D.qX := inferInstance
  first
    | exact inferInstance
    | exact Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat D.qX

instance effectiveEpi_qA : EffectiveEpi D.qA := effectiveEpi_of_isPullback D.hpb

theorem qAA_w : D.qAA ≫ (Over.mk D.b ⊗ Over.mk D.b).hom = (D.A.F ⊗ D.A.F).hom ≫ D.qX :=
  calc D.qAA ≫ (Over.mk D.b ⊗ Over.mk D.b).hom
      = D.PhiIso.inv.left ≫ pullback.fst (Over.mk D.b ⊗ Over.mk D.b).hom D.qX ≫
          (Over.mk D.b ⊗ Over.mk D.b).hom := Category.assoc _ _ _
    _ = D.PhiIso.inv.left ≫ pullback.snd (Over.mk D.b ⊗ Over.mk D.b).hom D.qX ≫ D.qX := by
        rw [pullback.condition]
    _ = (D.PhiIso.inv.left ≫ pullback.snd (Over.mk D.b ⊗ Over.mk D.b).hom D.qX) ≫ D.qX :=
        (Category.assoc _ _ _).symm
    _ = (D.A.F ⊗ D.A.F).hom ≫ D.qX := congrArg (fun k => k ≫ D.qX) (Over.w D.PhiIso.inv)

/-- The fibre-power map is a base change of `qX`. -/
theorem qAA_isPullback :
    IsPullback D.qAA (D.A.F ⊗ D.A.F).hom (Over.mk D.b ⊗ Over.mk D.b).hom D.qX :=
  IsPullback.of_iso_pullback ⟨D.qAA_w⟩ ((Over.forget X).mapIso D.PhiIso.symm) rfl
    (Over.w D.PhiIso.inv)

instance effectiveEpi_qAA : EffectiveEpi D.qAA := effectiveEpi_of_isPullback D.qAA_isPullback

/-! ### The action and the kernel pairs -/

theorem incX_a_assoc (g : D.G) {Z : Scheme.{0}} (h : X ⟶ Z) :
    D.incX g ≫ D.aX ≫ h = D.actX g ≫ h := by rw [← Category.assoc, D.incX_a]

theorem incX_pr_assoc (g : D.G) {Z : Scheme.{0}} (h : X ⟶ Z) :
    D.incX g ≫ D.prX ≫ h = h := by rw [← Category.assoc, D.incX_pr, Category.id_comp]

theorem incA_a_assoc (g : D.G) {Z : Scheme.{0}} (h : D.A.F.left ⟶ Z) :
    D.incA g ≫ D.aA ≫ h = D.actA g ≫ h := by rw [← Category.assoc, D.incA_a]

theorem incA_pr_assoc (g : D.G) {Z : Scheme.{0}} (h : D.A.F.left ⟶ Z) :
    D.incA g ≫ D.prA ≫ h = h := by rw [← Category.assoc, D.incA_pr, Category.id_comp]

theorem incAA_a_assoc (g : D.G) {Z : Scheme.{0}} (h : (D.A.F ⊗ D.A.F).left ⟶ Z) :
    D.incAA g ≫ D.aAA ≫ h = D.actAA g ≫ h := by rw [← Category.assoc, D.incAA_a]

theorem incAA_pr_assoc (g : D.G) {Z : Scheme.{0}} (h : (D.A.F ⊗ D.A.F).left ⟶ Z) :
    D.incAA g ≫ D.prAA ≫ h = h := by rw [← Category.assoc, D.incAA_pr, Category.id_comp]

/-- The quotient map is invariant. -/
theorem act_qA (g : D.G) : D.actA g ≫ D.qA = D.qA := by
  rw [← D.incA_a g, Category.assoc, D.hKA.w, ← Category.assoc, D.incA_pr g, Category.id_comp]

/-- An equivariant endomorphism followed by `qA` equalizes the kernel pair of `qA`. -/
theorem compatA (f : D.A.F.left ⟶ D.A.F.left) (hf : ∀ g, D.actA g ≫ f = f ≫ D.actA g) :
    D.aA ≫ f ≫ D.qA = D.prA ≫ f ≫ D.qA :=
  D.incA_jointlyEpi _ _ fun g => by
    rw [D.incA_a_assoc, D.incA_pr_assoc, ← Category.assoc, hf g, Category.assoc, D.act_qA]

/-- An equivariant map from `X` followed by `qA` equalizes the kernel pair of `qX`. -/
theorem compatX (e₀ : X ⟶ D.A.F.left) (he₀ : ∀ g, D.actX g ≫ e₀ = e₀ ≫ D.actA g) :
    D.aX ≫ e₀ ≫ D.qA = D.prX ≫ e₀ ≫ D.qA :=
  D.incX_jointlyEpi _ _ fun g => by
    rw [D.incX_a_assoc, D.incX_pr_assoc, ← Category.assoc, he₀ g, Category.assoc, D.act_qA]

/-- An equivariant map from the fibre square followed by `qA` equalizes the kernel pair of
the fibre-power map. -/
theorem compatAA (m : (D.A.F ⊗ D.A.F).left ⟶ D.A.F.left)
    (hm : ∀ g, D.actAA g ≫ m = m ≫ D.actA g) :
    D.aAA ≫ m ≫ D.qA = D.prAA ≫ m ≫ D.qA :=
  D.incAA_jointlyEpi _ _ fun g => by
    rw [D.incAA_a_assoc, D.incAA_pr_assoc, ← Category.assoc, hm g, Category.assoc, D.act_qA]

/-! ## 4. The action `ι` downstairs -/

/-- `ι(a)` on `B`, descended along `qA`. -/
def iotaB (a : O) : D.B ⟶ D.B :=
  Y3QuotientDescent.descend D.hKA (D.A.iota a ≫ D.qA) (D.compatA _ fun g => D.act_iota g a)

@[reassoc]
theorem qA_iotaB (a : O) : D.qA ≫ D.iotaB a = D.A.iota a ≫ D.qA :=
  Y3QuotientDescent.descend_fac D.hKA (D.A.iota a ≫ D.qA) (D.compatA _ fun g => D.act_iota g a)

theorem iotaB_over (a : O) : D.iotaB a ≫ D.b = D.b :=
  Y3QuotientDescent.descend_over D.hKA D.hpb.w (D.A.iota a) (D.A.iota_over a) _

theorem iotaB_one : D.iotaB 1 = 𝟙 D.B := by
  apply Y3QuotientDescent.eq_of_effectiveEpi D.qA
  rw [D.qA_iotaB, D.A.iota_one, Category.id_comp, Category.comp_id]

theorem iotaB_mul (a a' : O) : D.iotaB (a * a') = D.iotaB a' ≫ D.iotaB a := by
  apply Y3QuotientDescent.eq_of_effectiveEpi D.qA
  simp only [D.qA_iotaB, D.qA_iotaB_assoc, D.A.iota_mul, Category.assoc]

/-! ## 5. The group structure downstairs -/

theorem oneL_sec : oneL D.A ≫ D.A.F.hom = 𝟙 X := Over.w (MonObj.one : 𝟙_ (Over X) ⟶ D.A.F)

theorem invL_over : invL D.A ≫ D.A.F.hom = D.A.F.hom := Over.w (GrpObj.inv : D.A.F ⟶ D.A.F)

theorem mulL_over : mulL D.A ≫ D.A.F.hom = (D.A.F ⊗ D.A.F).hom :=
  Over.w (MonObj.mul : D.A.F ⊗ D.A.F ⟶ D.A.F)

/-- The unit section downstairs, descended along `qX`. -/
def oneB : 𝟙_ (Over Y) ⟶ Over.mk D.b :=
  Over.homMk (Y3QuotientDescent.descend D.hKX (oneL D.A ≫ D.qA) (D.compatX _ D.act_one))
    (Y3QuotientDescent.descend_section D.hKX D.hpb.w (oneL D.A) D.oneL_sec _)

theorem qX_oneB : D.qX ≫ D.oneB.left = oneL D.A ≫ D.qA :=
  Y3QuotientDescent.descend_fac D.hKX (oneL D.A ≫ D.qA) (D.compatX _ D.act_one)

/-- The inverse downstairs, descended along `qA`. -/
def invB : Over.mk D.b ⟶ Over.mk D.b :=
  Over.homMk (Y3QuotientDescent.descend D.hKA (invL D.A ≫ D.qA) (D.compatA _ D.act_inv))
    (Y3QuotientDescent.descend_over D.hKA D.hpb.w (invL D.A) D.invL_over _)

theorem qA_invB : D.qA ≫ D.invB.left = invL D.A ≫ D.qA :=
  Y3QuotientDescent.descend_fac D.hKA (invL D.A ≫ D.qA) (D.compatA _ D.act_inv)

theorem mulB_over :
    Y3QuotientDescent.descend D.hKAA (mulL D.A ≫ D.qA) (D.compatAA _ D.act_mul) ≫ D.b =
      (Over.mk D.b ⊗ Over.mk D.b).hom := by
  apply Y3QuotientDescent.eq_of_effectiveEpi D.qAA
  rw [← Category.assoc,
    Y3QuotientDescent.descend_fac D.hKAA (mulL D.A ≫ D.qA) (D.compatAA _ D.act_mul),
    Category.assoc, D.hpb.w, ← Category.assoc, D.mulL_over, D.qAA_w]

/-- The multiplication downstairs, descended along the fibre-power map. -/
def mulB : Over.mk D.b ⊗ Over.mk D.b ⟶ Over.mk D.b :=
  Over.homMk (Y3QuotientDescent.descend D.hKAA (mulL D.A ≫ D.qA) (D.compatAA _ D.act_mul))
    D.mulB_over

theorem qAA_mulB : D.qAA ≫ D.mulB.left = mulL D.A ≫ D.qA :=
  Y3QuotientDescent.descend_fac D.hKAA (mulL D.A ≫ D.qA) (D.compatAA _ D.act_mul)

/-! ### Comparison with `A` on the pullback -/

/-- The group structure of `A`, transported to the pullback of `Over.mk b`. -/
abbrev grpPB : GrpObj ((Over.pullback D.qX).obj (Over.mk D.b)) := GrpObj.ofIso D.sqIso

theorem one_PB : MonObj.one (self := D.grpPB.toMonObj) =
    (MonObj.one : 𝟙_ (Over X) ⟶ D.A.F) ≫ D.sqIso.hom := by
  first
    | exact GrpObj.ofIso_one D.sqIso
    | rfl

theorem mul_PB : MonObj.mul (self := D.grpPB.toMonObj) =
    MonoidalCategoryStruct.tensorHom D.sqIso.inv D.sqIso.inv ≫
      (MonObj.mul : D.A.F ⊗ D.A.F ⟶ D.A.F) ≫ D.sqIso.hom := by
  first
    | exact GrpObj.ofIso_mul D.sqIso
    | rfl

theorem inv_PB : GrpObj.inv (self := D.grpPB) =
    D.sqIso.inv ≫ (GrpObj.inv : D.A.F ⟶ D.A.F) ≫ D.sqIso.hom := by
  first
    | exact GrpObj.ofIso_inv D.sqIso
    | rfl

theorem PhiIso_hom : D.PhiIso.hom =
    Functor.OplaxMonoidal.δ (Over.pullback D.qX) (Over.mk D.b) (Over.mk D.b) ≫
      MonoidalCategoryStruct.tensorHom D.sqIso.inv D.sqIso.inv := by
  first
    | rfl
    | simp [sqTensorIsoOf]

theorem sqIso_hom_fst : D.sqIso.hom.left ≫ pullback.fst D.b D.qX = D.qA :=
  D.hpb.isoPullback_hom_fst

theorem sqIso_inv_fst : D.sqIso.inv.left ≫ D.qA = pullback.fst D.b D.qX :=
  D.hpb.isoPullback_inv_fst

theorem PhiIso_hom_qAA :
    D.PhiIso.hom.left ≫ D.qAA = pullback.fst (Over.mk D.b ⊗ Over.mk D.b).hom D.qX := by
  show D.PhiIso.hom.left ≫ D.PhiIso.inv.left ≫ _ = _
  rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp]

theorem eta_left : (Functor.OplaxMonoidal.η (Over.pullback D.qX)).left =
    pullback.snd (𝟙 Y) D.qX :=
  (Category.comp_id _).symm.trans (Over.w (Functor.OplaxMonoidal.η (Over.pullback D.qX)))

/-- Maps into the pullback of `Over.mk b` agree once their first components agree. -/
theorem pb_hom_ext {U : Over X} {f g : U ⟶ (Over.pullback D.qX).obj (Over.mk D.b)}
    (h : f.left ≫ pullback.fst D.b D.qX = g.left ≫ pullback.fst D.b D.qX) : f = g := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  exact (Over.w f).trans (Over.w g).symm

/-- A map downstairs whose square with `qA` commutes with `hA` pulls back to the conjugate of
`hA` by the comparison isomorphism. -/
theorem map_conj (hA : D.A.F ⟶ D.A.F) (hB : Over.mk D.b ⟶ Over.mk D.b)
    (hc : D.qA ≫ hB.left = hA.left ≫ D.qA) :
    (Over.pullback D.qX).map hB = D.sqIso.inv ≫ hA ≫ D.sqIso.hom := by
  apply D.pb_hom_ext
  calc ((Over.pullback D.qX).map hB).left ≫ pullback.fst D.b D.qX
      = pullback.fst D.b D.qX ≫ hB.left := map_left_fst D.qX hB
    _ = D.sqIso.inv.left ≫ D.qA ≫ hB.left := by rw [← D.sqIso_inv_fst, Category.assoc]
    _ = D.sqIso.inv.left ≫ hA.left ≫ D.qA := by rw [hc]
    _ = (D.sqIso.inv ≫ hA ≫ D.sqIso.hom).left ≫ pullback.fst D.b D.qX := by
        simp only [Over.comp_left, Category.assoc, D.sqIso_hom_fst]

theorem hone : (Over.pullback D.qX).map D.oneB =
    Functor.OplaxMonoidal.η (Over.pullback D.qX) ≫ MonObj.one (self := D.grpPB.toMonObj) := by
  apply D.pb_hom_ext
  calc ((Over.pullback D.qX).map D.oneB).left ≫ pullback.fst D.b D.qX
      = pullback.fst (𝟙 Y) D.qX ≫ D.oneB.left := map_left_fst D.qX D.oneB
    _ = pullback.snd (𝟙 Y) D.qX ≫ D.qX ≫ D.oneB.left := by
        rw [← Category.assoc, ← pullback.condition, Category.comp_id]
    _ = pullback.snd (𝟙 Y) D.qX ≫ oneL D.A ≫ D.qA := by rw [D.qX_oneB]
    _ = (Functor.OplaxMonoidal.η (Over.pullback D.qX) ≫
          MonObj.one (self := D.grpPB.toMonObj)).left ≫ pullback.fst D.b D.qX := by
        rw [D.one_PB]
        simp only [Over.comp_left, Category.assoc, D.sqIso_hom_fst, D.eta_left]

theorem hmul : (Over.pullback D.qX).map D.mulB =
    Functor.OplaxMonoidal.δ (Over.pullback D.qX) (Over.mk D.b) (Over.mk D.b) ≫
      MonObj.mul (self := D.grpPB.toMonObj) := by
  apply D.pb_hom_ext
  calc ((Over.pullback D.qX).map D.mulB).left ≫ pullback.fst D.b D.qX
      = pullback.fst (Over.mk D.b ⊗ Over.mk D.b).hom D.qX ≫ D.mulB.left :=
        map_left_fst D.qX D.mulB
    _ = D.PhiIso.hom.left ≫ D.qAA ≫ D.mulB.left := by
        rw [← Category.assoc, D.PhiIso_hom_qAA]
    _ = D.PhiIso.hom.left ≫ mulL D.A ≫ D.qA := by rw [D.qAA_mulB]
    _ = (Functor.OplaxMonoidal.δ (Over.pullback D.qX) (Over.mk D.b) (Over.mk D.b) ≫
          MonObj.mul (self := D.grpPB.toMonObj)).left ≫ pullback.fst D.b D.qX := by
        rw [D.mul_PB, D.PhiIso_hom]
        simp only [Over.comp_left, Category.assoc, D.sqIso_hom_fst]

theorem hinv : (Over.pullback D.qX).map D.invB = GrpObj.inv (self := D.grpPB) :=
  (D.map_conj (GrpObj.inv : D.A.F ⟶ D.A.F) D.invB D.qA_invB).trans D.inv_PB.symm

/-- The descended group structure on `Over.mk b`. -/
def descGrp : GrpObj (Over.mk D.b) :=
  Y3GrpObjDescent.grpObjOverOfPullback (S := D.grpPB) D.qX D.b D.oneB D.mulB D.invB
    D.hone D.hmul D.hinv

theorem descGrp_one : MonObj.one (self := D.descGrp.toMonObj) = D.oneB := rfl

theorem descGrp_mul : MonObj.mul (self := D.descGrp.toMonObj) = D.mulB := rfl

attribute [local instance] descGrp

/-! ## 6. `ι` is by group endomorphisms and additive -/

theorem map_iotaB (a : O) :
    (Over.pullback D.qX).map (Over.homMk (D.iotaB a) (D.iotaB_over a) :
        Over.mk D.b ⟶ Over.mk D.b) =
      D.sqIso.inv ≫ (Over.homMk (D.A.iota a) (D.A.iota_over a) : D.A.F ⟶ D.A.F) ≫
        D.sqIso.hom :=
  D.map_conj _ _ (D.qA_iotaB a)

/-! ### Reflection of monoid morphisms -/

/-- A faithful strong monoidal functor reflects monoid morphisms: if `F.map f` is a monoid
morphism for the transported structures, then so is `f`. -/
theorem isMonHom_of_map {C₁ : Type*} [Category C₁] [MonoidalCategory C₁]
    {C₂ : Type*} [Category C₂] [MonoidalCategory C₂] (F : C₁ ⥤ C₂) [F.Monoidal] [F.Faithful]
    {M N : C₁} [MonObj M] [MonObj N] (f : M ⟶ N) (h : IsMonHom (F.map f)) : IsMonHom f := by
  haveI := h
  refine ⟨?_, ?_⟩
  · apply F.map_injective
    calc F.map ((MonObj.one : 𝟙_ C₁ ⟶ M) ≫ f)
        = F.map (MonObj.one : 𝟙_ C₁ ⟶ M) ≫ F.map f := F.map_comp _ _
      _ = Functor.OplaxMonoidal.η F ≫ Functor.LaxMonoidal.ε F ≫
            F.map (MonObj.one : 𝟙_ C₁ ⟶ M) ≫ F.map f :=
          Eq.symm (Functor.Monoidal.η_ε_assoc ..)
      _ = Functor.OplaxMonoidal.η F ≫ ((MonObj.one : 𝟙_ C₂ ⟶ F.obj M) ≫ F.map f) := by
          first
            | exact congrArg (fun k => Functor.OplaxMonoidal.η F ≫ k)
                (Functor.obj.η_def_assoc (F := F) M (F.map f)).symm
            | rw [Functor.obj.η_def, Category.assoc]
      _ = Functor.OplaxMonoidal.η F ≫ (MonObj.one : 𝟙_ C₂ ⟶ F.obj N) := by
          first
            | exact congrArg (fun k => Functor.OplaxMonoidal.η F ≫ k)
                (IsMonHom.one_hom (F.map f))
            | exact congrArg (fun k => Functor.OplaxMonoidal.η F ≫ k)
                (IsMonHom.one_hom (f := F.map f))
      _ = Functor.OplaxMonoidal.η F ≫ Functor.LaxMonoidal.ε F ≫
            F.map (MonObj.one : 𝟙_ C₁ ⟶ N) := by
          first
            | exact congrArg (fun k => Functor.OplaxMonoidal.η F ≫ k)
                (Functor.obj.η_def (F := F) N)
            | rw [Functor.obj.η_def]
      _ = F.map (MonObj.one : 𝟙_ C₁ ⟶ N) := Functor.Monoidal.η_ε_assoc ..
  · apply F.map_injective
    calc F.map ((MonObj.mul : M ⊗ M ⟶ M) ≫ f)
        = F.map (MonObj.mul : M ⊗ M ⟶ M) ≫ F.map f := F.map_comp _ _
      _ = Functor.OplaxMonoidal.δ F M M ≫ Functor.LaxMonoidal.μ F M M ≫
            F.map (MonObj.mul : M ⊗ M ⟶ M) ≫ F.map f :=
          Eq.symm (Functor.Monoidal.δ_μ_assoc ..)
      _ = Functor.OplaxMonoidal.δ F M M ≫
            ((MonObj.mul : F.obj M ⊗ F.obj M ⟶ F.obj M) ≫ F.map f) := by
          first
            | exact congrArg (fun k => Functor.OplaxMonoidal.δ F M M ≫ k)
                (Functor.obj.μ_def_assoc (F := F) M (F.map f)).symm
            | rw [Functor.obj.μ_def, Category.assoc]
      _ = Functor.OplaxMonoidal.δ F M M ≫
            ((F.map f ⊗ₘ F.map f) ≫ (MonObj.mul : F.obj N ⊗ F.obj N ⟶ F.obj N)) := by
          first
            | exact congrArg (fun k => Functor.OplaxMonoidal.δ F M M ≫ k)
                (IsMonHom.mul_hom (F.map f))
            | exact congrArg (fun k => Functor.OplaxMonoidal.δ F M M ≫ k)
                (IsMonHom.mul_hom (f := F.map f))
      _ = Functor.OplaxMonoidal.δ F M M ≫ (F.map f ⊗ₘ F.map f) ≫
            Functor.LaxMonoidal.μ F N N ≫ F.map (MonObj.mul : N ⊗ N ⟶ N) := by
          first
            | exact congrArg (fun k => Functor.OplaxMonoidal.δ F M M ≫ (F.map f ⊗ₘ F.map f) ≫ k)
                (Functor.obj.μ_def (F := F) N)
            | rw [Functor.obj.μ_def]
      _ = Functor.OplaxMonoidal.δ F M M ≫ Functor.LaxMonoidal.μ F M M ≫
            F.map (f ⊗ₘ f) ≫ F.map (MonObj.mul : N ⊗ N ⟶ N) := by
          first
            | exact congrArg (fun k => Functor.OplaxMonoidal.δ F M M ≫ k)
                (Functor.LaxMonoidal.μ_natural_assoc F f f (F.map (MonObj.mul : N ⊗ N ⟶ N)))
            | exact congrArg (fun k => Functor.OplaxMonoidal.δ F M M ≫ k)
                (Functor.LaxMonoidal.μ_natural_assoc ..)
            | exact congrArg (fun k => Functor.OplaxMonoidal.δ F M M ≫ k)
                (by rw [← Category.assoc, Functor.LaxMonoidal.μ_natural, Category.assoc])
      _ = F.map (f ⊗ₘ f) ≫ F.map (MonObj.mul : N ⊗ N ⟶ N) := Functor.Monoidal.δ_μ_assoc ..
      _ = F.map ((f ⊗ₘ f) ≫ (MonObj.mul : N ⊗ N ⟶ N)) := (F.map_comp _ _).symm

/-- Transport of `IsMonHom` for an endomorphism along an equality of monoid structures. -/
theorem isMonHom_of_monObj_eq {C₁ : Type*} [Category C₁] [MonoidalCategory C₁] {M : C₁}
    {S T : MonObj M} (h : S = T) {f : M ⟶ M} (hf : @IsMonHom C₁ _ _ M M T T f) :
    @IsMonHom C₁ _ _ M M S S f :=
  Eq.mpr (congrArg (fun U : MonObj M => @IsMonHom C₁ _ _ M M U U f) h) hf

/-! ### The comparison isomorphism is a monoid isomorphism -/

/-- `sqIso.hom` is a monoid morphism from the structure of `A` to `grpPB`. -/
theorem sqIso_hom_isMonHom :
    @IsMonHom (Over X) _ _ D.A.F ((Over.pullback D.qX).obj (Over.mk D.b)) _ D.grpPB.toMonObj
      D.sqIso.hom := by
  refine @IsMonHom.mk (Over X) _ _ D.A.F ((Over.pullback D.qX).obj (Over.mk D.b)) _
    D.grpPB.toMonObj D.sqIso.hom ?_ ?_
  · exact D.one_PB.symm
  · calc (MonObj.mul : D.A.F ⊗ D.A.F ⟶ D.A.F) ≫ D.sqIso.hom
        = (𝟙 D.A.F ⊗ₘ 𝟙 D.A.F) ≫ (MonObj.mul : D.A.F ⊗ D.A.F ⟶ D.A.F) ≫ D.sqIso.hom := by
          first
            | rw [MonoidalCategory.id_tensorHom_id, Category.id_comp]
            | simp only [MonoidalCategory.id_tensorHom_id, Category.id_comp]
      _ = ((D.sqIso.hom ≫ D.sqIso.inv) ⊗ₘ (D.sqIso.hom ≫ D.sqIso.inv)) ≫
            (MonObj.mul : D.A.F ⊗ D.A.F ⟶ D.A.F) ≫ D.sqIso.hom := by
          first
            | rw [Iso.hom_inv_id]
            | simp only [Iso.hom_inv_id]
      _ = (D.sqIso.hom ⊗ₘ D.sqIso.hom) ≫ (D.sqIso.inv ⊗ₘ D.sqIso.inv) ≫
            (MonObj.mul : D.A.F ⊗ D.A.F ⟶ D.A.F) ≫ D.sqIso.hom := by
          first
            | rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
            | simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
      _ = (D.sqIso.hom ⊗ₘ D.sqIso.hom) ≫ MonObj.mul (self := D.grpPB.toMonObj) := by
          first
            | rw [D.mul_PB]
            | exact congrArg (fun k => (D.sqIso.hom ⊗ₘ D.sqIso.hom) ≫ k) D.mul_PB.symm

/-- `sqIso.inv` is a monoid morphism from `grpPB` to the structure of `A`. -/
theorem sqIso_inv_isMonHom :
    @IsMonHom (Over X) _ _ ((Over.pullback D.qX).obj (Over.mk D.b)) D.A.F D.grpPB.toMonObj _
      D.sqIso.inv := by
  first
    | exact @CategoryTheory.instIsMonHomInvOfHom (Over X) _ _ D.A.F
        ((Over.pullback D.qX).obj (Over.mk D.b)) _ D.grpPB.toMonObj D.sqIso D.sqIso_hom_isMonHom
    | exact @IsMonHom.mk (Over X) _ _ ((Over.pullback D.qX).obj (Over.mk D.b)) D.A.F
        D.grpPB.toMonObj _ D.sqIso.inv
        (by rw [D.one_PB, Category.assoc, Iso.hom_inv_id, Category.comp_id])
        (by rw [D.mul_PB, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id])
    | exact ⟨by simp only [D.one_PB, Category.assoc, Iso.hom_inv_id, Category.comp_id],
        by simp only [D.mul_PB, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩

/-- Conjugating a monoid endomorphism of `A` by the comparison isomorphism gives a monoid
endomorphism for `grpPB`. -/
theorem conj_isMonHom (g : D.A.F ⟶ D.A.F) [IsMonHom g] :
    @IsMonHom (Over X) _ _ ((Over.pullback D.qX).obj (Over.mk D.b))
      ((Over.pullback D.qX).obj (Over.mk D.b)) D.grpPB.toMonObj D.grpPB.toMonObj
      (D.sqIso.inv ≫ g ≫ D.sqIso.hom) := by
  haveI := D.sqIso_hom_isMonHom
  haveI := D.sqIso_inv_isMonHom
  first
    | exact inferInstance
    | exact @CategoryTheory.instIsMonHomComp _ _ _ _ D.A.F _ D.grpPB.toMonObj _
        D.grpPB.toMonObj D.sqIso.inv (g ≫ D.sqIso.hom) D.sqIso_inv_isMonHom
        (@CategoryTheory.instIsMonHomComp _ _ _ D.A.F D.A.F _ _ _ D.grpPB.toMonObj g
          D.sqIso.hom _ D.sqIso_hom_isMonHom)

/-- Conjugation by the comparison isomorphism carries the product of `A` to the product of
`grpPB`, in the form `lift f g ≫ μ`. -/
theorem conj_lift_mul (f g : D.A.F ⟶ D.A.F) :
    D.sqIso.inv ≫ (CartesianMonoidalCategory.lift f g ≫
        (MonObj.mul : D.A.F ⊗ D.A.F ⟶ D.A.F)) ≫ D.sqIso.hom =
      CartesianMonoidalCategory.lift (D.sqIso.inv ≫ f ≫ D.sqIso.hom)
          (D.sqIso.inv ≫ g ≫ D.sqIso.hom) ≫ MonObj.mul (self := D.grpPB.toMonObj) := by
  calc D.sqIso.inv ≫ (CartesianMonoidalCategory.lift f g ≫
          (MonObj.mul : D.A.F ⊗ D.A.F ⟶ D.A.F)) ≫ D.sqIso.hom
      = D.sqIso.inv ≫ CartesianMonoidalCategory.lift f g ≫
          (MonObj.mul : D.A.F ⊗ D.A.F ⟶ D.A.F) ≫ D.sqIso.hom :=
        congrArg (fun k => D.sqIso.inv ≫ k) (Category.assoc _ _ _)
    _ = CartesianMonoidalCategory.lift (D.sqIso.inv ≫ f) (D.sqIso.inv ≫ g) ≫
          (MonObj.mul : D.A.F ⊗ D.A.F ⟶ D.A.F) ≫ D.sqIso.hom := by
        first
          | exact CartesianMonoidalCategory.comp_lift_assoc ..
          | simp only [CartesianMonoidalCategory.comp_lift_assoc]
          | rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
    _ = CartesianMonoidalCategory.lift ((D.sqIso.inv ≫ f ≫ D.sqIso.hom) ≫ D.sqIso.inv)
          ((D.sqIso.inv ≫ g ≫ D.sqIso.hom) ≫ D.sqIso.inv) ≫
          (MonObj.mul : D.A.F ⊗ D.A.F ⟶ D.A.F) ≫ D.sqIso.hom := by
        simp only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.comp_id]
    _ = CartesianMonoidalCategory.lift (D.sqIso.inv ≫ f ≫ D.sqIso.hom)
          (D.sqIso.inv ≫ g ≫ D.sqIso.hom) ≫ (D.sqIso.inv ⊗ₘ D.sqIso.inv) ≫
          (MonObj.mul : D.A.F ⊗ D.A.F ⟶ D.A.F) ≫ D.sqIso.hom := by
        first
          | exact Eq.symm (CartesianMonoidalCategory.lift_map_assoc ..)
          | simp only [CartesianMonoidalCategory.lift_map_assoc]
          | rw [← Category.assoc, CartesianMonoidalCategory.lift_map]
    _ = CartesianMonoidalCategory.lift (D.sqIso.inv ≫ f ≫ D.sqIso.hom)
          (D.sqIso.inv ≫ g ≫ D.sqIso.hom) ≫ MonObj.mul (self := D.grpPB.toMonObj) :=
        congrArg (fun k => CartesianMonoidalCategory.lift (D.sqIso.inv ≫ f ≫ D.sqIso.hom)
          (D.sqIso.inv ≫ g ≫ D.sqIso.hom) ≫ k) D.mul_PB.symm

/-! ### The transported structure -/

/-- The group structure transported along `Over.pullback qX` from `descGrp` is `grpPB`. -/
theorem grpObjObj_descGrp :
    Functor.grpObjObj (F := Over.pullback D.qX) (G := Over.mk D.b) = D.grpPB :=
  Y3GrpObjDescent.grpObjObj_grpObjOverOfPullback (S := D.grpPB) D.qX D.b D.oneB D.mulB D.invB
    D.hone D.hmul D.hinv

/-- The monoid structure transported along `Over.pullback qX` from `descGrp` is that of
`grpPB`. -/
theorem monObjObj_descGrp :
    Functor.monObjObj (F := Over.pullback D.qX) (Over.mk D.b) = D.grpPB.toMonObj := by
  first
    | exact congrArg GrpObj.toMonObj D.grpObjObj_descGrp
    | exact Y3GrpObjDescent.monObjObj_monObjOfFaithful (S := D.grpPB.toMonObj)
        (Over.pullback D.qX) D.oneB D.mulB D.hone D.hmul
    | (apply MonObj.ext
       show Functor.LaxMonoidal.μ (Over.pullback D.qX) (Over.mk D.b) (Over.mk D.b) ≫
           (Over.pullback D.qX).map D.mulB = _
       rw [D.hmul, Functor.Monoidal.μ_δ_assoc])

/-! ### `ι` downstairs -/

theorem iotaB_isMonHom (a : O) :
    IsMonHom (Over.homMk (D.iotaB a) (D.iotaB_over a) : Over.mk D.b ⟶ Over.mk D.b) := by
  haveI := D.A.iota_hom a
  have h1 : @IsMonHom (Over X) _ _ ((Over.pullback D.qX).obj (Over.mk D.b))
      ((Over.pullback D.qX).obj (Over.mk D.b)) D.grpPB.toMonObj D.grpPB.toMonObj
      ((Over.pullback D.qX).map
        (Over.homMk (D.iotaB a) (D.iotaB_over a) : Over.mk D.b ⟶ Over.mk D.b)) :=
    Eq.mpr (congrArg (fun k => @IsMonHom (Over X) _ _ ((Over.pullback D.qX).obj (Over.mk D.b))
        ((Over.pullback D.qX).obj (Over.mk D.b)) D.grpPB.toMonObj D.grpPB.toMonObj k)
        (D.map_iotaB a))
      (D.conj_isMonHom (Over.homMk (D.A.iota a) (D.A.iota_over a)))
  exact isMonHom_of_map (Over.pullback D.qX) _ (isMonHom_of_monObj_eq D.monObjObj_descGrp h1)

/-- Additivity of `ι` after pulling back along `qX`. -/
theorem map_iotaB_add (a a' : O) :
    (Over.pullback D.qX).map
        (Over.homMk (D.iotaB (a + a')) (D.iotaB_over (a + a')) : Over.mk D.b ⟶ Over.mk D.b) =
      (Over.pullback D.qX).map
        (Over.homMk (D.iotaB a) (D.iotaB_over a) * Over.homMk (D.iotaB a') (D.iotaB_over a') :
          Over.mk D.b ⟶ Over.mk D.b) := by
  have hadd : (Over.homMk (D.A.iota (a + a')) (D.A.iota_over _) : D.A.F ⟶ D.A.F) =
      CartesianMonoidalCategory.lift
          (Over.homMk (D.A.iota a) (D.A.iota_over a) : D.A.F ⟶ D.A.F)
          (Over.homMk (D.A.iota a') (D.A.iota_over a')) ≫ MonObj.mul :=
    D.A.iota_add a a'
  have h1 : (Over.pullback D.qX).map
        (Over.homMk (D.iotaB (a + a')) (D.iotaB_over (a + a')) : Over.mk D.b ⟶ Over.mk D.b) =
      D.sqIso.inv ≫ (Over.homMk (D.A.iota (a + a')) (D.A.iota_over (a + a')) :
        D.A.F ⟶ D.A.F) ≫ D.sqIso.hom :=
    D.map_iotaB (a + a')
  have h2 : D.sqIso.inv ≫ (Over.homMk (D.A.iota (a + a')) (D.A.iota_over (a + a')) :
        D.A.F ⟶ D.A.F) ≫ D.sqIso.hom =
      D.sqIso.inv ≫ (CartesianMonoidalCategory.lift
          (Over.homMk (D.A.iota a) (D.A.iota_over a) : D.A.F ⟶ D.A.F)
          (Over.homMk (D.A.iota a') (D.A.iota_over a') : D.A.F ⟶ D.A.F) ≫
            (MonObj.mul : D.A.F ⊗ D.A.F ⟶ D.A.F)) ≫ D.sqIso.hom :=
    congrArg (fun k => D.sqIso.inv ≫ k ≫ D.sqIso.hom) hadd
  have h3 : D.sqIso.inv ≫ (CartesianMonoidalCategory.lift
          (Over.homMk (D.A.iota a) (D.A.iota_over a) : D.A.F ⟶ D.A.F)
          (Over.homMk (D.A.iota a') (D.A.iota_over a') : D.A.F ⟶ D.A.F) ≫
            (MonObj.mul : D.A.F ⊗ D.A.F ⟶ D.A.F)) ≫ D.sqIso.hom =
      CartesianMonoidalCategory.lift
          (D.sqIso.inv ≫ (Over.homMk (D.A.iota a) (D.A.iota_over a) : D.A.F ⟶ D.A.F) ≫
            D.sqIso.hom)
          (D.sqIso.inv ≫ (Over.homMk (D.A.iota a') (D.A.iota_over a') : D.A.F ⟶ D.A.F) ≫
            D.sqIso.hom) ≫ MonObj.mul (self := D.grpPB.toMonObj) :=
    D.conj_lift_mul _ _
  have h4a : CartesianMonoidalCategory.lift
          (D.sqIso.inv ≫ (Over.homMk (D.A.iota a) (D.A.iota_over a) : D.A.F ⟶ D.A.F) ≫
            D.sqIso.hom)
          (D.sqIso.inv ≫ (Over.homMk (D.A.iota a') (D.A.iota_over a') : D.A.F ⟶ D.A.F) ≫
            D.sqIso.hom) ≫ MonObj.mul (self := D.grpPB.toMonObj) =
      CartesianMonoidalCategory.lift
          ((Over.pullback D.qX).map
            (Over.homMk (D.iotaB a) (D.iotaB_over a) : Over.mk D.b ⟶ Over.mk D.b))
          (D.sqIso.inv ≫ (Over.homMk (D.A.iota a') (D.A.iota_over a') : D.A.F ⟶ D.A.F) ≫
            D.sqIso.hom) ≫ MonObj.mul (self := D.grpPB.toMonObj) :=
    congrArg (fun u => CartesianMonoidalCategory.lift u
          (D.sqIso.inv ≫ (Over.homMk (D.A.iota a') (D.A.iota_over a') : D.A.F ⟶ D.A.F) ≫
            D.sqIso.hom) ≫ MonObj.mul (self := D.grpPB.toMonObj))
      (D.map_iotaB a).symm
  have h4b : CartesianMonoidalCategory.lift
          ((Over.pullback D.qX).map
            (Over.homMk (D.iotaB a) (D.iotaB_over a) : Over.mk D.b ⟶ Over.mk D.b))
          (D.sqIso.inv ≫ (Over.homMk (D.A.iota a') (D.A.iota_over a') : D.A.F ⟶ D.A.F) ≫
            D.sqIso.hom) ≫ MonObj.mul (self := D.grpPB.toMonObj) =
      CartesianMonoidalCategory.lift
          ((Over.pullback D.qX).map
            (Over.homMk (D.iotaB a) (D.iotaB_over a) : Over.mk D.b ⟶ Over.mk D.b))
          ((Over.pullback D.qX).map
            (Over.homMk (D.iotaB a') (D.iotaB_over a') : Over.mk D.b ⟶ Over.mk D.b)) ≫
        MonObj.mul (self := D.grpPB.toMonObj) :=
    congrArg (fun v => CartesianMonoidalCategory.lift
          ((Over.pullback D.qX).map
            (Over.homMk (D.iotaB a) (D.iotaB_over a) : Over.mk D.b ⟶ Over.mk D.b)) v ≫
        MonObj.mul (self := D.grpPB.toMonObj))
      (D.map_iotaB a').symm
  have hmu : MonObj.mul (self := D.grpPB.toMonObj) =
      MonObj.mul (self := Functor.monObjObj (F := Over.pullback D.qX) (Over.mk D.b)) :=
    congrArg (fun S : MonObj ((Over.pullback D.qX).obj (Over.mk D.b)) => MonObj.mul (self := S))
      D.monObjObj_descGrp.symm
  have h5 : CartesianMonoidalCategory.lift
          ((Over.pullback D.qX).map
            (Over.homMk (D.iotaB a) (D.iotaB_over a) : Over.mk D.b ⟶ Over.mk D.b))
          ((Over.pullback D.qX).map
            (Over.homMk (D.iotaB a') (D.iotaB_over a') : Over.mk D.b ⟶ Over.mk D.b)) ≫
        MonObj.mul (self := D.grpPB.toMonObj) =
      CartesianMonoidalCategory.lift
          ((Over.pullback D.qX).map
            (Over.homMk (D.iotaB a) (D.iotaB_over a) : Over.mk D.b ⟶ Over.mk D.b))
          ((Over.pullback D.qX).map
            (Over.homMk (D.iotaB a') (D.iotaB_over a') : Over.mk D.b ⟶ Over.mk D.b)) ≫
        MonObj.mul (self := Functor.monObjObj (F := Over.pullback D.qX) (Over.mk D.b)) :=
    congrArg (fun k => CartesianMonoidalCategory.lift
          ((Over.pullback D.qX).map
            (Over.homMk (D.iotaB a) (D.iotaB_over a) : Over.mk D.b ⟶ Over.mk D.b))
          ((Over.pullback D.qX).map
            (Over.homMk (D.iotaB a') (D.iotaB_over a') : Over.mk D.b ⟶ Over.mk D.b)) ≫ k) hmu
  have h6 : CartesianMonoidalCategory.lift
          ((Over.pullback D.qX).map
            (Over.homMk (D.iotaB a) (D.iotaB_over a) : Over.mk D.b ⟶ Over.mk D.b))
          ((Over.pullback D.qX).map
            (Over.homMk (D.iotaB a') (D.iotaB_over a') : Over.mk D.b ⟶ Over.mk D.b)) ≫
        MonObj.mul (self := Functor.monObjObj (F := Over.pullback D.qX) (Over.mk D.b)) =
      ((Over.pullback D.qX).map
          (Over.homMk (D.iotaB a) (D.iotaB_over a) : Over.mk D.b ⟶ Over.mk D.b) *
        (Over.pullback D.qX).map
          (Over.homMk (D.iotaB a') (D.iotaB_over a') : Over.mk D.b ⟶ Over.mk D.b) :
        (Over.pullback D.qX).obj (Over.mk D.b) ⟶ (Over.pullback D.qX).obj (Over.mk D.b)) :=
    (CategoryTheory.Hom.mul_def _ _).symm
  have h7 : ((Over.pullback D.qX).map
          (Over.homMk (D.iotaB a) (D.iotaB_over a) : Over.mk D.b ⟶ Over.mk D.b) *
        (Over.pullback D.qX).map
          (Over.homMk (D.iotaB a') (D.iotaB_over a') : Over.mk D.b ⟶ Over.mk D.b) :
        (Over.pullback D.qX).obj (Over.mk D.b) ⟶ (Over.pullback D.qX).obj (Over.mk D.b)) =
      (Over.pullback D.qX).map
        (Over.homMk (D.iotaB a) (D.iotaB_over a) * Over.homMk (D.iotaB a') (D.iotaB_over a') :
          Over.mk D.b ⟶ Over.mk D.b) :=
    (CategoryTheory.Functor.map_mul (Over.pullback D.qX) _ _).symm
  exact h1.trans (h2.trans (h3.trans (h4a.trans (h4b.trans (h5.trans (h6.trans h7))))))

theorem iotaB_add (a a' : O) :
    (Over.homMk (D.iotaB (a + a')) (D.iotaB_over _) : Over.mk D.b ⟶ Over.mk D.b) =
      Over.homMk (D.iotaB a) (D.iotaB_over a) * Over.homMk (D.iotaB a') (D.iotaB_over a') :=
  (Over.pullback D.qX).map_injective (D.map_iotaB_add a a')

/-! ## 7. The descended family -/

/-- The false elliptic curve over `Y` descended from `A`. -/
def descFEC (hP : ProperLocalOnBase) (hS : SmoothOfRelativeDimension 2 D.b)
    (hG : GeomConnLocalOnBase) : FEC Y where
  F := Over.mk D.b
  proper := hP D.qA D.A.F.hom D.b D.qX D.hpb D.flat D.surj inferInstance D.A.proper
  smooth := hS
  iota := D.iotaB
  iota_over := D.iotaB_over
  grp := D.descGrp
  geomConn := hG D.qA D.A.F.hom D.b D.qX D.hpb D.surj D.A.geomConn
  iota_hom := D.iotaB_isMonHom
  iota_one := D.iotaB_one
  iota_mul := D.iotaB_mul
  iota_add := D.iotaB_add

variable (hP : ProperLocalOnBase) (hS : SmoothOfRelativeDimension 2 D.b)
  (hG : GeomConnLocalOnBase)

/-- `A` is the base change of the descended curve along `qX`, with `h := qA`. -/
theorem descFEC_fibre : FECFibre (D.descFEC hP hS hG) D.qX D.A :=
  ⟨D.qA, D.hpb, fun a => (D.qA_iotaB a).symm⟩

/-! ## 8. The descended section and its generator property -/

/-- The section `P3` descended along `qX`. -/
def descP3 : Y ⟶ D.B :=
  Y3QuotientDescent.descend D.hKX (D.P3 ≫ D.qA) (D.compatX _ D.P3_inv)

theorem P3_qA : D.P3 ≫ D.qA = D.qX ≫ D.descP3 :=
  Y3QuotientDescent.section_clause D.hKX D.P3 _

theorem descP3_sec : D.descP3 ≫ D.b = 𝟙 Y :=
  Y3QuotientDescent.descend_section D.hKX D.hpb.w D.P3 D.P3_sec _

/-- The descended section generates the 3-torsion. -/
theorem isGen_descP3 (hD : IsGenDescent) : IsGen 3 (D.descFEC hP hS hG) D.descP3 := by
  have h1 : IsGen 3 (D.descFEC hP hS hG) (D.P3 ≫ D.qA) :=
    (isGen_iff_of_fibre (A := D.descFEC hP hS hG) (A' := D.A) (g := D.qX) (h := D.qA)
      D.hpb (fun a => (D.qA_iotaB a).symm)).1 D.P3_gen
  have h2 : IsGen 3 (D.descFEC hP hS hG) (D.qX ≫ D.descP3) :=
    (congrArg (fun P => IsGen 3 (D.descFEC hP hS hG) P) D.P3_qA).mp h1
  exact hD 3 Y (D.descFEC hP hS hG) Y X D.qX D.descP3 D.flat D.surj inferInstance h2

/-- Summary: the fibre square, the section equation, the section property and the generator
property of the descended data. -/
theorem descended_summary (hD : IsGenDescent) :
    FECFibre (D.descFEC hP hS hG) D.qX D.A ∧ D.P3 ≫ D.qA = D.qX ≫ D.descP3 ∧
      D.descP3 ≫ D.b = 𝟙 Y ∧ IsGen 3 (D.descFEC hP hS hG) D.descP3 :=
  ⟨D.descFEC_fibre hP hS hG, D.P3_qA, D.descP3_sec, D.isGen_descP3 hP hS hG hD⟩

end DescentInput

end Y3Buzzard
