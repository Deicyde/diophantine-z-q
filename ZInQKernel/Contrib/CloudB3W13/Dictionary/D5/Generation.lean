import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.Construction
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.FiniteLevel
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_torsionBy_algPoints_eq_pow_of_topologicalKrullDim_eq

/-!
# D5: full level three on the supplied kernel surface

Original dictionary proof, 2026-11-16, W13 D5 with Metamate/agentcloud assistance.
The cardinality theorem is the genuine algebraically closed field theorem from
Anthropic FLT (Apache-2.0; revision 6e837e75355538c7f80bab5b956861e86c4eacc2).
It is applied to the original abelian variety at *every* field extension. The
81 points embedded by the original level map exhaust its genuine geometric
three-torsion. The distinguished point remains the original `eta(1)`.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D5

open CategoryTheory Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 LeafQM
open ZInQ.Contrib.CloudW03NeronSurj
open FLT.NeronModelInfra FLT.GoodReductionJacobian
open FLT.CerednikDrinfeld.QM
open scoped Quaternion

variable {K k : Type} [Field K] [Field k]

/-- The original order-linear point formula, as an actual section equality. -/
theorem kernelPt_action (P : AV.QML3 K) (a b : O) :
    pushPt (P.q.iota a).hom.left (Over.w _)
      (kernelPt P.A (Additive.toMul (P.e.eta b))) =
        kernelPt P.A (Additive.toMul (P.e.eta (a * b))) := by
  apply Subtype.ext
  change (Additive.toMul (P.e.eta b)).left ≫ (P.q.iota a).hom.left =
    (Additive.toMul (P.e.eta (a * b))).left
  rw [P.e.linear]
  rfl

/-- The two natural-number multiplication conventions agree on actual points. -/
theorem nsmulPt_eq_nsmul {A : Scheme} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K))
    (n : ℕ) (Q : SchemeHomOver t f) : nsmulPt L t n Q = L.nsmul t n Q := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun R => L.mul t R Q) ih

theorem kernelPt_pow (A : AbVar K) (x : A.Pt K) (n : ℕ) :
    nsmulPt (kernelLaw A) (𝟙 _) n (kernelPt A x) = kernelPt A (x ^ n) := by
  induction n with
  | zero => exact (kernelPt_one A).symm
  | succ n ih =>
      change (kernelLaw A).mul (𝟙 _) (nsmulPt (kernelLaw A) (𝟙 _) n (kernelPt A x))
        (kernelPt A x) = _
      rw [ih, ← kernelPt_mul, pow_succ]

section Geometric

variable [Algebra K k]

/-- Precomposition of the supplied kernel level map, in the canonical FLT group
of algebraic points. The scalar structure is the actual supplied field map. -/
def algLevelMap (P : AV.QML3 K) : O →+ (kernelLaw P.A).AlgPoints (kernelLaw_comm P.A) k where
  toFun a := RelativeGroupLaw.AlgPoints.ofPoint
    (FakeEllipticCurve.sectionAt (kernelPt P.A (Additive.toMul (P.e.eta a))) k (algebraMap K k))
  map_zero' := by
    apply RelativeGroupLaw.AlgPoints.toPoint_injective
    rw [RelativeGroupLaw.AlgPoints.toPoint_zero]
    change FakeEllipticCurve.sectionAt (kernelPt P.A (Additive.toMul (P.e.eta 0)))
      k (algebraMap K k) = _
    rw [map_zero, Additive.toMul_zero, kernelPt_one]
    exact (kernelLaw P.A).one_natural (𝟙 _) _ _ (Category.comp_id _)
  map_add' a b := by
    apply RelativeGroupLaw.AlgPoints.toPoint_injective
    rw [RelativeGroupLaw.AlgPoints.toPoint_add]
    change FakeEllipticCurve.sectionAt (kernelPt P.A (Additive.toMul (P.e.eta (a + b))))
      k (algebraMap K k) = _
    rw [map_add, Additive.toMul_add, kernelPt_mul]
    exact (kernelLaw P.A).mul_natural (𝟙 _) _ _ (Category.comp_id _) _ _

/-- Base-change identity for the unchanged level points. -/
theorem algLevelMap_left (P : AV.QML3 K) (a : O) :
    (RelativeGroupLaw.AlgPoints.toPoint (algLevelMap (k := k) P a)).1 =
      geomPoint k (algebraMap K k) ≫ (Additive.toMul (P.e.eta a)).left := rfl

/-- No new geometric annihilator assumption: faithfulness of field spectra
carries the original kernel condition to every geometric field. -/
theorem algLevelMap_ker (P : AV.QML3 K) (a : O) :
    algLevelMap (k := k) P a = 0 ↔ ∃ b : O, a = 3 * b := by
  rw [← P.e.ker]
  constructor
  · intro h
    haveI : Epi (geomPoint k (algebraMap K k)) := SGRSplit.epi_spec_field _
    have hraw := congrArg (fun x => (RelativeGroupLaw.AlgPoints.toPoint x).1) h
    have hone := congrArg Subtype.val ((kernelLaw P.A).one_natural (𝟙 _)
      (geomPoint k (algebraMap K k)) (geomPoint k (algebraMap K k)) (Category.comp_id _))
    rw [← kernelPt_one] at hone
    apply Additive.toMul.injective
    apply Over.OverMorphism.ext
    apply (cancel_epi (geomPoint k (algebraMap K k))).mp
    exact hraw.trans hone.symm
  · intro h
    apply RelativeGroupLaw.AlgPoints.toPoint_injective
    change FakeEllipticCurve.sectionAt (kernelPt P.A (Additive.toMul (P.e.eta a)))
      k (algebraMap K k) = (kernelLaw P.A).one _
    rw [h, Additive.toMul_zero, kernelPt_one]
    exact (kernelLaw P.A).one_natural (𝟙 _) _ _ (Category.comp_id _)

/-- The canonical genuine torsion cardinality, at every algebraically closed
extension. This is 81 for the original surface, not for a substitute model. -/
theorem algLevel_torsion_card [CharZero K] [IsAlgClosed k] (P : AV.QML3 K) :
    Nat.card {x : (kernelLaw P.A).AlgPoints (kernelLaw_comm P.A) k //
      (3 : ℕ) • x = 0} = 81 := by
  let G := (kernelLaw P.A).AlgPoints (kernelLaw_comm P.A) k
  let e : {x : G // (3 : ℕ) • x = 0} ≃ Submodule.torsionBy ℤ G (3 : ℤ) :=
    { toFun := fun x => ⟨x.1, by
        rw [Submodule.mem_torsionBy_iff]
        change ((3 : ℕ) : ℤ) • x.1 = 0
        simpa only [natCast_zsmul] using x.2⟩
      invFun := fun x => ⟨x.1, by
        have h := (Submodule.mem_torsionBy_iff _ _ _).mp x.2
        change ((3 : ℕ) : ℤ) • x.1 = 0 at h
        simpa only [natCast_zsmul] using h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simpa only [Nat.reduceMul, Nat.reducePow] using
    (kernelLaw P.A).natCard_torsionBy_algPoints_eq_pow_of_topologicalKrullDim_eq
      (kernelLaw_comm P.A) (kernel_bundle P.A) 2 (kernel_dim_fibre P) k 3 (by norm_num)

/-- Multiplying the unchanged distinguished point gives the unchanged geometric
level point, with the exact action of the supplied order element. -/
theorem geom_action_level (P : AV.QML3 K) (x : ↥Λ) :
    pushPt (kernelAct P x) (kernelAct_over P x)
      (FakeEllipticCurve.sectionAt (kernelPt P.A (Additive.toMul (P.e.eta 1)))
        k (algebraMap K k)) =
      RelativeGroupLaw.AlgPoints.toPoint (algLevelMap (k := k) P (fromΛ x)) := by
  apply Subtype.ext
  change (geomPoint k (algebraMap K k) ≫ (Additive.toMul (P.e.eta 1)).left) ≫
      (P.q.iota (fromΛ x)).hom.left =
    geomPoint k (algebraMap K k) ≫ (Additive.toMul (P.e.eta (fromΛ x))).left
  rw [Category.assoc]
  have h := congrArg Subtype.val (kernelPt_action P (fromΛ x) 1)
  simpa only [mul_one] using congrArg (fun z => geomPoint k (algebraMap K k) ≫ z) h

end Geometric

/-- The original two descriptions of `3𝒪`, with no alteration of the lattice. -/
theorem fromΛ_three_iff (x : ↥Λ) :
    (∃ b : O, fromΛ x = 3 * b) ↔
      ∃ y : ↥Λ, (x : ℍ[ℚ, 2, -3]) = (3 : ℚ) • (y : ℍ[ℚ, 2, -3]) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨toΛ b, ?_⟩
    have h := congrArg Subtype.val hb
    simpa [Algebra.smul_def] using h
  · rintro ⟨y, hy⟩
    refine ⟨fromΛ y, Subtype.ext ?_⟩
    simpa [Algebra.smul_def] using hy

/-- Full level three, retaining literally the given kernel point `eta(1)`.
Generation is proved using the actual geometric cardinality 81 at each field. -/
def kernelFullLevel [CharZero K] (P : AV.QML3 K) : (kernelFakeEC P).FullLevel 3 where
  P := kernelPt P.A (Additive.toMul (P.e.eta 1))
  torsion := by
    change nsmulPt (kernelLaw P.A) (𝟙 _) 3 (kernelPt P.A (Additive.toMul (P.e.eta 1))) = _
    rw [kernelPt_pow, ← kernelPt_one]
    apply congrArg (kernelPt P.A)
    have h3 := eta_three P.e.eta P.e.ker (1 : O)
    exact congrArg Additive.toMul h3
  generates k sk Q hQ := by
    letI : Algebra K k := sk.toAlgebra
    have hx : (3 : ℕ) • RelativeGroupLaw.AlgPoints.ofPoint Q = 0 := by
      rw [RelativeGroupLaw.AlgPoints.nsmul_eq_zero_iff]
      exact (nsmulPt_eq_nsmul (kernelLaw P.A) _ 3 Q).symm.trans hQ
    obtain ⟨a, ha⟩ := eta_surjective_of_torsion_card (algLevelMap (k := k) P)
      (algLevelMap_ker P) (algLevel_torsion_card P) (RelativeGroupLaw.AlgPoints.ofPoint Q) hx
    refine ⟨toΛ a, ?_⟩
    have hp := geom_action_level (k := k) P (toΛ a)
    rw [fromΛ_toΛ, ha] at hp
    exact hp
  annihilator k sk x := by
    letI : Algebra K k := sk.toAlgebra
    change pushPt (kernelAct P x) (kernelAct_over P x)
      (FakeEllipticCurve.sectionAt (kernelPt P.A (Additive.toMul (P.e.eta 1))) k sk) =
        (kernelLaw P.A).one _ ↔ _
    rw [geom_action_level]
    change algLevelMap (k := k) P (fromΛ x) = 0 ↔ _
    rw [algLevelMap_ker, fromΛ_three_iff]

/-- The complete FLT datum with exactly the original surface, action and point. -/
def kernelWithFullLevel [CharZero K] (P : AV.QML3 K) : FLTL3 K :=
  ⟨kernelFakeEC P, kernelFullLevel P⟩

/-- The FLT packaging has literally the supplied kernel level points. -/
theorem kernelWithFullLevel_points [CharZero K] (P : AV.QML3 K) (a : O) :
    fltLevelPoint (kernelWithFullLevel P) a = (Additive.toMul (P.e.eta a)).left := by
  have h := congrArg Subtype.val (kernelPt_action P a 1)
  simpa only [mul_one, kernelWithFullLevel, fltLevelPoint, kernelFakeEC_act,
    kernelFullLevel, kernelPt] using h

#print axioms algLevel_torsion_card
#print axioms kernelFullLevel

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D5
