import ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.KernelGroup
import ZInQKernel.Contrib.CloudB3W13.Dictionary.Interfaces
import ZInQKernel.Contrib.OneProof.ShimuraGoodReductionNoGuard
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_CerednikDrinfeld_QM_trace_eq_intCast_of_charZero_of_smoothOfRelativeDimension_two

/-!
# D5: the original kernel surface as a fake elliptic curve, with `N=1`

Original dictionary proof, 2026-11-16, W13 D5 with Metamate/agentcloud assistance.
The quaternion trace theorem and the actual tangent-space bridge are reused from
Anthropic FLT, revision 6e837e75355538c7f80bab5b956861e86c4eacc2, through the
canonical retargeted providers; see their Apache-2.0 attribution notices.
Only the identity subgroup is used at N=1. All source data come from the given
kernel object; no assertion of full level, or of generation, is used here.
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

variable {K : Type} [Field K]

/-- Read the unchanged lattice element as a kernel order element. -/
def fromΛ (x : ↥Λ) : O :=
  ⟨(x : ℍ[ℚ, 2, -3]), (order_bridge.2.2 _).mp x.2⟩

@[simp] theorem fromΛ_toΛ (a : O) : fromΛ (toΛ a) = a := Subtype.ext rfl
@[simp] theorem toΛ_fromΛ (x : ↥Λ) : toΛ (fromΛ x) = x := Subtype.ext rfl
@[simp] theorem fromΛ_add (x y : ↥Λ) : fromΛ (x + y) = fromΛ x + fromΛ y :=
  Subtype.ext rfl

/-- The action is precisely the original `iota`, on the original carrier. -/
def kernelAct (P : AV.QML3 K) (x : ↥Λ) : P.A.X.left ⟶ P.A.X.left :=
  (P.q.iota (fromΛ x)).hom.left

theorem kernelAct_over (P : AV.QML3 K) (x : ↥Λ) :
    kernelAct P x ≫ P.A.X.hom = P.A.X.hom := Over.w _

theorem kernelAct_hom (P : AV.QML3 K) (x : ↥Λ) {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of K)) (Q R : SchemeHomOver t P.A.X.hom) :
    pushPt (kernelAct P x) (kernelAct_over P x) ((kernelLaw P.A).mul t Q R) =
      (kernelLaw P.A).mul t
        (pushPt (kernelAct P x) (kernelAct_over P x) Q)
        (pushPt (kernelAct P x) (kernelAct_over P x) R) := by
  letI : GrpObj (Over.mk P.A.X.hom) := P.A.grp
  apply Subtype.ext
  exact congrArg CommaMorphism.left
    (MonObj.mul_comp (schemeHomOverToOverHom Q) (schemeHomOverToOverHom R)
      (P.q.iota (fromΛ x)).hom)

theorem kernelAct_one (P : AV.QML3 K) (h : (1 : ℍ[ℚ, 2, -3]) ∈ Λ) :
    kernelAct P ⟨1, h⟩ = 𝟙 _ := by
  change (P.q.iota (1 : O)).hom.left = _
  rw [map_one]
  rfl

theorem kernelAct_mul (P : AV.QML3 K) (x y : ↥Λ)
    (h : (x : ℍ[ℚ, 2, -3]) * (y : ℍ[ℚ, 2, -3]) ∈ Λ) :
    kernelAct P ⟨(x : ℍ[ℚ, 2, -3]) * (y : ℍ[ℚ, 2, -3]), h⟩ =
      kernelAct P y ≫ kernelAct P x := by
  change (P.q.iota (fromΛ x * fromΛ y)).hom.left = _
  rw [map_mul]
  rfl

theorem kernelAct_add (P : AV.QML3 K) (x y : ↥Λ) {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of K)) (Q : SchemeHomOver t P.A.X.hom) :
    pushPt (kernelAct P (x + y)) (kernelAct_over P (x + y)) Q =
      (kernelLaw P.A).mul t
        (pushPt (kernelAct P x) (kernelAct_over P x) Q)
        (pushPt (kernelAct P y) (kernelAct_over P y) Q) := by
  letI : GrpObj (Over.mk P.A.X.hom) := P.A.grp
  apply Subtype.ext
  change Q.1 ≫ (P.q.iota (fromΛ (x + y))).hom.left = _
  rw [fromΛ_add, map_add]
  exact congrArg CommaMorphism.left
    (MonObj.comp_mul (schemeHomOverToOverHom Q)
      (P.q.iota (fromΛ x)).hom (P.q.iota (fromΛ y)).hom)

/-- The actual tangent trace condition, for every geometric field and every
honest tangent-space presentation. No tangent representation is supplied as an
extra assumption: the canonical provider constructs it and proves its dimension. -/
theorem kernelAct_trace [CharZero K] (P : AV.QML3 K)
    (k : Type) [Field k] [IsAlgClosed k] (sk : K →+* k)
    (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (τ : V → SchemeHomOver (tangentBase k sk) P.A.X.hom)
    (hinj : Function.Injective τ)
    (hrange : ∀ Q, Q ∈ Set.range τ ↔ IsTangentVector (kernelLaw P.A) k sk Q)
    (hadd : ∀ v w, τ (v + w) = (kernelLaw P.A).mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ c v, (τ (c • v)).1 = tangentScale k c ≫ (τ v).1)
    (m : ↥Λ) (Φ : V →ₗ[k] V)
    (hΦ : ∀ v, τ (Φ v) = pushPt (kernelAct P m) (kernelAct_over P m) (τ v))
    (n : ℤ) (hn : (m : ℍ[ℚ, 2, -3]) + star (m : ℍ[ℚ, 2, -3]) =
      ((n : ℚ) : ℍ[ℚ, 2, -3])) : LinearMap.trace k V Φ = (n : k) := by
  letI : CharZero k := CharZero.of_addMonoidHom sk.toAddMonoidHom sk.map_one sk.injective
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : SmoothOfRelativeDimension 2 P.A.X.hom :=
    SGRSplit.abVarSurfaceRelDim K P.A P.surface
  exact trace_eq_intCast_of_charZero_of_smoothOfRelativeDimension_two
    (q := 2) (q' := 3) (by norm_num) order_bridge.1 Λ order_bridge.2.1
    (kernelLaw P.A) (kernelAct P) (kernelAct_over P) (kernelAct_hom P)
    (kernelAct_one P) (kernelAct_mul P) (kernelAct_add P)
    k sk V τ hinj hrange hadd hsmul m Φ hΦ n hn

/-- A singleton identity subgroup, with its actual original point. -/
def identityLevelEquiv (P : AV.QML3 K) (k : Type) [Field k] (sk : K →+* k) :
    ZMod 1 × ZMod 1 ≃
      {Q : SchemeHomOver (geomPoint k sk) P.A.X.hom //
        FactorsThrough (kernelIdentity P.A) Q} where
  toFun _ := ⟨(kernelLaw P.A).one _, (factors_kernelIdentity_iff P.A _ _).mpr rfl⟩
  invFun _ := (0, 0)
  left_inv _ := Subsingleton.elim _ _
  right_inv Q := Subtype.ext ((factors_kernelIdentity_iff P.A _ _).mp Q.2).symm

/-- The supplied kernel object as the genuine FLT fake elliptic curve at `N=1`.
Full level three is constructed separately from its unchanged `eta(1)`. -/
def kernelFakeEC [CharZero K] (P : AV.QML3 K) : FakeEC K where
  A := P.A.X.left
  f := P.A.X.hom
  L := kernelLaw P.A
  comm := kernelLaw_comm P.A
  bundle := kernel_bundle P.A
  dim_fibre := kernel_dim_fibre P
  act := kernelAct P
  act_over := kernelAct_over P
  act_hom := kernelAct_hom P
  act_one := kernelAct_one P
  act_mul := kernelAct_mul P
  act_add := kernelAct_add P
  act_trace := kernelAct_trace P
  C := Spec (CommRingCat.of K)
  lev := kernelIdentity P.A
  lev_closed := kernelIdentity_closed P.A
  lev_sub t Q R hQ hR := by
    have hQ' := (factors_kernelIdentity_iff P.A t Q).mp hQ
    have hR' := (factors_kernelIdentity_iff P.A t R).mp hR
    rw [hQ', hR']
    constructor
    · apply (factors_kernelIdentity_iff P.A _ _).mpr
      exact (kernelLaw P.A).one_mul _ _
    · apply (factors_kernelIdentity_iff P.A _ _).mpr
      exact ((kernelLaw P.A).mul_one _ _).symm.trans
        ((kernelLaw P.A).inv_mul_cancel _ _)
  lev_one t := (factors_kernelIdentity_iff P.A t _).mpr rfl
  lev_torsion t Q hQ := by
    change (kernelLaw P.A).mul t ((kernelLaw P.A).one t) Q = _
    rw [(kernelLaw P.A).one_mul]
    exact (factors_kernelIdentity_iff P.A t Q).mp hQ
  lev_stable x t Q hQ := by
    apply (factors_kernelIdentity_iff P.A t _).mpr
    rw [(factors_kernelIdentity_iff P.A t Q).mp hQ]
    apply Subtype.ext
    exact kernelEnd_one P.A (P.q.iota (fromΛ x)) t
  lev_finite := by rw [kernelIdentity_over]; infer_instance
  lev_flat := by rw [kernelIdentity_over]; infer_instance
  lev_finitePresentation := by rw [kernelIdentity_over]; infer_instance
  lev_rank s := by rw [kernelIdentity_over, Scheme.Hom.finrank_eq_one_of_isIso]; rfl
  lev_fibre k sk _ := ⟨identityLevelEquiv P k sk, fun _ _ =>
    ((kernelLaw P.A).one_mul (geomPoint k sk) ((kernelLaw P.A).one _)).symm⟩

@[simp] theorem kernelFakeEC_act [CharZero K] (P : AV.QML3 K) (a : O) :
    (kernelFakeEC P).act (toΛ a) = (P.q.iota a).hom.left := by
  simp only [kernelFakeEC, kernelAct, fromΛ_toΛ]

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D5
