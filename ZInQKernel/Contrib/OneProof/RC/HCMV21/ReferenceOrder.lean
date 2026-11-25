import ZInQKernel.Contrib.OneProof.RC.HCMV21.CompletedMaximalOrder
import ZInQKernel.Contrib.OneProof.RC.HCMV21.DetectorIdeal
import ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricRightIdeal
import ZInQKernel.Contrib.OneProof.RC.DivisionJoin.Identification
import ZInQKernel.Contrib.OneProof.RC.ExplicitSplit.Ramification
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Tex 8462–8476 and 9146–9148. Transport the level-one endomorphism order
to the detector's rational presentation, and compare its completed order
with the explicit division coordinates. -/

namespace ZInQ.Manuscript.RC.HCMV21

open Eichler Adelic QuaternionAlgebra PkgI3.AbVar
open scoped CategoryTheory.MonObj TensorProduct

/-- **Printed candidate, UNVERIFIED until the reading desk's two-lens pass.**
Voight, *Quaternion Algebras*, GTM 288 (Springer numbering), Main Theorem 14.1.3,
p. 218: the classification of quaternion algebras over `ℚ`, proved in Ch. 14.
Uniqueness is the injectivity of `B ↦ Ram B`. This is that injectivity
restricted to `Ram B = {q, ∞}`, the two places of tex 8462–8463. The existence
clause, as the manuscript cites it, is `AppF.VoightMainThm1461`. -/
def QuaternionRamificationUniqueness : Prop :=
  ∀ (q : ℕ) (a b c d : ℚ),
    AppF.RamifiedExactlyAtEll0Infty q a b → AppF.RamifiedExactlyAtEll0Infty q c d →
      Nonempty (B a b ≃ₐ[ℚ] B c d)

variable {a b c d : ℚ} {k : Type} [Field k] {A : PkgI3.AbVar k}

/-- Transport an order and its full lattice by a rational algebra equivalence. -/
noncomputable def transportOrder (S : Order c d) (e : B c d ≃ₐ[ℚ] B a b) : Order a b where
  ring := S.ring.map e.toRingHom
  full := by
    let f := (e.toLinearMap.restrictScalars ℤ : B c d →ₗ[ℤ] B a b)
    change FullLattice (S.lattice.map f)
    refine ⟨S.full.fg.map f, ?_⟩
    rw [Submodule.map_coe]
    change Submodule.span ℚ (e.toLinearMap '' (S.lattice : Set (B c d))) = ⊤
    rw [← Submodule.map_span, S.full.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective]

/-- Use the Deuring endomorphism theorem in the already fixed detector algebra. -/
theorem exists_referenceEndOrder
    (hD : DeuringSupersingularEndOrder) (hV : QuaternionRamificationUniqueness)
    (q : ℕ) [Fact q.Prime] [IsAlgClosed k] [CharP k q]
    (hram : AppF.RamifiedExactlyAtEll0Infty q a b)
    (hdim : A.dim = 1) (hss : ∀ P : A.Pt k, P ^ q = 1 → P = 1) :
    ∃ S : Order a b, Nonempty (A.End ≃+* S.ring) ∧
      ∀ T : Order a b, S.ring ≤ T.ring → T.ring ≤ S.ring := by
  obtain ⟨c, d, hcd, U, ⟨j⟩, hmax⟩ := hD q k A hdim hss
  obtain ⟨e⟩ := hV q c d a b hcd hram
  let S := transportOrder U e
  let i : U.ring ≃+* S.ring := e.toRingEquiv.subringMap (s := U.ring)
  refine ⟨S, ⟨j.trans i⟩, ?_⟩
  intro T hST x hx
  let V := transportOrder T e.symm
  have hUV : U.ring ≤ V.ring := fun y hy =>
    ⟨e y, hST ⟨y, hy, rfl⟩, e.symm_apply_apply y⟩
  have hh : e.symm x ∈ U.ring := hmax V hUV ⟨x, hx, rfl⟩
  exact ⟨e.symm x, hh, e.apply_symm_apply x⟩

/-- The standard local coordinates take each rational basis vector to
the corresponding vector of the basis over the completion. -/
private theorem localBasis_apply (p : Prime) (e : Module.Basis (Fin 4) ℚ (B a b))
    (i : Fin 4) :
    Module.Basis.ofEquivFun (localCoordinates p e) i = toLocal p.val (e i) := by
  apply (localCoordinates p e).injective
  rw [localCoordinates_toLocal]
  simp only [Module.Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply, Module.Basis.repr_self]
  ext j
  simp [Finsupp.single_apply, Pi.single_apply, apply_ite, eq_comm]

/-- Scalar extension from the rational presentation to its coefficientwise
p-adic presentation, with the prescribed image on rational quaternions. -/
noncomputable def quaternionBaseChange (p : Prime) :
    (ℚ_[p.val] ⊗[ℚ] B a b) ≃ₐ[ℚ_[p.val]] Bp p.val a b := by
  let f := AlgHom.liftEquiv ℚ ℚ_[p.val] (B a b) (Bp p.val a b) (toLocal p.val).toRatAlgHom
  let e := basisOneIJK a 0 b
  let U := e.baseChange ℚ_[p.val]
  let V := Module.Basis.ofEquivFun (localCoordinates p e)
  have he : f.toLinearMap = (U.equiv V (Equiv.refl (Fin 4))).toLinearMap := by
    apply U.ext
    intro i
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, localBasis_apply]
    rw [Module.Basis.baseChange_apply]
    change f (1 ⊗ₜ[ℚ] e i) = toLocal p.val (e i)
    dsimp only [f]
    rw [AlgHom.liftEquiv_tmul, one_smul]
    rfl
  exact AlgEquiv.ofBijective f (by
    change Function.Bijective f.toLinearMap
    rw [he, LinearEquiv.coe_coe]
    exact (U.equiv V (Equiv.refl _)).bijective)

@[simp] theorem quaternionBaseChange_tmul (p : Prime) (u : ℚ_[p.val]) (x : B a b) :
    quaternionBaseChange p (u ⊗ₜ[ℚ] x) = u • toLocal p.val x :=
  by
    change (AlgHom.liftEquiv ℚ ℚ_[p.val] (B a b) (Bp p.val a b) (toLocal p.val).toRatAlgHom)
      (u ⊗ₜ[ℚ] x) = _
    rw [AlgHom.liftEquiv_tmul]
    rfl

/-- Extend a rational identification of quaternion presentations to a local one. -/
noncomputable def localQuaternionEquiv (p : Prime) (e : B c d ≃ₐ[ℚ] B a b) :
    Bp p.val c d ≃ₐ[ℚ_[p.val]] Bp p.val a b :=
  (quaternionBaseChange p).symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : ℚ_[p.val] ≃ₐ[ℚ_[p.val]] ℚ_[p.val]) e).trans
      (quaternionBaseChange p)

@[simp] theorem localQuaternionEquiv_toLocal (p : Prime) (e : B c d ≃ₐ[ℚ] B a b) (x : B c d) :
    localQuaternionEquiv p e (toLocal p.val x) = toLocal p.val (e x) := by
  have hx : quaternionBaseChange p ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] x) = toLocal p.val x := by simp
  have he : (quaternionBaseChange p).symm (toLocal p.val x) = 1 ⊗ₜ[ℚ] x := by
    rw [← hx, AlgEquiv.symm_apply_apply]
  simp only [localQuaternionEquiv, AlgEquiv.trans_apply, he]
  change quaternionBaseChange p ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] e x) = _
  rw [quaternionBaseChange_tmul, one_smul]

/-- The ambient local division coordinates of the pinned rational algebra. -/
noncomputable def referenceDivisionChart (hV : QuaternionRamificationUniqueness)
    (q : Prime) (h3 : q.val % 4 = 3)
    (hram : AppF.RamifiedExactlyAtEll0Infty q.val a b) :
    Bp q.val a b ≃ₐ[ℚ_[q.val]] LocalDivision.D q.val :=
  (localQuaternionEquiv q (hV q.val a b (-1) (-(q.val : ℚ)) hram
    (ExplicitSplit.explicit_ramifiedExactlyAtEll0Infty q.property h3)).some).trans
      (DivisionJoin.ambientEquiv q.val)

private noncomputable def orderToCompletion (p : Prime) (S : Order a b) : S.ring →+* S.completion p.val :=
  ((toLocal p.val).comp S.ring.subtype).codRestrict (S.completion p.val).toSubring fun x =>
    Algebra.subset_adjoin ⟨x.val, x.property, rfl⟩

set_option maxHeartbeats 750000 in
/-- The tensor completion of the endomorphism ring equals the embedded
completion of its full integral lattice, on the actual endomorphisms. -/
noncomputable def completedReferenceEnd (p : Prime) (S : Order a b)
    (j : A.End ≃+* S.ring) : (ℤ_[p.val] ⊗[ℤ] A.End) ≃ₐ[ℤ_[p.val]] S.completion p.val := by
  let f := AlgHom.liftEquiv ℤ ℤ_[p.val] A.End (S.completion p.val)
    (((orderToCompletion p S).comp j.toRingHom).toIntAlgHom)
  let e := S.full.ratBasis (basisOneIJK a 0 b)
  let bE := S.basis.map j.toAddEquiv.symm.toIntLinearEquiv
  let bL := Module.Basis.ofEquivFun (localCoordinates p e)
  let g := (S.completion p.val).val.toLinearMap.comp f.toLinearMap
  have hg (i : Fin 4) : g (bE.baseChange ℤ_[p.val] i) = bL i := by
    rw [Module.Basis.baseChange_apply, localBasis_apply]
    change ((f (1 ⊗ₜ[ℤ] (j.symm (S.basis i))) : S.completion p.val) : Bp p.val a b) = _
    dsimp only [f]
    rw [AlgHom.liftEquiv_tmul, one_smul]
    change toLocal p.val ((j (j.symm (S.basis i))) : B a b) = _
    rw [RingEquiv.apply_symm_apply]
    have hr : e i = (S.basis i : B a b) := by
      letI : FullLattice S.lattice := S.full
      exact Module.Basis.extendOfIsLattice_apply ℚ
        (S.full.basis (basisOneIJK a 0 b)) i
    exact congrArg (toLocal p.val : B a b →+* Bp p.val a b) hr.symm
  have hi : Function.Injective g := by
    have hb : LinearIndependent ℤ_[p.val] bL :=
      LinearIndependent.restrict_scalars
        (K := ℚ_[p.val]) (by
          change Function.Injective fun r : ℤ_[p.val] => (r : ℚ_[p.val]) * 1
          intro x y h
          simp only [mul_one] at h
          exact PadicInt.coe_inj.mp h)
        bL.linearIndependent
    have he : g ∘ bE.baseChange ℤ_[p.val] = bL := funext hg
    have hh := Submodule.range_ker_disjoint (f := g) (v := bE.baseChange ℤ_[p.val])
      (he.symm ▸ hb)
    rw [(bE.baseChange ℤ_[p.val]).span_eq, top_disjoint] at hh
    exact LinearMap.ker_eq_bot.mp hh
  refine AlgEquiv.ofBijective f ⟨fun x y h => hi (congrArg Subtype.val h), ?_⟩
  change Function.Surjective f.toLinearMap
  rw [← LinearMap.range_eq_top, ← top_le_iff]
  intro x _
  have hx := x.property
  have hx' : (x : Bp p.val a b) ∈ localLattice p.val S.lattice := by
    rw [← S.completion_toSubmodule]
    exact hx
  change (x : Bp p.val a b) ∈ localLattice p.val S.ring.toAddSubgroup.toIntSubmodule at hx'
  rw [← S.full.span_ratBasis (basisOneIJK a 0 b), localLattice_basis] at hx'

  have hsub : Submodule.span ℤ_[p.val] (Set.range bL) ≤ LinearMap.range g :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ⟨_, hg i⟩)
  obtain ⟨y, hy⟩ := hsub hx'
  exact ⟨y, Subtype.ext hy⟩

@[simp] theorem completedReferenceEnd_one_tmul (p : Prime) (S : Order a b)
    (j : A.End ≃+* S.ring) (x : A.End) :
    (completedReferenceEnd p S j (1 ⊗ₜ[ℤ] x)).val = toLocal p.val (j x).val := by
  change ((AlgHom.liftEquiv ℤ ℤ_[p.val] A.End (S.completion p.val)
    (((orderToCompletion p S).comp j.toRingHom).toIntAlgHom) (1 ⊗ₜ[ℤ] x)) :
      Bp p.val a b) = _
  rw [AlgHom.liftEquiv_tmul, one_smul]
  rfl

/-- In the detector chart the maximal geometric completion is exactly
the valuation order. -/
theorem referenceCompletion_map_eq (q : Prime) [Fact (q.val % 4 = 3)]
    (S : Order a b) (hmax : ∀ T : Order a b, S.ring ≤ T.ring → T.ring ≤ S.ring)
    (e : Bp q.val a b ≃ₐ[ℤ_[q.val]] LocalDivision.D q.val) :
    (S.completion q.val).map e.toAlgHom = LocalDivision.order q.val := by
  have hS := completion_maximal_of_order_maximal S hmax q
  let U := S.completion q.val
  let : Module.Finite ℤ_[q.val] U := hS.1
  have hU : Module.Finite ℤ_[q.val] (U.map e.toAlgHom) :=
    Module.Finite.of_surjective (e.subalgebraMap U).toLinearMap (e.subalgebraMap U).surjective
  apply detector_order_eq_of_maximal _ hU
  intro T hT hle
  let V := T.map e.symm.toAlgHom
  have hV : Module.Finite ℤ_[q.val] V :=
    Module.Finite.of_surjective (e.symm.subalgebraMap T).toLinearMap (e.symm.subalgebraMap T).surjective
  have hUV : U ≤ V := by
    intro x hx
    exact ⟨e x, hle ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
  have hfull : Submodule.span ℚ_[q.val] (V : Set (Bp q.val a b)) = ⊤ :=
    top_unique (hS.2.1 ▸ Submodule.span_mono hUV)
  intro x hx
  refine ⟨e.symm x, hS.2.2 V hV hfull hUV ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩

/-- The actual enhanced reference and the detector have the same completion
at the detector prime. The cyclic level is a unit there. -/
theorem reference_levelCompletion_eq (q : ℕ) [Fact q.Prime] [Fact (q % 4 = 3)]
    (S : Order (-1) (-(q : ℚ))) (j : A.End ≃+* S.ring)
    (hmax : ∀ T : Order (-1) (-(q : ℚ)), S.ring ≤ T.ring → T.ring ≤ S.ring)
    (C : Subgroup (A.Pt k)) (N : ℕ) (hN : N ≠ 0) (hC : ∀ x ∈ C, x ^ N = 1)
    (hqN : IsUnit (N : ℤ_[q])) :
    (levelOrderOfEndOrder S j C N hN hC).completion q =
      DivisionJoin.completedOrder q (Fact.out : q % 4 = 3) := by
  rw [levelOrderOfEndOrder_completion_eq S j C N hN hC q hqN]
  let e := DivisionJoin.ambientIntegralEquiv q
  apply Subalgebra.map_injective (f := e.toAlgHom) e.injective
  exact (referenceCompletion_map_eq (⟨q, Fact.out⟩ : Prime) S hmax e).trans
    (DivisionJoin.completion_map q (Fact.out : q % 4 = 3)).symm

/-- A normalized completed algebra isomorphism, retaining the image of
each geometric endomorphism in the detector's division coordinates. -/
noncomputable def completedReferenceDivision (q : Prime) [Fact (q.val % 4 = 3)]
    (S : Order a b) (j : A.End ≃+* S.ring)
    (hmax : ∀ T : Order a b, S.ring ≤ T.ring → T.ring ≤ S.ring)
    (e : Bp q.val a b ≃ₐ[ℤ_[q.val]] LocalDivision.D q.val) :
    (ℤ_[q.val] ⊗[ℤ] A.End) ≃ₐ[ℤ_[q.val]] LocalDivision.order q.val :=
  (completedReferenceEnd q S j).trans <| (e.subalgebraMap (S.completion q.val)).trans
    (Subalgebra.equivOfEq _ _ (referenceCompletion_map_eq q S hmax e))

@[simp] theorem completedReferenceDivision_one_tmul (q : Prime) [Fact (q.val % 4 = 3)]
    (S : Order a b) (j : A.End ≃+* S.ring)
    (hmax : ∀ T : Order a b, S.ring ≤ T.ring → T.ring ≤ S.ring)
    (e : Bp q.val a b ≃ₐ[ℤ_[q.val]] LocalDivision.D q.val) (x : A.End) :
    (completedReferenceDivision q S j hmax e (1 ⊗ₜ[ℤ] x)).val =
      e (toLocal q.val (j x).val) := by
  change e ((completedReferenceEnd q S j (1 ⊗ₜ[ℤ] x)).val) = _
  rw [completedReferenceEnd_one_tmul]

end ZInQ.Manuscript.RC.HCMV21
