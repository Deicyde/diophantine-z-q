import ZInQKernel.Contrib.OneProof.RC.HCMV21.DetectorReference
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceTateLevel

/-! The identification of the enhanced reference order with the explicit
`levelOrder` on class sets (tex 8464–8468). A reference coordinate `z` with
`ReferenceOrderCoordinates R S z` gives an equivalence between the class
sets of `S` and `R`, by right multiplication by `z` on double cosets. It sends
the unit class to the class of `fromAdelic z` and keeps left rings. Two Eichler
orders of one level are locally conjugate; no equality of orders is claimed. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open Eichler Adelic PkgI3.AbVar
open scoped CategoryTheory.MonObj

variable {a b : ℚ}

section Transport

variable {R S : Order a b} {z : FiniteUnits R}

/-- A family of local units that are all integral is a restricted unit. -/
def integralFamily (R : Order a b) (f : LocalFamily a b) (hf : ∀ p, f p ∈ localUnits R p) :
    FiniteUnits R :=
  ⟨f, by
    apply Set.finite_empty.subset
    intro p hp
    exact (hp (hf p)).elim⟩

/-- The inverse reference coordinate, read in the restricted units of `S`. -/
def inverseReference (z : FiniteUnits R) : FiniteUnits S :=
  multiplyReference (R := S) (S := R) z⁻¹ (1 : FiniteUnits S)

@[simp] theorem multiplyReference_val {R S : Order a b} (w : FiniteUnits S)
    (z : FiniteUnits R) (p : Prime) :
    (multiplyReference w z).val p = w.val p * z.val p := rfl

@[simp] theorem inverseReference_val (z : FiniteUnits R) (p : Prime) :
    (inverseReference (S := S) z).val p = (z.val p)⁻¹ := by
  change (z⁻¹).val p * 1 = _
  rw [mul_one]
  rfl

theorem conj_mem_localUnits (hz : ReferenceOrderCoordinates R S z) (p : Prime)
    (r : (Bp p.val a b)ˣ) (hr : r ∈ localUnits S p) :
    (z.val p)⁻¹ * r * z.val p ∈ localUnits R p := by
  change (↑((z.val p)⁻¹ * r * z.val p) : Bp p.val a b) ∈ R.completion p.val ∧
    (↑((z.val p)⁻¹ * r * z.val p)⁻¹ : Bp p.val a b) ∈ R.completion p.val
  rw [mul_inv_rev, mul_inv_rev, inv_inv]
  simp only [Units.val_mul]
  rw [← mul_assoc (↑(z.val p)⁻¹ : Bp p.val a b)]
  exact ⟨(hz p _).mpr hr.1, (hz p _).mpr hr.2⟩

theorem conj_inv_mem_localUnits (hz : ReferenceOrderCoordinates R S z) (p : Prime)
    (r : (Bp p.val a b)ˣ) (hr : r ∈ localUnits R p) :
    z.val p * r * (z.val p)⁻¹ ∈ localUnits S p := by
  have key (y : (Bp p.val a b)ˣ) (hy : (y : Bp p.val a b) ∈ R.completion p.val) :
      ((z.val p * y * (z.val p)⁻¹ : (Bp p.val a b)ˣ) : Bp p.val a b) ∈ S.completion p.val := by
    apply (hz p _).mp
    simpa only [Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc,
      Units.mul_inv, mul_one, Units.inv_mul_cancel_left] using hy
  refine ⟨key r hr.1, ?_⟩
  rw [show (z.val p * r * (z.val p)⁻¹)⁻¹ = z.val p * r⁻¹ * (z.val p)⁻¹ by group]
  exact key r⁻¹ hr.2

/-- Right multiplication by the reference coordinate, on restricted units. -/
def toReference (z : FiniteUnits R) (w : FiniteUnits S) : FiniteUnits R :=
  multiplyReference w z

/-- Right multiplication by the inverse reference coordinate. -/
def fromReference (z : FiniteUnits R) (w : FiniteUnits R) : FiniteUnits S :=
  multiplyReference (R := S) (S := R) w (inverseReference z)

theorem fromReference_toReference (w : FiniteUnits S) :
    fromReference z (toReference z w) = w := by
  apply Subtype.ext
  funext p
  change (w.val p * z.val p) * (inverseReference (S := S) z).val p = w.val p
  rw [inverseReference_val, mul_inv_cancel_right]

theorem toReference_fromReference (w : FiniteUnits R) :
    toReference z (fromReference (S := S) z w) = w := by
  apply Subtype.ext
  funext p
  change (w.val p * (inverseReference (S := S) z).val p) * z.val p = w.val p
  rw [inverseReference_val, inv_mul_cancel_right]

theorem toReference_rel (hz : ReferenceOrderCoordinates R S z) {w w' : FiniteUnits S}
    (h : (doubleCosetRel S).r w w') : (doubleCosetRel R).r (toReference z w) (toReference z w') := by
  obtain ⟨u, r, rfl⟩ := h
  let r' := integralFamily R (fun p => (z.val p)⁻¹ * r.val.val p * z.val p)
    (fun p => conj_mem_localUnits hz p _ (r.prop p))
  refine ⟨u, ⟨r', fun p => conj_mem_localUnits hz p _ (r.prop p)⟩, ?_⟩
  apply Subtype.ext
  funext p
  change ((diagonal S u).val p * w.val p * r.val.val p) * z.val p =
    (diagonal R u).val p * (w.val p * z.val p) * ((z.val p)⁻¹ * r.val.val p * z.val p)
  change (Units.map (toLocal p.val).toMonoidHom u * w.val p * r.val.val p) * z.val p =
    Units.map (toLocal p.val).toMonoidHom u * (w.val p * z.val p) *
      ((z.val p)⁻¹ * r.val.val p * z.val p)
  group

theorem fromReference_rel (hz : ReferenceOrderCoordinates R S z) {w w' : FiniteUnits R}
    (h : (doubleCosetRel R).r w w') :
    (doubleCosetRel S).r (fromReference (S := S) z w) (fromReference z w') := by
  obtain ⟨u, r, rfl⟩ := h
  let r' := integralFamily S (fun p => z.val p * r.val.val p * (z.val p)⁻¹)
    (fun p => conj_inv_mem_localUnits hz p _ (r.prop p))
  refine ⟨u, ⟨r', fun p => conj_inv_mem_localUnits hz p _ (r.prop p)⟩, ?_⟩
  apply Subtype.ext
  funext p
  change ((diagonal R u).val p * w.val p * r.val.val p) * (inverseReference (S := S) z).val p =
    (diagonal S u).val p * (w.val p * (inverseReference (S := S) z).val p) *
      (z.val p * r.val.val p * (z.val p)⁻¹)
  rw [inverseReference_val]
  change (Units.map (toLocal p.val).toMonoidHom u * w.val p * r.val.val p) * (z.val p)⁻¹ =
    Units.map (toLocal p.val).toMonoidHom u * (w.val p * (z.val p)⁻¹) *
      (z.val p * r.val.val p * (z.val p)⁻¹)
  group

/-- Right multiplication by the reference coordinate on double cosets. -/
def doubleCosetsEquivOfReference (hz : ReferenceOrderCoordinates R S z) :
    DoubleCosets S ≃ DoubleCosets R where
  toFun := Quotient.map (toReference z) (fun _ _ h => toReference_rel hz h)
  invFun := Quotient.map (fromReference (S := S) z) (fun _ _ h => fromReference_rel hz h)
  left_inv x := by
    induction x using Quotient.inductionOn with
    | _ w => exact congrArg (Quotient.mk _) (fromReference_toReference w)
  right_inv x := by
    induction x using Quotient.inductionOn with
    | _ w => exact congrArg (Quotient.mk _) (toReference_fromReference w)

/-- The class-set equivalence attached to a reference coordinate. -/
def classSetEquivOfReference (hz : ReferenceOrderCoordinates R S z) :
    ClassSet S ≃ ClassSet R :=
  ((classesEquiv S).trans (doubleCosetsEquivOfReference hz)).trans (idealsEquiv R)

/-- The trivial restricted unit gives the order itself. -/
theorem fromAdelic_one (R : Order a b) :
    fromAdelic (1 : FiniteUnits R) = ⟨RightIdeal.self R, RightIdeal.self_locallyPrincipal R⟩ := by
  apply Subtype.ext
  apply RightIdeal.ext
  ext x
  rw [mem_fromAdelic]
  change (∀ p : Prime, toLocal p.val x ∈ localRight R p 1) ↔ x ∈ R.lattice
  simp_rw [localRight_one]
  exact (mem_iff_all_local R.full x).symm

theorem classesEquiv_self (R : Order a b) :
    classesEquiv R (Quotient.mk _ ⟨RightIdeal.self R, RightIdeal.self_locallyPrincipal R⟩) =
      Quotient.mk _ (1 : FiniteUnits R) := by
  apply (idealsEquiv R).injective
  change (idealsEquiv R) ((idealsEquiv R).symm _) = _
  rw [Equiv.apply_symm_apply, idealsEquiv_mk, fromAdelic_one]

theorem classSetEquivOfReference_mk (hz : ReferenceOrderCoordinates R S z) (w : FiniteUnits S) :
    classSetEquivOfReference hz (Quotient.mk _ (fromAdelic w)) =
      Quotient.mk _ (fromAdelic (toReference z w)) := by
  have hw : classesEquiv S (Quotient.mk _ (fromAdelic w)) = Quotient.mk _ w := by
    apply (idealsEquiv S).injective
    change (idealsEquiv S) ((idealsEquiv S).symm _) = _
    rw [Equiv.apply_symm_apply, idealsEquiv_mk]
  change idealsEquiv R (doubleCosetsEquivOfReference hz (classesEquiv S _)) = _
  rw [hw]
  rfl

/-- The unit class goes to the class of `fromAdelic z`. -/
theorem classSetEquivOfReference_self (hz : ReferenceOrderCoordinates R S z) :
    classSetEquivOfReference hz
        (Quotient.mk _ ⟨RightIdeal.self S, RightIdeal.self_locallyPrincipal S⟩) =
      Quotient.mk _ (fromAdelic z) := by
  rw [← fromAdelic_one, classSetEquivOfReference_mk]
  change Quotient.mk _ (fromAdelic (multiplyReference 1 z)) = _
  rw [multiplyReference_one]

/-- Left rings are kept: the representative `fromAdelic (w z)` of the image
class has the same left ring as the representative `fromAdelic w`. -/
theorem leftRing_toReference (hz : ReferenceOrderCoordinates R S z) (w : FiniteUnits S) :
    (fromAdelic (toReference z w)).val.leftRing = (fromAdelic w).val.leftRing := by
  ext x
  rw [mem_leftRing_iff, mem_leftRing_iff]
  apply forall_congr'
  intro p
  change (↑(w.val p * z.val p)⁻¹ : Bp p.val a b) * toLocal p.val x *
      (↑(w.val p * z.val p) : Bp p.val a b) ∈ R.completion p.val ↔ _
  rw [mul_inv_rev]
  simp only [Units.val_mul]
  rw [show (↑(z.val p)⁻¹ : Bp p.val a b) * (↑(w.val p)⁻¹ : Bp p.val a b) * toLocal p.val x *
      ((w.val p : Bp p.val a b) * (z.val p : Bp p.val a b)) =
      (↑(z.val p)⁻¹ : Bp p.val a b) * ((↑(w.val p)⁻¹ : Bp p.val a b) * toLocal p.val x *
        (w.val p : Bp p.val a b)) * (z.val p : Bp p.val a b) by simp only [mul_assoc]]
  exact hz p _

/-- Every representative of an image class has left ring conjugate to the
left ring of a representative of the source class. -/
theorem leftRing_classSetEquivOfReference (hz : ReferenceOrderCoordinates R S z)
    (I : LPIdeal S) (J : LPIdeal R)
    (hJ : classSetEquivOfReference hz (Quotient.mk _ I) = Quotient.mk _ J) :
    ∃ u : (B a b)ˣ, ∀ x : B a b,
      x ∈ J.val.leftRing ↔ (↑u⁻¹ : B a b) * x * (u : B a b) ∈ I.val.leftRing := by
  obtain ⟨w, rfl⟩ := exists_adelic_representative I
  rw [classSetEquivOfReference_mk] at hJ
  obtain ⟨u, hu⟩ := Quotient.exact hJ
  refine ⟨u, fun x => ?_⟩
  rw [← leftRing_toReference hz w, ← hu]
  constructor
  · intro hx y hy
    have hy' : (u : B a b) * y ∈ ((fromAdelic (toReference z w)).val.translate u).lattice := by
      rw [RightIdeal.mem_translate]
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using hy
    have h := hx _ hy'
    rw [RightIdeal.mem_translate] at h
    simpa only [mul_assoc] using h
  · intro hx y hy
    rw [RightIdeal.mem_translate] at hy ⊢
    have h := hx _ hy
    simpa only [mul_assoc, Units.mul_inv_cancel_left, ← mul_assoc (u : B a b) (↑u⁻¹ : B a b),
      Units.mul_inv, one_mul] using h

end Transport

section Level

variable {k : Type} [Field k] [IsAlgClosed k] {A : PkgI3.AbVar k}

set_option maxHeartbeats 400000 in
/-- The reference coordinate of the enhanced order of an actual cyclic
reference in the explicit level order. The split profile at every prime
other than `q` comes from `splitProfile_of_cyclicReference` with the
integral basis read off the frame `j`; no Deuring hypothesis enters. -/
theorem exists_levelReferenceCoordinates (hT : PkgI3.TateModuleFree)
    (q : ℕ) [Fact q.Prime] (h : q % 4 = 3) [CharP k q]
    (N : ℕ) (hN : 0 < N) (hcop : N.Coprime q)
    (S : Order (-1) (-(q : ℚ))) (j : A.End ≃+* S.ring)
    (hmax : ∀ T : Order (-1) (-(q : ℚ)), S.ring ≤ T.ring → T.ring ≤ S.ring)
    (hdim : A.dim = 1) (P : A.Pt k) (hP : orderOf P = N)
    (hC : ∀ x ∈ Subgroup.zpowers P, x ^ N = 1) :
    ∃ z : Adelic.FiniteUnits (levelOrder q h N hN),
      ReferenceOrderCoordinates (levelOrder q h N hN)
        (levelOrderOfEndOrder S j (Subgroup.zpowers P) N hN.ne' hC) z := by
  have : Fact (q % 4 = 3) := ⟨h⟩
  have hqN : IsUnit (N : ℤ_[q]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcop.symm)
  apply detector_referenceCoordinates q N hN hcop hqN S j hmax (Subgroup.zpowers P) hC
  intro p hp
  have hp' : (p.val : k) ≠ 0 := by
    intro hz
    have hd := (CharP.cast_eq_zero_iff k q p.val).mp hz
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out p.property).mp hd).symm
  let bE := S.basis.map j.symm.toAddEquiv.toIntLinearEquiv
  obtain ⟨hFree, hFinite, hRank⟩ := hT k A p.val hp'
  have hRank' : ((Module.finrank ℤ_[p.val] (A.T p.val) : ℕ∞) : WithBot ℕ∞) = 2 := by
    simpa only [hdim, mul_one] using hRank
  let bT := Module.finBasisOfFinrankEq ℤ_[p.val] (A.T p.val)
    (WithTop.coe_inj.mp (WithBot.coe_inj.mp hRank'))
  exact splitProfile_of_cyclicReference p hp' N hN.ne' P hP _
    (S.ring.subtype.comp j.toRingHom) rfl bE bT

end Level

end ZInQ.Manuscript.RC.HCMV21
