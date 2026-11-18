import ZInQKernel.Contrib.OneProof.RC.Odd.Detector

/-! Tex 8378–8391. Use the fixed subgroup of geometric points to represent
rational points. In the cardinality argument only this subgroup needs to be finite. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Stages

variable {X : Type*} [AddCommGroup X] (F : X →+ X) (n : ℕ)

/-- Fixed points of Frobenius squared. -/
abbrev FixedSq : AddSubgroup X := (F.comp F - AddMonoidHom.id X).ker

theorem mem_fixedSq {P : X} : P ∈ FixedSq F ↔ F (F P) = P := by
  change F (F P) - P = 0 ↔ _
  exact sub_eq_zero

/-- Frobenius on the subgroup of points rational over the quadratic residue field. -/
def fixedFrob : FixedSq F →+ FixedSq F :=
  (F.comp (FixedSq F).subtype).codRestrict (FixedSq F) (fun P =>
    (mem_fixedSq F).mpr (congrArg F ((mem_fixedSq F).mp P.property)))

/-- Frobenius on finite torsion. -/
def torsionFrob : AddSubgroup.torsionBy X (n : ℤ) →+ AddSubgroup.torsionBy X (n : ℤ) :=
  (F.comp (AddSubgroup.torsionBy X (n : ℤ)).subtype).codRestrict _ fun P =>
    AddSubgroup.torsionBy.nsmul_iff.mpr (by
      change n • F P.val = 0
      rw [← map_nsmul, (AddSubgroup.torsionBy.nsmul_iff.mp P.property), map_zero])

variable (hdiv : Function.Surjective (fun R : X => n • R))
  (htriv : ∀ t : X, n • t = 0 → F (F t) = t)

private def kappaValue (P : FixedSq F) : AddSubgroup.torsionBy X (n : ℤ) :=
  ⟨F (F ((hdiv P.val).choose)) - (hdiv P.val).choose, AddSubgroup.torsionBy.nsmul_iff.mpr
    (Odd.kummer_mem_torsion (F.comp F) n (mem_fixedSq F |>.mp P.property)
      (hdiv P.val).choose_spec)⟩

include htriv in
private theorem kappaValue_apply (P : FixedSq F) (R : X) (hR : n • R = P.val) :
    (kappaValue F n hdiv P).val = F (F R) - R :=
  Odd.kummer_indep (F.comp F) n htriv ((hdiv P.val).choose_spec.trans hR.symm)

/-- The finite-field Kummer homomorphism, with codomain exactly the n-torsion. -/
def kappa : FixedSq F →+ AddSubgroup.torsionBy X (n : ℤ) where
  toFun := kappaValue F n hdiv
  map_zero' := Subtype.ext (by
    rw [kappaValue_apply F n hdiv htriv 0 0 (by simp)]
    simp)
  map_add' P Q := Subtype.ext (by
    obtain ⟨R, hR⟩ := hdiv P.val
    obtain ⟨S, hS⟩ := hdiv Q.val
    change n • R = P.val at hR
    change n • S = Q.val at hS
    have hRS : n • (R + S) = (P + Q).val := by rw [smul_add, hR, hS]; rfl
    change (kappaValue F n hdiv (P + Q)).val =
      (kappaValue F n hdiv P).val + (kappaValue F n hdiv Q).val
    rw [kappaValue_apply F n hdiv htriv _ _ hRS, kappaValue_apply F n hdiv htriv _ _ hR,
      kappaValue_apply F n hdiv htriv _ _ hS]
    exact Odd.kummer_add (F.comp F) R S)

/-- The exact normalization: any division point computes the same value. -/
theorem kappa_apply (P : FixedSq F) {R : X} (hR : n • R = P.val) :
    (kappa F n hdiv htriv P).val = F (F R) - R :=
  kappaValue_apply F n hdiv htriv P R hR

/-- The kernel consists exactly of n times the points rational over the quadratic field. -/
theorem kappa_ker : (kappa F n hdiv htriv).ker =
    (nsmulAddMonoidHom (α := FixedSq F) n).range := by
  ext P
  obtain ⟨R, hR⟩ := hdiv P.val
  change n • R = P.val at hR
  change kappa F n hdiv htriv P = 0 ↔ ∃ V : FixedSq F, n • V = P
  have he : kappa F n hdiv htriv P = 0 ↔ (F.comp F) R - R = 0 := by
    constructor
    · intro hk
      change F (F R) - R = 0
      rw [← kappa_apply F n hdiv htriv P hR, hk]
      rfl
    · intro hk
      exact Subtype.ext ((kappa_apply F n hdiv htriv P hR).trans hk)
  rw [he, Odd.kummer_eq_zero_iff (F.comp F) n htriv hR]
  constructor
  · rintro ⟨T, ht, h⟩
    exact ⟨⟨T, (mem_fixedSq F).mpr ht⟩, Subtype.ext h⟩
  · rintro ⟨T, ht⟩
    exact ⟨T.val, (mem_fixedSq F).mp T.property, congrArg Subtype.val ht⟩

/-- The elementary surjectivity proof (provenance (c)): on the finite fixed subgroup,
the quotient by multiplication by n has order equal to the kernel of that multiplication.
All geometric n-torsion already belongs to the fixed subgroup. -/
theorem kappa_surjective [Finite (FixedSq F)] :
    Function.Surjective (kappa F n hdiv htriv) := by
  let m := nsmulAddMonoidHom (α := FixedSq F) n
  let k := kappa F n hdiv htriv
  let e : m.ker ≃ AddSubgroup.torsionBy X (n : ℤ) :=
    { toFun := fun P => ⟨P.val.val, AddSubgroup.torsionBy.nsmul_iff.mpr
        (congrArg Subtype.val P.property)⟩
      invFun := fun T => ⟨⟨T.val, (mem_fixedSq F).mpr
        (htriv _ (AddSubgroup.torsionBy.nsmul_iff.mp T.property))⟩,
        Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp T.property)⟩
      left_inv := fun P => rfl
      right_inv := fun T => rfl }
  let : Finite (AddSubgroup.torsionBy X (n : ℤ)) := Finite.of_equiv _ e
  apply AddMonoidHom.surjective_of_card_ker_le_div
  have hc := AddSubgroup.card_ker_mul_card_range m
  rw [show k.ker = m.range from kappa_ker F n hdiv htriv]
  rw [← Nat.card_congr e, ← hc, Nat.mul_comm, Nat.mul_div_cancel _ Nat.card_pos]

/-- Frobenius equivariance follows by taking F R as a division point of F P. -/
theorem kappa_equivariant (P : FixedSq F) :
    kappa F n hdiv htriv (fixedFrob F P) =
      torsionFrob F n (kappa F n hdiv htriv P) := by
  obtain ⟨R, hR⟩ := hdiv P.val
  change n • R = P.val at hR
  apply Subtype.ext
  change (kappa F n hdiv htriv (fixedFrob F P)).val =
    F (kappa F n hdiv htriv P).val
  have hFR : n • F R = (fixedFrob F P).val := by rw [← map_nsmul, hR]; rfl
  rw [kappa_apply F n hdiv htriv _ hFR, kappa_apply F n hdiv htriv _ hR, map_sub]

/-- Frobenius sign +1 for a row defined only on finite torsion. -/
theorem lambda_frobenius_plus {B : Type*} [AddCommGroup B]
    (b : AddSubgroup.torsionBy X (n : ℤ) →+ B)
    (hb : ∀ T, b (torsionFrob F n T) = b T) (P : FixedSq F) :
    (b.comp (kappa F n hdiv htriv)) (fixedFrob F P) =
      (b.comp (kappa F n hdiv htriv)) P := by
  simp only [AddMonoidHom.comp_apply, kappa_equivariant, hb]

#print axioms kappaValue_apply
#print axioms mem_fixedSq
#print axioms kappa
#print axioms kappa_apply
#print axioms kappa_ker
#print axioms kappa_surjective
#print axioms kappa_equivariant
#print axioms lambda_frobenius_plus

end ZInQ.Manuscript.RC.Stages
