import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinQuotientConstants

/-!
# Actual finite translation fibres in the complete principal quotient

The positive-axis stabilizer in SL₂(ℤ/Nℤ) is exactly the N unipotent matrices;
the negative-axis fibre is exactly their negatives. Explicit equivalences
produce these fibres, and for N≥3 their union is enumerated by Bool × ZMod N.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Complex Filter Set UpperHalfPlane Matrix Matrix.SpecialLinearGroup
open scoped Topology MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinInterpolation
open ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinConstants

/-- Actual finite unipotent matrix with parameter t. -/
def unipotent (N : ℕ) (t : ZMod N) : SL(2, ZMod N) := ⟨!![1,t;0,1],by simp⟩

lemma positive_row_action (N : ℕ) (A : SL(2, ZMod N)) :
    positiveRow N ᵥ* A = (fun i => A 1 i) := by
  ext i
  simp [positiveRow,Matrix.vecMul,Fin.sum_univ_two]
  rfl

lemma unipotent_positive (N : ℕ) (t : ZMod N) : positiveRow N ᵥ* unipotent N t = positiveRow N := by
  rw [positive_row_action]
  funext i
  fin_cases i <;> simp [unipotent,positiveRow]

lemma unipotent_negative (N : ℕ) (t : ZMod N) : positiveRow N ᵥ* (-unipotent N t) = negativeRow N := by
  rw [positive_row_action]
  funext i
  fin_cases i <;> simp [unipotent,negativeRow]

lemma positive_fibre_classification (N : ℕ) (A : SL(2, ZMod N))
    (h : positiveRow N ᵥ* A = positiveRow N) : A = unipotent N (A 0 1) := by
  rw [positive_row_action] at h
  have h0 : A 1 0 = 0 := congrFun h 0
  have h1 : A 1 1 = 1 := congrFun h 1
  have ha : A 0 0 = 1 := by simpa only [Matrix.det_fin_two,h0,h1,mul_zero,mul_one,sub_zero] using A.det_coe
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotent,ha,h0,h1]

lemma negative_fibre_classification (N : ℕ) (A : SL(2, ZMod N))
    (h : positiveRow N ᵥ* A = negativeRow N) : A = -unipotent N (-A 0 1) := by
  rw [positive_row_action] at h
  have h0 : A 1 0 = 0 := congrFun h 0
  have h1 : A 1 1 = -1 := congrFun h 1
  have hd := A.det_coe
  simp only [Matrix.det_fin_two,h0,h1,mul_zero,mul_neg_one,sub_zero] at hd
  have ha : A 0 0 = -1 := neg_eq_iff_eq_neg.mp hd
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotent,ha,h0,h1]

/-- A proved finite equivalence with the entire positive-axis fibre. -/
def positiveFibreEquiv (N : ℕ) : ZMod N ≃ {A : SL(2, ZMod N) // positiveRow N ᵥ* A = positiveRow N} where
  toFun t := ⟨unipotent N t,unipotent_positive N t⟩
  invFun A := A.1 0 1
  left_inv t := by simp [unipotent]
  right_inv A := Subtype.ext (positive_fibre_classification N A.1 A.2).symm

/-- A proved finite equivalence with the entire negative-axis fibre. -/
def negativeFibreEquiv (N : ℕ) : ZMod N ≃ {A : SL(2, ZMod N) // positiveRow N ᵥ* A = negativeRow N} where
  toFun t := ⟨-unipotent N t,unipotent_negative N t⟩
  invFun A := -A.1 0 1
  left_inv t := by simp [unipotent]
  right_inv A := Subtype.ext (negative_fibre_classification N A.1 A.2).symm

lemma residue_signs_ne (N : ℕ) (hN : 3 ≤ N) : (1 : ZMod N) ≠ -1 := by
  intro he
  have ht : (1 : ZMod N)+(1 : ZMod N) = 0 :=
    (congrArg (fun x : ZMod N => x+1) he).trans (neg_add_cancel 1)
  have h2 : (2 : ZMod N) = 0 := by convert ht using 1 <;> ring
  have hd : N ∣ 2 := (ZMod.natCast_eq_zero_iff 2 N).mp h2
  have hn := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

/-- The full ±axis fibre, not an assumed orbit. -/
abbrev axisFibre (N : ℕ) := {A : SL(2, ZMod N) //
  positiveRow N ᵥ* A = positiveRow N ∨ positiveRow N ᵥ* A = negativeRow N}

def axisElement (N : ℕ) (p : Bool × ZMod N) : axisFibre N :=
  if p.1 then ⟨-unipotent N p.2,Or.inr (unipotent_negative N p.2)⟩
  else ⟨unipotent N p.2,Or.inl (unipotent_positive N p.2)⟩

lemma axisElement_bijective (N : ℕ) (hN : 3 ≤ N) : Function.Bijective (axisElement N) := by
  constructor
  · rintro ⟨b,s⟩ ⟨c,t⟩ he
    cases b <;> cases c
    · have h := congrArg (fun A : axisFibre N => A.1 0 1) he
      have hs : s = t := by simpa [axisElement,unipotent] using h
      exact congrArg (fun u : ZMod N => (false,u)) hs
    · have h := congrArg (fun A : axisFibre N => A.1 1 1) he
      exact (residue_signs_ne N hN (by simpa [axisElement,unipotent] using h)).elim
    · have h := congrArg (fun A : axisFibre N => A.1 1 1) he
      exact (residue_signs_ne N hN (by simpa [axisElement,unipotent] using h.symm)).elim
    · have h := congrArg (fun A : axisFibre N => A.1 0 1) he
      have hs : s = t := neg_inj.mp (by simpa [axisElement,unipotent] using h)
      exact congrArg (fun u : ZMod N => (true,u)) hs
  · intro A
    rcases A.2 with hp | hn
    · refine ⟨(false,A.1 0 1),?_⟩
      apply Subtype.ext
      exact (positive_fibre_classification N A.1 hp).symm
    · refine ⟨(true,-A.1 0 1),?_⟩
      apply Subtype.ext
      exact (negative_fibre_classification N A.1 hn).symm

/-- An explicit complete ±T enumeration, giving the exact 2N multiplicity. -/
def axisFibreEquiv (N : ℕ) (hN : 3 ≤ N) : (Bool × ZMod N) ≃ axisFibre N :=
  Equiv.ofBijective (axisElement N) (axisElement_bijective N hN)

lemma axisFibre_card (N : ℕ) [NeZero N] (hN : 3 ≤ N) : Fintype.card (axisFibre N) = 2*N := by
  rw [← Fintype.card_congr (axisFibreEquiv N hN),Fintype.card_prod,Fintype.card_bool,ZMod.card]

lemma unipotent_inv (N : ℕ) (t : ZMod N) : (unipotent N t)⁻¹ = unipotent N (-t) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotent,Matrix.adjugate_fin_two]

/-- The finite unipotent is the actual reduction of an integral translation. -/
lemma reduce_T (N : ℕ) [NeZero N] (t : ZMod N) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) (ModularGroup.T^(t.val : ℤ)) = unipotent N t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,ModularGroup.coe_T_zpow,
      unipotent,Int.cast_natCast,ZMod.natCast_zmod_val,-map_zpow]

/-- The actual quotient constants, not given orbit coefficients, obey translation invariance. -/
lemma finiteConstants_unipotent (N : ℕ) [NeZero N] (k : ℤ) (f : ModularForm (principalReal N) k)
    (A : SL(2, ZMod N)) (t : ZMod N) : finiteConstants N k f (A*unipotent N t) = finiteConstants N k f A := by
  obtain ⟨γ,rfl⟩ := Matrix.SpecialLinearGroup.map_intCast_zmod_surjective (d := N) A
  rw [← reduce_T N t,← map_mul,finiteConstants_reduce,constantAt_T,finiteConstants_reduce]

lemma reduce_neg (N : ℕ) (γ : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) (-γ) =
      -(Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ) := by
  apply Subtype.ext
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply]

lemma finiteConstants_neg (N : ℕ) [NeZero N] (k : ℕ) (f : ModularForm (principalReal N) (k : ℤ))
    (A : SL(2, ZMod N)) : finiteConstants N (k : ℤ) f (-A) = (-1 : ℂ)^k * finiteConstants N (k : ℤ) f A := by
  obtain ⟨γ,rfl⟩ := Matrix.SpecialLinearGroup.map_intCast_zmod_surjective (d := N) A
  rw [← reduce_neg,finiteConstants_reduce,constantAt_neg,finiteConstants_reduce]

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinInterpolation
