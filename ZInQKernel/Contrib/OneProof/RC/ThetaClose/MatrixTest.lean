import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Coordinates
import ZInQKernel.Contrib.OneProof.RC.LineIndex.LocalPrincipal
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! The integer test uses the same basis and the same mod-p² divisibility
as the endomorphism condition on the completed neighbour lattice. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaClose

open Adelic Eichler LineIndex ThetaJoin
open Matrix

variable {p : ℕ} [Fact p.Prime]

/-- The integer basis whose completion is the line preimage basis. -/
def integerBasis (p : ℕ) : Option (ZMod p) → Mat ℤ
  | none => !![(p : ℤ), 0; 0, 1]
  | some t => !![1, 0; (t.val : ℤ), (p : ℤ)]

private theorem integerBasis_det (L : Option (ZMod p)) : (integerBasis p L).det = p := by
  cases L <;> simp [integerBasis, Matrix.det_fin_two_of]

private theorem integerBasis_cast (L : Option (ZMod p)) :
    (Int.castRingHom ℤ_[p]).mapMatrix (integerBasis p L) = basisMatrix p L := by
  cases L <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [integerBasis, basisMatrix]

private theorem integerBasis_image (L : Option (ZMod p)) (v : ℤ × ℤ) :
    AppF.InL p L v ↔ ∃ w : Vec ℤ, (integerBasis p L).mulVec w = ![v.1, v.2] := by
  have h (w : Vec ℤ) :
      (integerBasis p L).mulVec w =
        (match L with
        | none => ![(p : ℤ) * w 0, w 1]
        | some t => ![w 0, (t.val : ℤ) * w 0 + (p : ℤ) * w 1]) := by
    cases L <;> funext i <;> fin_cases i <;>
      simp [integerBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  cases L with
  | none =>
    simp only [AppF.InL, h]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨![k, v.2], by simp [hk]⟩
    · rintro ⟨w, hw⟩
      exact ⟨w 0, (congrFun hw 0).symm⟩
  | some t =>
    have htest : AppF.InL p (some t) v ↔ (p : ℤ) ∣ v.2 - (t.val : ℤ) * v.1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp [AppF.InL, sub_eq_zero]
    rw [htest]
    simp only [h]
    constructor
    · rintro ⟨k, hk⟩
      have he : (t.val : ℤ) * v.1 + (p : ℤ) * k = v.2 := by omega
      refine ⟨![v.1, k], ?_⟩
      funext i
      fin_cases i
      · rfl
      · exact he
    · rintro ⟨w, hw⟩
      have h₀ : w 0 = v.1 := congrFun hw 0
      have h₁ : (t.val : ℤ) * w 0 + (p : ℤ) * w 1 = v.2 := congrFun hw 1
      exact ⟨w 1, by rw [← h₀, ← h₁, add_sub_cancel_left]⟩

private def ternaryMatrix (a b c : ℤ) : Mat ℤ := !![a, b; c, -a]

private theorem integer_test (a b c : ℤ) (L : Option (ZMod p)) :
    AppF.MemNbr p 1 a b c L ↔
      ∃ T : Mat ℤ, ternaryMatrix a b c * integerBasis p L =
        (p : ℤ) • (integerBasis p L * T) := by
  let Y := ternaryMatrix a b c
  let B := integerBasis p L
  have hact (v : ℤ × ℤ) : Y.mulVec ![v.1, v.2] =
      ![(AppF.act a b c v).1, (AppF.act a b c v).2] := by
    funext i
    fin_cases i <;> simp [Y, ternaryMatrix, AppF.act, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, sub_eq_add_neg]
  constructor
  · intro hh
    have hj (j : Fin 2) : ∃ t : Vec ℤ, (Y * B).mulVec (Pi.single j 1) =
        (p : ℤ) • B.mulVec t := by
      let e : Vec ℤ := Pi.single j 1
      let v : ℤ × ℤ := (B.mulVec e 0, B.mulVec e 1)
      have hv : B.mulVec e = ![v.1, v.2] := by
        funext i
        fin_cases i <;> rfl
      obtain ⟨w, hw, hwL⟩ := hh v ((integerBasis_image L v).mpr ⟨e, hv⟩)
      obtain ⟨t, ht⟩ := (integerBasis_image L w).mp hwL
      use t
      change (Y * B).mulVec e = _
      rw [← Matrix.mulVec_mulVec, hv, hact v, ht, hw, pow_one]
      funext i
      fin_cases i <;> rfl
    choose t ht using hj
    let T : Mat ℤ := fun i j => t j i
    refine ⟨T, Matrix.ext_of_mulVec_single fun j => ?_⟩
    rw [ht j, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    congr 2
    funext i
    rw [Matrix.mulVec_single_one]
    rfl
  · rintro ⟨T, hT⟩ v hv
    obtain ⟨e, he⟩ := (integerBasis_image L v).mp hv
    let w : ℤ × ℤ := (B.mulVec (T.mulVec e) 0, B.mulVec (T.mulVec e) 1)
    have hw : B.mulVec (T.mulVec e) = ![w.1, w.2] := by
      funext i
      fin_cases i <;> rfl
    refine ⟨w, ?_, (integerBasis_image L w).mpr ⟨_, hw⟩⟩
    have H : ![(AppF.act a b c v).1, (AppF.act a b c v).2] =
        (p : ℤ) • ![w.1, w.2] := by
      rw [← hact v, ← he, Matrix.mulVec_mulVec, hT,
        Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hw]
    exact Prod.ext (by simpa using congrFun H 0) (by simpa using congrFun H 1)

private theorem basis_test {S : Type*} [CommRing S] [IsDomain S] {r : S}
    (hr : r ≠ 0) (B Y : Mat S) (hdet : B.det = r) :
    (∃ T : Mat S, Y * B = r • (B * T)) ↔ ∀ i j, r ^ 2 ∣ (B.adjugate * Y * B) i j := by
  constructor
  · rintro ⟨T, hT⟩
    have he : B.adjugate * Y * B = r ^ 2 • T := by
      rw [Matrix.mul_assoc, hT, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.adjugate_mul,
        hdet, Matrix.smul_mul, Matrix.one_mul, smul_smul, pow_two]
    rw [he]
    exact fun i j => dvd_mul_right _ _
  · intro h
    choose T hT using h
    let V : Mat S := T
    have he : B.adjugate * Y * B = r ^ 2 • V := Matrix.ext hT
    have hh := congrArg (B * ·) he
    rw [← Matrix.mul_assoc B, ← Matrix.mul_assoc B, Matrix.mul_adjugate, hdet,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      pow_two, ← smul_smul] at hh
    exact ⟨V, smul_right_injective _ hr hh⟩

/-- Congruence modulo the square of the prime transfers the integer
endomorphism test to the basis over p-adic integers. -/
theorem memNbr_iff_padic_basis (Y : Mat ℤ_[p]) (L : Option (ZMod p)) (a b c : ℤ)
    (hY : (PadicInt.toZModPow 2).mapMatrix Y =
      (Int.castRingHom (ZMod (p ^ 2))).mapMatrix (ternaryMatrix a b c)) :
    AppF.MemNbr p 1 a b c L ↔
      ∃ T : Mat ℤ_[p], Y * basisMatrix p L = (p : ℤ_[p]) • (basisMatrix p L * T) := by
  have hℤ : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hℤp : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [integer_test, basis_test hℤ _ _ (integerBasis_det L),
    basis_test hℤp _ _ (basisMatrix_det L)]
  let f : ℤ_[p] →+* ZMod (p ^ 2) := PadicInt.toZModPow 2
  let g : ℤ →+* ZMod (p ^ 2) := Int.castRingHom _
  have hB : f.mapMatrix (basisMatrix p L) = g.mapMatrix (integerBasis p L) := by
    rw [← integerBasis_cast]
    ext i j
    exact map_intCast f _
  have hA : f.mapMatrix ((basisMatrix p L).adjugate * Y * basisMatrix p L) =
      g.mapMatrix ((integerBasis p L).adjugate * ternaryMatrix a b c * integerBasis p L) := by
    simp only [map_mul]
    rw [RingHom.map_adjugate, RingHom.map_adjugate]
    change (f.mapMatrix (basisMatrix p L)).adjugate * f.mapMatrix Y * f.mapMatrix (basisMatrix p L) =
      (g.mapMatrix (integerBasis p L)).adjugate * g.mapMatrix (ternaryMatrix a b c) * g.mapMatrix (integerBasis p L)
    rw [hB, hY]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [← Int.natCast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    ← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  exact Iff.symm (congrArg (· = 0) (congrFun (congrFun hA i) j)).to_iff

/-- The frame entries are precisely the integer representatives required by
the p-adic basis condition. -/
theorem coord_memNbr_iff {a b : ℚ} {R : Order a b} {q : Prime} {z : FiniteUnits R}
    (D : FrameCoordinates q z) (y : Ternary z) (L : Option (ZMod q.val)) :
    AppF.MemNbr q.val 1 (D.coord y).1 (D.coord y).2.1 (D.coord y).2.2 L ↔
      ∃ T : Mat ℤ_[q.val], D.matrix y * basisMatrix q.val L =
        (q.val : ℤ_[q.val]) • (basisMatrix q.val L * T) := by
  apply memNbr_iff_padic_basis
  have hrep (v : ℤ_[q.val]) :
      ((((PadicInt.toZModPow 2 v).val : ℕ) : ℤ) : ZMod (q.val ^ 2)) =
        PadicInt.toZModPow 2 v := by
    have : NeZero (q.val ^ 2) := ⟨pow_ne_zero _ q.prop.ne_zero⟩
    simp
  have htr := D.trace y
  rw [Matrix.trace_fin_two] at htr
  have he := eq_neg_of_add_eq_zero_right htr
  ext i j
  fin_cases i <;> fin_cases j
  · exact (hrep (D.matrix y 0 0)).symm
  · exact (hrep (D.matrix y 0 1)).symm
  · exact (hrep (D.matrix y 1 0)).symm
  · change PadicInt.toZModPow 2 (D.matrix y 1 1) =
      ((-((D.coord y).1) : ℤ) : ZMod (q.val ^ 2))
    rw [he, map_neg, Int.cast_neg]
    exact congrArg Neg.neg (hrep (D.matrix y 0 0)).symm

end ZInQ.Manuscript.RC.ThetaClose
