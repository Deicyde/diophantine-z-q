import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimeProductTraceSplitting

/-!
# Bijective coprime torsion-label splitting

The map (A,T) ↦ pA+NT gives an actual bijection of the finite residue groups
at levels N and p with the group at pN. Its inverse is given by reduction
and the proved inverses of the coprime level scalars.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace

open TorsionCorrelation

/-- Reduction of both actual residue coordinates along a divisibility. -/
def reducePoint (n m : ℕ) (hnm : n ∣ m) (P : Point m) : Point n :=
  ((ZMod.castHom hnm (ZMod n)) P.1, (ZMod.castHom hnm (ZMod n)) P.2)

/-- The actual residue point of the coprime split label. -/
def splitPoint (p N : ℕ) (A : Point N) (T : Point p) : Point (p * N) :=
  label (p * N) ((p : ℤ) * A.1.val + (N : ℤ) * T.1.val)
    ((p : ℤ) * A.2.val + (N : ℤ) * T.2.val)

lemma reduce_split_N (p N : ℕ) [NeZero N] (A : Point N) (T : Point p) :
    reducePoint N (p * N) (dvd_mul_left N p) (splitPoint p N A T) = scale (p : ZMod N) A := by
  apply Prod.ext <;> simp only [reducePoint, splitPoint, label, scale, Prod.fst, Prod.snd,
    map_intCast, map_add, map_mul, map_natCast, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
    ZMod.natCast_self, zero_mul, mul_zero, add_zero, zero_add]

lemma reduce_split_p (p N : ℕ) [NeZero p] (A : Point N) (T : Point p) :
    reducePoint p (p * N) (dvd_mul_right p N) (splitPoint p N A T) = scale (N : ZMod p) T := by
  apply Prod.ext <;> simp only [reducePoint, splitPoint, label, scale, Prod.fst, Prod.snd,
    map_intCast, map_add, map_mul, map_natCast, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
    ZMod.natCast_self, zero_mul, mul_zero, add_zero, zero_add]

lemma scale_scale {K : Type*} [CommRing K] (a b : K) (P : Pair K) :
    scale a (scale b P) = scale (a * b) P := by apply Prod.ext <;> simp [scale, mul_assoc]

lemma scale_one {K : Type*} [CommRing K] (P : Pair K) : scale (1 : K) P = P := by
  apply Prod.ext <;> simp [scale]

/-- Both coprime reductions together are injective on actual torsion residues. -/
theorem point_eq_of_reductions (p N : ℕ) [NeZero p] [NeZero N] (hcop : Nat.Coprime p N)
    (P Q : Point (p * N))
    (hp : reducePoint p (p * N) (dvd_mul_right p N) P = reducePoint p (p * N) (dvd_mul_right p N) Q)
    (hN : reducePoint N (p * N) (dvd_mul_left N p) P = reducePoint N (p * N) (dvd_mul_left N p) Q) : P = Q := by
  let : NeZero (p * N) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne N)⟩
  let e := ZMod.chineseRemainder hcop
  apply Prod.ext
  · apply e.injective
    conv_lhs => rw [← ZMod.natCast_zmod_val P.1]
    conv_rhs => rw [← ZMod.natCast_zmod_val Q.1]
    rw [map_natCast, map_natCast]
    change ((P.1.val : ZMod p),(P.1.val : ZMod N)) = ((Q.1.val : ZMod p),(Q.1.val : ZMod N))
    have hpp : (P.1.val : ZMod p) = (Q.1.val : ZMod p) := by
      simpa only [reducePoint, ZMod.castHom_apply, ZMod.cast_eq_val] using congrArg Prod.fst hp
    have hNN : (P.1.val : ZMod N) = (Q.1.val : ZMod N) := by
      simpa only [reducePoint, ZMod.castHom_apply, ZMod.cast_eq_val] using congrArg Prod.fst hN
    exact Prod.ext hpp hNN
  · apply e.injective
    conv_lhs => rw [← ZMod.natCast_zmod_val P.2]
    conv_rhs => rw [← ZMod.natCast_zmod_val Q.2]
    rw [map_natCast, map_natCast]
    change ((P.2.val : ZMod p),(P.2.val : ZMod N)) = ((Q.2.val : ZMod p),(Q.2.val : ZMod N))
    have hpp : (P.2.val : ZMod p) = (Q.2.val : ZMod p) := by
      simpa only [reducePoint, ZMod.castHom_apply, ZMod.cast_eq_val] using congrArg Prod.snd hp
    have hNN : (P.2.val : ZMod N) = (Q.2.val : ZMod N) := by
      simpa only [reducePoint, ZMod.castHom_apply, ZMod.cast_eq_val] using congrArg Prod.snd hN
    exact Prod.ext hpp hNN

/-- The genuine finite CRT splitting, not an assumed decomposition of an orbit. -/
def splitPointEquiv (p N : ℕ) [NeZero p] [NeZero N] (hcop : Nat.Coprime p N) :
    Point N × Point p ≃ Point (p * N) where
  toFun AT := splitPoint p N AT.1 AT.2
  invFun P :=
    (scale ((p : ZMod N)⁻¹) (reducePoint N (p * N) (dvd_mul_left N p) P),
     scale ((N : ZMod p)⁻¹) (reducePoint p (p * N) (dvd_mul_right p N) P))
  left_inv AT := by
    dsimp only
    rw [reduce_split_N, reduce_split_p, scale_scale, scale_scale,
      show (p : ZMod N)⁻¹ * p = 1 from by
        rw [mul_comm]; exact ZMod.coe_mul_inv_eq_one p hcop,
      show (N : ZMod p)⁻¹ * N = 1 from by
        rw [mul_comm]; exact ZMod.coe_mul_inv_eq_one N hcop.symm,
      scale_one, scale_one]
  right_inv P := by
    apply point_eq_of_reductions p N hcop
    · rw [reduce_split_p, scale_scale, ZMod.coe_mul_inv_eq_one N hcop.symm, scale_one]
    · rw [reduce_split_N, scale_scale, ZMod.coe_mul_inv_eq_one p hcop, scale_one]

end ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace
