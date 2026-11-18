import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimeProductTraceCRT

/-!
# Actual completed torsion Fourier duality in coprime split coordinates

All values are the unchanged zero-extended theta logarithmic derivatives,
multiplied by κ=-2πi. The finite Fourier coefficient is exactly -1/(pN), and
the split pairings are derived from the actual exponential identity.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane
open scoped BigOperators

namespace ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace

open TorsionCorrelation

/-- The actual completed value on a residue point. -/
def lambdaPointValue (N : ℕ) (τ : ℍ) (P : Point N) : ℂ :=
  TorsionWeierstrassData.scale * TorsionCorrelation.h N τ P

/-- The actual value at a coprime direct-sum label. -/
def splitLambda (p N : ℕ) (τ : ℍ) (A : Point N) (T : Point p) : ℂ :=
  lambdaPointValue (p * N) τ (splitPoint p N A T)

lemma pairing_labels (N : ℕ) [NeZero N] (a b r s : ℤ) :
    pairing N (label N a b) (label N r s) = TorsionFourierComparison.character N a b r s := by
  unfold pairing det label TorsionFourierComparison.character
  have h := phase_eq_exp N (b * r - a * s)
  push_cast at h
  convert h using 1 <;> congr 1 <;> ring

lemma pairing_canonical (N : ℕ) [NeZero N] (P R : Point N) :
    pairing N P R = TorsionFourierComparison.character N (P.1.val : ℤ) (P.2.val : ℤ)
      (R.1.val : ℤ) (R.2.val : ℤ) := by
  have hN : 0 < N := NeZero.pos N
  have h := pairing_labels N (P.1.val : ℤ) (P.2.val : ℤ) (R.1.val : ℤ) (R.2.val : ℤ)
  rw [label_val hN P, label_val hN R] at h
  exact h

/-- The actual h-duality reindexed on both finite residue coordinates. -/
theorem h_point_fourier (N : ℕ) [NeZero N] (τ : ℍ) (R : Point N) :
    h N τ R = -(1 / (N : ℂ)) * ∑ P : Point N, h N τ P * pairing N P R := by
  have hN : 0 < N := NeZero.pos N
  have he : (∑ P : Point N, h N τ P * pairing N P R) =
      ∑ a : Fin N, ∑ b : Fin N, TorsionDistributionTwo.reg N (a : ℕ) (b : ℕ) τ *
        TorsionFourierComparison.character N (a : ℕ) (b : ℕ) (R.1.val : ℤ) (R.2.val : ℤ) := by
    rw [← (Equiv.prodCongr (ZMod.finEquiv N).toEquiv (ZMod.finEquiv N).toEquiv).sum_comp]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    change h N τ (ZMod.finEquiv N a,ZMod.finEquiv N b) *
      pairing N (ZMod.finEquiv N a,ZMod.finEquiv N b) R = _
    rw [pairing_canonical]
    simp only [h, finite_residue_val]
  rw [he]
  exact TorsionFourierComparison.torsion_fourier_duality N τ (R.1.val : ℤ) (R.2.val : ℤ)

/-- The completed value has the same genuine Fourier factor -1/N. -/
theorem lambda_point_fourier (N : ℕ) [NeZero N] (τ : ℍ) (R : Point N) :
    lambdaPointValue N τ R = -(1 / (N : ℂ)) *
      ∑ P : Point N, lambdaPointValue N τ P * pairing N P R := by
  unfold lambdaPointValue
  rw [h_point_fourier N τ R]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

/-- The actual product of pairings in split coordinates. -/
theorem pairing_split (p N : ℕ) [NeZero p] [NeZero N] [NeZero (p * N)]
    (C B : Point N) (V U : Point p) :
    pairing (p * N) (splitPoint p N C V) (splitPoint p N B U) =
      pairing N (scale (p : ZMod N) C) B * pairing p (scale (N : ZMod p) V) U := by
  rw [splitPoint, splitPoint, pairing_labels]
  have h := character_split p N ((C.1.val : ℤ),(C.2.val : ℤ)) ((V.1.val : ℤ),(V.2.val : ℤ))
    ((B.1.val : ℤ),(B.2.val : ℤ)) ((U.1.val : ℤ),(U.2.val : ℤ))
  have hC : label N ((p : ℤ) * C.1.val) ((p : ℤ) * C.2.val) = scale (p : ZMod N) C := by
    apply Prod.ext <;> simp only [label, scale, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_zmod_val, Prod.fst, Prod.snd]
  have hV : label p ((N : ℤ) * V.1.val) ((N : ℤ) * V.2.val) = scale (N : ZMod p) V := by
    apply Prod.ext <;> simp only [label, scale, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_zmod_val, Prod.fst, Prod.snd]
  have hL := pairing_labels N ((p : ℤ) * C.1.val) ((p : ℤ) * C.2.val) (B.1.val : ℤ) (B.2.val : ℤ)
  have hR := pairing_labels p ((N : ℤ) * V.1.val) ((N : ℤ) * V.2.val) (U.1.val : ℤ) (U.2.val : ℤ)
  rw [hC, label_val (NeZero.pos N) B] at hL
  rw [hV, label_val (NeZero.pos p) U] at hR
  rw [hL, hR]
  exact h

/-- The actual split-coordinate Fourier identity, including every zero class. -/
theorem split_lambda_fourier (p N : ℕ) [NeZero p] [NeZero N]
    (hcop : Nat.Coprime p N) (τ : ℍ) (B : Point N) (U : Point p) :
    splitLambda p N τ B U = -(1 / ((p * N : ℕ) : ℂ)) *
      ∑ C : Point N, ∑ V : Point p, splitLambda p N τ C V *
        pairing N (scale (p : ZMod N) C) B * pairing p (scale (N : ZMod p) V) U := by
  let : NeZero (p * N) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne N)⟩
  rw [splitLambda, lambda_point_fourier (p * N) τ]
  rw [← (splitPointEquiv p N hcop).sum_comp]
  simp only [splitPointEquiv, Equiv.coe_fn_mk, pairing_split]
  rw [Fintype.sum_prod_type]
  apply congrArg (fun z : ℂ => -(1 / ((p * N : ℕ) : ℂ)) * z)
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro V _
  dsimp only [splitLambda]
  ring

end ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace
