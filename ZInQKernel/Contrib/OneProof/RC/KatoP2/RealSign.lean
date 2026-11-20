import ZInQKernel.Contrib.OneProof.RC.KatoP2.Abelian
import ZInQKernel.Contrib.CloudB3RC53.DetTateCyclotomic.Basic
import ZInQKernel.Contrib.CloudB3RC53.OpenImage.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! The real eigenspaces of the genuine dyadic Tate twist (tex 7222). -/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2

open PrintsArith ZInQ.Contrib.CloudB3RC53
open scoped TensorProduct

private theorem realConj_sq : OpenImage.complexConj * OpenImage.complexConj = 1 := by
  ext x
  apply OpenImage.iota.injective
  change OpenImage.iota (OpenImage.complexConj (OpenImage.complexConj x)) = OpenImage.iota x
  rw [OpenImage.iota_complexConj, OpenImage.iota_complexConj, starRingEnd_apply, starRingEnd_apply,
    star_star]

/-- Determinant one would fix every dyadic root of unity by the Weil
pairing. Complex conjugation moves a square root of minus one. -/
private theorem realConj_tate_det (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    LinearMap.det (tateRep E 2 OpenImage.complexConj) = -1 := by
  have hsq :
      LinearMap.det (tateRep E 2 OpenImage.complexConj) *
        LinearMap.det (tateRep E 2 OpenImage.complexConj) = 1 := by
    rw [← map_mul, ← map_mul, realConj_sq, map_one, map_one]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · obtain ⟨s, hs⟩ := OpenImage.exists_sqrt (-1 : ℚ)
    have hs4 : s ^ (2 ^ (2 : ℕ)) = 1 := by
      change s ^ (2 * 2) = 1
      rw [pow_mul, hs, map_neg, map_one, neg_sq, one_pow]
    have hfix := DetTateCyclotomic.detTateTwoCyclotomic E OpenImage.complexConj h 2 s hs4
    exact (OpenImage.complexConj_not_mem (by norm_num) hs
      (by rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def])).elim
  · exact h

/-- A rank-two involution of determinant minus one has one negative eigenline. -/
private theorem finrank_ker_add_one_of_involution {V : Type} [AddCommGroup V]
    [Module ℚ_[2] V] [FiniteDimensional ℚ_[2] V] (A : Module.End ℚ_[2] V)
    (hdim : Module.finrank ℚ_[2] V = 2) (hsq : A * A = 1)
    (hdet : LinearMap.det A = -1) :
    Module.finrank ℚ_[2] (LinearMap.ker (A + 1)) = 1 := by
  have hfix : A * (A + 1) = A + 1 := by rw [mul_add, hsq, mul_one, add_comm]
  have hd := congrArg (LinearMap.det : Module.End ℚ_[2] V →* ℚ_[2]) hfix
  rw [map_mul, hdet, neg_one_mul] at hd
  have hbot : LinearMap.ker (A + 1) ≠ ⊥ :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mp (CharZero.neg_eq_self_iff.mp hd)
  have htop : LinearMap.ker (A + 1) ≠ ⊤ := by
    intro h
    have hA : A = -1 := eq_neg_of_add_eq_zero_left (LinearMap.ker_eq_top.mp h)
    rw [hA, ← neg_one_smul ℚ_[2] (1 : Module.End ℚ_[2] V),
      LinearMap.det_smul, hdim, map_one] at hdet
    norm_num at hdet
  have hpos : 0 < Module.finrank ℚ_[2] (LinearMap.ker (A + 1)) :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hbot)
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr htop)
  rw [finrank_top, hdim] at hlt
  omega

/-- Actual complex conjugation on the rational Tate twist of any elliptic
curve over ℚ has one line of each sign. The twist may interchange the lines. -/
theorem rationalTwist_realSigns (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (χ : GalQ →* ℤˣ) :
    Module.finrank ℚ_[2]
        (LinearMap.ker (rationalTwist E χ OpenImage.complexConj + 1)) = 1 ∧
      Module.finrank ℚ_[2]
        (LinearMap.ker (rationalTwist E χ OpenImage.complexConj - 1)) = 1 := by
  let V := ℚ_[2] ⊗[ℤ_[2]] TateMod E 2
  let A : Module.End ℚ_[2] V := rationalTwist E χ OpenImage.complexConj
  have hdim : Module.finrank ℚ_[2] V = 2 := by
    rw [Module.finrank_baseChange, tateMod_two_finrank]
  have hsq : A * A = 1 := by
    change rationalTwist E χ OpenImage.complexConj * rationalTwist E χ OpenImage.complexConj = 1
    rw [← map_mul, realConj_sq, map_one]
  have hdet : LinearMap.det A = -1 := by
    change LinearMap.det
      ((((χ OpenImage.complexConj : ℤˣ) : ℤ) : ℚ_[2]) •
        (tateRep E 2 OpenImage.complexConj).baseChange ℚ_[2]) = -1
    rw [LinearMap.det_smul, hdim, LinearMap.det_baseChange, realConj_tate_det]
    rcases Int.units_eq_one_or (χ OpenImage.complexConj) with h | h <;> simp [h]
  have hnegdet : LinearMap.det (-A) = -1 := by
    rw [← neg_one_smul ℚ_[2] A, LinearMap.det_smul, hdim, hdet]
    norm_num
  have hk : LinearMap.ker (-A + 1) = LinearMap.ker (A - 1) := by
    rw [show -A + 1 = -(A - 1) by abel]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.neg_apply, neg_eq_zero]
  have hnegsq : (-A) * (-A) = 1 := by
    apply LinearMap.ext
    intro x
    change -(A (-(A x))) = x
    rw [map_neg, neg_neg]
    exact DFunLike.congr_fun hsq x
  exact ⟨finrank_ker_add_one_of_involution A hdim hsq hdet,
    hk ▸ finrank_ker_add_one_of_involution (-A) hdim hnegsq hnegdet⟩

end ZInQ.Manuscript.RC.KatoP2
