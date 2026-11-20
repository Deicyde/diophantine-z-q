import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Frame
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.ReducedNorm
import ZInQKernel.Contrib.OneProof.RC.LineIndex.Reduction

/-! Good-prime coordinates on the actual trace-zero left-order lattice. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic Eichler LocalWeights
open scoped Quaternion

variable {a b : ℚ} {R : Order a b}

theorem atRep_re (z : FiniteUnits R) (q : Prime) (x : B a b) :
    (atRep z q x).re = (x.re : ℚ_[q.val]) := by
  have hc (x y : Bp q.val a b) : (x * y).re = (y * x).re := by
    simp only [QuaternionAlgebra.re_mul]
    ring
  unfold atRep
  rw [hc, ← mul_assoc, Units.mul_inv, one_mul]
  rfl

theorem atRep_rat_smul (z : FiniteUnits R) (q : Prime) (c : ℚ) (x : B a b) :
    atRep z q (c • x) = (c : ℚ_[q.val]) • atRep z q x := by
  have ht : toLocal q.val (c • x) = (c : ℚ_[q.val]) • toLocal q.val x := by
    apply QuaternionAlgebra.ext <;> simp [toLocal, smul_eq_mul]
  unfold atRep
  rw [ht, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

namespace GoodCoordinates

variable (p : Prime) (z : FiniteUnits R) (U : LineIndex.Split R p.val)

def matrix (x : Ternary z) : M2 ℤ_[p.val] :=
  have h : atRep z p x.val ∈ Set.range U.embed :=
    U.range_embed.symm ▸ (mem_leftRing_iff z x.val).mp x.prop.1 p
  h.choose

theorem embed_matrix (x : Ternary z) : U.embed (matrix p z U x) = atRep z p x.val :=
  (show atRep z p x.val ∈ Set.range U.embed from
    U.range_embed.symm ▸ (mem_leftRing_iff z x.val).mp x.prop.1 p).choose_spec

theorem cast_matrix (x : Ternary z) :
    integralMat p.val (matrix p z U x) = U.alg (atRep z p x.val) := by
  have hh := congrArg U.alg (embed_matrix p z U x)
  change U.alg (U.alg.symm (integralMat p.val (matrix p z U x))) = _ at hh
  rwa [AlgEquiv.apply_symm_apply] at hh

/-- Dividing by `p` preserves the rational lattice once the matrix is
entrywise divisible by `p` in its good completion. -/
theorem divisible (y : Ternary z) (hy : ∀ i j, (p.val : ℤ_[p.val]) ∣ matrix p z U y i j) :
    ∃ x : Ternary z, scaleVector z p.val x = y := by
  let x : B a b := (p.val : ℚ)⁻¹ • y.val
  have hn : (p.val : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
  have hx : p.val • x = y.val := by
    rw [← Nat.cast_smul_eq_nsmul ℚ, show x = (p.val : ℚ)⁻¹ • y.val from rfl,
      smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hr : x.re = 0 := by
    rw [show x = (p.val : ℚ)⁻¹ • y.val from rfl, QuaternionAlgebra.re_smul, y.prop.2, smul_zero]
  refine ⟨⟨x, (mem_leftRing_iff z x).mpr ?_, hr⟩, Subtype.ext hx⟩
  intro q
  have hlocal : atRep z q y.val ∈ R.completion q.val :=
    (mem_leftRing_iff z y.val).mp y.prop.1 q
  by_cases hq : q = p
  · subst q
    choose T hT using hy
    let T' : LineIndex.Mat ℤ_[p.val] := T
    have he : matrix p z U y = (p.val : ℤ_[p.val]) • T' := Matrix.ext hT
    apply U.range_embed ▸ (show atRep z p x ∈ Set.range U.embed from ?_)
    refine ⟨T', ?_⟩
    have hl := embed_matrix p z U y
    rw [he, U.embed_smul, ← hx, atRep_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p.val]] at hl
    change (p.val : ℚ_[p.val]) • U.embed T' = (p.val : ℚ_[p.val]) • atRep z p x at hl
    exact smul_right_injective _ (Nat.cast_ne_zero.mpr p.prop.ne_zero :
      (p.val : ℚ_[p.val]) ≠ 0) hl
  · have hd : ¬ q.val ∣ p.val := fun h =>
      hq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.prop p.prop).mp h))
    let v := PhaseData.natUnit q p.val hd
    rw [← hx, atRep_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[q.val],
      ← PhaseData.natUnit_val q p.val hd] at hlocal
    change (v : ℤ_[q.val]) • atRep z q x ∈ (R.completion q.val).toSubmodule at hlocal
    have hh := (R.completion q.val).toSubmodule.smul_mem ((v⁻¹ : ℤ_[q.val]ˣ) : ℤ_[q.val]) hlocal
    exact (congrArg (fun y : Bp q.val a b => y ∈ (R.completion q.val).toSubmodule)
      (localUnit_smul_cancel q v (atRep z q x))).mp hh

/-- Construct the frame coordinates and saturation in the actual split chart;
the only extra datum is that reduced norms are natural integers on this lattice. -/
def coordinates (hInt : ∀ x : Ternary z, ∃ n : ℕ, Visibility.nrd x.val = (n : ℚ)) :
    FrameCoordinates p z where
  matrix := matrix p z U
  trace x := PadicInt.coe_eq_zero.mp (by
    rw [← integralMat_trace, cast_matrix, (split_invariants _ _ U.alg _).1,
      atRep_re, x.prop.2, Rat.cast_zero, mul_zero])
  det x := by
    rw [show (↑(matrix p z U x).det : ℚ_[p.val]) = (integralMat p.val (matrix p z U x)).det from
      RingHom.map_det (algebraMap ℤ_[p.val] ℚ_[p.val]) (matrix p z U x),
      cast_matrix, (split_invariants _ _ U.alg _).2]
    exact norm_atRep z p x.val
  scale x := U.embed_injective (by
    rw [embed_matrix, U.embed_smul, embed_matrix]
    change atRep z p (p.val • x.val) = _
    rw [atRep_nsmul, Nat.cast_smul_eq_nsmul])
  divisible := divisible p z U
  integralNorm := hInt

end GoodCoordinates

/-- The norm of a vector in the rational left order of the explicit level
order is a natural integer, by local integrality and definiteness. -/
theorem lattice_norm_integral {ell N : ℕ} [Fact ell.Prime] (h : ell % 4 = 3) (hN : 0 < N)
    (z : FiniteUnits (levelOrder ell h N hN)) (x : Ternary z) :
    ∃ n : ℕ, Visibility.nrd x.val = (n : ℚ) := by
  obtain ⟨t, ht⟩ := rat_integral_of_local (Visibility.nrd x.val) (fun q => by
    obtain ⟨u, hu⟩ := completion_norm_integral h hN q (atRep z q x.val)
      ((mem_leftRing_iff z x.val).mp x.prop.1 q)
    exact ⟨u, hu.trans (norm_atRep z q x.val)⟩)
  have ha : (-1 : ℚ) < 0 := by norm_num
  have hb : -(ell : ℚ) < 0 := neg_lt_zero.mpr (Nat.cast_pos.mpr (Fact.out : ell.Prime).pos)
  have hpos : 0 ≤ Visibility.nrd x.val := by
    by_cases hx : x.val = 0
    · simp [hx, Visibility.nrd]
    · exact (nrd_pos ha hb hx).le
  have ht' : 0 ≤ t := by exact_mod_cast (ht.symm ▸ hpos)
  exact ⟨t.toNat, by rw [← ht, ← Int.cast_natCast, Int.toNat_of_nonneg ht']⟩

end ZInQ.Manuscript.RC.ThetaJoin
