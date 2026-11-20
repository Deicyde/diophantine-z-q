import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Analytic
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Coordinates

/-! The two pullback coordinates of the involution at tex 2943–2944 and
8487–8489. Matrix factorization: on the spot (c). -/

set_option autoImplicit false

noncomputable section

open Filter Function UpperHalfPlane ModularCurve Polynomial Matrix
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TauCeti.ExactDivisor
open ZInQ.Manuscript.RC.AtkinPin ZInQ.Manuscript.RC.ModFnField
open ZInQ.Manuscript.RC.ModFnClassify

namespace ZInQ.Manuscript.RC.AtkinRational

variable {N Q : ℕ} [NeZero N]

omit [NeZero N] in
private theorem coe_atkin (hQ : Q ∥ N) {M : ℕ}
    {a b c d : ℤ}
    (h : TauCeti.atkinLehnerMatrix N Q =
      !![(Q : ℤ) * a, b; (Q : ℤ) * M * c, (Q : ℤ) * d]) (τ : ℍ) :
    ((atkinGL hQ • τ : ℍ) : ℂ) =
      ((Q : ℂ) * a * τ + b) / ((Q : ℂ) * M * c * τ + (Q : ℂ) * d) := by
  unfold atkinGL
  rw [coe_smul_of_det_pos (TauCeti.val_det_atkinLehnerGL_pos hQ.pos _)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, TauCeti.coe_atkinLehnerGL, Matrix.map_apply, h]
  change (((((Q : ℤ) * a : ℤ) : ℝ) : ℂ) * τ + ((b : ℝ) : ℂ)) /
    (((((Q : ℤ) * (M : ℤ) * c : ℤ) : ℝ) : ℂ) * τ + ((((Q : ℤ) * d : ℤ) : ℝ) : ℂ)) = _
  push_cast
  rfl

set_option maxHeartbeats 500000 in
/-- On the chart the first $j$-coordinate pulls back to $j(Q\tau)$ and
the second to $j((N/Q)\tau)$. For an integral matrix with entries
$Qa,b,Nc,Qd$ and $m=N/Q$, use the two determinant-one matrices with entries
$a,b,mc,Qd$ and $Qa,mb,c,d$ respectively. -/
theorem chart_coordinates (hQ : Q ∥ N)
    [NeZero Q] [NeZero (N / Q)] (τ : ℍ) :
    X0Model.analyticJ (atkinGL hQ • τ) = X0Model.analyticJN Q τ ∧
    X0Model.analyticJN N (atkinGL hQ • τ) = X0Model.analyticJN (N / Q) τ := by
  let M := N / Q
  have hm : N = Q * M := (Nat.mul_div_cancel' hQ.dvd).symm
  obtain ⟨a, b, c, d, h, hd⟩ :=
    (TauCeti.isAtkinLehnerMatrix_atkinLehnerMatrix hQ).exists_entries hQ.pos.ne' hm
  let g : SL(2, ℤ) := ⟨!![a, b; (M : ℤ) * c, (Q : ℤ) * d], by
    rw [Matrix.det_fin_two_of]
    linear_combination hd⟩
  let k : SL(2, ℤ) := ⟨!![(Q : ℤ) * a, (M : ℤ) * b; c, d], by
    rw [Matrix.det_fin_two_of]
    linear_combination hd⟩
  have hg : atkinGL hQ • τ = g • X0Model.dilate Q τ := by
    apply UpperHalfPlane.ext
    rw [coe_atkin hQ h, coe_specialLinearGroup_apply]
    simp only [algebraMap_int_eq, Int.coe_castRingHom, Complex.ofReal_intCast]
    change _ = (((a : ℂ) * ((Q : ℂ) * τ) + b) /
      ((((M : ℤ) * c : ℤ) : ℂ) * ((Q : ℂ) * τ) + ((((Q : ℤ) * d : ℤ)) : ℂ)))
    push_cast
    congr 1 <;> ring
  have hk : X0Model.dilate N (atkinGL hQ • τ) = k • X0Model.dilate M τ := by
    apply UpperHalfPlane.ext
    change (N : ℂ) * ((atkinGL hQ • τ : ℍ) : ℂ) = _
    rw [coe_atkin hQ h, coe_specialLinearGroup_apply]
    simp only [algebraMap_int_eq, Int.coe_castRingHom, Complex.ofReal_intCast]
    change _ = (((((Q : ℤ) * a : ℤ) : ℂ) * ((M : ℂ) * τ) +
      ((((M : ℤ) * b : ℤ)) : ℂ)) / ((c : ℂ) * ((M : ℂ) * τ) + d))
    push_cast
    have hq : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.pos.ne'
    have hN : (N : ℂ) = (Q : ℂ) * M := by exact_mod_cast hm
    rw [hN, ← mul_div_assoc,
      show (Q : ℂ) * M * c * τ + (Q : ℂ) * d =
        (Q : ℂ) * ((c : ℂ) * ((M : ℂ) * τ) + d) by ring,
      show (Q : ℂ) * M * ((Q : ℂ) * a * τ + b) =
        (Q : ℂ) * ((Q : ℂ) * a * ((M : ℂ) * τ) + (M : ℂ) * b) by ring,
      mul_div_mul_left _ _ hq]
  constructor
  · rw [X0Model.analyticJN, hg]
    simpa only [jFunction, ofComplex_apply] using jFunction_invariant g (X0Model.dilate Q τ)
  · rw [X0Model.analyticJN, X0Model.analyticJN, hk]
    simpa only [jFunction, ofComplex_apply] using jFunction_invariant k (X0Model.dilate M τ)


end ZInQ.Manuscript.RC.AtkinRational
