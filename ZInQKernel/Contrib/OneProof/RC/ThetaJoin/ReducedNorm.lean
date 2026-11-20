import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.LocalOrder
import ZInQKernel.Contrib.OneProof.RC.Adelic.FiniteUnits

/-! Reduced norms in the completed level orders. -/

noncomputable section

open scoped Quaternion

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic Eichler

/-- Reduced norm, valid also in the split ambient algebra. -/
def reducedNorm {K : Type*} [Field K] (a b : K) : ℍ[K,a,0,b] →* K where
  toFun x := (x * star x).re
  map_one' := by simp
  map_mul' x y := by
    have hn (u : ℍ[K,a,0,b]) : algebraMap K ℍ[K,a,0,b] (u * star u).re = u * star u := by
      rw [QuaternionAlgebra.coe_algebraMap]
      exact (QuaternionAlgebra.mul_star_eq_coe u).symm
    apply QuaternionAlgebra.algebraMap_injective (R := K) (c₁ := a) (c₂ := 0) (c₃ := b)
    rw [hn, map_mul, hn, star_mul]
    calc (x * y) * (star y * star x) = x * (y * star y) * star x := by
           simp only [mul_assoc]
      _ = x * algebraMap K ℍ[K,a,0,b] (y * star y).re * star x := by rw [hn]
      _ = x * star x * algebraMap K ℍ[K,a,0,b] (y * star y).re := by
           rw [mul_assoc, Algebra.commutes, ← mul_assoc]

theorem norm_toLocal {a b : ℚ} (q : Prime) (x : B a b) :
    reducedNorm (a : ℚ_[q.val]) (b : ℚ_[q.val]) (toLocal q.val x) =
      (Visibility.nrd x : ℚ_[q.val]) := by
  change ((toLocal q.val x * star (toLocal q.val x)).re) = _
  rw [show star (toLocal q.val x) = toLocal q.val (star x) from by
    apply QuaternionAlgebra.ext <;> simp [toLocal]]
  rw [← map_mul]
  rfl

theorem norm_atRep {a b : ℚ} {R : Order a b} (z : FiniteUnits R) (q : Prime)
    (x : B a b) :
    reducedNorm (a : ℚ_[q.val]) (b : ℚ_[q.val])
      (↑(z.val q)⁻¹ * toLocal q.val x * (z.val q : Bp q.val a b)) =
      (Visibility.nrd x : ℚ_[q.val]) := by
  let U := Units.map (reducedNorm (a : ℚ_[q.val]) (b : ℚ_[q.val])) (z.val q)
  change (reducedNorm _ _) (_ * _ * _) = _
  rw [map_mul, map_mul, norm_toLocal]
  change (U.inv * (Visibility.nrd x : ℚ_[q.val])) * U.val = _
  rw [mul_comm U.inv, mul_assoc, U.inv_val, mul_one]

variable {ell N : ℕ} [Fact ell.Prime] (h : ell % 4 = 3) (hN : 0 < N)

/-- The reduced norm of a vector in a completed level order is integral. -/
theorem completion_norm_integral (q : Prime) (x : Bp q.val (-1) (-(ell : ℚ)))
    (hx : x ∈ (levelOrder ell h N hN).completion q.val) :
    ∃ t : ℤ_[q.val], (t : ℚ_[q.val]) = reducedNorm _ _ x := by
  by_cases hq : q.val = ell
  · have he : q = ⟨ell, Fact.out⟩ := Subtype.ext hq
    subst q
    let : Fact (ell % 4 = 3) := ⟨h⟩
    rw [divisionCompletion ell h N hN] at hx
    have hy : DivisionJoin.ambientEquiv ell x ∈ LocalDivision.order ell := by
      rw [← DivisionJoin.completion_map ell h]
      exact ⟨x, hx, rfl⟩
    have hh := (LocalDivision.mem_order_iff_nrd (DivisionJoin.ambientEquiv ell x)).mp hy
    exact ⟨⟨_, hh⟩, DivisionJoin.ambient_norm ell x⟩
  · rw [levelOrder_completion] at hx
    obtain ⟨A, _, hA⟩ := (levelLocal_mem_split ell h N q hq x).mp hx
    refine ⟨A.det, ?_⟩
    calc (A.det : ℚ_[q.val]) = (matrixCast q.val A).det :=
          RingHom.map_det (algebraMap ℤ_[q.val] ℚ_[q.val]) A
      _ = _ := (congrArg Matrix.det hA).trans (split_invariants _ _ _ _).2

end ZInQ.Manuscript.RC.ThetaJoin
