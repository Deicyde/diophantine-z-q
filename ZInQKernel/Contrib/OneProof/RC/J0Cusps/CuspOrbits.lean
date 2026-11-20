import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import ZInQKernel.Contrib.OneProof.RC.ElkikPrint.Finiteness

/-! The cusps used in the quadratic sum lie in the orbit of zero.
Tex 1785–1787, 2404–2410, 2937–2940; on the spot (c). -/

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace ZInQ.Manuscript.RC.J0Cusps

/-- A fraction with denominator prime to the level is carried from zero by a level
matrix. The numerator and denominator are assumed coprime. -/
theorem exists_gamma0_smul_zero (N a m : ℕ) (hm : m ≠ 0)
    (ham : a.Coprime m) (hmN : m.Coprime N) :
    ∃ g ∈ CongruenceSubgroup.Gamma0 N,
      mapGL ℚ g • ((0 : ℚ) : OnePoint ℚ) = (((a : ℚ) / m : ℚ) : OnePoint ℚ) := by
  have ha : IsCoprime (a : ℤ) (m : ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa)
  have hN : IsCoprime (N : ℤ) (m : ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using hmN.symm)
  obtain ⟨u, v, huv⟩ := ha.mul_left hN
  let g : SL(2, ℤ) := ⟨!![v, (a : ℤ); -(u * N), (m : ℤ)], by
    rw [Matrix.det_fin_two_of]
    calc
      v * (m : ℤ) - a * -(u * N) = u * (a * N) + v * m := by ring
      _ = 1 := huv⟩
  refine ⟨g, ?_, ?_⟩
  · change ((-(u * (N : ℤ)) : ℤ) : ZMod N) = 0
    simp
  · rw [OnePoint.smul_some_eq_ite]
    simp only [mul_zero, zero_add]
    change (if ((m : ℤ) : ℚ) = 0 then OnePoint.infty
      else ((((a : ℤ) : ℚ) / ((m : ℤ) : ℚ) : ℚ) : OnePoint ℚ)) = _
    simp [hm]

/-- The analogous statement in the cusp orbit type used by the Elkik reduction. -/
theorem cuspOrbit_eq_zero_of_coprime (N a m : ℕ) [NeZero N] (hm : m ≠ 0)
    (ham : a.Coprime m) (hmN : m.Coprime N) :
    ElkikPrint.cuspOrbit N (((a : ℚ) / m : ℚ) : OnePoint ℚ) =
      ElkikPrint.cuspOrbit N ((0 : ℚ) : OnePoint ℚ) := by
  obtain ⟨g, hg, h⟩ := exists_gamma0_smul_zero N a m hm ham hmN
  apply Quotient.eq.mpr
  refine ⟨⟨mapGL ℝ g, ?_⟩, Subtype.ext ?_⟩
  · exact ⟨g, hg, rfl⟩
  · change mapGL ℝ g • OnePoint.map (Rat.cast : ℚ → ℝ) ((0 : ℚ) : OnePoint ℚ) =
      OnePoint.map (Rat.cast : ℚ → ℝ) (((a : ℚ) / m : ℚ) : OnePoint ℚ)
    rw [← Rat.coe_castHom, ← (Rat.castHom ℝ).algebraMap_toAlgebra]
    simpa only [OnePoint.map_smul, map_mapGL] using
      congrArg (OnePoint.map (algebraMap ℚ ℝ)) h

/-- Only one geometric cusp is needed for the nonzero weights in the quadratic
sum, once its modulus is prime to the level. -/
theorem cuspOrbit_eq_zero_of_jacobi_ne_zero (N a m : ℕ) [NeZero N] [NeZero m]
    (hmN : m.Coprime N) (hχ : jacobiSym (a : ℤ) m ≠ 0) :
    ElkikPrint.cuspOrbit N (((a : ℚ) / m : ℚ) : OnePoint ℚ) =
      ElkikPrint.cuspOrbit N ((0 : ℚ) : OnePoint ℚ) := by
  apply cuspOrbit_eq_zero_of_coprime N a m (NeZero.ne m) _ hmN
  by_contra ha
  apply hχ
  exact jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa [Nat.Coprime, Int.gcd_eq_natAbs] using ha)


end ZInQ.Manuscript.RC.J0Cusps
