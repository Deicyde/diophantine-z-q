import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Torsion
import ZInQKernel.Contrib.OneProof.RC.ElkikMD.Prints
import ZInQKernel.Contrib.OneProof.RC.ElkikPrint.Prints

/-! # From torsion of cusp classes to the finite subgroup used in the manuscript -/

open scoped MatrixGroups

namespace ZInQ.Manuscript.RC.ElkikPrint

/-- The cusp of `Γ₀(N)` represented by `r ∈ ℙ¹(ℚ)`. -/
noncomputable def cuspOrbit (N : ℕ) [NeZero N] (r : OnePoint ℚ) :
    CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
  ⟦⟨OnePoint.map Rat.cast r,
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
      (isCusp_SL2Z_iff.mpr (Set.mem_range_self r))⟩⟧

/-- The class map has finite range once it descends to the actual cusp orbits. Mathlib
proves that those orbits are finite for arithmetic subgroups. This is on-the-spot glue (c)
for tex 2937–2940. -/
theorem cuspClass_finiteRange_of_cuspOrbits {N : ℕ} [NeZero N] {J : Type*}
    {cuspClass : OnePoint ℚ → J}
    (classOfCusp : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) → J)
    (hCuspFactor : ∀ r, cuspClass r = classOfCusp (cuspOrbit N r)) :
    (Set.range cuspClass).Finite := by
  refine (Set.finite_range classOfCusp).subset ?_
  rintro _ ⟨r, rfl⟩
  exact ⟨cuspOrbit N r, (hCuspFactor r).symm⟩

/-- The finite group in tex 2937–2940 follows from Elkik's torsion theorem and the
finite range of the class map. The group argument is on-the-spot (c). -/
theorem maninDrinfeld_of_torsion {N : ℕ} [NeZero N] {J : Type*} [AddCommGroup J]
    {cuspClass : OnePoint ℚ → J} (hTorsion : ManinDrinfeldTorsion N cuspClass)
    (hFinite : (Set.range cuspClass).Finite) : ElkikMD.ManinDrinfeld N cuspClass := by
  let : Finite (Set.range cuspClass) := hFinite
  change Finite (AddSubgroup.closure (Set.range cuspClass))
  apply AddCommGroup.finite_of_fg_isAddTorsion
  have hle : AddSubgroup.closure (Set.range cuspClass) ≤ AddCommGroup.torsion J := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨r, rfl⟩
    exact (AddCommGroup.mem_torsion _).mpr (isOfFinAddOrder_iff_nsmul_eq_zero.mpr (hTorsion r))
  intro x
  obtain ⟨n, hn, hx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp
    ((AddCommGroup.mem_torsion _).mp (hle x.property))
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, Subtype.ext hx⟩


end ZInQ.Manuscript.RC.ElkikPrint
