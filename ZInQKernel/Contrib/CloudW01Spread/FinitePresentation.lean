import ZInQKernel.Contrib.SpreadOut.Spread
import ZInQKernel.Contrib.CloudW01Spread.StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing

/-!
# Finite presentation descends to a finite stage

This proves the fixed `ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii` by the
actual essential-surjectivity proof of Stacks 01ZM(1) in AxiomMath/Stacks,
revision c496df0d9beea9deaeabcea8492605f9a0a2313b. The proof descends
finitely presented affine pieces and their overlaps, then glues the pieces.
See NOTICE.md for the exact source paths, license, and port modifications.

The upstream `FinitePresentation` predicate is precisely the conjunction of
Mathlib's `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated`.
The only translation below unpacks that conjunction and reverses the supplied
isomorphism. No additional hypothesis or replacement definition is used.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.SpreadOut

/-- EGA IV₃ 8.8.2(ii), with exactly the fixed target's hypotheses. -/
theorem EGAIV_8_8_2_ii_proof : EGAIV_8_8_2_ii := by
  intro J _ _ _ D _ _ _ c hc X hlfp hqc hqs
  obtain ⟨i, Xi, hXi, ⟨e⟩⟩ :=
    AlgebraicGeometry.LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall
      D c hc X ⟨hlfp, hqc, hqs⟩
  exact ⟨i, Xi, hXi.1, hXi.2.1, hXi.2.2, ⟨e.symm⟩⟩

end ZInQ.Contrib.SpreadOut

#print axioms ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof
