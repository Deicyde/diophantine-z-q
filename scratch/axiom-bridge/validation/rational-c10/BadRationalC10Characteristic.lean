import RationalC10Cases

/-
UNCOMPILED PRIVATE NEGATIVE CONTROL: the original ell:k nonzero guard must
reject ell=characteristic. Invoke the same native self-comparison case helper,
which derives finite target data only AFTER that guard; do not add caller
Free/Finite/CharZero data at forbidden characteristic. Accept only the intended
false (3 : ZMod 3) != 0 rejection, not another synthesis/import/parser error.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped MonObj TensorProduct
open PkgI3 GlueC10Link
open AxiomBridge.NativeEndTrace

example (A : AbVar (ZMod 3)) (α : AbVar.End A) :
    LinearMap.trace ℚ_[3] (ℚ_[3] ⊗[ℚ_[3]] A.V 3) (endE α 3 ℚ_[3]) =
      (rationalTrace A α : ℚ_[3]) :=
  RationalC10Cases.selfComparison A α 3 (by decide) ℚ_[3]
