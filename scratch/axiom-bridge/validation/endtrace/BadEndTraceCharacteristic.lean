import NativeEndTrace

/- UNRUN PRIVATE NEGATIVE CASE: ell equals the characteristic.
Accept only the intended rejection of the false original invertibility guard,
not an unrelated missing prime/typeclass/import error. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped MonObj

example (A : PkgI3.AbVar (ZMod 3)) (φ : PkgI3.AbVar.End A) :
    LinearMap.trace ℚ_[3] (A.V 3)
      ((PkgI3.AbVar.homT (ℓ := 3) φ).baseChange ℚ_[3]) =
        (AxiomBridge.NativeEndTrace.rationalTrace A φ : ℚ_[3]) :=
  AxiomBridge.NativeEndTrace.trace_homT_baseChange A φ 3 (by decide)
