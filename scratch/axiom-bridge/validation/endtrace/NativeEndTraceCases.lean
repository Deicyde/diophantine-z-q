import NativeEndTrace

/-
UNRUN PRIVATE POSITIVE CASES.
These apply the bounded rational result to genuine original objects, maps,
bases and coefficient data. They do not assert the stronger integer leaf,
construct descended C10 representations, or infer success from empty stdout.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped MonObj

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace NativeEndTraceCases

def zeroAbVar (k : Type) [Field k] : PkgI3.AbVar k :=
  { X := 𝟙_ (Over (Spec (CommRingCat.of k)))
    proper := by change IsProper (𝟙 (Spec (CommRingCat.of k))); infer_instance
    smooth := by change Smooth (𝟙 (Spec (CommRingCat.of k))); infer_instance
    geomInt := by change GeometricallyIntegral (𝟙 (Spec (CommRingCat.of k))); infer_instance }

-- A single rational witness for the SAME original endomorphism at three and five.
example (A : PkgI3.AbVar ℚ) (φ : PkgI3.AbVar.End A) :
    ∃ t : ℚ,
      LinearMap.trace ℚ_[3] (A.V 3)
        ((PkgI3.AbVar.homT (ℓ := 3) φ).baseChange ℚ_[3]) = (t : ℚ_[3]) ∧
      LinearMap.trace ℚ_[5] (A.V 5)
        ((PkgI3.AbVar.homT (ℓ := 5) φ).baseChange ℚ_[5]) = (t : ℚ_[5]) := by
  refine ⟨AxiomBridge.NativeEndTrace.rationalTrace A φ, ?_, ?_⟩
  · exact AxiomBridge.NativeEndTrace.trace_homT_baseChange A φ 3 (by norm_num)
  · exact AxiomBridge.NativeEndTrace.trace_homT_baseChange A φ 5 (by norm_num)

-- Actual further scalar maps and actual coefficient embeddings remain inputs.
example (A : PkgI3.AbVar ℚ) (φ : PkgI3.AbVar.End A)
    (C L₃ L₅ : Type) [Field C] [CharZero C]
    [Field L₃] [CharZero L₃] [Algebra ℚ_[3] L₃]
    [Field L₅] [CharZero L₅] [Algebra ℚ_[5] L₅]
    (ι₃ : C →+* L₃) (ι₅ : C →+* L₅) :
    ∃ c : C,
      LinearMap.trace L₃ (TensorProduct ℚ_[3] L₃ (A.V 3))
        (((PkgI3.AbVar.homT (ℓ := 3) φ).baseChange ℚ_[3]).baseChange L₃) = ι₃ c ∧
      LinearMap.trace L₅ (TensorProduct ℚ_[5] L₅ (A.V 5))
        (((PkgI3.AbVar.homT (ℓ := 5) φ).baseChange ℚ_[5]).baseChange L₅) = ι₅ c := by
  obtain ⟨c, hc⟩ := AxiomBridge.NativeEndTrace.exists_common_coefficient_trace A φ C
  exact ⟨c, hc 3 (by norm_num) L₃ ι₃, hc 5 (by norm_num) L₅ ι₅⟩

example (A : PkgI3.AbVar ℚ) (φ : PkgI3.AbVar.End A) :
    LinearMap.trace ℚ_[2] (A.V 2)
      ((PkgI3.AbVar.homT (ℓ := 2) φ).baseChange ℚ_[2]) =
        (AxiomBridge.NativeEndTrace.rationalTrace A φ : ℚ_[2]) :=
  AxiomBridge.NativeEndTrace.trace_homT_baseChange A φ 2 (by norm_num)

example (A : PkgI3.AbVar (ZMod 3)) (φ : PkgI3.AbVar.End A) :
    LinearMap.trace ℚ_[5] (A.V 5)
      ((PkgI3.AbVar.homT (ℓ := 5) φ).baseChange ℚ_[5]) =
        (AxiomBridge.NativeEndTrace.rationalTrace A φ : ℚ_[5]) :=
  AxiomBridge.NativeEndTrace.trace_homT_baseChange A φ 5 (by decide)

example :
    LinearMap.trace ℚ_[3] ((zeroAbVar ℚ).V 3)
      ((PkgI3.AbVar.homT (ℓ := 3) (0 : PkgI3.AbVar.End (zeroAbVar ℚ))).baseChange ℚ_[3]) =
        (AxiomBridge.NativeEndTrace.rationalTrace (zeroAbVar ℚ) 0 : ℚ_[3]) :=
  AxiomBridge.NativeEndTrace.trace_homT_baseChange (zeroAbVar ℚ) 0 3 (by norm_num)

example (A : PkgI3.AbVar ℚ) :
    LinearMap.trace ℚ_[3] (A.V 3)
      ((PkgI3.AbVar.homT (ℓ := 3) (1 : PkgI3.AbVar.End A)).baseChange ℚ_[3]) =
        (AxiomBridge.NativeEndTrace.rationalTrace A 1 : ℚ_[3]) :=
  AxiomBridge.NativeEndTrace.trace_homT_baseChange A 1 3 (by norm_num)

-- A genuine supplied empty-index basis is respected; this fixture does not
-- construct such a basis or infer the rank-zero result from an assumption.
example (b : Module.Basis (Fin 0) ℚ_[3] ((zeroAbVar ℚ).V 3)) :
    (LinearMap.toMatrix b b
      ((PkgI3.AbVar.homT (ℓ := 3) (0 : PkgI3.AbVar.End (zeroAbVar ℚ))).baseChange ℚ_[3])).charpoly =
        (AxiomBridge.NativeEndTrace.rationalCharPoly (zeroAbVar ℚ) 0).map
          (algebraMap ℚ ℚ_[3]) :=
  AxiomBridge.NativeEndTrace.charpoly_homT_baseChange (zeroAbVar ℚ) 0 3 (by norm_num) b

end NativeEndTraceCases
