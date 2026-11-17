import ZInQKernel.Contrib.CloudR2Poincare.L3.NativeLerayOneExact

/-!
# Default-source canonical low-degree Leray public ABI

Source-only in the reactivated world. This wrapper uses only the new owned
candidate modules, never the historical original same-name Leray modules.
The two original public statement headers and maps are unchanged. A current
parent-reviewed default-budget native selection remains required.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits

namespace ZInQ.Contrib.CloudR2Poincare.L3

universe u

/-- The actual canonical edge construction is fixed, not selected from a rank argument. -/
theorem nativeLerayOneEdge_def {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) :
    nativeLerayOneEdge f F =
      LerayOneConstruction.resolutionEdge f F (injectiveResolution F) := rfl

/-- The actual low-degree Leray segment, with the literal native adjunction inflation. -/
theorem nativeLerayOneExact {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) :
    Function.Injective
      (Scheme.Modules.H.mapOfAdjunction f (𝟙 ((Scheme.Modules.pushforward f).obj F)) 1) ∧
      (Scheme.Modules.H.mapOfAdjunction f (𝟙 ((Scheme.Modules.pushforward f).obj F)) 1).range =
        (nativeLerayOneEdge f F).ker :=
  LerayOneConstruction.resolutionEdge_exact f F (injectiveResolution F)

end ZInQ.Contrib.CloudR2Poincare.L3
