import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral

/-!
# frob-pieces: `SmoothGeomConnIntegral` (alg-frob-red's leaf candidate), proved

Task frob-pieces. The statement `SmoothGeomConnIntegral` below is a verbatim copy of the `def`
of the same name in `scratch/alg-frob-red/part_red.lean` (namespace `AlgFrobRedRed`; checked by
`scratch/frob-pieces/py/verbatim_check.py`). It is proved by the vendored Tau Ceti instance
`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral` (Tau Ceti commit 5a01f5fe, module
`TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral`): a smooth, geometrically
connected morphism is geometrically integral (after a field base change, a smooth scheme is
locally noetherian with regular, hence domain, local rings, and a connected such scheme is
integral). Quasi-compactness is not needed.
-/

noncomputable section

namespace FrobPieces

open CategoryTheory AlgebraicGeometry

/-- **`SmoothGeomConnIntegral` (LEAF candidate, textbook; Stacks Project / EGA IV₂).** A smooth,
quasi-compact, geometrically connected scheme over a field is geometrically integral (smooth ⇒
geometrically normal, EGA IV₂ 6.8.1 / 6.7.4 (UNVERIFIED); a connected, quasi-compact, locally
Noetherian normal scheme is integral, Stacks Tag 033M (UNVERIFIED); applied after every field
base change, which preserves smoothness and connectedness). -/
def SmoothGeomConnIntegral : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (.of k)),
    Smooth f → GeometricallyConnected f → QuasiCompact f → GeometricallyIntegral f

/-- **`SmoothGeomConnIntegral`, proved** (from the vendored Tau Ceti theorem
`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`). -/
theorem smoothGeomConnIntegral : SmoothGeomConnIntegral := by
  intro k _ X f hS hC _
  exact TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral f

end FrobPieces

end
