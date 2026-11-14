import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.NormalModel

/-!
# cloud-w07: exact-type and axiom checks for frontier rows H-36 and H-80

Both statements are the fixed `def`s of fork `main` (`cba8157f`, unchanged at `f70ec251`):
`LeafModCurves.JacobianExists` in `ZInQKernel/HDecomp/ModCurves/Defs.lean` and
`ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ` in `ZInQKernel/Contrib/CurvesG/CurveSplit.lean`.
-/

/-- H-36 (`t33`), with exactly the fixed type. -/
example : LeafModCurves.JacobianExists ℚ :=
  ZInQ.Contrib.CloudW07JacobiansCurves.JacobianExists_proof

/-- H-36 in the general form proved (every field). -/
example : ∀ (K : Type) [Field K], LeafModCurves.JacobianExists K :=
  fun K _ => ZInQ.Contrib.CloudW07JacobiansCurves.jacobianExists_of_field K

/-- H-80, with exactly the fixed type. -/
example : ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ :=
  ZInQ.Contrib.CloudW07JacobiansCurves.NormalModelOfFunctionFieldQ_proof

#print axioms ZInQ.Contrib.CloudW07JacobiansCurves.JacobianExists_proof
#print axioms ZInQ.Contrib.CloudW07JacobiansCurves.jacobianExists_of_field
#print axioms ZInQ.Contrib.CloudW07JacobiansCurves.NormalModelOfFunctionFieldQ_proof
