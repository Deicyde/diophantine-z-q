import ZInQKernel.Contrib.CurvesG.RatPoint
import ZInQKernel.Contrib.CurvesG.GenusSplit

/-- The kernel owner's statement, by name: the proved reduction has exactly this type. -/
example : ZInQ.Contrib.CurvesG.CurveOfFunctionFieldQNoPoint → X1Belyi.CurveOfFunctionFieldQ :=
  ZInQ.Contrib.CurvesG.curveOfFunctionFieldQ_of_noPoint

#print axioms ZInQ.Contrib.CurvesG.hom_to_specQ_ext
#print axioms ZInQ.Contrib.CurvesG.residueToRat
#print axioms ZInQ.Contrib.CurvesG.nonempty_ratPt_of_place
#print axioms ZInQ.Contrib.CurvesG.curveOfFunctionFieldQ_of_noPoint

#print axioms ZInQ.Contrib.CurvesG.dimJ1Genus_of_split

example : ZInQ.Contrib.CurvesG.DimJacobianEqGenus → ZInQ.Contrib.CurvesG.GenusX1Field →
    LeafModCurves.DimJ1Genus := ZInQ.Contrib.CurvesG.dimJ1Genus_of_split
