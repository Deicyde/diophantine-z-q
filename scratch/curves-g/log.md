# curves-g results log

Base: 8ec80711 + merge of origin/wip/leaf-fold3 (f7951690). Fields: t33 (`LeafModCurves.JacobianExists ℚ`),
t34 (`LeafModCurves.DimJ1Genus`), t38 (`X1Belyi.CurveOfFunctionFieldQ`). Owner files (kernel modules):
`ZInQKernel/HDecomp/ModCurves/Defs.lean` (JacobianExists), `.../Leaves.lean` (DimJ1Genus), `.../X1Belyi.lean`
(CurveOfFunctionFieldQ). leaf-fold3's flat file `scratch/leaf-fold3/Leaves3.lean` has copies under `HDec.`.

## t38
- 18:20 `ZInQKernel/Contrib/CurvesG/RatPoint.lean`: `nonempty_ratPt_of_place` (proper integral ℚ-scheme +
  degree-1 place of its function field ⇒ ℚ-point, via Mathlib `UniversallyClosed.eq_valuativeCriterion`),
  new Prop `CurveOfFunctionFieldQNoPoint` (T38 minus the point clause), `curveOfFunctionFieldQ_of_noPoint :
  CurveOfFunctionFieldQNoPoint → X1Belyi.CurveOfFunctionFieldQ`. VERIFIED: `lake build
  ZInQKernel.Contrib.CurvesG.RatPoint` 27 s, 0 errors; `scratch/curves-g/AxiomsContrib.lean`: all four
  `#print axioms` read `[propext, Classical.choice, Quot.sound]` (axioms_contrib_out.txt).
