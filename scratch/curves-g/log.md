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

## t34
- 18:40 `ZInQKernel/Contrib/CurvesG/GenusSplit.lean`: `fieldGenus F` (ℚ-dimension of the differentials of
  `Ω[F⁄ℚ]` regular at every valuation subring containing ℚ); leaves `DimJacobianEqGenus` (Milne: dim of a
  Jacobian = genus, for every curve over ℚ) and `GenusX1Field` (genus of `K_N` = `genus Γ₁(N)`);
  `dimJ1Genus_of_split : DimJacobianEqGenus → GenusX1Field → LeafModCurves.DimJ1Genus`. VERIFIED: lake build
  0 errors; `#print axioms` standard three (axioms_contrib_out.txt).
- Consumers of t34 in leaf-fold3's flat file (VERIFIED by grep of Leaves3.lean): only through
  `LeafModCurves.dim_J1_le` (`dim J ≤ N²`), at lines 16897, 33861, 34333, 71883 (javanpeykarJ1 and E2).
