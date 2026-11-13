# curve-facts results log

## Setup
- Merged origin/wip/mobius-glue (CurveRatFactor, CurveSurj in scratch/mobius-glue/MobiusGlue.lean §2).
- `lake build ZInQKernel.HDecomp.QM.Pairs` OK (build_pairs.txt).

## Mathlib v4.35 survey (VERIFIED by grep in .lake/packages/mathlib)
- Present: IsProper (extends IsSeparated, UniversallyClosed, LocallyOfFiniteType); valuative
  criteria (ValuativeCriterion.lean); IsNoetherian schemes, LocallyOfFiniteType.isLocallyNoetherian,
  IsLocallyNoetherian/CompactSpace instances for pullbacks; NoetherianSpace.finite_irreducibleComponents;
  irreducibleComponent_subset_connectedComponent; Scheme.functionField; Scheme.ordHom (order of
  vanishing at codim-1 points, OrderOfVanishing.lean); AffineSpace; Proj proper
  (ProjectiveSpectrum/Proper.lean); AlgClosed/Basic.lean (closed points = K-points over alg. closed K);
  GeometricallyConnected; SmoothOfRelativeDimension (stable under base change, comp).
- Absent: P¹ as a scheme with P¹(K) = K ∪ {∞}; dimension theory of smooth morphisms (rel. dim n ⇒
  fibres of dim n); curves (dimension 1 integral schemes) and their function fields as
  trdeg-1 extensions; degree of a finite morphism of curves, fibre counts; Hartshorne II.6.8.

## CurveFacts.lean (compiled, EXIT 0, run4.txt; axioms propext, Classical.choice, Quot.sound)
- §0 CurveRatFactor, CurveSurj, Mob.ratEval copied verbatim; ToP1/fieldPt/Qbar imported from
  ZInQKernel.HDecomp.QM.Pairs.
- §1 defs bcQbar S := pullback S.hom (Spec ℚ̄ → Spec ℚ); bcPt y := pullback.lift y.left (𝟙 _);
  geomComp y := connectedComponent of the point of bcPt y.
- §2 named Props: GeomCompInfinite (C1), GeomCompConstOrOnto (C2), GeomCompRatFactor (C3),
  GeomCompFinite (C4).
- §3 geomCompFinite : GeomCompFinite PROVED (S_ℚ̄ Noetherian ⇒ finitely many irreducible comps,
  each inside a connected comp).
- §4 Mob.exists_interp PROVED (values in P¹ at finitely many nodes by coprime [F : G]).
- §5 curveSurj_of_comp : C1 → C2 → CurveSurj; curveRatFactor_of_comp : C2 → C3 → CurveRatFactor;
  curveFacts_of_comp. All compiled.

## Step 2: C1 from C1a (compiled, EXIT 0, run5.txt; axioms propext, Classical.choice, Quot.sound)
- bcQbar made an `abbrev` (own definition; no statement of the task changed).
- named Prop SmoothCurveNoIsolatedPoint (C1a): ∀ field K, X, f : X ⟶ Spec K smooth of rel. dim 1,
  ∀ x, ¬ IsOpen {x}.
- PROVED: isOpen_connectedComponent_of_noetherian; exists_isOpen_singleton_of_finite_closedPoints
  (Jacobson space); geomCompInfinite_of : C1a → GeomCompInfinite (S_ℚ̄ Noetherian, Jacobson via
  LocallyOfFiniteType.jacobsonSpace; closed points ↔ ℚ̄-points via Mathlib's pointOfClosedPoint).
- curveFacts_of_named : C1a → C2 → C3 → CurveRatFactor ∧ CurveSurj.
