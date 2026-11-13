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

## Step 3: verbatim check, report
- py/verbatim.py: CurveRatFactor, CurveSurj, ratEval IDENTICAL to scratch/mobius-glue (VERIFIED).
- docs/research/curve-facts.md written (result, definitions, truth arguments, survey, remaining).

## Step 4: leaves over an algebraically closed field (compiled, EXIT 0, run6.txt; std axioms)
- named Props ConstOrOntoAlgClosed (C2K) and RatFactorAlgClosed (C3K, with [CharZero K]):
  any alg. closed K : Type, X : Scheme, f : X ⟶ Spec K proper, smooth rel. dim 1, σ (ρ) : ToP1 X,
  K-points = sections p (p ≫ f = 𝟙), components = connectedComponent (ptOf p).
- PROVED: dictionary (bcSnd, bcPt_snd, ptOfSection, bcPt_ptOfSection, val_bcPt);
  geomCompConstOrOnto_of : C2K → C2; geomCompRatFactor_of : C3K → C3;
  curveFacts_of_algClosed : C1a → C2K → C3K → CurveRatFactor ∧ CurveSurj.

## Step 5: C1a from C1b (compiled, EXIT 0, run7.txt; std axioms)
- named Prop SmoothStalkDimOne (C1b): X → Spec K smooth rel. dim 1, x closed ⇒
  ringKrullDim (X.presheaf.stalk x) = 1.
- PROVED smoothCurveNoIsolatedPoint_of : C1b → C1a (open point closed by Jacobson;
  IsMax in specialization order; Mathlib ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero).
- curveFacts_of_leaves : C1b → C2K → C3K → CurveRatFactor ∧ CurveSurj.

## Step 6: independent model review (fresh agent, statements only; not human)
- C1a, C2K, C3K: all TRUE, none vacuous (P¹_K satisfies all hypotheses). C2K needs properness and
  alg. closure, not smoothness; C3K needs char 0 and alg. closure. C1b not reviewed (STANDARD).
