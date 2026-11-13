# curve-glue results log

## 1. CM points for MobiusGlue (`CMPoints.lean`)
- Compiled 06:3x, 0 errors 0 warnings; axioms [propext, Classical.choice, Quot.sound] (VERIFIED).
- `cm_points_of_objects : R2fpProps Y Φ π → CMObjects → CMPoints Y Φ π` (Φ onto; one-way clauses suffice).
- `cm_points_of_R1R2fp`, `cm_points_of_R1R2fpRep` (CMExists from R2X6PropsIff + X6Surj.1; level-3 from X6Surj.2).
- `mobiusGlue_noCM_of(_rep) : MobiusGlue → bundle → MobiusGlueNoCM`.
- Finding: kernel `MobiusGlue` already has the CM objects as a premise; consumers already supply them
  (`cm_objects_of_R1R2fp`, pin-apply `sameTripleMor_of_leaves`). Gap is closed; no statement changes.

## 2. C2K from the leaf (L) GlobalFunctionsConst (`C2K.lean`)
- `theorem constOrOntoAlgClosed_of (hL : GlobalFunctionsConst) : ConstOrOntoAlgClosed` — compiled,
  0 errors 0 warnings, axioms [propext, Classical.choice, Quot.sound] (VERIFIED, `run_c2k.txt`).
- (L) `GlobalFunctionsConst`: K alg. closed, X → Spec K proper + smooth rel. dim 1, W clopen preconnected open,
  s ∈ Γ(X,W) ⇒ ∃ c : K, IsNilpotent (s − cst f W c). Textbook leaf (consequence of finiteness of Γ for
  proper schemes / Γ = K for proper connected reduced; numbering UNVERIFIED).
- Lean proof: values `ev p` of sections at K-points (ring hom; `ev_cst`: constants evaluate to themselves,
  via Mathlib `germ_stalkClosedPointTo`); units detected by values at K-points (Jacobson + `pointOfClosedPoint`);
  missed value ∞: W ⊆ U, f|_W constant; missed value a: glue 1/(f−a) and g/(1−ag) with
  `objSupIsoProdEqLocus`, apply (L), case analysis on c.

## 3. C3K from the glue (G1) ImagePlaneCurve and Lean algebra (`C3K.lean`)
- `Alg.exists_two_roots`: P ∈ K[x][y] irreducible, deg_y P ≥ 2, K alg. closed char 0 ⇒ some fibre P(t,·) has two
  distinct roots. Proof: Gauss lemma (`IsPrimitive.irreducible_iff_irreducible_map_fraction_map`), separable in
  char 0, `resultant_ne_zero`, `resultant_map_map` to K[x] then to K at a good t, `resultant_eq_zero_iff`,
  `nodup_roots`, `Splits.natDegree_eq_card_roots`. Compiled.
- `Alg.isCoprime_coeff_of_irreducible`: deg_y P = 1, irreducible ⇒ coefficients coprime. Compiled.
- `theorem ratFactorAlgClosed_of (hG : ImagePlaneCurve) : RatFactorAlgClosed` — compiled, 0 errors 0 warnings,
  axioms [propext, Classical.choice, Quot.sound] (VERIFIED, `run_C3K.txt`).
- (G1) `ImagePlaneCurve` (glue): ρ ≡ ∞ on W, or ∃ irreducible P of y-degree ≥ 1 with (a) P(σ,ρ)=0 at finite points,
  (b) every affine root (t,u) is hit by a K-point of W, (c) ρ=∞ ∧ σ=t finite ⇒ lc_y(P)(t)=0. No char-0 hypothesis.

## 4. Composite (`CurveGlueAll.lean`)
- CurveFacts.lean verbatim + C2K.lean §1-4 + C3K.lean §1-2;
  `curveFacts_of_glue (h1 : SmoothStalkDimOne) (hL : GlobalFunctionsConst) (hG : ImagePlaneCurve) :
  CurveRatFactor ∧ CurveSurj` — compiled, axioms standard (VERIFIED, `run_CurveGlueAll.txt`).

## 5. Verbatim copies
- `py/verbatim.py` → `verbatim.txt`: all copied declarations IDENTICAL to sources (VERIFIED).
