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

## 6. Independent model check (fresh agent, given only the Lean files; no human)
- `GlobalFunctionsConst`: TRUE, not vacuous (empty W: Γ = 0; nonempty: Γ(W) finite connected K-algebra ⇒ K ⊕ nilradical;
  X = P¹_K satisfies the hypotheses).
- `ImagePlaneCurve`: TRUE without char 0, not vacuous (cases ρ ≡ ∞, ρ ≡ b (P = y − b), ρ nonconstant (D ∩ 𝔸² = V(P)));
  variable direction of `evalXY` and `leadingCoeff` checked; spot checks ρ = 1/σ (P = xy − 1), Frobenius (P = y^p − x).

## 7. End-to-end files
- `MobiusEnd.lean` (imports kernel QM.Pin + Textbook.SkolemNoether): mobius-glue §1-§5 and §7-§8 verbatim except the
  destructuring of `h1' : R1fpProps Y' Φ'` (kernel clause order), + CurveGlueAll body + CMPoints body.
  `mobiusGlue_of_glue (h1 : SmoothStalkDimOne) (hL) (hG) (hT : ObjBridge.TorsionStructure) : MobiusGlue` (kernel's
  `LeafQM.AV.Pin.MobiusGlue`), `mobiusGlueNoCM_of_glue`. Compiled, standard axioms (VERIFIED, `run_MobiusEnd.txt`).
- Merged origin/wip/infra-smooth-dim (proves `SmoothStalkDimOne`, 2b0e44f4). `MobiusFinal.lean` = `import Mathlib` +
  infra §0-§4 verbatim (in a section) + MobiusEnd body + infra proof of `smoothStalkDimOne` + L0 block:
  `mobiusGlue_of_L_G1_T5`, `mobiusGlue_of_L0_G1_T5 (hL0 : FiniteGlobalSections) (hG : ImagePlaneCurve)
  (hT : ObjBridge.TorsionStructure) : MobiusGlue`, `mobiusGlueNoCM_of_L0_G1_T5 … (h : R1R2fp) : MobiusGlueNoCM`,
  `curveFacts_of_L0_G1`. Compiled, 0 errors, standard axioms (VERIFIED, `run_MobiusFinal.txt`; warnings only in copied
  mobius-glue/infra code: linter).

## 8. (L) from (L0) FiniteGlobalSections (`L0.lean`)
- `globalFunctionsConst_of (h : FiniteGlobalSections) : GlobalFunctionsConst` compiled, standard axioms (VERIFIED, `run_L0.txt`).
- (L0): X → Spec K proper, W clopen ⇒ `(cstHom f W).Finite` (EGA III 3.2.1-type finiteness; no smoothness, no alg. closed).
- Lean lemmas: `exists_nilpotent_sub_of_finite` (Artinian + trivial idempotents ⇒ unit or nilpotent via
  `IsArtinian.exists_pow_succ_smul_dvd`; eigenvalue via `Module.End.exists_eigenvalue`);
  `idempotent_trivial_of_isPreconnected` (germs of idempotents in local rings; `IsPreconnected.subset_or_subset`).

## 9. (G1) reduced to (G1') ImagePlaneCurveClosed + C2K (`C3K.lean` §2 additions)
- `Alg.finite_common_zeros` (Bezout-type: P irreducible, deg_y ≥ 1, P ∤ Q ⇒ V(P,Q) ⊆ K² finite; resultant +
  `exists_mul_add_mul_eq_C_resultant` + `map_eval_ne_zero`) compiled.
- (G1') = (G1) with (b) replaced by (b''): the affine image {(σ p, ρ p)} is the zero set of some S ⊆ K[x][y].
- `imagePlaneCurve_of (h2 : ConstOrOntoAlgClosed) (hG : ImagePlaneCurveClosed) : ImagePlaneCurve`,
  `ratFactorAlgClosed_of_closed` compiled, standard axioms (VERIFIED, `run_C3K.txt`).
- `py/assemble.py` regenerates CurveGlueAll/MobiusEnd/MobiusFinal; all three recompiled, 0 errors (VERIFIED).
  New: `curveFacts_of_glue'`, `curveFacts_of_L0_G1'`, `mobiusGlue_of_L0_G1'_T5`, `mobiusGlueNoCM_of_L0_G1'_T5`.

## 10. Second independent model check (fresh agent, Lean files only)
- `FiniteGlobalSections`: TRUE, not vacuous (RingHom.Finite = Module.Finite for the K-structure through f; empty W;
  properness alone suffices; clopen needed: 𝔸¹ ⊂ P¹ fails for merely open W).
- `ImagePlaneCurveClosed`: TRUE, not vacuous (S = {P} works; S = ∅ would force the image to be all of K², so the
  clause is a real constraint; cases ρ ≡ c, ρ ≡ ∞, σ = ∞ checked).

## 11. Clause (c) from irreducibility (`ClauseC.lean.part`, assembled into CurveGlueAll/MobiusEnd/MobiusFinal)
- (CI) `ComponentIrreducible`: smooth rel. dim 1 over a field ⇒ connected components irreducible (glue, STANDARD).
- (G1'') `ImagePlaneCurveIrr` = (G1') without clause (c).
- `lc_eval_eq_zero_of_irreducible`: section P^rev(σ, 1/ρ) on W ∩ {σ≠∞} ∩ {ρ≠0} vanishes on the dense open {ρ≠∞}
  (via (a), `eval₂_reverse_mul_pow`), hence at p₁ (closure, `subset_closure_inter_of_isPreirreducible_of_isOpen`),
  where it is lc(P)(t) (`eval₂_at_zero`, `coeff_zero_reverse`).
- `imagePlaneCurveClosed_of (hI) (hG'') : ImagePlaneCurveClosed`, `ratFactorAlgClosed_of_irr`,
  `curveFacts_of_glue''`, `curveFacts_of_L0_CI_G1''`, `mobiusGlue_of_L0_CI_G1''_T5`, `mobiusGlueNoCM_of_L0_CI_G1''_T5`.
  All three composite files recompiled: 0 errors, standard axioms (VERIFIED, run_*.txt).
