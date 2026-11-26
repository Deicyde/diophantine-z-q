# rc-model-target results log

## Setup
- Merge of main 29bfbc3f6 into wip/rc-model-neron 64a338f49: commit 11b3db714.
- Item 6 (rc-model-neron.md same-place row): commit 8dee6dc8f.
- Build seed: copy of a prebuilt tree at a later main (3 added files only) plus the neron worktree build.

## Item 4 (generic): RC/ModelTarget/ComplexReading.lean
- IsComplexLaw g : ∀ p q : complexBase ⟶ ellipticTarget E₀, projectiveValue (p*q).left = pv p.left + pv q.left
- exists_complexLaw := J0Cusps.projectiveGroup_exists; complexLaw (choice), complexLaw_spec
- targetReading g hg : (complexBase ⟶ ellipticTarget E₀) →* Multiplicative (E₀.baseChange ℂ).toAffine.Point
- readComplex E jE g hg (hj : IsMonHom jE.hom) := targetReading ∘ IsMonHom.monoidHom jE.hom
- readComplex_eq : (readComplex .. a).toAdd = projectiveValue (a.left ≫ jE.hom.left) (rfl)
- Build OK (13472 jobs), axioms: propext, Classical.choice, Quot.sound.

## Item 4 (local instance): RC/ModelTarget/LocalReading.lean
- neronDVRLocal : NeronExt.NeronDVRLocal := dvrLocal_of_extension (neronSchemeExtensionExists_of_dedekind neronSchemeExtensionDedekind_proof)
- detectorTarget ell E₀ := ModelNeron.localTarget neronDVRLocal
- neronLaw T : GrpObj T.E := grpObjOfNeron … (complexLaw E₀) T.jE (Néron transport)
- neronLaw_isMonHom T : IsMonHom T.jE.hom (isMonHom_of_neron)
- localReadComplex T, localReadComplex_eq T (rfl), localReadComplex_fits
- Build OK (14381 jobs, no warnings in module), axioms standard.
- Note: LocalTarget.groupE is an arbitrary field; the GoodRow supply uses groupE := neronLaw T, not T.groupE.

## Item 1 (smoothness), chart algebra
- ChartRing.lean: Chart W i := Away grading (coord i); chartConst, ratio, ratio_self, dehomogenize,
  chart_equation, chart_ringHom_ext, chartLift (+_mk/_ratio/_const), chartEquiv. Build OK, std axioms.
- ChartPresentation.lean: presLift/presDehom/presEquiv (AdjoinRoot q ≃+* Chart W i);
  zyEquiv : W.toAffine.CoordinateRing ≃+* Chart W 2; zxEquiv : AdjoinRoot (zxPoly W) ≃+* Chart W 2 (monic in x);
  yEquiv hw : AdjoinRoot (yPoly W c w) ≃+* Chart W 1 (shear x = x'+cz; hw : w*(c³+a₂c²+a₄c+a₆) = -1). Build OK, std axioms.
- ChartSmooth.lean: smooth_away_derivative (monic q over R[X], localized at q' : smooth over R via StandardEtalePair),
  smooth_transport, smooth_zy, smooth_zx, span_partials_zChart [W.IsElliptic], smooth_chartZ : RingHom.Smooth (chartConst W 2). Build OK, std axioms.
- ChartSmoothY.lean: yDeriv, derivative_yPoly, yPoly_monic, smooth_ydz hw, span_yChart hw,
  smooth_yChart_awayZ [W.IsElliptic] (overlap D₊(YZ) via Away.isLocalization_mul twice),
  smooth_chartY [W.IsElliptic] hw : RingHom.Smooth (chartConst W 1). Build OK, std axioms.
- WeierstrassSmooth.lean: projStructure W := Proj.toSpecZero ≫ Spec.map gradingZeroEquiv (= weierstrassModel hom);
  coord_zero_cube; iSup_basicOpen_YZ (D₊(Y) ∪ D₊(Z) = Proj); smooth_chart_iff; smooth_projStructure [IsElliptic] hw;
  exists_shear (ℓ ≥ 5: third finite difference 6); **weierstrassModel_smooth h₅ W₀ hΔ :
  Smooth (ModelNeron.weierstrassModel ell (W₀.map (algebraMap ℤ (LocalIntegers ell)))).hom**. Build OK, std axioms.
  Note: Mathlib instance IsZariskiLocalAtSource @Smooth needs `backward.isDefEq.respectTransparency false` outside Mathlib.

## Item 2 (group law), relative chart calculus
- ChartMorphism.lean: evalAway(+_fraction/_algebraMap), chartEval g v hv i hi (+_ratio/_const/_eq_of), chartMorphism,
  chartι_structure, chartMorphism_structure, chartMorphism_smul, chartMorphism_map, chartMorphism_independent,
  eq_chartMorphism (any base-scheme map Spec A → chart is a chart morphism). Build OK, std axioms.
- FieldValue.lean: coord_mem_iff_chart, equiv_of_chartMorphism_eq (same morphism from Spec F ⇒ proportional vectors),
  chartMorphism_eq_of_equiv, exists_chartMorphism, fieldValue (affine point on W.map g), fieldValue_eq,
  fieldValue_chartMorphism, equiv_of_toAffine_eq, fieldValue_injective [W.IsElliptic]. Build OK, std axioms.
- FormulaGluing.lean: fieldValue_congr, pointRing, eq_of_fieldValues (reduced source, separated cubic), Computes, morphism_of_local. OK.
- FormulaMorphism.lean: nonsingular_of_unit_coord, equation_map, morphism_of_formulas (relative J0Cusps formula gluing). OK.
- GroupLaw.lean: cubic W := Over.mk (projStructure W); fieldPt g; val; cubicHom_ext; cubicOne (0:1:0), val_one;
  cubicInv (neg formula), val_inv; addLaws (addXYZ / Tau Ceti dblAddXYZ), cubicMul, val_mul. Build OK, std axioms.
- GroupObj.lean: isReduced_of_smooth_hom (vendored FLT solution: smooth over reduced noetherian ⇒ reduced);
  cubicGrp W hs : GrpObj (cubic W) [noetherian domain, IsElliptic, Smooth]; **weierstrassModelGrp h₅ W₀ hΔ :
  GrpObj (weierstrassModel ell (W₀.map …))**; **weierstrassModel_isNeron h₅ W₀ hΔ : IsNeronModelOver (LocalIntegers ell) ℚ (cubic)**.
  Build OK, std axioms.
- RuleGluing.lean: PointRule, morphism_of_rule (gluing with a field-point rule). OK.
- BaseChange.lean: baseChangeScheme W ψ, bcVec, exists_baseChangeHom (Proj W ×_R S → Proj (W.map ψ)). OK.
  Pitfall: stating values across defeq curves ((W.map ψ).map g vs W.map (g.comp ψ)) in a calc caused whnf timeouts; use vectors (toAffine of bcVec) instead.
- BaseChangeInv.lean: structR, invVec, chart_equation_self/comp, exists_baseChangeInvHom (Proj (W.map ψ) → Proj W over ψ). OK.
- BaseChangeIso.lean: **bcIso W ψ : (Over.pullback (Spec.map ψ)).obj (cubic W) ≅ cubic (W.map ψ)** (identity in coordinates),
  under [W.IsElliptic] [(W.map ψ).IsElliptic] [IsReduced (baseChangeScheme W ψ)] [IsReduced (Proj (W.map ψ))]. Build OK, std axioms.
- DetectorModel.lean: detW, exists_detShear, smooth_mapped, reduced_mapped, reduced_baseChange, detFibreIso ψ,
  detW_map_eq, **detGenericIso : (generic R ℚ).obj (weierstrassModel ell (detW)) ≅ ellipticTarget (W₀⁄ℚ)**,
  detProperGeneric, detGeomIntGeneric (transport from J0Cusps.projectiveAbVar via jE). Build OK, std axioms.
- PullbackMul.lean: upHom, mul_left_fst ((a*b).left ≫ fst = (lift a↑ b↑ ≫ μ).left for Over.pullback). OK.
- Link found: PMWire.Assembly fixes E₀ = (EcurveZ ℓ)⁄ℚ, Ebar = ReducedEquation (EcurveZ ℓ) p; stage primes satisfy
  ¬ p ∣ (EcurveZ ℓ).Δ (StageWitness.stage_facts, RC/Wiring/StageWitness.lean:141).
- Read.lean: pointCongr, pointCongr_toAffine, map_toAffine (Point.map σ ∘ toAffine = toAffine ∘ σ), detE, resRing, special,
  resRing_curve, residue_structure, residueIso, resUp, readFun, readFun_mul. OK (compile ~10 min).
- ReadEquiv.lean: readFun_eq, readFun_injective, readFun_surjective, **read h₅ hΔ : (residueSource ℓ K ⟶ special.obj E) ≃*
  Multiplicative ((ReducedEquation W₀ ℓ)⁄K).Point**, read_apply, **read_frob**. Build OK, std axioms.
- CubicComplex.lean: projectiveValue_eq_fieldValue (J0Cusps value = fieldValue on Proj E₀), fieldValue_eqToHom, complexRing,
  complexIso, complexUp, complex_curve, bcEq_value, detRational_isElliptic, cubicJE (= detGenericIso's composite, unfolded),
  projectiveValue_cubicJE, **readComplexCubic h₅ hΔ** (monoid hom), **readComplexCubic_eq** (rfl vs projectiveValue ∘ cubicJE).
  Build OK, std axioms. Pitfall: unifying detGenericIso with its bcIso composite timed out; use the composite (cubicJE) directly.
- Supply.lean: GoodTarget (exactly the target-side GoodRow fields with closed := ModelNeron.closed ℓ);
  **goodTarget ℓ W₀ K h₅ hΔ : GoodTarget ℓ K (ReducedEquation W₀ ℓ) (W₀⁄ℚ)** (all fields from the cubic);
  GoodTarget.toGoodRow (assembles PMWire.GoodRow from it plus M/source/point/extension/point_W/point_frob/frobenius_sq).
  Build OK (13591 jobs), std axioms.
