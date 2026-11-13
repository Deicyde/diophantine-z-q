# hecke-rest results log

Base: wip/hecke-rest (b7cdba8e) + merge of origin/wip/ts-hecke. Targets (verbatim in
scratch/ts-hecke/TSHecke.lean): CurveGaloisChart (via CurveNormChart), CurveChartInf,
HeckeFibreSizes, HeckeNoVertRam.

## Step 0. Kernel oleans
- `lake build ZInQKernel.HDecomp.QM.Pin ZInQKernel.HDecomp.Descent.B2Glue
  ZInQKernel.HDecomp.Textbook.SkolemNoether`: built (9057 jobs), VERIFIED.

## Step 1. Computation for HeckeFibreSizes (`fibre_sizes.py`, output `fibre_sizes.out`) — VERIFIED (computed)
- |O/3O| = 81, |(O/3O)^x| = 72 = #{nrd ≢ 0 mod 3}.
- CM elements in O: x^2 = -1 (e.g. (-1,-1,2,0)), x^2 - x + 1 = 0 (e.g. (-1,-2,3,1)), x^2 = -6
  (e.g. (-2,-2,4,1)); unit groups of orders 4, 6, 2.
- No nontrivial finite-order unit is ≡ 1 mod 3O (nrd(g-1) ∈ {1,2,3,4}; 9 | nrd of 3O).
- Right multiplication by these unit groups on (O/3O)^x is free: 18, 12, 36 orbits.
- Elliptic μ ∈ O of norm m ∈ {2,3,6}, trace t (t^2 < 4m): the field Q(sqrt(t^2-4m)) embeds in B
  only for (m,t) = (2,2) [Q(i)], (3,0),(3,3) [Q(sqrt-3)], (6,0) [Q(sqrt-6)]; Q(sqrt-2),
  Q(sqrt-7), Q(sqrt-11), Q(sqrt-5), Q(sqrt-15), Q(sqrt-23) do not embed (2 or 3 splits).
- tt_k * tt_l is a rational multiple of tt_(k xor l) (W = (Z/2)^2).
- Sizes r*72/a: generic 4*36 = 144; CM4 2*18 = 36; CM3 2*12 = 24; CM24 2*36 = 72; 144 divides
  4*36, 6*24, 2*72.

## Step 2. Lean: HeckeFibreSizes (`FibreSizes.lean`, assembled by `assemble.py`) — VERIFIED (compiled, 0 errors, ~20 s)
- Verbatim copies from TSHecke.lean: 3563-4606 (aut-o-finite), 5511-5717 (Units), 6132-6135
  (twistFibre), 6154-6213 (Count), 6215-6227 (exists_sub_liftO), 6553-6577 (HeckeFibreSizes).
- New leaves (defs, docstrings with sources): `QMAutCard` (|Aut(A,ι)| = 4/6/2 by CM type, CM
  types exclusive), `SerreRigidity3` (finite-order endomorphism fixing A[3] is 1),
  `ALFixedPoints` ((A, ι∘t_m) ≅ (A, ι) for m = 1,2,3 ⇒ CM by Z[i], Z[ζ3], Z[√-6]).
- Proved: `lvEquiv : Good ≃ Level3 P.q` (72 level structures, from TorsionStructure),
  `rep_rep : rep k (rep l a) = rep (xr k l) a`, `push_injective` (Serre), `fibre_card`
  (each fibre of (k,c) ↦ class has s·a elements), `ncard_mul : #twistFibre · s · a = 288`,
  `heckeFibreSizes_of : TorsionStructure → QMAutCard → SerreRigidity3 → ALFixedPoints →
  HeckeFibreSizes` (M = 144).
- `#print axioms`: heckeFibreSizes_of, ncard_mul: [propext, Classical.choice, Quot.sound].

## Step 3. Lean: HeckeNoVertRam (`NoVert.lean`, assembled by `assemble.py`) — VERIFIED (compiled, 0 errors, ~15 s)
- Verbatim copies from TSHecke.lean: 6-889 (prop-ts prefix: NoVerticalRam, intPolyAlg,
  vertPrime, NormalizationModel), 3427-3437 (HeckeNoVertRam, inside namespace PropTSGlue).
- Proved: `ramIdx_eq_of_under_eq` (Galois E/F, A integrally closed domain with Frac A = F: two
  primes of integralClosure A E over the same prime have equal ramificationIdx; via
  IsGaloisGroup.of_isFractionRing, Algebra.IsInvariant.exists_smul_of_under_eq,
  Ideal.ramificationIdx_smul), `isFractionRing_int` (ℚ(X) = Frac ℤ[X]),
  `noVerticalRam_of_witness : VertUnramWitness E p → NoVerticalRam E p` (Galois E),
  `heckeNoVertRam_of_witness : HeckeVertWitness → HeckeNoVertRam`.
- New glue Prop `HeckeVertWitness` (one prime over pℤ[X] with e = 1, p > 324), with routes GR and
  NV in its docstring.
- `#print axioms` (3 lines): [propext, Classical.choice, Quot.sound].

## Step 4. Review of Steps 2-3 (read-only model agent, no Lean)
- Verdict: QMAutCard, SerreRigidity3, ALFixedPoints TRUE as stated, consequences of published
  results, not vacuous, not disguised; count n·s·a = 288 and case analysis correct.
- Citation fix applied: Serre leaf cites the finite-order form (Silverberg–Zarhin JPAA 111 (1996),
  UNVERIFIED); Mumford §21 Thm 5 is the polarized form.
- HeckeVertWitness is EQUIVALENT to HeckeNoVertRam (lying over gives a prime over pℤ[X]), not
  strictly weaker: a reduction of shape (one prime instead of all), not of content.
- Caveat raised: the coordinate X must be the canonical one (X = p·j would ramify vertically);
  R2fp pins π's values 0, ∞, −16/27 at the three CM types, and π induces Y/Γ' ≅ P¹, so π is the
  canonical coordinate up to a Möbius map fixing three points, i.e. exactly (SPECULATIVE
  argument, not formalized).

## Step 5. Lean: CurveNormChart (`CurveChart.lean`, assembled by `assemble.py`) — VERIFIED (compiled, 0 errors, ~15 s)
- Verbatim copies: TSHecke.lean 6-889 (prop-ts prefix) and 6444-6455 (CurveNormChart);
  image-plane AlgDepProof.lean 15-171 and 277-322 (value calculus ptOf/ev/ev_comp/ev_spec_top/
  val_of_mem/val_of_not_mem).
- New glue Props: `ChartFinite` (π.U nonempty affine, ℚ[X] → Γ(Y, π.U) injective and finite, X ↦ π.f),
  `ChartNormal` (nonempty affine opens of a smooth irreducible curve have integrally closed
  domain sections).
- Proved: `ev_fromSpec` (value of a section at Spec χ → Spec Γ(X,U) → X is χ s),
  `curveNormChart_of : ChartFinite → ChartNormal → CurveNormChart` (E = Frac Γ(Y, π.U),
  Γ(Y, π.U) ≅ integralClosure ℚ[X] E by IsIntegralClosure.equiv, FiniteDimensional via
  IsIntegralClosure.isLocalization + Module.Finite.of_isLocalization).
- `#print axioms HeckeRestCurve.curveNormChart_of`: [propext, Classical.choice, Quot.sound].

## Step 6. Lean: CurveChartInf and normality (`CurveChart.lean`) — VERIFIED (compiled, 0 errors, ~35 s)
- Added verbatim copies: TSHecke.lean 6526-6551 (NormalizationModelInf,
  CurveChartInf), 4613-5002 (infra-smooth-dim stalk dimensions), 5010-5173 (curve-glue CI copy).
- New glue Props: `ChartFiniteInf` (π.V affine, ℚ[s] → Γ(Y, π.V), s ↦ π.g, injective and
  finite), `InfFnField` (E is the fraction field of Γ(Y, π.V) via a map with π.g ↦ 1/X).
- Proved: `curveChartInf_of : ChartFiniteInf → ChartNormalD → InfFnField → CurveChartInf`;
  `loc_max_dvr` (localizations of Γ(Y,U) at maximal ideals are integrally closed domains);
  `chartNormalD`, `curveSectionsDomain`, `chartNormal` (both normality Props are theorems);
  `curveNormChart_of' : ChartFinite → CurveNormChart`;
  `curveChartInf_of' : ChartFiniteInf → InfFnField → CurveChartInf`.
- `#print axioms` (5 lines): [propext, Classical.choice, Quot.sound].

## Step 7. Lean: ChartFinite(Inf) from proper + quasi-finite + dominant (`CurveChart.lean`) — VERIFIED (compiled, 0 errors)
- `secHom Y W s : ℚ[X] →+* Γ(Y, W)` (X ↦ s), `secMor Y W s : W ⟶ Spec ℚ[X]`.
- Proved: `finite_of_proper_qf` (IsProper + LocallyQuasiFinite secMor ⇒ W affine and
  Γ(Y,W) module-finite; via IsFinite.of_isProper_of_locallyQuasiFinite, isAffine_of_isAffineHom,
  IsFinite.SpecMap_iff), `chartFinite_of`, `chartFiniteInf_of`,
  `curveNormChart_of_charts : ChartProper → ChartQuasiFinite → ChartDominant → CurveNormChart`,
  `curveChartInf_of_charts : ChartProper → ChartQuasiFinite → ChartDominant → InfFnField →
  CurveChartInf`.
- New glue Props: `ChartProper` (both charts IsProper), `ChartQuasiFinite` (both
  LocallyQuasiFinite), `ChartDominant` (π.U nonempty, both ring maps injective).
- `#print axioms`: [propext, Classical.choice, Quot.sound].
- FIX (self-review): `ChartFiniteInf` and `ChartDominant` as first written were FALSE for
  `Y = ∅` (Γ(Y, V) = 0, so injectivity and nonemptiness fail; all other hypotheses hold).
  Both now assume `Nonempty Y.left`; `curveChartInf_of` derives it from `NormalizationModel`
  (Spec B ≠ ∅ maps into Y). Recompiled: 0 errors, standard axioms.

## Step 8. Integrated file (`HeckeRestAll.lean`) — VERIFIED (compiled, 0 errors, 46 s)
- TSHecke.lean (all 7109 lines) + image-plane value calculus + the three `*Main.lean.part`
  files + `AllMain.lean.part`; verbatim by construction (`assemble.py` copies line ranges).
- `HeckeRestAll.coverModelOfHecke_of_heckeRest` : Y3Connected → R1R2fp → TorsionStructure →
  QMAutCard → SerreRigidity3 → ALFixedPoints → ChartProper → ChartQuasiFinite → ChartDominant →
  InfFnField → HeckeVertWitness → CoverModelOfHecke.
- `HeckeRestAll.propTSAll_of_heckeRest` (same, through propTSAll_of_tsHecke').
- All 14 HeckeRest* `#print axioms` lines: [propext, Classical.choice, Quot.sound]. The token `sorry`
  occurs only in comments.

## Step 9. Lean: InfFnField proved from ChartFiniteInf + ChartIrreducible (`InfFnMain.lean.part`, in `CurveChart.lean`) — VERIFIED (compiled, 0 errors)
- Added verbatim copy TSHecke.lean 5725-5858 (TSHeckeGal: exists_qbar_point, eq_of_forall_qbar).
- New glue Prop `ChartIrreducible` (a proper smooth curve with finite π-fibres and a chart over
  𝔸¹ is irreducible).
- Proved: `range_chart_eq` (range of the chart = π⁻¹(𝔸¹), Jacobson), `app_f_eq` (h^*π.f = X,
  separation by ℚ̄-points), `infCoord_injective`, `res_appLE`, `appLE_res`, `loc_helper`,
  `infFnField_of : ChartFiniteInf → ChartIrreducible → InfFnField` (φ = Γ(Y,V) → Γ(Spec B, D(X))
  = B[1/X] → E; injective by incomparability over ℚ[s]; fractions via h.appIso and the
  localization Γ(Y, D(g)) = Γ(Y,V)[1/g]), `curveChartInf_of_charts' : ChartProper →
  ChartQuasiFinite → ChartDominant → ChartIrreducible → CurveChartInf`.
- Composite updated (`AllMain.lean.part`): InfFnField replaced by ChartIrreducible.
  `HeckeRestAll.lean` recompiled: 0 errors; 16 HeckeRest* `#print axioms` lines, all
  [propext, Classical.choice, Quot.sound].

## Step 10. Lean: ChartIrreducible and ChartDominant proved (`PointsMain.lean.part`) — VERIFIED (compiled, 0 errors)
- Proved: `not_isOpen_closed_point` (no closed point of a smooth curve is open: stalk dimension 1
  vs. Spec of the stalk a single point via range_fromSpecStalk and the preimmersion
  fromSpecStalk), `infinite_closedPoints_of_isOpen` (Jacobson), `infinite_qbar_points`,
  `chartIrreducible` (chart image dense, closure of irreducible), `ev_secHom`,
  `mem_roots_of_eval₂`, `chartDominant` (π.U ≠ ∅, π.V ≠ ∅, no polynomial relation for π.f, π.g:
  values in a finite set on infinitely many ℚ̄-points contradict finite fibres),
  `curveNormChart_of_pq : ChartProper → ChartQuasiFinite → CurveNormChart`,
  `curveChartInf_of_pq : ChartProper → ChartQuasiFinite → CurveChartInf`.
- Composite updated: `coverModelOfHecke_of_heckeRest` now takes only ChartProper and
  ChartQuasiFinite on the curve side. `HeckeRestAll.lean` recompiled: 0 errors; 20 HeckeRest*
  `#print axioms` lines, all [propext, Classical.choice, Quot.sound].
