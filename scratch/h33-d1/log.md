# h33-d1 log

- 11-17 01:10 start; merged 92fd272e (hgz-steps) cleanly into wip/h33-d1 (943889a87).
- Plan (design decision): new leaf `ZInQ.H33D1.TYZThm33Curve` over integral proper `X/ℚ` with
  `ι : K(X) ≃ X0Field 32` and an ISOMORPHISM of schemes `i₀ : X ⟶ ESch curveA` over ℚ with `i₀(∞) ∉ D₊(Z)`,
  CM points as ℂ-points `IsPointAt 32 ι τ_n`, values `GZSch.ptOf curveA (x ≫ i₀)`. Normality/dim of X omitted:
  `X ≅ A` forces X to be the smooth projective curve with function field ℚ(X₀(32)), i.e. the canonical model
  (reading, Hartshorne I.6.12, UNVERIFIED number).
- Bridge strategy: X := ESch curveA, i₀ := 𝟙, ι := φ ∘ ffEquiv. Avoids valuative extension and normality of
  ESch (the valuative-extension route needs ESch curveA normal over ℚ to invert π; Dedekind property of
  ℚ[x,y]/(W) is vendored only over algebraically closed fields). Needs: ESch integral, K(ESch) ≅ ℚ(E) via
  chart D₊(Z), values at ℂ-points via charts D₊(Z), D₊(Y) (Z/Y = 1/y vanishes at O).
- 11-17 01:55 RETARGET adopted. Charts.lean draft (from the interrupted run) does NOT compile (≈15 errors); to be fixed.
- 11-17 02:00 VERIFIED (compiled, `lake env lean`): `ZInQKernel/Contrib/OneProof/CurveModelUnique.lean`:
  `ZInQ.CurveModel.exists_iso_of_functionField` (X, Y integral, proper over ℚ, stalks valuation rings,
  e : K(X) ≃ K(Y) ⇒ ∃ f : X ⟶ Y iso with Spec K(X) → X → Y = Spec(e⁻¹) ≫ Spec K(Y) → Y),
  `ext_of_fromSpecFunctionField` (uniqueness), `algebraMap_stalkMap` (stalk maps induce c on K).
- 11-17 02:15 VERIFIED (compiled): `ZInQKernel/Contrib/OneProof/GrossZagierModelUnique.lean`: transport lemmas
  `isCuspInfty_map`, `isPointAt_comp`; `gzModelBody_transfer`; new leaf `ZInQ.GZUnique.GrossZagierCurveCdSome`
  (GZ on SOME normal proper model of X₀(N)); `grossZagierCurveCd_of_some`, `grossZagierAlgOptCd_of_some`.
  S1 discharged: the ∀-model leaf follows from the ∃-model leaf in Lean.
- 11-17 02:00 VERIFIED (compiled, axioms standard): `TYZThm33Curve/Charts.lean` (ESch E integral,
  `ffEquiv : K(ESch E) ≃ ℚ(E)`, `azEquiv : A_(Z) ≃ ℚ[x,y]/(W)`, G4(b) `mem_basicOpen_Y_of_not_mem_Z`) and
  `TYZThm33Curve/Normal.lean`: `valuationRing_stalk_ESch [E.IsElliptic] : ∀ p, ValuationRing 𝒪_{ESch E,p}`
  (D₊(Z): localization of the Dedekind domain ℚ[x,y]/(W); off D₊(Z): chart D₊(Y), prime ⊇ (u,v) = it,
  v·w = u³ with w ≡ 1, maximal ideal (u), noetherian local domain ⇒ valuation ring).
- 11-17 02:15 VERIFIED (compiled): `ZInQKernel/Contrib/OneProof/TYZThm33Curve.lean`: leaf
  `ZInQ.H33D1.TYZThm33CurveSome` (∃ normal proper model (X, ι) of X₀(32) s.t. for every iso i₀ : X ⟶ ESch curveA
  over ℚ with i₀(∞) ∉ D₊(Z), w n = ptOf(x ≫ i₀) at the points τ_n ⇒ TYZThm33EpsAfter), `TYZThm33Curve` (∀ models),
  `tyzThm33CurveSome_of_all`, `exists_iso_of_phi` (D1 both directions via model uniqueness + ESch normal),
  `tyzThm33Alg_of_curveSome`, `tyzThm33_of_curveSome`.
- 11-17 02:35 merged origin/wip/eps-splitting (5e3d65de; only its own Lean files + main's docs/.github changes).
  VERIFIED (compiled): `GrossZagierSplitUnique.lean`: leaf `ZInQ.GZSplitUnique.GrossZagierCurveCdSplitSome`
  (one model + split twist), `gzSplitBody_transfer`, `grossZagierAlgOptCd_of_splitSome`;
  `GrossZagierModelUnique.model_transfer` (inverse isos, cusp/point transport both ways).
- 11-17 02:40 VERIFIED (compiled): `TYZThm33Curve.lean` §5 `tyzThm33Curve_of_some` (∃ ⇒ ∀ models),
  `tyzThm33Curve_hyps_satisfiable` (given hCM, on every model). Normal.lean §5 G4(b):
  `not_mem_chartZ_iff : p ∉ D₊(Z) ↔ p = ptO E` (ptO = chartY(ker χ_O), χ_O = evaluation at [0:1:0]),
  `eq_ker_chiO`. Leaf cusp condition restated as `i₀ p = ptO curveA` (i₀(∞) = O literally).
- 11-17 02:30 VERIFIED: FoldCheck.lean (frozenTarget_d1, frozenTarget_d1s recommended, rfl-equalities,
  std axioms); #discharges: [h33] by H33D1.tyzThm33_of_curveSome (assumes ShimuraMainCM, TYZThm33CurveSome);
  [hGZ] by GZSplitUnique.grossZagierAlgOptCd_of_splitSome (assumes GrossZagierCurveCdSplitSome);
  [hGZ] by GZUnique.grossZagierAlgOptCd_of_some. 0 sorry.
- 11-17 02:45 scratch copies of the final Contrib files (the interrupted run's non-compiling drafts Charts.lean/TYZThm33Curve.lean replaced); build-deps.txt (stale) removed. The compiled versions are the ones under ZInQKernel/Contrib/OneProof/.
- 11-17 03:00 report and fleet note written; final.
