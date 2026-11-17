# gzopt-dict results log

Base: wip/period-odd 6382ef59, merged origin/main e41a7169 (merge 812b36c0). Build tree copied from the period-odd worktree.

## Statements (ZInQKernel/Contrib/OneProof/GrossZagierAlgebraic.lean, namespace ZInQ.GZAlg)
- Model of Q(X0(N)): vendored FLT `ModularCurve.modularFunctionField N` = Q(jq, jq(q^N)) ⊂ LaurentSeries Q (abbrev `X0Field`).
- `HasQExp X x`: X(τ) = Σ_{m∈ℤ} x_m q^m for Im τ > T.
- Leaf `Gamma0QExpansion`: IsRatModFnMero N g → HasQExp g x → x ∈ X0Field N (Shimura 1971 Prop 6.9, UNVERIFIED).
- Leaf `GrossZagierAlgOptAt E`: φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N, ord φ(x) < 0, X Y meromorphic with q-expansions φ(x), φ(y), IsOptimalParam, rest as GZOptimal.GrossZagierModuliOptAt.
- `GrossZagierAlgOptCd` (restriction to short models in the isogeny class of C_d).
- compile: `lake env lean` OK, no errors (VERIFIED).
- §2 algebra (aeval_ne_zero_of_order_neg, psi0, psi0_injective via Ideal.eq_bot_of_under_eq_bot, phiOf via IsFractionRing.liftAlgHom, eval₂_polynomial_of_wEq): compiles (VERIFIED). Pitfall: Algebra ℚ (LaurentSeries ℚ) diamond between IntermediateField's instance and default; bridge with Subsingleton.elim on ℚ →+* L.
- §3 analysis (le_radius, regularAt_of, hasQExp_laurentOf, tay_weq, tay_eq_zero_of_punctured, wEq_laurent, wEq_of, order_neg_of) and §4 bridge (grossZagierModuliOptAt_of_alg, grossZagierModuliOptCd_of_alg, grossZagierFormulaCd_of_alg): whole file compiles with lake env lean, no errors/warnings (VERIFIED, 11-16 ~16:40).
- §5 sanity (hasQExp_j, scaleN, hasQExp_jN: generators of X0Field are q-expansions of E4^3/Δ at τ and Nτ): compiles (VERIFIED).
- Build: `lake build ZInQKernel.Contrib.OneProof.GrossZagierAlgebraic ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ...HeegnerPointRationalCd ...GrossConjugationCd`: completed, 13752 jobs, 25m47s (VERIFIED).
- AxMain.lean + MainEdit.lean (out_axioms.txt): grossZagierModuliOptAt_of_alg, grossZagierModuliOptCd_of_alg, grossZagierFormulaCd_of_alg, wEq_of, order_neg_of, phiOf_genX, aeval_ne_zero_of_order_neg, frozenTarget_gzoptdict: [propext, Classical.choice, Quot.sound] (VERIFIED).
- #discharges (discharges-output.txt): 56 open hypotheses, 3984 theorems checked, 10 discharge one; none by GZAlg — expected: hL3 is a frozenTarget argument for all E, the fields grossZagierModuliOptCd / grossZagierFormulaCd exist only after the C_d split is folded (VERIFIED).
- autofold.py --dry-run: autofold.json -> "not a field of the current bundles: ['grossZagierModuliOptCd']"; autofold-formula.json -> same for grossZagierFormulaCd (VERIFIED; expected, as for period-odd).
- Helper ZInQKernel/Contrib/OneProof/GrossZagierAlgebraic/X0Model.lean: `ker_evJ` (ker of ℚ[X][Y] → ℚ((q)), (X,Y) ↦ (jq, jq(q^N)) is (Φ_N), any ModularPolynomialData N) and `nonempty_ringEquiv_fractionRing` (X0Field N ≃+* FractionRing (ℚ[X][X] ⧸ (Φ_N))). Inputs: vendored finrank_adjoin_jqN_eq_dedekindPsi, aeval_jqN_toAdjoin; jq transcendental (order −1). lake build OK; axioms standard (out_axioms_model.txt) (VERIFIED). Kept out of the main file because the vendored theorem modules set global `attribute [-instance]/[-simp]`.
