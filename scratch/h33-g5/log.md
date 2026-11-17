# h33-g5 results log

## 2026-11-17 02:40 start (fresh run; no earlier log)
- TYZ L1179-1181 U0(32), L1183 U (index 2), L1236-1240 P_n = [h,1] in X_U(C), h the fixed point in CH of the
  embedding K_n -> M2(Q) (L1225-1227), L1518-1520: complex uniformization X0(32)(C) = GL2(Q)_+ \ (CH ∪ P1(Q)) x
  GL2(Qhat)/U0(32) (VERIFIED, read).
- Existing tools: Tau Ceti `Matrix.SpecialLinearGroup.map_intCast_zmod_surjective` (SL2(Z)->SL2(Z/d) onto),
  Tau Ceti `IsDedekindDomain.FiniteAdeleRing.{integralAdeles, algebraMap_mem_integralAdeles_iff,
  mul_nonZeroDivisor_mem_integralAdeles, closure_range_algebraMap}` (VERIFIED, read).
- Gamma0QExp: `jf_smul` (SL2(Z)-invariance of j), `jN_smul_of_mem` (Gamma0(N)-invariance of j(N.)) (VERIFIED, read).
- 03:40 VERIFIED (compiled): AdelicX0/StrongApprox.lean: det_U0, sl2_reduction_surjective, lattice_basis(_pos), exists_GLpos_mul_GLZhat, exists_SL2Z_mul, strong_approx (GL2(A_f) = GL2(Q)^+ U0(N), N≠0).
- 03:55 VERIFIED (compiled): Sh U (quotient type), shMap, toSh_eq_toSh_iff, toSh_surjective, gamma0OrbitsEquiv (bijection Γ0(N)\H ≃ GL2(Q)+\(H×GL2(A_f)/U0(N))).
- 05:00 VERIFIED (compiled): CMPoints (UTYZ subgroup, fixed_tyzEmb5_iff/7, tyzP5_eq/7, f0_tyzP5/7), TYZThm33Adelic (TYZThm33AdelicSome, tyzThm33CurveSome_of_adelic, tyzThm33_of_adelic, isPointAt_smul_iff, isShPointAt_toSh_iff, isShPointAt_iff_exists, tyzThm33AdelicSome_iff). Docstring TYZThm33Alg.lean:65 constant 16 -> 8 (task-authorized edit).
- 08:xx VERIFIED: lake build TYZThm33Adelic+Main+Discharges+GrossZagierSplitUnique 14295 jobs OK; FoldCheck: frozenTarget_g5(s) standard axioms; #discharges: [h33] by ZInQ.H33G5.tyzThm33_of_adelic still assumes [T5Glue.ShimuraMainCM, ZInQ.H33G5.TYZThm33AdelicSome], 0 sorry.
- VERIFIED (compiled): §5b G2 analytic: isRatModFnMero_j, isRatModFnMero_jN, x0Field_eq_adjoin_ratFnSh (X0Field N = adjoin ℚ (q-expansions of rational fns on Sh (U0 N))). Final build 14295 jobs OK; FoldCheck/#discharges re-run, standard axioms, 0 sorry.
- Remaining (readings, not Lean): G2 scheme level (canonical model = (X, ι), definitional), G6 sign of [i] incl. f_n = f0 - f0∘[i] read on A; journal version unchecked.
