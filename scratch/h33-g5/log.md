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
