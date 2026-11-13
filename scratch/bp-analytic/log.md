# bp-analytic results log

## 2026-11-12

- Torus.lean §1 (charts, manifold): `exists_gap`, `eventuallyEq_add_const`, `contDiffOn_of_sub_mem`,
  `Torus`, `proj`, `proj_eq_iff`, `isAddQuotientCoveringMap_proj`, `isCoveringMap_proj`,
  `isLocalHomeomorph_proj`, `chartOf` (+ API), `ChartedSpace E (Torus Λ)`, `transition_sub_mem`,
  `IsManifold 𝓘(ℂ, E) ω (Torus Λ)`. COMPILED (lake env lean, 1m13s, warnings only).
- Mathlib facts used (VERIFIED by reading .lake/packages/mathlib): `AddSubgroup.isAddQuotientCoveringMap_of_comm`
  (Topology/Covering/Quotient.lean), `IsLocalHomeomorph.localInverseAt` (Topology/IsLocalHomeomorph.lean),
  `isManifold_of_contDiffOn` (Geometry/Manifold/IsManifold/Basic.lean). Mathlib's
  `Geometry/Manifold/Instances/Quotient.lean` gives only a `ChartedSpace` on `orbitRel.Quotient`; its TODO
  is exactly the `IsManifold` instance built here.
- Torus.lean §2-3: `contMDiff_proj` (proj analytic), `contMDiff_of_comp_proj`, `contMDiff_of_comp_proj₂`
  (descent of C^n maps along proj), `lieAddGroup_torus : LieAddGroup 𝓘(ℂ, E) ω (Torus Λ)`,
  `connectedSpace_torus`, `compactSpace_torus` (full lattice), `AddGroupLieAlgebra 𝓘(ℂ,E) (Torus Λ) = E` (rfl),
  `torusExp : E →+ Torus Λ`, `torusExp_surjective`, `ker_torusExp : ker = Λ`, `contMDiff_torusExp`,
  `contMDiff_torusExp_smul` (one-parameter subgroups analytic), `holomorphic_const` (Liouville on the torus,
  from Mathlib `MDifferentiable.exists_eq_const_of_compactSpace`). COMPILED, no errors/warnings;
  `#print axioms` on isManifold_torus, lieAddGroup_torus, compactSpace_torus, holomorphic_const, ker_torusExp,
  contMDiff_torusExp_smul: [propext, Classical.choice, Quot.sound].
- Torus.lean §4 (Siegel period lattice): `SiegelSpace g`, `periodVec`, `periodVec_linearIndependent`
  (needs only det Im Ω ≠ 0), `card_periodIndex`, `periodBasis`, `periodLattice Ω hΩ` (= Ωℤ^g + ℤ^g), its
  `DiscreteTopology`/`IsZLattice ℝ` instances (from Mathlib's ZSpan instances), `det_im_ne_zero_of_mem_siegelSpace`,
  `mem_periodLattice_iff`, `SiegelTorus` with LieAddGroup/CompactSpace by inferInstance. COMPILED.
- Torus.lean §5 (theta): `intVec`, `riemannTheta`, `riemannTheta_add_int`, `riemannTheta_add_mulVec`
  (θ(z+Ωm) = exp(-πi mᵀΩm - 2πi mᵀz) θ(z) for Ωᵀ = Ω), `riemannTheta_add_period`, `thetaChar`,
  `thetaChar_eq` (θ[c,d](Ω) = exp(πi cᵀΩc + 2πi cᵀd) θ(Ωc+d, Ω)), pkg-I1 `thetaConst` copied verbatim,
  `thetaConst_eq_thetaChar`, `thetaConst_eq_riemannTheta`, `two_nsmul_proj_charPoint` ((Ωa+b)/2 is 2-torsion
  on ℂ²/Λ_Ω). All by tsum reindexing (Equiv.tsum_eq, tsum_mul_left): no convergence hypothesis. COMPILED,
  no errors, no warnings.
- Torus.lean §6: `torusAddEquiv` (T : E ≃L[ℂ] E' with T(Λ) = Λ' gives E/Λ ≃+ E'/Λ'), `torusAddEquiv_proj`,
  `torusAddEquiv_symm_proj`, `torusDiffeo : Torus Λ ≃ₘ^ω⟮𝓘(ℂ,E), 𝓘(ℂ,E')⟯ Torus Λ'` (biholomorphic), `torusDiffeo_apply`.
  COMPILED, no warnings.
- Torus.lean §7 (pkg-I1 QM lattice; pkg-I1 defs B, oBasis, Mi, Mj, iota, latVec, Emat, F0mat, Pinv, Omega
  copied verbatim): `latVec0..3` (explicit: (τ,1), (√2τ,−√2), ((τ−3)/2,(τ+1)/2), (√2(τ−3)/2, −√2(τ+1)/2)),
  `Emat_eq`, `F0mat_eq`, `Fp`, `det_Fp` (= −√2(τ−3)(τ+1)/2), `det_Fp_ne_zero` (Im τ ≠ 0), `Fp_mul_Omega`,
  `qmVec`, `qmVec_linearIndependent` (over ℝ, Im τ ≠ 0), `qmBasis`, `qmLattice` (+ DiscreteTopology, IsZLattice),
  `qmLattice_eq`, `QMTorus` (LieAddGroup, CompactSpace by inferInstance), `Fp_mulVec_periodVec(')`, `imgVec`,
  `det_im_ne_zero_of_linearIndependent` (generic converse of §4), `imgVec_linearIndependent`, `span_imgVec`,
  `FpEquiv`, `det_im_Omega_ne_zero`, `map_periodLattice_Omega` (F'(τ)(Ω(τ)ℤ²+ℤ²) = ι(𝒪)(τ,1)ᵀ),
  `qmPeriodDiffeo : SiegelTorus (Omega τ) _ ≃ₘ^ω QMTorus hτ`, `qmPeriodDiffeo_add`, `qmPeriodDiffeo_proj`.
  COMPILED, no warnings; axioms [propext, Classical.choice, Quot.sound] for qmPeriodDiffeo(_add),
  det_im_Omega_ne_zero, torusDiffeo, thetaConst_eq_riemannTheta, riemannTheta_add_period, two_nsmul_proj_charPoint.
- sympy (VERIFIED, computed): Ω(τ) symmetric; det Im Ω(x+iy) = 12y²/(((x−3)²+y²)((x+1)²+y²)) > 0 for y ≠ 0.
