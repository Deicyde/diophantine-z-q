# tc-survey results log

Task tc-survey (2026-11-13). Read-only survey of Tau Ceti (~/tc-main 4d91513e, Lean v4.36.0-rc2,
2026-11-13; ~/tc-oct16 5a01f5fe, Lean v4.35.0) against the open leaves of
docs/research/h-decomposition.md (base 883c4ddf).

## Leaf status at base (VERIFIED from docs/research/*.md at 883c4ddf)
- Proved elsewhere (not to survey in depth): T2 (t-brauer-purity), T13, T19 (t-skolem-kw),
  T20/T21 local forms, T22a/b (t-different), T32 (glue), T12 (glue target), T30 = glue from T16
  (t30-adelic). T15 real-place conjunct proved (t-brauer-purity).
- In progress elsewhere: T18 (cheb-bridge), T17 (kw-new), T16 (lkw), T20/T21 global (diff-bridge);
  other host: T14, T15, T1, T2, T10, T28.

## Findings
### Tooling
- `scratch/tc-survey/clos.py ROOT MOD...`: closure size + count of modules NOT already vendored on
  origin/wip/kw-new (d639402b; 1162 files under ZInQKernel/Contrib/TauCeti, list in
  `scratch/tc-survey/vendored-kwnew.txt`). VERIFIED: tc-port vendored port1 (397) and 714 oct16
  modules of kw-rest; kw-new vendored the 44 nov01 modules.

### In-progress leaves (brief)
- T18: TC `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet (C : ConjClasses (L ≃ₐ[K] L)) :
  NumberField.Set.HasNaturalDensity (frobeniusPrimeSet K L C) ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L))`,
  oct16 `Chebotarev/PrimeCounting/FrobeniusPrimeCount.lean:108` (VERIFIED read). Leaf `PkgI6.ChebotarevExists`
  (exists p ∉ S unramified, Q | p, IsArithFrobAt σ Q) is a CONSEQUENCE (density > 0 ⇒ infinitely many):
  DIFFERENT OBJECTS (frobeniusPrimeSet vs IsArithFrobAt; bridge = cheb-bridge). Closure oct16: 292
  modules, 57.6k lines, 0 not vendored (VERIFIED, clos.py).
- T17: TC `TauCeti.ClassFieldTheory.kroneckerWeber (E : Type) [Field E] [NumberField E] [IsAbelianGalois ℚ E] :
  ∃ n : ℕ, n ≠ 0 ∧ Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ)` (tc-main ClassFields/KroneckerWeber.lean:178;
  not at oct16). Leaf `KroneckerWeber`: IsGalois + commuting automorphisms, n : ℕ+. SAME up to
  IsAbelianGalois ↔ (IsGalois ∧ commutative) and ℕ+ ↔ n ≠ 0 (cheap bridge). Closure nov01: 949, 0 not
  vendored; main: 1035 modules, 86 not vendored (VERIFIED).
- T20 global: TC `IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one :
  multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) = ∑ᶠ i : ℕ, (Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i) - 1)`
  (oct16 LocalGlobal/Different/Exponent.lean:239). Leaf `GlueConductor.HilbertDifferentFormula`: ∃ n, G_n = ⊥ and exact
  power ∑_{i<n}(|G_i|-1). DIFFERENT OBJECTS (TC ramificationGroup vs leaf `(P^(i+1)).inertia`; finsum vs finite
  sum + existence of n): bridge = diff-bridge. Closure 156 (Exponent+Permutation), 0 not vendored.
- T21 global: TC `multiplicity_differentIdeal_le_ramificationIdx_sub_one_add_multiplicity_span :
  multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) ≤ e - 1 + multiplicity w.asIdeal (span {(e : 𝓞 L)})`
  (oct16 LocalGlobal/Different/Wild.lean:47). Leaf `GlueConductor.SerreDifferentBound`:
  ¬ P^(e-1+e·v_p(e)+1) ∣ D over ℚ. SAME after bridge v_P(e) = e·v_p(e), multiplicity ↔ ∣. Closure Wild:
  177 modules, 11 not vendored (1.2k lines) (VERIFIED).

### Compile check (VERIFIED, 2026-11-13 ~03:35 PST)
- Merged origin/wip/tc-port (f22bb604) for the vendored oct16 modules (no file vendored here).
- `lake build ZInQKernel.HDecomp.Conductor.I6Base ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison`:
  Build completed successfully (9097 jobs).
- `lake env lean scratch/tc-survey/Compare.lean`: exit 0, no errors. Proved:
  - `TCSurvey.h2Equiv K : H2 (Field.absoluteGaloisGroup K) (PkgI6.Z2 K).V ≃+ continuousCohomology 2 (PkgI6.Z2 K)`
    (= TC `TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete`, [CharZero K]; needs a
    `CompactSpace G_K` instance (memory trick), the `DistribMulAction` from `TopRep.distribMulAction`
    given as an explicit instance (instance search does not unify `?X.V` with the abbrev `Z2 K`), and
    `ContinuousSMul` from triviality).
  - `TCSurvey.mem_Z2_iff : (fun q => ε q.1 q.2) ∈ ContCohomology.Z2 G_K (Z2 K).V ↔ PkgI6.IsCocycle2 ε`
  - `TCSurvey.mem_B2_iff : (fun q => ε q.1 q.2) ∈ ContCohomology.B2 G_K (Z2 K).V ↔ PkgI6.IsCoboundary2 ε`
  - `#print axioms`: all three `[propext, Classical.choice, Quot.sound]`.
  Conclusion: TC's degree-2 cochain comparison is exactly the project's cochain convention
  (same d1, d2 formulas, VERIFIED by compile). The cochain leaves T14a′, T14b′, T15′ are equivalent to
  their `continuousCohomology` forms (naturality: TC `explicitH2AddEquivContinuousCohomologyOfDiscrete_map`,
  oct16, for the restriction maps `resC` vs `loc`); this is the WP3 bridge, already vendored.

### Candidate findings (VERIFIED by reading TC source unless marked)
- T25 `PkgI4.NewformOfEigenform`: TC `HeckeRing.GL2.EigenformAwayFromLevel.exists_newform_eigenvalue_eq`
  (oct16 + main, Newforms/Decomposition.lean:222): `∃ M (_ : NeZero M) (hM : M ∣ N) (g : Newform M k), ∀ p prime,
  coprime p N → g.eigenvalue p = f.eigenvalue p`. TC cusp forms are Mathlib `CuspForm ((Gamma1 N).map (mapGL ℝ)) k`.
  Bridges available in TC (oct16): `heckeTNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul`
  (HeckeSlash/Nebentypus/Eigenvector.lean:120, eigen ⇔ coefficient recurrence at good p);
  `Newform.toEigenform`, `toEigenform_eigenvalue_eq_qExpansion_coeff` (FullEigenform), `Eigenform.eigenvalue_mul`,
  `eigenvalue_prime_pow_add_two` (all T_n incl. bad p); `disjoint_cuspFormsOld_cuspFormsNew`; TC old space =
  span of `levelRaise d` images (Newforms/Basic.lean:105), new space = Petersson complement (:202).
  Verdict SAME up to medium bridge. Closure oct16 Decomposition: 216 modules, 204 not vendored (45.6k lines).
- T24 `EigenformTwist`: TC `HeckeRing.GL2.Newform.exists_newform_qExpansion_coeff_prime_eq_twist` (oct16+main,
  Newforms/Twist.lean:59): newform g of level R ∣ L (N·M ∣ L, M·M ∣ L) with a_p(g) = ψ(p) a_p(f), p ∤ L.
  WEAKER: leaf wants a normalized eigenform of ALL T_n at exact level N·m² (needs p-stabilization at primes
  dividing N m²/R; not in TC). Closure oct16 Twist: 219 modules, 207 not vendored.
- T31 `GlueDescent.B2Q.LeafUnramified`: TC `TauCeti.ClassFieldTheory.mk_eq_zero_of_forall_mem_unitFiltration_zero`,
  `brBaseChange_relBrInfl_eq_zero` (oct16 Brauer/Unramified.lean:416, :433; unit-valued cocycles of an unramified
  layer vanish in H²(G_K, (Kˢ)ˣ)) + `h2MuToBr_injective` (Brauer/Torsion.lean:114, H²(μ_n) ↪ Br). DIFFERENT OBJECTS
  (Br vs ±1 sign cocycles into ℂˣ; global L/ℚ vs local layer), medium bridge. Closure: Unramified 253 (0 new),
  Torsion 159 (7 new, 1.6k lines).
- T15 (other host) ℚ_p half: TC `natCard_cohomFp_two_absoluteGaloisGroup_of_isPrimitiveRoot` (oct16
  Brauer/RootsOfUnity.lean:238): `Nat.card (cohomFp n G_F 2) = n` for F a nonarchimedean local field with a primitive
  n-th root of unity; `cohomFp n G := continuousCohomology n (trivialFp n G)`. With ζ = -1, n = 2 and the cochain
  comparison above: DIFFERENT OBJECTS, cheap-medium bridge (trivialFp vs Z2 restricted; ℚ_[p] local-field instances).
  Closure RootsOfUnity oct16: 296 modules, 8 not vendored (1.9k lines).
- T14 (other host): TC main `brLocalization_injective` (Global/Brauer/SumFormula.lean:71; NOT at oct16, where only
  conditional forms exist), `sumLocalInv_brLocalization_eq_zero` (main). DIFFERENT OBJECTS (Br ℚ vs H²(ℤ/2)):
  bridge h2MuToBr + cochain comparison. Closure main SumFormula: 919 modules, 45 not vendored.
- T16b `LocalReciprocityUpper`: TC main `unitFiltration_le_normGroup_iff_upperRamificationGroup_eq_bot`
  (Local/Conductor/UpperNumbering.lean:64; not oct16) is only the kernel-level case; image identity θ''U^v = G^v
  NOT FOUND (grep). WEAKER. `localArtinEquiv` (Local/Reciprocity.lean:85, oct16+main).
- T16a: no local Kronecker–Weber statement in TC main (grep `local.*kronecker` empty); ingredients
  `localAbelianExistence` (LocalExistence/Existence.lean:159), Local/Cyclotomic.lean. Task lkw.
- T1 (other host): TC main `purityHolds_of_ringKrullDim_eq_two` (FiniteEtale/Purity.lean),
  `Algebra.etale_of_isUnramifiedAt_height_eq_one_of_purityHolds` (FiniteEtale/BranchPurity.lean); not at oct16. WEAKER.
- G15 transport (D_P ≅ Gal(L_P/ℚ_p) with filtrations): TC `IsDedekindDomain.HeightOneSpectrum.decompositionEquiv`
  (oct16 LocalGlobal/DecompositionGroup.lean:391), `map_ramificationGroup_decompositionHom` (RamificationGroup.lean:127:
  image of global G_i = local lower G_i), `card_ramificationGroup_eq_card_lowerRamificationGroup` (:139). Closure 114,
  0 not vendored. Krasner's lemma: NOT FOUND as a theorem (only mentioned in docstrings).
- Abelian varieties: TC `AlgebraicGeometry.AbelianVariety` (oct16+main, AbelianVariety/Basic.lean: toOver, GrpObj,
  IsProper, GeometricallyIntegral; smoothness derived) = same data as `PkgI3.AbVar`. Nonzero example: TC main
  `WeierstrassCurve.toAbelianVariety` (EllipticCurve/Scheme/AbelianVariety.lean:65), `dim_toAbelianVariety = 1`,
  `dim_prod_toAbelianVariety = 2`; not at oct16; closure main 342 modules, 325 not vendored.
- Elliptic-only (g = 1) analogues, WEAKER than the leaves (all g): T26 `free_tateModule` (TateModule/Basic.lean),
  T5 `card_ker_mulByIntIsogeny` (Isogeny/MulByInt/IsSepClosed.lean), T9 `tateModuleWeilPairing` (TateModule/WeilPairing.lean),
  R7a `hasGoodReduction_iff_tateModuleGaloisRepresentation_eq_one` (TateModule/GoodReduction.lean, main only),
  R7b `HasPotentialGoodReduction.finite_image_tateModuleGaloisRepresentation` (docstring), T35/T11a g=1 (ComplexTorus,
  Elliptic/Uniformization; main only).
- NOT FOUND (grep of tc-main for the key terms): p-adic Hodge theory (B_dR/de Rham/Hodge–Tate: only manifold de Rham;
  `HodgeTate` 0 files) — T23, R10-R13; Igusa invariants (0 files) — T28, R3; Faltings height (2 hits, both a
  polynomial lemma) — R18-R22, H5; Néron models of abelian varieties, Raynaud, Grothendieck monodromy, Faltings'
  theorems — T3, R6, R8, R9; Poincaré reducibility — T8; Galois reps of eigenforms, Carayol (0 files) — R14-R17;
  Shimura curves/QM — R1-R5; Jacobian existence (Picard representability explicitly not treated) — T33; genus of
  Γ₁(N) — T34; maximal quaternion orders — T29; SemisimpleBaseChange; LeafConj (as stated).

## Deliverables
- docs/research/tc-survey.md (committed), .fleet/tc-survey.md (last commit).
