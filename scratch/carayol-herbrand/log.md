# carayol-herbrand log

- 2026-11-17 00:10 start; merged origin/main (c40109f3) into wip/carayol-herbrand (bae8f7dc), no conflicts.
- VERIFIED (read): `Swan.swanIntegral_proved : LadicCond.SwanIntegral`, `Swan.swanIndependent_proved`,
  `Swan.adaptedExists_proved` are theorems in ZInQKernel/OneProof/H/TailB.lean (namespace HDec, l. 6990-7004),
  from `PkgI6.herbrandQuotient` (Herbrand's theorem, proved in Contrib/Different/Local.lean).
  `Swan.swanAtIntegral` (finite-level change of variables), `Swan.upperAbsWild`, `Swan.upperAbsSurj_of_herbrand`
  hold for every coefficient field k; `AdaptedExists` is stated only for coefficients `PadicAlgCl ℓ`.
- Mathlib has `instNormedFieldValuedAdicCompletion` (FinitePlace.lean:162, uniform structure = Valued's) and
  `FinitePlace.norm_lt_one_iff_mem`.
- Plan: (1) generalize `adaptedExists` to ultrametric normed coefficient fields with ‖ℓ‖ < 1 (K_λ);
  (2) prove condExp = codim V^I + ∫₀^∞ codim V^{G^u} du for continuous ρ : G_{Q_p} → GL_n(K_λ), p ≠ ℓ;
  (3) DDT-form leaf CarayolThmAIrrDDT ↔ CarayolThmAIrr; discharge r17.
- VERIFIED (read): Mathlib v4.35 `Mathlib/RingTheory/Valuation/RamificationGroup.lean` has only
  `decompositionSubgroup` and `inertiaSubgroup` ("TODO: Define higher ramification groups in lower numbering");
  no Herbrand function, no upper numbering. Higher ramification groups available: Tau Ceti vendored
  `Contrib/TauCeti/NumberTheory/LocalField/RamificationGroup.lean` (lowerRamificationGroup), the kernel's
  `LadicCond.ramSet/phiAt/upperSet/upperAbs`, Herbrand's theorem in `Contrib/Different/Local.lean`.
- VERIFIED (read): LadicCond's `phiAt L u = ∫₀ᵘ g_t/g_0 dt` with `g_t = |G_{⌈t⌉}|` (Serre IV §3 φ), `upperSet L v =
  G_{ψ(v)}` with ψ(v) = sInf{u ≥ -1 | v ≤ φ(u)}, `upperAbs p v` = σ with σ|_L ∈ G^v(L) for all finite Galois L.
- COMPILED: ZInQKernel/Contrib/OneProof/CarayolHerbrand.lean (lake build OK, 6.4 s for the file; no warnings after
  cleanup). Axioms of adaptedExists_of_norm, condExp_eq_ddt, condExp_decomp_eq_ddt, carayolThmAIrr_iff_DDT,
  carayolR17'_of_DDT: [propext, Classical.choice, Quot.sound] (scratch/carayol-herbrand/axioms.txt).
  Statements:
  * `adaptedExists_of_norm`: K normed, ultrametric, ‖ℓ‖<1, ℓ≠p, ρ : G_{Q_p} →* GL_n(K) continuous ⇒ ∃ adapted L.
  * `condExp_eq_ddt`: same hypotheses ⇒ (condExp ρ : ℝ) = codim V^{I_p} + ∫_{Ioi 0} codim V^{upperAbs p u}.
  * `norm_natCast_lt_one`: ℓ ∈ λ ⇒ ‖(ℓ : K_λ)‖ < 1 (Mathlib FinitePlace.norm_lt_one_iff_mem).
  * `CarayolThmAIrrDDT` (new leaf) and `carayolThmAIrr_iff_DDT : CarayolThmAIrr ↔ CarayolThmAIrrDDT`.
  * `carayolR17'_of_DDT : CarayolThmAIrrDDT → EigenformCoeffFieldFinite → LadicCond.CarayolR17'`.
- Mathlib's `IsUltrametricDist (adicCompletion K v)` is found by instance search; the topology of the Mathlib
  NormedField on adicCompletion is defeq to the one used in CarayolThmAIrr (the proof typechecks with `exact`).
- autofold dry run (scratch/carayol-herbrand/autofold.json, field r17, leaf carayolThmAIrrDDT published, unread):
  `strict count: 11/18 on 29 -> 12/17 on 29; strictest 11/18 -> 12/17` (autofold-dryrun.txt).
- COMPILED: lake build +OneProof.Main +OneProof.Discharges +CarayolHerbrand: 14232 jobs OK (build2.txt).
- #discharges (discharges.txt): `DISCHARGES [OpenResearchLeaves31.r17] by CarayolHerbrand.carayolR17'_of_DDT`,
  still assumes [CarayolHerbrand.CarayolThmAIrrDDT, DSCoeffExt.EigenformCoeffFieldFinite], standard axioms.
- COMPILED: AutofoldDryRun.lean (dry-run output minus line 1): sixContactMin_of_open49 standard axioms.
- Report docs/research/carayol-herbrand.md written.
