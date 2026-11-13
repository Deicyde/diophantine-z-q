# t-purity2 (fleet summary)

**Main results.** All are compiled with `lake env lean`, with no sorry and axioms
`[propext, Classical.choice, Quot.sound]`. The report is docs/research/t-purity2.md and the Lean
files are in scratch/t-purity2/.

- **T2 (Abhyankar) is proved.** t-brauer-purity proved the whole leaf, not only the case `L = K`.
  I recompiled `scratch/t-brauer-purity/T2Kernel.lean` at this base:
  `TBrauerPurityT2K.abhyankarDVR : PkgI2.AbhyankarDVR.{0}`. T2 can move from leaf to glue.
- **T1 (Zariski–Nagata) ⇔ T1″ (Nagata's form): regular *local* base, module-finite `R → S`,
  `q` over `𝔪_R`, `dim ≥ 2`, no quasi-finiteness hypothesis.** Both directions are proved over
  the kernel definition (`T1Kernel.lean`: `TPurity2K.purityBranchLocus_of_local`,
  `local_of_purityBranchLocus`). The glue proved for this:
  - the dimension-one case, by Nakayama, DVR, flatness, and a local "flat + unramified ⇒ étale"
    (Mathlib has only the global version);
  - the reduction to finite algebras, via Mathlib's Zariski Main Theorem;
  - the localization of the base.
- **T14/T15 narrowed.** The only consumer (`GlueWP3.b3_degree_le_QM_of_T14_T15`) needs only
  glue-descent's `LeafHasse` and `LeafLocalTwo`. So T14a, T14b and T15 can be announced as two
  weaker Props: `BrauerHasseFin2C` (trivial at every prime ⇒ trivial; no reciprocity, no real
  place) and `LocalTwo2C` (local uniqueness). Both are proved to be consequences of T14 and T15,
  and to imply what the consumer needs (`T14Narrow.lean`).
- **T14/T15 without topology.** Continuous `ℤ/2`-cochains on profinite `G_K` are exactly those
  inflated from finite quotients. Lean equivalences `localH2CardC_iff_fin`,
  `brauerHasse2C_iff_fin`, `brauerReciprocity2C_iff_fin`; the narrowed Props in this form are
  `BrauerHasseFin2Fin` and `LocalTwo2Fin` (`T14T15Final.lean`).

**What remains unproved.**
- T1″ itself (dimension ≥ 2). It needs Serre's criterion, Auslander–Buchsbaum and the
  discriminant; none of these is in Mathlib.
- The arithmetic content of T14/T15: the Hasse principle for `Br(ℚ)[2]` and `|Br(ℚ_p)[2]| ≤ 2`.
  Both need class field theory and the Kummer bridge to `Br`.
