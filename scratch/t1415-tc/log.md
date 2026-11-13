# t1415-tc results log

- 04:17 start. Merged origin/wip/tc-survey (docs + scratch only).
- Survey of vendored TC (oct16): `invMap K : Br K ≃+ AddCircle (1:ℚ)` for `IsNonarchimedeanLocalField K`
  (Brauer/Invariant.lean:200) VERIFIED vendored. Hasse/reciprocity for Br of a number field vendored
  only CONDITIONALLY: `brLocalization_injective_of_subsingleton_h1_globalFormation` (Global/Brauer/
  LocalizationKernel.lean:155), whose hypothesis follows from the Kummer-case index bound
  (`subsingleton_h1_globalFormation_of_forall_index_le`, IdeleClass/SecondInequality.lean:150);
  the Kummer case itself is NOT proved in vendored TC (its docstring says so). VERIFIED by reading.
- No TC sources (tc-main, tc-oct16) on this host; only the vendored 1118 modules. No prebuilt TC
  oleans in any worktree on this host: building the closure of Brauer/Invariant + I6Base myself.
- Plan: (1) Kummer bridge on explicit cochains: ZMod 2-cocycles ↔ 2-torsion of H2(G_K,(Kˢ)ˣ),
  using TC Hilbert 90 (`subsingleton_H1_unitsCoeff`) and square roots in Kˢ; (2) T15 at ℚ_p from
  invMap; real place copied from t-brauer-purity; (3) T14: reduce to TC's conditional theorems.
