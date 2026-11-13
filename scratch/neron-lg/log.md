# neron-lg results log

Start 2026-11-13 05:52 PST. Base 89a5e60e. `lake build ZInQKernel.HDecomp.Faltings.H5BaseChange`: OK (cached).

## NeronLG.lean §1 — verbatim copies from scratch/tau-n1n2/N1N2.lean
Lines copied by script (python slice of the source lines, no edit): Copies section
(`IsBaseChangeOf`, `IsOpenSubgroupModel`), `NeronModelExists`, `NeronModelOver` (+ attribute),
`AbelianSchemeIsNeron`, `NeronLocalToGlobal`, `resHom`, `bcProj`, `LocalSemistableAt`,
`SemistableNeronAt`, `SemistableLocalToGlobal`.

## NeronLG.lean §2–§3 — COMPILED 06:04 (0 errors; #print axioms: propext, Classical.choice, Quot.sound)
- `dvrAt v` (valuation subring of the v-adic valuation; DVR instance found by `infer_instance`).
- `IsNeronOver`, `spec_square`, `bcGenO` (generic fibre of `G ×_R O` identified with `B`).
- New leaf `NeronLocalOnBase` (NL; BLR §1.2 Prop 4, UNVERIFIED locator): Néron over Dedekind `R`
  ⟺ Néron after base change to every DVR `O ⊇ R` in `L`.
- `NeronOverAway`, `HasAbelianSchemeAway`; glue `AbVarSpreadsOut` (N1-g1), `NeronNearPoint`
  (N1-g2), `NeronGlueAway` (N1-g3).
- `neronLocalToGlobal_of : AbVarSpreadsOut → NeronLocalOnBase → NeronNearPoint → NeronGlueAway →
  NeronLocalToGlobal` PROVED (covering argument: maximal ideal ⊇ span of neighbourhoods is a
  nonzero prime, contradiction; `Ideal.span_eq_top_iff_finite`).
- `neronOverAway_of_abelian` PROVED (abelian scheme over 𝓞_L[1/f] is Néron by N1-ab; IsDomain,
  IsDedekindDomain, IsFractionRing of the localization from Mathlib).

## NeronLG.lean §4 — COMPILED 06:08 (0 errors; all 6 #print axioms: propext, Classical.choice, Quot.sound)
- `LocalSemistableWith A O L₀` (body of `LocalSemistableAt`), `localSemistableAt_iff` (Iff.rfl).
- Glue `GoodPlacesAnyField` (N2-g1), `LocalSemistableMono` (N2-g2), `SemistableGlobalOfLocal` (N2-g3).
- `compositumFinset` PROVED (Finset induction over `H5Neron.compositum`).
- `semistableCommonField` PROVED (N2-g1 + N2-g2 + compositum: one `L₀` for all DVRs).
- `semistableLocalToGlobal_of : NeronLocalOnBase → AbVarSpreadsOut → GoodPlacesAnyField →
  LocalSemistableMono → SemistableGlobalOfLocal → SemistableLocalToGlobal` PROVED (𝒱 from the
  build's proved H4b `H5Neron.groupModelBaseChangeExists`).
- Lean note: `ι` is a reserved token here (open NumberField?); renamed binder to `I`.
