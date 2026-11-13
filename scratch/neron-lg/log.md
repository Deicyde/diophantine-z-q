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

## NeronLG.lean classification + N2-g1' — COMPILED 06:31 (0 errors; all 9 #print axioms standard)
- `ringOfIntegers_mem` (𝓞_K ⊆ every valuation subring), `toO`, `center O` (nonzero prime of 𝓞_K
  under a DVR `O`), `dvrAt_center : dvrAt (center O) = O` PROVED: every DVR valuation subring of a
  number field is `𝓞_{K,v}` (Mathlib `exists_primeCompl_mul_eq_of_integer`,
  `ValuationSubring.eq_of_le_of_ne_top`).
- `badPlaces_finite` PROVED: `{O | DVR O ∧ (1/f) ∉ O}` is finite for `f ≠ 0` (`Ideal.finite_factors`).
- Glue `GoodPlaceAnyField` (N2-g1', one place with an abelian-scheme model); `goodPlacesAnyField_of :
  GoodPlaceAnyField → GoodPlacesAnyField` PROVED.
- Lean note: `open … MonObj` shadows `mul_one` (`MonObj.mul_one`); use `_root_.mul_one`.

## Review (subagent, read-only) of §2–§4 — 06:15
No PROBLEM. Every new def true and non-vacuous; NL is BLR 1.2/4 specialized (bcGenO direction
checked; truth of IsNeronOver is independent of the chosen iso). MINOR docstring gaps fixed:
N1-g2 (h' ∉ v needs prime avoidance; isomorphism at v when f ∉ v), N1-g3 (g = 0 harmless),
N2-g1 (locators superfluous), N2-g2 (details of the generic-fibre equation), N2-g3 (c built from
the `IsBaseChangeOf` iso e and 𝒩₀.gen, not 𝒱.gen).

## NeronLG.lean localization — COMPILED 06:20 / 06:25 (0 errors; 13 #print axioms, all standard)
- `bcGenO` made `irreducible_def`; `bcGenO_hom₁..₄`, `bcGenO_hom`, `isMonHom_bcGenO`.
- `neronModelOver_localize` PROVED: Néron model over 𝓞_L ⇒ Néron model over every DVR O ⊂ L (NL ⇒).
- `localNeronModelExists_of_self` PROVED: leaf N1-loc ⇐ N1-self + NL (N1-loc not stronger than
  the published statements).
- `LocalNeronModelsOf A`, `localNeronModelsOf` PROVED (N1 + NL ⇒ local models of every A_{L₀});
  N2-g2 `LocalSemistableMono` now assumes only `LocalNeronModelsOf A` (smaller than N1 + NL).
- FINDING (Lean): the chain `(bcGenO …).hom = pbCompInv ≫ pbEq ≫ gen.hom` as ONE term
  (`(congrArg Iso.hom bcGenO_def).trans ((Iso.trans_hom _ _).trans (congrArg₂ …))`) gives
  "(kernel) deterministic timeout" even with `bcGenO` irreducible; the same chain split into four
  separately stated lemmas composed by `.trans` checks instantly.
