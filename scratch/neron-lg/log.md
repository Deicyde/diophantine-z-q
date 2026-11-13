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

## NeronLG.lean classification + N2-g1' — COMPILED 06:10 (0 errors; all 9 #print axioms standard)
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

## NeronLG.lean localization — COMPILED 06:19 / 06:20 (0 errors; 13 #print axioms, all standard)
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

## Final check — 06:22
- `lake env lean scratch/neron-lg/NeronLG.lean`: 0 errors, no sorry; 13 #print axioms, all
  `[propext, Classical.choice, Quot.sound]`.
- Verbatim check (python): the 12 copied blocks of scratch/tau-n1n2/N1N2.lean (§1 and §5) occur
  unchanged in NeronLG.lean.

## NeronLG.lean §6 — glue N2-g1' PROVED — COMPILED 06:57 (0 errors; 16 #print axioms, all standard)
- Copied (verbatim, tau-n1n2) `isMonHom_of_reflect`, `NeronModelOver.neronProp`, `NeronModelOver.uniqueIso`.
- Pasting lemmas: `pbCompInv_fst` (via `conjugateEquiv_counit`; `simp [pbCompInv, Over.pullbackComp,
  conjugateIsoEquiv, Over.mapComp]` closes it), `pbCompHom_fst`, `pbEq_fst`, `pbMap_fst`.
- `genSq` (base change of a generic-fibre identification along a commutative square; irreducible_def),
  `genSq_hom`, `isMonHom_genSq`, `genSq_cond`, `genSq_fst`, `genSq_compat`.
- `bcA'`/`bcA` ((A_{L₀})_{L'} ≅ A_{L'}), `isMonHom_bcA`, `bcProj'`, `bcA_proj` (bcA ≫ bcProj = fst).
- `isProper_of_abelian` (local Néron model is proper where A has an abelian-scheme model: N1-ab +
  uniqueness), `iso_baseChange_of_proper` (𝒩' ≅ 𝒩₀ ×_{O₀} O' compatibly with gen: N1-ab + uniqueness).
- `goodPlaceAnyField : GoodPlaceAnyField` PROVED (U = 𝒩', i = 𝟙, j = φ).
- `semistableLocalToGlobal_of'`, `n1_n2_of_leaves_and_glue'` (N1 ∧ N2 from 4 leaves + 5 glue) PROVED.
- FINDING (Lean): kernel "deterministic timeout" on every declaration applying N1-ab to `genSq …`
  while `genSq` (contains `pbEqIso` = `eqToIso`) was a plain `def`, even though elaboration
  succeeded and an isolated `IsMonHom` check passed; making `genSq` and `bcA'` `irreducible_def`
  fixed all of them (bisected with test lemmas).
- FINDING (Lean): `(A.baseChange L).X.left` vs `pullback A.X.hom κ` blocks `rw` ("motive not
  type-correct at implicit transparency"); state lemmas at the syntactic pullback types (`bcA'`,
  `bcProj'`) and transfer by `exact`.

## NeronLG.lean N1-g2 bad primes — COMPILED 06:59 (0 errors; 18 #print axioms, all standard)
- `goodPlacesAnyField` (N2-g1 as a theorem). Glue `NeronNearBadPoint` (N1-g2 only at primes ∋ f);
  `neronNearPoint_of` PROVED (other primes: `neronOverAway_of_abelian`);
  `n1_n2_of_leaves_and_glue''` : N1 ∧ N2 from N1-loc, N1-ab, N2-loc, NL + N1-g1, N1-g2(bad),
  N1-g3, N2-g2, N2-g3 PROVED.

## NeronLG.lean §7 — COMPILED 07:05 (0 errors; 20 #print axioms, all standard)
- `neronModelExists_iff`, `semistableNeronIdentityComponent_iff` (Iff.rfl with the build's H5Neron Props);
  `h5neron_n1_n2_of_leaves_and_glue` (the build's N1 ∧ N2 from 4 leaves + 5 glue) PROVED.
- `hasAbelianSchemeAway_zero` (sanity: conclusion of N1-g1 for the zero AV, any f) PROVED.

## NeronLG.lean §8 — COMPILED 07:08 (0 errors; 22 #print axioms, all standard)
- Alternative leaf `LocalSemistableIdentityComponentMono` (N2-loc⁺: the local statement for every
  L₁ ⊇ L₀; SGA 7 IX 3.6 + 3.3); `localSemistableIdentityComponent_of_mono` (N2-loc⁺ ⇒ N2-loc),
  `semistableCommonField_mono`, `semistableNeronIdentityComponent_of_mono`,
  `h5neron_n1_n2_of_leaves_and_glue_mono` (build's N1 ∧ N2 from N1-loc, N1-ab, N2-loc⁺, NL and the
  four glue N1-g1, N1-g2(bad), N1-g3, N2-g3) PROVED.

## Review of §8 (subagent, read-only) — 07:10
N2-loc⁺ OK: a consequence of SGA 7 IX 3.6 + 3.3 (+ SGA 3 VI_B 3.10), not stronger; not vacuous,
not trivially satisfiable; Lean instance binders as intended; N2-loc⁺ is itself derivable from
N2-loc + N2-g2 + localNeronModelsOf. One docstring point (O₁ ∩ L₀ is a DVR over O) added.

## NeronLG.lean §9 — COMPILED 07:13 (0 errors; 24 #print axioms, all standard)
- `center'`, `dvrAt_center'`: every valuation subring O ≠ ⊤ of a number field is 𝓞_{K,v} PROVED.
- `isDiscreteValuationRing_of_ne_top` PROVED.
- `isDiscreteValuationRing_comap`: O₁ ∩ L₀ is a DVR for a DVR O₁ of a finite extension L₁ ⊇ L₀
  of number fields PROVED (a step of N2-g2 and of the N2-loc⁺ argument).

## Final check — 07:12
- `lake env lean scratch/neron-lg/NeronLG.lean`: 0 errors; no `sorry`, no `axiom`; 24 #print axioms,
  all `[propext, Classical.choice, Quot.sound]`.
- Verbatim check (python): the 14 copied blocks of scratch/tau-n1n2/N1N2.lean occur unchanged.
- Not done: proofs of glue N1-g1, N1-g2 (bad primes), N1-g3, N2-g2, N2-g3.
