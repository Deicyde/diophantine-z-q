# hdec-adopt2: the second round of H-decomposition glue in the built project

Status: task hdec-adopt2, 2026-11-12. Results log: `scratch/hdec-adopt2/log.md`; generator
`scratch/hdec-adopt2/adopt2.py` (it uses `scratch/hdec-adopt/wrap.py` for long lines).

## Result

VERIFIED: `lake build ZInQKernel` exits 0 (2026-11-12, 17:03 PST, after the last change), and
`lake env lean scripts/print_axioms.lean` prints 272 axiom lists, every one exactly
`[propext, Classical.choice, Quot.sound]`. 93 of those are the theorems added here (179 before).

All eleven clusters named by the task are adopted: 15 new modules (about 7,700 lines) under
`ZInQKernel/HDecomp/`, imported from `ZInQKernel/HDecomp.lean`. None was dropped. Verbatim copies
of existing HDecomp modules became imports (list below). No other statement changed. The leaves
stay `def … : Prop` hypotheses. There is no `sorry` and no `axiom` (grep, VERIFIED), and no line
of the new modules is longer than 100 characters (awk, VERIFIED).

## Layout (new modules)

| Cluster | Module | From |
|---|---|---|
| SemisimpleBaseChange, C2′, E1′, commutant glue | `I3Linalg.C2` | `scratch/glue-ssbc/C2.lean` |
| Tate modules along injective maps | `I3Linalg.TateBC` | `scratch/glue-I3-linalg/TateBC.lean` |
| Continuity of `ρ_ℓ` | `I3Linalg.RhoCont` | `scratch/glue-rho-cont/RhoCont.lean` |
| LeafHasse, LeafLocalTwo from T14-T15 | `Descent.WP3` | `scratch/glue-wp3/WP3.lean` |
| B3 (v) from T32(a); LeafB3b, LeafConj, T32(b) proved | `B3Unram.B3b` | `scratch/glue-b3b/B3b.lean` |
| C10 trace link | `C10.Link` | `scratch/glue-c10-link/Link.lean` |
| Vignéras normalizer index | `Vigneras.Local`, `Vigneras.Global` | `scratch/glue-vigneras/` |
| Local square-root criterion | `Sqrt.SqrtLocal`, `Sqrt.Disj` | `scratch/glue-sqrt-local/SqrtLocal.lean`, `scratch/glue-sqrt-disj/Disj.lean` |
| ℓ-adic conductor exponent, R17/L8 stated | `Conductor.LadicCond` | `scratch/def-ladic-cond/LadicCond.lean` |
| Elementary assembly glue | `Assembly.{C8,E1Lin,E2Index,F3Glue}` | `scratch/glue-assembly/` |

Superseded drafts, not adopted separately because their content is inside an adopted file
(VERIFIED from the drafts' logs and by the duplicate-name check `scratch/hdec-adopt2/decls.py`):
`glue-I3-linalg/{I3,Commutant,C2}.lean` and `glue-ssbc/SSBC.lean` (all inside
`glue-ssbc/C2.lean`); `glue-conj/{T1,T2,T3,Conj,UnramConj}.lean` (inside `glue-b3b/B3b.lean`, in
namespace `GlueB3Unram`); the glue-descent copies in `glue-wp3/` (byte-identical to the adopted
`Descent.*`, by glue-wp3's log); `glue-sqrt-local/{CycloPadic,SqrtFinite,Frob,Local,Unramified}`
(inside `SqrtLocal.lean` and `Disj.lean`); `glue-sqrt-disj/{Level,Plumb,Ram}` (inside `Disj.lean`).

## Verbatim copies replaced by imports (VERIFIED: compiled)

- `I3Linalg.C2`: the draft's §1-§4 (pkg-I3's `I3.lean`, 670 lines, a verbatim copy by a
  line diff) come from `Objects` §A. This also removes the draft's old leaf `PkgI3.QMDichotomy` and
  its `I3Leaves`; the only `I3Leaves` and QM leaf now are Objects' (`PkgI3.QMDichotomyYu`, with
  `QuatIndefinite`). No theorem of C2 used the QM leaf (grep).
- `I3Linalg.TateBC`: §1 (pkg-I3's Tate module) from `Objects`.
- `I3Linalg.RhoCont`: §1-§2 (pkg-I3's lines 15-335) and its copy of the leaf `PkgI3.TateModuleFree`
  from `Objects`.
- `Descent.WP3`: the copies of glue-descent come from `Descent.*`. The `PkgI6` cochain definitions
  and leaves (`IsCocycle2`, `IsCoboundary2`, `resC`, `BrauerHasse2C`, `BrauerReciprocity2C`,
  `H2TwoClasses`, `LocalH2CardC`) come from `Conductor.I6Base` (whitespace-normalized substring
  check: each block occurs in `I6Base`).
- `Sqrt.SqrtLocal`: its copy of `exists_half_iff` (from glue-I6-rest's `SqrtChar.lean`) is now
  proved by `GlueI6Rest.exists_half_iff` (`Conductor.SqrtChar`). The name
  `GlueSqrtLocal.exists_half_iff` and its statement are unchanged.
- `Sqrt.Disj`: its copy of `SqrtLocal.lean` lines 84-242 (`exists_half_iff`, `redU`,
  `redU_sq_eq_one` and helpers) is imported from `Sqrt.SqrtLocal`. Its copy of
  `PkgI6.LocalKroneckerWeber` comes from `Conductor.I6Base` (same definition body; only the
  docstring differed).

- `B3Unram.B3b`: its copies of glue-descent's `B2Glue` definitions and lemmas (`GQ` with its
  topological-group instance, `act`, `toRingAut`, `cyc`, `galChar`,
  `isLocallyConstant_of_openSubgroup`, `cyc_eq_of_agree`, `cyc_isLocallyConstant`,
  `galChar_isLocallyConstant`, `UnramifiedAt`) are dropped. They are replaced by
  `open GlueDescent.B2Q (…)` and an import of `Descent.B2Glue`. The code was identical after
  normalizing whitespace and docstrings (`scratch/hdec-adopt2/blocks.py`); `UnramifiedAt` differed
  only by writing `Qbar`, a reducible `abbrev` for `AlgebraicClosure ℚ`. The `GlueB3Unram.*` names
  of these copies disappear, and every theorem statement of the file now refers to glue-descent's
  `GQ`, `cyc` and `UnramifiedAt`.
- `Vigneras.Global`: its copies of `GlueRepo.A1.{B, comb, combMul}` (`Repo.A1Quaternion`, the same
  code) are dropped and replaced by `open GlueRepo.A1 (B comb combMul)`.
  `GlueVigneras.Global.comb_mul`, which now has the same statement as `GlueRepo.A1.comb_mul`, is
  proved by it. The draft's `O` stays: it is a `Set`, while `GlueRepo.A1.O` is a `Subring`.

Duplicates left alone: `Sqrt.Disj` proves `card_quotient_maximalIdeal` and
`eq_of_pow_eq_one_of_sub_mem` twice, in `GlueSqrtLocal` and in `GlueSqrtDisj`. Both copies come
from glue-sqrt-local's `Frob.lean`, which is not an HDecomp module. A body-level duplicate scan of
all HDecomp modules found no other duplicate involving the new modules (VERIFIED, 17:02).

One edit beyond the copies: in `Vigneras.Global` (`phi_eq_one_iff`), a 104-character
`first | … | …` line is broken by hand into `first` plus two lines of alternatives. `wrap.py` broke
it inside a parenthesized tactic sequence, which does not parse.

## Axioms

`scripts/print_axioms.lean` ends with a new section that lists the top-level theorems of the
adopted modules: every `#print axioms` target of the drafts, plus the main theorems of the drafts
that had none (`GlueVigneras.vigneras_local`, `split_normalizer_iff`, `unramified_normalizer`,
`GlueVigneras.Global.{nrd_dvd_six,global_index,normalizer_index_four}`,
`GlueAssembly.{weight_match,weight_match_coh,twist_finite,invariants_ne_bot_of_baseChange,
index_Gamma1_le,logHeight_le_log_mulHeightL2,logHeight_sixteen_eq,mulHeight_rootsOfUnity_mul}`).

VERIFIED (17:03 PST): all 93 new entries, like the 179 earlier ones, depend on exactly
`[propext, Classical.choice, Quot.sound]` (output in `scratch/hdec-adopt2/axioms.txt`).

Headline glue theorems now in the build:
- `GlueI3.semisimpleBaseChange`, `PkgI3.C2_absolutelyIrreducible'`, `PkgI3.E1_exists_hom_ne_zero'`
  (C2 and E1 with no `SemisimpleBaseChange` hypothesis; only I3 leaves remain).
- `GlueWP3.leafHasse_of_T14`, `leafLocalTwo_of_T15`, `b3_degree_le_QM_of_T14_T15`, `leafHasse_iff`.
- `GlueB3Unram.unramified_outside_t32a` (B3 (v) from leaf T32(a) only), `leafB3b`, `leafConj`,
  `t32b`, `leafB3a_of_t32a`.
- `GlueC10Link.trace_link`, `c10_of_trace_link`, `c10_of_squares`.
- `PkgI3.continuous_galRep_of_tateModuleFree`; `PkgI3.Tate.map_bijective`.
- `GlueSqrtLocal.gal_sqrt_criterion`, `GlueSqrtDisj.sqrt_criterion_muField`, `le_muField_of_lkw`.
- `LadicCond.condAt_eq_artinAt_of_surj`, `condAt_le_of_upper`, `carayolR17_of_R17'`.

## How to reproduce

`python3 -I scratch/hdec-adopt2/adopt2.py` regenerates the 15 modules from the drafts. Then
run `lake build ZInQKernel` and `lake env lean scripts/print_axioms.lean`.
