# hdec-adopt3: the third round of H-decomposition glue in the built project

Status: task hdec-adopt3, 2026-11-12. Results log: `scratch/hdec-adopt3/log.md`; generator
`scratch/hdec-adopt3/adopt3.py` (it uses `scratch/hdec-adopt/wrap.py` for long lines and
`scratch/hdec-adopt2/blocks.py`); duplicate scan `scratch/hdec-adopt3/dups.py`; statement check
`scratch/hdec-adopt3/same.py`.

## Result

VERIFIED: `lake build ZInQKernel` exits 0 (2026-11-12, 19:46 PST, after the last change), and
`lake env lean scripts/print_axioms.lean` prints 332 axiom lists, every one exactly
`[propext, Classical.choice, Quot.sound]`. 60 of those are the declarations added here (272
before).

All four developments named by the task are adopted, none dropped: 13 new modules (about 4,960
lines) under `ZInQKernel/HDecomp/`, imported from `ZInQKernel/HDecomp.lean`.

- `GlueB3Unram.t32a : LeafPush.T32a_TameQuadratic`, `GlueB3Unram.leafB3a : LeafB3a` and
  `GlueB3Unram.unramified_outside_noLeaf` (B3 (v) with no leaf) are in the build.
- The modular-curve layer (`IsX1Model`, `IsJacobian`, `IsJ1`, the leaves R16
  `R16_EichlerShimuraJ1'`, `JacobianExists`, `DimJ1Genus`, `X1ModelExists`, the glue target
  `BelyiX1`, the bundle `ModCurveLeaves`, and the proved glue `genus_Gamma1_le`, `dim_J1_le`,
  `exists_J1_dim_le`, `exists_J1_quotient`, `rhoF_traces`, `g13_constituent`, `rhoF_attached`).
- The QM field-point leaves (`R1fp`, `R1R2fp`, `R1rec`, `R5fp`, `R5fpCount`, the bundle
  `QMLeaves`) with their objects and glue (`Level3.onto`, `Level3.torsor`, `QML3.goodReduction`,
  `unramified_over_branch`, `leaves_on_one_witness`, …).
- The stable Faltings height `ZInQ.DefFaltings.stableFaltingsHeight` with the leaves R19-R21
  (`R19_GaudronRemond`, `R20_FaltingsLemma5`, `R21_Bost`) and the conditional acceptance tests,
  now over the shared `PkgI3.AbVar`.

Every declaration of the drafts that is kept has the same whitespace-normalized text (statement
and proof) as in the draft (`same.py`, VERIFIED): T32a 19/19 (after the copied part), modular
curves 84/99, QM 143/143, Faltings 133/138. (Since then notes-fix strengthened the kernel's
`LeafQM.AV.fibre_conjugates_isomorphic`, so that one QM declaration now differs from the draft.) The 20 missing names are exactly the verbatim copies
replaced by imports, and two renamed definitions (below). Leaves stay `def … : Prop`. There is no
`sorry` and no `axiom` (grep, VERIFIED), and no line of the new modules is longer than 100
characters (awk, VERIFIED).

## Layout (new modules)

| Development | Module | Draft sections |
|---|---|---|
| T32(a) proved; B3 (v) on no leaf | `B3Unram.T32a` | `glue-t32a/T32a.lean`, from "# glue-t32a" |
| Belyi degree and genus of `Γ₁(N)` | `ModCurves.Genus` | `leaf-modcurves/ModCurveLeaves.lean` §A |
| `ℚ̄`, cusp forms, `j`-line, `IsX1Model`, `IsJacobian`, `IsJ1` | `ModCurves.Defs` | §B-§E |
| R16 and `ρ_{f,ι}`, genus and Belyi leaves, bundle | `ModCurves.Leaves` | §F-§H |
| G13 constituent, C9 bridge | `ModCurves.Glue` | §I-§J |
| Order `𝒪`, QM and level-3 structures, classes, A3/A6 glue | `QM.Structures` | `leaf-qm-fp/QMLeaves.lean` §0-§3 |
| QM pairs, CM, fields of moduli, maps to `P¹`, field points | `QM.Pairs` | §4-§7 |
| The leaves R1fp … R5fp and their glue | `QM.Leaves` | §8 |
| Arakelov degree, torus metric, `HodgeData`, AT interface | `Faltings.HodgeData` | `def-faltings/Faltings.lean` §1-§6 |
| Fractional-ideal Hermitian lines, base change, AT1 | `Faltings.IdealLines` | §7-§14 |
| Group models, Hodge line, analytic uniformization | `Faltings.Models` | §15-§17 |
| Metrized models, stable height, AT1, AT2 | `Faltings.Height` | §18-§20 |
| Leaves R19-R21 | `Faltings.Leaves` | §21-§22 |

Splits are at the drafts' section boundaries. Each continuation module reopens the draft's
namespace and repeats the `open` lines and the namespace-level `variable` line in force at that
point (QM: `variable {K : Type} [Field K]` in `LeafQM.AV`; Faltings: the `ModelsSec` opens).

## Verbatim copies replaced by imports (VERIFIED: compiled)

The scan `dups.py` compares every top-level declaration of the drafts with the HDecomp
declarations of the same last name component, after normalizing whitespace.

- `B3Unram.T32a`: the draft's lines 17-1816 are glue-b3b's `B3b.lean` lines 11-1810 (a `diff`,
  VERIFIED); they are imported from `B3Unram.B3b`. As there, `GQ`, `cyc`, `galChar`,
  `UnramifiedAt`, … are glue-descent's (`open GlueDescent.B2Q (…)` after `namespace GlueB3Unram`).
- `ModCurves.Genus`: `firstColMod`, `firstCol_algebra`, `firstColMod_eq_iff`, `index_Gamma1_le`
  are `GlueAssembly`'s (`Assembly.E2Index`, identical code): `open GlueAssembly (…)`.
- `ModCurves.Defs` (and the later ModCurves modules): `Qbar`, `GQ`, `LiesOver`, `IsArithFrob`,
  `CF`, `coeff`, `HasNebentypus`, `IsNormalizedEigenform`, `scaleH`, `oldSpace`, `IsNewform` are
  `PkgI4`'s (`Conductor.LadicCond`, identical code): `open PkgI4 (…)`. The names
  `LeafModCurves.<these>` disappear; every statement now refers to `PkgI4`'s definitions, with the
  same text.
- `Faltings.Models` (and later Faltings modules): the draft's `AbVar` (a declared copy of
  `PkgI3.AbVar` restricted to `Type`), `AbVar.baseChange` and `AbVar.dim` (declared copies of
  `PkgI3.AbVar.baseChange` and `PkgI3.AbVar.dim`; the bodies are identical, only docstrings,
  `noncomputable` and the universe differ) are dropped for `open PkgI3 (AbVar)`. So
  `GroupModel`, `MetrizedModel`, `stableFaltingsHeight` and R19-R21 are now stated over the
  project's shared abelian-variety type. The draft's new definitions `AbVar.structMapOn` and
  `AbVar.origin` are declared as `PkgI3.AbVar.structMapOn` and `PkgI3.AbVar.origin`, so that the
  unchanged statement text `A.origin`, `A.structMapOn U c` (in `IsEllipticCurveOf`) still
  elaborates by dot notation. These two are the only renamed declarations.

Left alone: `LeafQM.AV.Qbar` (a one-line `abbrev` equal to `PkgI4.Qbar`; importing
`Conductor.LadicCond` for it would add a large dependency), `LeafQM.B` and `LeafQM.O` (the same
quaternion order as `GlueRepo.A1.O`, but built differently: `ofInt`/`InO` against `comb`/`range`).

## Axioms

`scripts/print_axioms.lean` ends with a new section listing every `#print axioms` target of the
four drafts that was not already there: 6 from glue-t32a (`exists_kummer`, `val_pow_eq_zpow`,
`char_eq_sgn_zpow`, `t32a`, `leafB3a`, `unramified_outside_noLeaf`), 10 from leaf-modcurves, 28
from leaf-qm-fp, 16 from def-faltings. VERIFIED (19:46 PST): all 60, like the 272 earlier ones,
depend on exactly `[propext, Classical.choice, Quot.sound]` (output in
`scratch/hdec-adopt3/axioms.txt`).

## How to reproduce

`python3 -I scratch/hdec-adopt3/adopt3.py` regenerates the 13 modules from the drafts. Then run
`lake build ZInQKernel` and `lake env lean scripts/print_axioms.lean`.
