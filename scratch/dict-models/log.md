# dict-models results log

Base e22df37c (origin/main; top module TailZ41, `sixContactMin_of_open34`). Four research fields, all in
`HDec.HSyn.OpenResearchLeaves26` (ZInQKernel/OneProof/H/TailZ41.lean).

## Statements located (VERIFIED, read in the tree)

| field | Lean constant | file |
| --- | --- | --- |
| sga7_IX_3_3_SH | `SGA7PersistsNF.SGA7_IX_3_3_SH` | ZInQKernel/Contrib/OneProof/SGA7PersistsNF.lean:60 |
| raynaudSemistableSH | `ReductGlue.RaynaudSemistableSH` | ZInQKernel/OneProof/H/TailZ14.lean:1105 |
| mumfordGroupLaw | `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw` | ZInQKernel/Contrib/OneProof/MumfordRigidity.lean:82 |
| neronBaseChangeStrictHenselization | `GapSHPair.NeronBaseChangeStrictHenselization` | ZInQKernel/Contrib/OneProof/StrictHenselizationPair.lean:1527 |

Consumers in the chain (VERIFIED, git grep of `.field` reads):
- `sga7_IX_3_3_SH`: TailZ33:104 (`sga7_IX_3_3_of_SH`), TailZ41:88 (`semistablePersistsSHcp_of_SH`).
- `raynaudSemistableSH`: TailZ23:723 (`ReductB.raynaudSemistable_of_SH_pair`).
- `mumfordGroupLaw`: TailZ23:708/760/786 and TailZ34:159, all through `qmFamilyGroupLaw_of_groupLaw`
  (TailZ40:205), whose `S` is any proper smooth curve over ℚ (not assumed connected).
- `neronBaseChangeStrictHenselization`: TailZ28:113, TailZ33:101, TailZ41:88.

Existing pieces reused (VERIFIED, read): `CToPrinted.idComp_baseChange` (TailZ19:1238; from SGA3_VIB_3_10 and
GeomConnOfRationalPoint); `UnipotentForward.IsSemistableRes` (the k(s) form, UnipotentForward.lean:88);
`ReductGlue.hasSemiAbelian_pullback` (TailZ14:1006, field isomorphisms only);
`GapSHPair.neronBaseChangeStrictHenselization_of_unramified` (StrictHenselizationPair.lean).

## Build

- 02:5x copied ~/dzq-check2/.lake/build (at 2880fef1) and lean/.lake/build; LPrefix etc. out of date for e22df37c,
  rebuilding the three import cones with `lake build`.
- 03:12 build of the three import cones done (19 min, 0 errors).

## New leaves and proofs (all VERIFIED: `lake env lean`, no errors, no sorry)

| field | new leaf | proof | extra inputs |
| --- | --- | --- | --- |
| sga7_IX_3_3_SH | `DictModels.SGA7Pre.SGA7_IX_3_3_SHpre` (U = pullback.fst⁻¹ N⁰) | `sga7_IX_3_3_SH_of_pre` | sga3_VIB_3_10, geomConnOfRationalPoint (via `idComp_baseChange`) |
| raynaudSemistableSH | `DictModels.RaynaudOr.RaynaudSemistableSHOr` (k(s) form, general torus, ∨ geometric form) | `raynaudSemistableSH_of_or` | geomConnOfRationalPoint |
| mumfordGroupLaw | `DictModels.MumfordConn.MumfordGroupLawConn` (+ ConnectedSpace S) | `mumfordGroupLaw_of_conn` (gluing over components proved) | none |
| neronBaseChangeStrictHenselization | `DictModels.NeronBLR72.BLR_7_2_1` (= ReductGlue.NeronBaseChangeUnramifiedDVR) | `neronBaseChangeStrictHenselization_of_BLR72` | none |

Converses (leaf from field): `pre_of_SH`, `or_of_field`, `conn_of_field` (VERIFIED). BLR_7_2_1 is more general than
its field (by design: printed form).

Proved glue (VERIFIED): `hasSemiAbelian_pullback_bar` (k(s) semi-abelian with general torus ⇒ split semi-abelian over
k̄, any field, with 04KV), `isSemistable_of_resT`, `glue_ext`, `glue_exists`, `grpObj_of_pieces`, `pb_eta`.

## Checks

- 03:21 `lake build +Main +Discharges +4 contributions`: 13699 jobs, success, 2.5 min.
- `#discharges` (scratch/dict-models/discharges.txt; VERIFIED): the four new theorems each DISCHARGE their field;
  still assumes: SHpre + SGA3_VIB_3_10 + GeomConnOfRationalPoint; RaynaudSemistableSHOr + GeomConnOfRationalPoint;
  MumfordGroupLawConn; BLR_7_2_1. Axioms [propext, Classical.choice, Quot.sound] for all four.
- scratch/dict-models/Statements.lean: verbatim copies of the four field statements, each `rfl` to the original:
  compiles, no errors (VERIFIED).
- autofold dry run (scratch/dict-models/autofold-dryrun.txt): strict 40/8 -> 40/8, strictest 39/9 -> 39/9 (rows are LEAF
  on this base). FoldCheck.lean (dry-run output minus line 1) compiles; `sixContactMin_of_open35` axioms standard (VERIFIED).
