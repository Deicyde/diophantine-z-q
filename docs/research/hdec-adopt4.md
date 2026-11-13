# hdec-adopt4: leaf-push2, bp-analytic and rv-qm-polar in the built project

Status: task hdec-adopt4, 2026-11-12. Results log: `scratch/hdec-adopt4/log.md`. Generator:
`scratch/hdec-adopt4/adopt4.py`, which uses `scratch/hdec-adopt/wrap.py` for long lines and
`scratch/hdec-adopt2/blocks.py`. Statement check: `same.py`. Part I check: `partI.py`. Docstring
repairs: `docfix.py`. Axiom section: `axsec.py`.

## Result

VERIFIED (23:10 PST, after the last Lean change):

- `lake build ZInQKernel` exits 0 (9990 jobs).
- `lake env lean scripts/print_axioms.lean` prints 396 axiom lists, each exactly
  `[propext, Classical.choice, Quot.sound]`. 64 of them are new here (332 before).
- The list is in `scratch/hdec-adopt4/axioms.txt`.

All three developments named by the task are adopted, and nothing was dropped. There are 10 new
modules (about 3,125 lines) under `ZInQKernel/HDecomp/`, all imported from
`ZInQKernel/HDecomp.lean`:

- **leaf-push2** is in `HDecomp/LeafPush2/{R18,R22,R3,T}.lean`. The leaves are `def … : Prop`:
  - `R18_Javanpeykar`, `R22_Pazuki` and `R03_LinYang`;
  - `UniformizationExists`, `T11a_RiemannEnd` and `T11b_Rigidity`;
  - the glue targets `R03_LinYang_algClosed`, `T12_ComplexConjEigen` and `T10_groupIso`.

  The definitions are `IsSiegel`, `IsPeriodMatrix`, `Char2`, `thetaConst`, `absLogHeight`,
  `CPts`, `IsUniformization`, `ffAlgebra`, `HasSexticModel`, the Igusa invariants and
  `LinYangTuple`. The proved glue is `R18_real`, `javanpeykarBound_pos`/`_mono`, `R22_plus3`,
  `isSiegel_I`, `linYangTuple_onQMLocus`, `onQMLocus_of_linYangTuple`, `linYang_j_eq`,
  `R03_of_algClosed` and `exists_isComplexConj`.
- **bp-analytic** is in `HDecomp/Analytic/{Torus,QMLattice,Hom,Uniformization}.lean`. It
  contains:
  - complex tori `E ⧸ Λ` as compact complex Lie groups;
  - the Siegel space, period lattices, Riemann theta and theta characteristics;
  - pkg-I1's QM lattice and `Ω(τ) ∈ 𝔥₂` (`Omega_mem_siegelSpace`);
  - continuous homomorphisms of tori as linear maps (node T2), and `covol = |det Im Ω|`;
  - the leaf `UniformizationLeaf`/`UniformizationLeafAll` (AN3, coordinate form), with its glue:
    uniqueness up to `ℂ`-linear isomorphism, the analytic representation `analyticRep` of
    `End(A)`, and torsion points.
- **rv-qm-polar** is in `HDecomp/QM/Polar.lean`. It contains Lemma P's lattice cores:
  `eq_pm_E0_of_principal`, `two_principal_types`, `type_eq_mu_mul`, `twist_type`, the
  Atkin–Lehner twists, `riemann_sign` and `lemmaP_lattice`.
- **The rv-qm-polar docstring repairs** (rv-qm-polar.md §4 item 2) are applied to the docstrings
  of `QML3` (`QM/Structures.lean`) and of `R1fp`, `R5fp`, `R5fpCount` and `QMLeaves`
  (`QM/Leaves.lean`). "bp-qmmoduli §2.2 … SPECULATIVE" becomes Lemma P (for a fixed `μ`,
  VERIFIED as an argument, lattice cores compiled in `QM/Polar.lean`, published locators
  UNVERIFIED). Only docstrings changed (`git diff`, VERIFIED).
- **New glue (no draft): `HDecomp/LeafPush2/Bridge.lean`.** It ties R22's data to bp-analytic:
  - `isSiegel_iff`: `IsSiegel Ω ↔ Ω ∈ SiegelSpace 2`;
  - `isPeriodMatrix_periodLattice` and `isPeriodMatrix_of_map`;
  - `isSiegel_Omega` and `isPeriodMatrix_qmLattice`: for `Im τ > 0`, pkg-I1's `Ω(τ)` is in `𝔥₂`
    and is a period matrix of the QM lattice `ι(𝒪)(τ,1)ᵀ`. So R22's `Ω`-quantifier is non-empty
    on every QM torus;
  - `thetaConst_eq`: leaf-push2's `θ[a;b](0,Ω)` equals pkg-I1's `thetaConst`.

The adopted declarations match the drafts (`same.py`, VERIFIED). Each kept declaration has the same
whitespace-normalized text, statement and proof, as in its draft:

| Draft | Identical | Missing names |
|---|---|---|
| leaf-push2, after Part I | 47 of 63 | 16 |
| bp-analytic | 143 of 146 | 3 |
| rv-qm-polar | 101 of 111 | 10 |

The missing names are exactly the verbatim copies replaced by imports (below). Leaves stay
`def … : Prop`. grep finds no `sorry`, `admit` or `axiom`, and awk finds no line of the new
modules longer than 100 characters (both VERIFIED). No build log was saved.

## Verbatim copies replaced by imports (VERIFIED: compiled)

- **leaf-push2 Part I, lines 19-1652 (def-faltings §§1-18 and H5).** All 115 declarations are SAME
  (`scratch/hdec-adopt3/dups.py`, output in `dups_lp2.txt`) as the `ZInQ.DefFaltings` declarations
  that hdec-adopt3 adopted into `Faltings/{HodgeData,IdealLines,Models,Height}.lean`.
  - `partI.py` checked the lines: of 1398 non-blank lines, 1392 occur in order in those modules,
    after renaming `LeafPush2` to `DefFaltings`.
  - The 6 that do not: 2 were rewrapped by `wrap.py`, 3 are comment lines, and 1 is
    `open PkgI3` where the module has `open PkgI3 (AbVar)`.
  - Part I is imported from `Faltings.Height` and opened (`open ZInQ.DefFaltings`). So
    `stableFaltingsHeight` in R18 and R22 is `ZInQ.DefFaltings.stableFaltingsHeight`, the
    project's one stable Faltings height.
- **leaf-push2 Part II.** `IsCurve`, `IsJacobian`, `JacobianExists` and `IsBelyiFunction` are now
  `LeafModCurves`'s (`ModCurves/Defs.lean`, `ModCurves/Leaves.lean`; SAME).
- **leaf-push2 R3.**
  - `B`, `ofInt`, `InO`, `mulCoord`, `ofInt_{mul,add,neg,zero,one}` and `O` are now `LeafQM`'s
    (`QM/Structures.lean`, SAME).
  - `QMStr` is now `LeafQM.AV.QMStr`. It is the same structure: fields
    `iota : O →+* AbVar.End A` and `injective`, over the same `O` and `PkgI3.AbVar.End`. Only the
    binders of `K` were written differently, so it is not textually SAME.
- **leaf-push2 T.** `IsComplexConj` is now `PkgI4.IsComplexConj` (`Conductor/LadicCond.lean`).
  The body is the same up to the name of the bound variable. `PkgI4.GQ` is an `abbrev` for
  `AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`, the draft's argument type, and
  `exists_isComplexConj` compiles unchanged. The draft's docstring had asked for this
  identification at integration.
- **bp-analytic §10.** The draft copied `PkgI3.AbVar` (the structure, its instances, `AbVar.ptObj`
  and `AbVar.Pt`, all SAME). That copy is dropped for `open PkgI3 (AbVar)`, so `UniformizationLeaf`
  is stated over the project's shared abelian varieties.
- **rv-qm-polar.** `B` … `O` are now `LeafQM`'s (SAME). It also has `trd`, whose text is the same
  as `GlueRepo.A1.trd`, but that one is over a different `B` (`GlueRepo.A1.B`, built
  differently), so `trd` is kept.

Left alone:

- `BPAnalytic.QM.B`, a one-line abbrev equal to `LeafQM.B`. Importing `QM.Structures` for it would
  add a large dependency.
- hdec-elementary's `dsq`, `IC2`…`IC10`, `IsGenus2` and `OnQMLocus`, copied in R3. They are not in
  the build.

## Layout

| Module | Draft part | Imports (new) |
|---|---|---|
| `LeafPush2.R18` | leaf-push2 Part II (`ffStructMap`, `ffAlgebra`) and R18 | `Faltings.Height`, `ModCurves.Leaves` |
| `LeafPush2.R22` | R22 (complex points, `IsUniformization`, `IsSiegel`, `IsPeriodMatrix`, theta) | `LeafPush2.R18` |
| `LeafPush2.R3` | R3 (Igusa invariants, Lin–Yang tuple, sextic model) | `LeafPush2.R22`, `QM.Structures` |
| `LeafPush2.T` | T10-T12, `UniformizationExists` | `LeafPush2.R3`, `Conductor.LadicCond` |
| `LeafPush2.Bridge` | new | `LeafPush2.R22`, `Analytic.QMLattice` |
| `Analytic.Torus` | bp-analytic §1-§6 | Mathlib |
| `Analytic.QMLattice` | §7 | `Analytic.Torus` |
| `Analytic.Hom` | §8-§9 | `Analytic.Torus` |
| `Analytic.Uniformization` | §10 | `Analytic.Hom`, `Objects` |
| `QM.Polar` | rv-qm-polar (all) | `QM.Structures` |

The modules split at the drafts' section boundaries. Each continuation module repeats the opens,
`set_option`, `noncomputable section`, namespace and namespace-level `variable` lines in force at
its split point.

## Axioms

`scripts/print_axioms.lean` ends with a new section of 64 entries:

- the 14 `#print axioms` targets of leaf-push2. Its 15th target, `stableFaltingsHeight`, is already
  listed as `ZInQ.DefFaltings.stableFaltingsHeight`;
- the 6 bridge theorems;
- the 10 targets of rv-qm-polar;
- 34 main theorems of bp-analytic, which had no `#print` lines.

VERIFIED (23:10 PST): all 396 entries are exactly `[propext, Classical.choice, Quot.sound]`.

## What remains (not done here)

- `scratch/h-decomposition/Leaves.lean` (outside this task's files) still lists R3, R18, R22, T11
  and T12 as opaque. Their concrete statements are now in the build, in `ZInQ.LeafPush2`.
- The analytic layer has two uniformization predicates, not yet identified with each other:
  - leaf-push2's `IsUniformization σ Λ Φ` (a map `ℂ^g → A(ℂ)_σ` for `A` over any `K`), with the
    leaf `UniformizationExists`;
  - bp-analytic's structure `BPAnalytic.Uniformization.IsUniformization A Λ φ` (`A` over `ℂ`; an
    isomorphism `ℂ^g/Λ ≃ A(ℂ)` with clauses (i)-(iii)), with the leaf `UniformizationLeafAll`.

  A bridge (bp-analytic's form, base-changed along `σ`, implies leaf-push2's) is the natural next
  piece of glue. One leaf would then suffice.
- leaf-push2's `R03_LinYang` docstring still calls the polarization step "SPECULATIVE in the
  repository, under review in rv-qm-polar". The repair was asked for in `QM/` only, so the
  adopted text is verbatim. It should cite Lemma P (`QM/Polar.lean`) at the next edit.
- leaf-push2's review RISKs stay open: R22's Pazuki Def. 2.6 coordinates, and the R3 tuple, which
  has been checked only against hdec-elementary.

## How to reproduce

1. Run `python3 -I scratch/hdec-adopt4/adopt4.py`. It regenerates the 9 adopted modules from the
   drafts, byte-identical (VERIFIED: `git status` clean after a rerun).
2. Run `python3 -I scratch/hdec-adopt4/docfix.py` on the hdec-adopt3 `QM` modules, then rewrap
   with `wrap.py`. This applies the docstring repairs once; the replaced text must be present.
3. `Bridge.lean` is hand-written.
4. Run `lake build ZInQKernel`, then `lake env lean scripts/print_axioms.lean`.
