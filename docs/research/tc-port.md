# tc-port: Tau Ceti vendored into ZInQKernel/Contrib/TauCeti

## Main result

1118 modules of Tau Ceti (commit 5a01f5fe, Lean v4.35.0) are vendored under
`ZInQKernel/Contrib/TauCeti/` and **all compile** against this project's pins (Lean 4.35.0,
Mathlib 56a00585), with 8 vendored files lightly edited and 1 backport file added. Every one of
the 24759 constants declared in the 1119 modules (1118 vendored + backport) depends only on
`propext`, `Classical.choice`, `Quot.sound` (VERIFIED, `scratch/tc-port/AllKW.lean`). No vendored
module uses `sorry`, `native_decide` (`Lean.ofReduceBool`) or any other axiom.

Main declarations now available (VERIFIED, `#check` in `scratch/tc-port/Axioms.lean`):

```lean
-- Chebotarev density theorem, module ZInQKernel.Contrib.TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount
NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet : ∀ (K : Type u_1) (L : Type u_2) [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field L] [inst_3 : NumberField L] [inst_4 : Algebra K L] [inst_5 : IsGalois K L]
  (C : ConjClasses Gal(L/K)),
  NumberField.Set.HasNaturalDensity (NumberField.Chebotarev.frobeniusPrimeSet K L C)
    (↑(Nat.card ↑C.carrier) / ↑(Nat.card Gal(L/K)))

-- Hilbert's different formula, global, module ...NumberField.LocalGlobal.Different.Exponent
IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one : ∀
  {K : Type u_1} {L : Type u_2} [inst : Field K] [NumberField K] [inst_2 : Field L] [inst_3 : NumberField L]
  [inst_4 : Algebra K L] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) [IsGalois K L],
  multiplicity w.asIdeal (differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) =
    ∑ᶠ (i : ℕ), (Nat.card ↥(Ideal.ramificationGroup Gal(L/K) w.asIdeal i) - 1)

-- different exponent in a fixed field, module ...NumberField.LocalGlobal.Different.Permutation
IsDedekindDomain.HeightOneSpectrum.ramificationIdx_mul_multiplicity_differentIdeal_fixedField : ∀ {K : Type u_1}
  {L : Type u_2} [inst : Field K] [inst_1 : NumberField K] [inst_2 : Field L] [inst_3 : NumberField L]
  [inst_4 : Algebra K L] [IsGalois K L] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
  (H : Subgroup Gal(L/K)),
  w.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥(IntermediateField.fixedField H)) *
      multiplicity
        (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ↥(IntermediateField.fixedField H))
            w).asIdeal
        (differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers ↥(IntermediateField.fixedField H))) =
    ∑ᶠ (i : ℕ),
      (Nat.card ↥(Ideal.ramificationGroup Gal(L/K) w.asIdeal i) -
        Nat.card ↥(Ideal.ramificationGroup Gal(L/K) w.asIdeal i ⊓ H))
```

The three Step-3 targets built with **no local change at all** (commit b962519c).
Kronecker–Weber itself (`TauCeti.ClassFieldTheory.kroneckerWeber`) is NOT here: it lives in the
44 nov01-only modules that task kw-new backports on top of this branch.

### `#print axioms` (VERIFIED, `scratch/tc-port/Axioms.out`)

Each of the following prints `depends on axioms: [propext, Classical.choice, Quot.sound]`:

- NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet
- NumberField.Chebotarev.tendsto_frobeniusPrimeCount
- IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one
- IsDedekindDomain.HeightOneSpectrum.differentExponent_adicCompletion_eq_multiplicity_differentIdeal
- IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_adicCompletionIntegers_eq_multiplicity_asIdeal
- IsDedekindDomain.HeightOneSpectrum.ramificationIdx_mul_multiplicity_differentIdeal_fixedField
- class field theory sample: TauCeti.ClassFieldTheory.ClassFormation.ker_artinMap,
  TauCeti.ClassFieldTheory.ClassFormation.surjective_artinMap,
  TauCeti.ClassFieldTheory.fixingSubgroup_classField, TauCeti.ClassFieldTheory.ker_localArtinMap,
  TauCeti.ClassFieldTheory.surjective_localArtinMap,
  TauCeti.ClassFieldTheory.index_normGroup_of_isMulCommutative,
  TauCeti.ClassFieldTheory.exists_openSubgroup_artinMap_mem_iff,
  TauCeti.ClassFieldTheory.isOpen_localNormSubgroup,
  TauCeti.ClassFieldTheory.herbrandQuotient_rep_globalFormation_eq_degree,
  TauCeti.ClassFieldTheory.subsingleton_h1_globalFormation_of_forall_index_le,
  TauCeti.ClassFieldTheory.globalNormSubgroup_eq_range_classField

Full audit (`scratch/tc-port/AllKW.lean`, imports all 1119 modules, runs `Lean.collectAxioms` on
every constant whose module is under `ZInQKernel.Contrib.TauCeti`):
```
modules: 1119; constants audited: 24759; axioms used (union): [Quot.sound, Classical.choice, propext]
constants with a nonstandard axiom: 0: []
```

## Provenance and license

- Repository: https://github.com/TauCetiProject/TauCeti
- Commit: 5a01f5fe3621126cccf9ba22e700493cbc7b7156 (2026-10-17 12:45 UTC), checkout ~/tc-oct16,
  Lean v4.35.0, Mathlib ccbef15e.
- License: Apache License 2.0. Authors: The Tau Ceti contributors.
- Every vendored file keeps its copyright header verbatim and gets one provenance line
  `-- Vendored from Tau Ceti (..., commit 5a01f5fe3621, module TauCeti.X), Apache-2.0.`
  Imports `TauCeti.X` are rewritten to `ZInQKernel.Contrib.TauCeti.X` (tool:
  ~/dzq-runs/tc/tcport.py). Names and namespaces unchanged.
- Attribution also in `ZInQKernel/Contrib/TauCeti/Notice.lean` (docstring only).

## Module lists

- port1.txt (397): oct16 import closures of `TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount`
  and `TauCeti.NumberTheory.NumberField.LocalGlobal.Different.{Exponent,Permutation}`.
- `scratch/tc-port/kw-oct16.txt` (714): kw-rest.txt minus kw-new-nov01.txt (the modules of the
  nov01 Kronecker–Weber closure that exist at oct16 and are not in port1).
- `scratch/tc-port/extra-oct16.txt` (7): oct16 modules imported by the oct16 versions of the
  above but in neither list (at nov01 those imports had changed), vendored with tcport.py:
  TauCeti.Algebra.Group.Coprime, TauCeti.Algebra.Order.Hom.MonoidWithZero,
  TauCeti.FieldTheory.IsRealClosed.Real, TauCeti.GroupTheory.GroupAction.Stabilizer,
  TauCeti.NumberTheory.NumberField.FinitePlace, TauCeti.NumberTheory.NumberField.Global.Adeles.Away,
  TauCeti.RepresentationTheory.FDRep.
- `scratch/tc-port/oct16-closure.txt` (1118): the oct16 import closure of all of these; it is
  closed (0 missing modules). 248300 lines of Lean in the vendored tree.

## Options (Step 2)

Tau Ceti's lakefile sets `weak.linter.mathlibStandardSet = true`, `weak.linter.style.longFile =
1500`, `weak.linter.style.longFileDefValue = 1500`, `weak.linter.style.header = true`,
`warningAsError = true`. These are linters / warnings-as-errors only; `autoImplicit` and
`maxHeartbeats` keep the Lean defaults in both projects. No file-level `set_option` was needed;
the lakefile is untouched.

## Local changes (one line per file; paths under ZInQKernel/Contrib/TauCeti/)

Cause: Mathlib commits between our pin 56a00585 and Tau Ceti's ccbef15e (85 commits).

- `Topology/Algebra/Group/Profinite/Generation.lean`: `rfl` added after `simp` in
  `TauCeti.convergesToOne_iff` (residual goal `s \ U = {x | x ∈ s ∧ x ∉ U}`; Mathlib #41506
  "Set as a one-field structure" is after our pin).
- `RepresentationTheory/Homological/ContCohomology/Coinduced/Discrete.lean`: explicit `G A` in the
  `IsZeroApply`, `IsAddApply`, `IsSMulApply ℕ` instances for `DiscreteCoind G U A` (Mathlib #42704
  made those arguments implicit after our pin).
- `RepresentationTheory/Homological/GroupCohomology/PrimeIndex.lean`: `.isPGroup` → `.isPGroup'`
  (2 places; Sylow field name at our pin, Mathlib #44454 after our pin).
- `RepresentationTheory/Homological/TateCohomology/TrivialityCriterion.lean`: `.isPGroup` → `.isPGroup'`.
- `NumberTheory/ClassFieldTheory/Formation/InvariantKernel.lean`: `.isPGroup` → `.isPGroup'`.
- `Topology/Algebra/Group/Profinite/Sylow/Basic.lean`: `.isPGroup` → `.isPGroup'`.
- `Topology/Algebra/Group/Profinite/Sylow/Existence.lean`: `.isPGroup` → `.isPGroup'`.
- `Topology/Algebra/Group/Profinite/Sylow/Containment.lean`: added
  `import ZInQKernel.Contrib.TauCeti.MathlibBackport.Sylow`.
- NEW `MathlibBackport/Sylow.lean`: `theorem Sylow.maximal_isPGroup (P : Sylow p G) :
  Maximal (fun Q : Subgroup G ↦ IsPGroup p Q) (P : Subgroup G)` (a field of `Sylow` after
  Mathlib #44454; here derived from `isPGroup'` and `is_maximal'`).
- NEW `Notice.lean`: attribution docstring, no declarations.

All other 1110 vendored files are byte-identical to the tcport.py output (VERIFIED by
regenerating each file from ~/tc-oct16 and comparing).

## Build measurements (VERIFIED)

Host: 192 cores, 235 GB RAM, shared with other agents (load 10–16 during the runs);
LEAN_NUM_THREADS=32; Mathlib oleans prebuilt.

- Full cold build of all 1119 modules (`lake build` of every module; the TauCeti build outputs
  had been moved aside): **real 6m02s**, user 66m43s, sys 8m22s, 5853 jobs, 1119 modules built.
  Sum of per-module times reported by lake: 3123 s. Slowest modules:
  FieldTheory.GaloisCohomology.Cyclic 70 s, RepresentationTheory.Homological.ContCohomology.RestrictScalars 45 s,
  NumberTheory.ClassFieldTheory.Local.Unramified 44 s,
  RepresentationTheory.Homological.ContCohomology.Corestriction.AllDegrees 39 s,
  NumberTheory.ClassFieldTheory.Global.Coefficients 30 s.
- Warm rebuild (no change): **real 5.8s**.
- The 397 port1 modules alone, cold: real 1m22s (user 14m57s).
- Build output size: 552 MB (lib: olean/ilean/ir), 1.5 GB (ir: generated C).
- `scratch/tc-port/AllKW.lean` (import everything + audit) runs in 1m57s.

Note: the `ZInQKernel` library has no globs, so `lake build ZInQKernel` builds only modules
imported from `ZInQKernel.lean`; the vendored modules are built by naming them (or by importing
them from a Contrib file).
