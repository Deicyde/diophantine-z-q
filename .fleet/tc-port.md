# tc-port report

**Main result.** 1118 Tau Ceti modules (commit 5a01f5fe, Apache-2.0, The Tau Ceti contributors)
are vendored under `ZInQKernel/Contrib/TauCeti/` and all compile at our pins (Lean 4.35.0,
Mathlib 56a00585). All 24759 constants of the vendored modules use only `propext`,
`Classical.choice`, `Quot.sound` (full audit, `scratch/tc-port/AllKW.lean`); no sorry, no
native_decide.

**What compiles (VERIFIED):**
- The three targets for cheb-bridge / diff-bridge, unmodified (commit b962519c):
  `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet` (FrobeniusPrimeCount),
  `IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one`
  (Different/Exponent), `IsDedekindDomain.HeightOneSpectrum.ramificationIdx_mul_multiplicity_differentIdeal_fixedField`
  (Different/Permutation). Exact types in docs/research/tc-port.md.
- All 714 oct16 modules of kw-rest (local + global class field theory up to, not including,
  Kronecker–Weber) plus 7 extra oct16 modules they import that were in neither list
  (listed in scratch/tc-port/extra-oct16.txt and the doc) (commit 395103a4).
- Local changes: 8 vendored files (Sylow `.isPGroup` → `.isPGroup'` ×6 files, explicit `G A` in
  three `Is*Apply` instances, one `rfl`, one import) and new
  `ZInQKernel/Contrib/TauCeti/MathlibBackport/Sylow.lean` proving `Sylow.maximal_isPGroup`.
  No set_option needed (Tau Ceti's global options are only linters / warningAsError).

**Build times:** cold full build of the 1119 modules 6m02s wall (66m43s CPU, LEAN_NUM_THREADS=32);
warm rebuild 5.8s.

**What remains:** `TauCeti.ClassFieldTheory.kroneckerWeber` needs the 44 nov01-only modules
(task kw-new). Not done here by design. The moved-aside old build outputs sit in
/tmp/tc-port-build-backup-1794568897 (≈2 GB, safe to delete).

Deliverables: ZInQKernel/Contrib/TauCeti/** (incl. Notice.lean, MathlibBackport/Sylow.lean),
docs/research/tc-port.md, scratch/tc-port/{log.md,Axioms.lean,Axioms.out,AllKW.lean}.
