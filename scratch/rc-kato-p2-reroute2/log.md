# Kato 1999 correction: results log

- **VERIFIED** (base report, log, summary and source): the old draft
  used dyadic-only localization and global torsion; its optional
  whole-H² estimate has no printed supplier. The earlier extended
  norms, §0.7 descent, finite detection and Serre proofs are retained.
- **VERIFIED** (reading desk): Kato 1999, pp. 314-319, read (AI reading
  of the published pages). The three corrections are all-prime local
  conditions, §0.6(iii) with weight −1, and primewise torsion. The
  discrepancy is in the earlier transcription and route through the
  unrevised manuscript, not in the published Theorem 0.8.
- **VERIFIED** (git grep against the base): see the
  [consumer inventory](consumers.md). 78 Lean lines match the old
  bound/interface/consumer/index names, including the base's new
  KatoP2 files and scratch audit. The old finite comparison only uses
  the `es` projection of the old bundle.
- **VERIFIED** (tool help): reviewed `lake --help` and
  `lake build --help`; Lake 5.0.0/Lean 4.35.0 exposes no jobs option.
  Use local serial commands and check `uptime` and `free -g` before
  each. Do not change `LEAN_NUM_THREADS`.
- **VERIFIED** (Lean): `KodaiLambdaTorsion.lean` elaborates with Lean
  4.35.0. At the two sign primes cut out by `X`, each localized torsion
  assumption supplies one sign annihilator. The combined annihilator
  is regular; finite generation gives one for the whole module.
- **VERIFIED** (Lean): `Kodai08Checked.lean` and `Kodai08Support.lean`
  elaborate. The full local sum is indexed by the complete set of
  prime factors of the base. The exact degree-two fragment and
  commutation at two induce the localized kernel isomorphism.
- **VERIFIED** (build): the copied build lacked the base's Kato modules
  and the helper package's objects. Source-matched local artifacts were
  reused only with the same toolchain and manifest. Lake attempted a
  wider dependency rebuild; the missing modules were then elaborated
  serially with `lake env lean -o` in dependency order. No dependency
  was left unchecked on account of a missing object. The host checks
  used the stated Linux thresholds.
- **VERIFIED** (git grep): [raw base references](base-references.txt)
  include both spellings of the fixed finite comparison.
