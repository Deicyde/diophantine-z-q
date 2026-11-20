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
