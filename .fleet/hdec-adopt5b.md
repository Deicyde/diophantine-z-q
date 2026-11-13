# hdec-adopt5b (fleet summary)

**Result.** All five developments are in the built project: 15 new modules (about 7,670 lines)
under `ZInQKernel/HDecomp/Textbook/`, all imported from `ZInQKernel/HDecomp.lean` in one block.
- t-different: T20-T22 local forms, proved over `Conductor/I6Base`'s leaf constants.
- t-skolem-kw: T13, T19, `FrobeniusDense` from `ChebotarevExists`, the C8 Kronecker–Weber glue,
  `c10_of_chebotarev`, and the cyclotomic Chebotarev check.
- t30-adelic: T30 from T16, and G1-adelic.
- t10-etale: the `ℤ_ℓ`-module structure, transport, the Galois action and the leaf
  `T10_TateDuality`.
- t28-igusa: the `⇒` half, the `iff`, `so3`, Mestre's step, and the reduction
  `igusaClebschSeparation_of`, plus five M3 identities proved by `ring`.

**Checked (VERIFIED).**
- `lake build ZInQKernel` exits 0 (10006 jobs).
- `lake env lean scripts/print_axioms.lean` prints 454 lists, each exactly
  `[propext, Classical.choice, Quot.sound]`; 58 are new, appended as one block.
- Verbatim copies became imports plus a selective `open`, so the theorems now prove the built
  constants (`PkgI6.*`, `GlueC10.*`, `PkgI4.*`, `GlueDescent.LeafSkolemNoether`,
  `ZInQ.LeafPush2.T10_groupIso`).
- `same.py`: every other draft declaration is identical up to whitespace.
- No `sorry` or `axiom`; no line over 100 characters.

**Not adopted.** The second batch of `ring` proofs of M3 (`m3_G23`, `m3_G33`, `m3_a112`) compiles
(7.5 min, about 15 GB) but is left out for cost, since it closes nothing.
`scratch/hdec-adopt5b/adopt5b.py --m3b` regenerates it.

**Remains.**
- Using these theorems in h-decomposition's `TextbookLeaves` bundle
  (`scratch/h-decomposition`, outside this task's files).
- The open leaves: `ChebotarevExists`, `KroneckerWeberCyclic`, `T10_TateDuality`,
  `M3Identities` (8 of 16 identities unproved), `SeparationSpecial`, and the global T20/T21.

Report: docs/research/hdec-adopt5b.md. Log: scratch/hdec-adopt5b/log.md.
