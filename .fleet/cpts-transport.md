# cpts-transport (2026-11-13)

**Result.** `FibreQM.CPtsTransport` (GLUE field 18 of g0-assemble3's `GluePieces4`) is **proved**, with no
hypotheses: `HSyn.G0Split.FibreQM.cPtsTransport_proof : CPtsTransport`. The same argument also proves period-map's
`BaseChangeClassUnique` (field 10): `HSyn.G0Split.FibreQM.PeriodMapH.baseChangeClassUnique_proof`.

**How.** Paste the pullback squares, use `IsPullback.isoIsPullback` to get `Q.A ≅ A_ℂ`, then recentre by `−E(0)`.
Rigidity (mul-rigidity's `G0FibreSimple.rigidityHom`, already proved from Mathlib) makes the recentred map a
homomorphism, and unram-tate's `bcPt` gives `A_ℂ(ℂ) ≃* A(ℂ)_σ`. Regular functions pull back along
`T = φ.left ≫ pullback.fst`. No leaf or glue is used. `UnifTransport` follows by fibre-qm-period's `unifTransport_of`.

**New bundle.** `HSyn.GluePieces5` is `GluePieces4` minus fields 10 and 18: 44 fields = 14 LEAF + 3 LEAF? + 27 GLUE.
Also compiled: `gluePieces4_of_gluePieces5`, `sixContactMin_of_leaves5 (r : ResearchLeaves4) (t : TextbookLeaves)
(gp : GluePieces5) : ZInQ.SixContactMin`, and `fibreQMPeriod_periodMap'` (without `hBC` and `hCP`).

**What compiles** (all over g0-assemble3's olean chain `import TailF`; no `sorry`; axioms `[propext, Classical.choice,
Quot.sound]`):
- `scratch/cpts-transport/CPtsTransport.lean`
- `BCUnique.lean`
- `Bundle5.lean`: `TailD.lean` body + both proofs + `GluePieces5`; 30 axiom reports, all standard.
- Flat check `Flat5.lean` (g0-assemble3's flat `G0Assemble3.lean`, md5-identical, + the new sections): exit 0 in 918 s, 0 errors, no sorry; 218 `#print axioms` reports (parsed by script, multi-line included), all `[propext, Classical.choice, Quot.sound]`, including `sixContactMin_of_leaves5`, `gluePieces4_of_gluePieces5`, `cPtsTransport_proof`, `baseChangeClassUnique_proof`

**fibre-qm-period's other three glue Props** (`PeriodMapGlue`, `HauptmodulUnique`, `QMDenZeroCM3`) are still open,
through period-map's pieces. The argument closes only the base-change piece `BaseChangeClassUnique`.
- `PiTwistC`: moduli on `ℂ`-points.
- `QMTwistLattice`: `Hom`-T11a plus Skolem–Noether.
- `CMDescends`: LEAF?, Shimura–Taniyama.
- `S8Nonzero`, `SphereFactorAffine`, `S8WeightExact`: numerics and complex analysis.
- `ValenceBoundGammaStar`: LEAF.

None of these is reachable by the pullback/rigidity argument.

**Remaining / integration.**
- Add the two proof files as a part after e20; they need a15, a45, a80 and e20.
- Swap `GluePieces4` for `GluePieces5`.
- A kernel port would need kernel copies of mul-rigidity and `bcPt`.
- Report: `docs/research/cpts-transport.md`. Model work only, no human review.
