# leafq-check (fleet summary)

**Verdict.** Of leaf-fold4's seven LEAF? fields, one is now a theorem and three were replaced by smaller
statements. All of this compiled, with no `sorry` and only `propext`, `Classical.choice`, `Quot.sound`.
- **`GammaStarGen` is proved from Mathlib alone.** It is a descent on the Γ*-orbit of i+j: four Dirichlet
  walls and a 3-variable certificate.
- **`ValenceBoundGammaStar` now rests only on `ValenceFormulaGammaStar`.** That leaf is the published
  valence formula, with e_P defined in Lean. The bound e_P ≤ 6 (crystallographic restriction) and the
  valence count are proved.
- **`CMDescends` now rests only on `STQM`.** That leaf is Shimura–Taniyama for QM surfaces with CM; the
  bundle leaves t11b, t5 and r1r2 are also used. The descent of ι, the CM and the level structure is
  proved, and so is torsion descent from T5.
- **`QMHauptmodul` is narrowed to `QMHauptmodulBase3`.** Four facts are now proved:
  - the CM points of each discriminant form one Γ*-orbit;
  - j_θ(√2+i) = 0;
  - the pole at i√3, from R4, GammaStarGen and the valence bound for a weight-20 form;
  - what is left is the Hauptmodul property plus the value −16/27.

`ThetaRatiosAlgebraic`, `X6ConicModel` and `Y3Connected` are true, consequences of published results, and
not splittable in Lean today. Their sources are listed in the report.

**What compiles.** `scratch/leafq-check/Fold.lean` (over leaf-fold4's olean chain):
`HDec.HSyn.sixContactMin_of_open10 : OpenResearchLeaves2 → OpenTextbookLeaves4 → OpenAddedLeaves10 →
OpenGlue4 → ZInQ.SixContactMin`. That is 26 + 19 + 19 + 1 = 65 fields, against leaf-fold4's 66, with 4
LEAF? instead of 7. Per-candidate files:
- `GammaStarGen.lean`, `ValenceBound.lean`, `QMHauptmodul.lean`: `import Mathlib`, checked with
  `lake env lean`;
- `CMDescendsGlue.lean`, `QMHauptmodulCM.lean` and the verbatim copies of the other four: checked with
  `chk.sh`, which needs leaf-fold4's compiled chain.

Report: `docs/research/leafq-check.md` (verdict table first); log: `scratch/leafq-check/log.md`.

**What remains.**
- LEAF?: thetaRatiosAlgebraic, qmHauptmodulBase3, x6ConicModel, y3Connected.
- Human checks: the new LEAFs `ValenceFormulaGammaStar` (normalization, constant m/12) and `STQM`
  (Shimura–Taniyama up to isomorphism). Every theorem number is UNVERIFIED (no network).
- Integration: append Fold.lean's body to the chain after TailK.
