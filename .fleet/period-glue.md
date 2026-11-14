# period-glue (2026-11-13)

**Result.** None of period-map's six glue Props was changed. All six are now proved or reduced
to leaves (report: `docs/research/period-glue.md`; Lean: `scratch/period-glue/`). Every theorem
named below compiles with no `sorry` and only the standard axioms.

**Proved outright:**
- `S8Nonzero` (`s8Nonzero_proof`). The point is `Ω(√2+i) = [[(−1+i)/2, 1], [1, −1+i]]`. Each
  theta constant there factors into one-variable thetas. Every `Re θ_m⁸ ≤ 0`, and one is `< 0`.
  The only numerics are crude bounds on `e^{−π/2}`.
- `BaseChangeClassUnique` (`baseChangeClassUnique_proof`), using mul-rigidity's rigidity.
- `SphereFactorAffine` (`sphereFactorAffine_proof`). This needed three complex-analysis lemmas on
  `P¹`: the open mapping theorem, removable singularities through a branched cover, and
  injective self-maps of `P¹` fixing `∞` being affine (via Liouville).

**Reduced to leaves:**
- `S8WeightExact ⇐ ThetaModularity + GammaStarGen` (`s8WeightExact_of`). This includes explicit
  `Sp₄(ℤ)` matrices for `ι(1+i+j)` and `ι((j−3)/2)`.
- `QMTwistLattice ⇐ T11aRiemannHom`, plus Skolem–Noether, which the kernel proves
  (`qmTwistLattice_of'`). This includes `QMLatticeTwistAlg`.
- `PiTwistC ⇐ R1fp, R1hecke, R2fp, T5`, plus `AutOInnerFinite`, which mobius-glue proves.
  - `twistOrbitFinite_of'` covers the twist relation; `UnitLiftMod3` is checked by `decide`
    over 81 classes.
  - `fibreTransferC_proof` is a Jacobson argument on `Y ×_ℚ Y`.

**End to end.** `fibreQMPeriod_periodGlue` compiles in one file (`build_all.sh`).
`ThetaPt.FibreQMPeriod` now rests on:
- leaves, including the flagged candidates `CMDescends`, `GammaStarGen` and
  `ValenceBoundGammaStar`;
- `MobiusGlue` and `AutOInnerFinite`, proved by other tasks;
- the inherited `CPtsTransport`.

**What remains.**
- **Human checks:** the three flagged leaves are restated with references in report §5. The
  locators are marked UNVERIFIED because there was no network, so a human should check them.
- **Integration:** replace the copied `LeafSkolemNoether` and `AutOInnerFinite` hypotheses by the
  kernel's and mobius-glue's theorems.
- **Out of scope:** `CPtsTransport` and `R1bFamily` were not among this task's targets.
