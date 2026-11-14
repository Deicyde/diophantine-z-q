# leaf-review-a results log

- 2026-11-13 18:07 merged origin/wip/leaf-fold3 (f7951690) into wip/leaf-review-a (fast-forward of 8ec80711 base).
- Statements read in `scratch/leaf-fold3/Leaves3.lean` (flat file of leaf-fold3; line numbers below refer to it).
- Bundle field types: `OpenResearchLeaves2` (l.83173), `OpenTextbookLeaves3`, `OpenAddedLeaves3` (partsF/d90_fold3.lean l.109-170).
- `t24 : EigenformTwist` inside `namespace HDec.HSyn` resolves to `HDec.HSyn.EigenformTwist` (l.21912);
  `HDec.PkgI4.EigenformTwist` (l.4617) has the identical body (VERIFIED, read).
- `PkgI1.ThetaModularity` (l.295): numerical check `py/theta_mod_check.py` (mpmath 1.3.0 from the uv cache, venv /tmp/lra-venv,
  30 digits, lattice sum |n_i| ≤ 7) at Ω = [[0.13+1.1i, 0.21+0.35i],[0.21+0.35i, −0.37+0.9i]] for 5 matrices
  satisfying Mathlib's `M J Mᵀ = J` (J, two symmetric translations, diag(U, U^{-T}), a partial J):
  `Σθ⁸(MΩ)/(det(CΩ+D)⁴Σθ⁸(Ω))` and `∏θ²(MΩ)/(det(CΩ+D)¹⁰∏θ²(Ω))` are 1 to ≥ 24 digits. VERIFIED (computed).
- Group F read (l.21761-21925 HSyn defs; l.4010-4560 PkgI4 defs; R14Det l.35290; R16 l.16804 with l.16485-16700;
  CarayolR17' l.40239 with LadicCond l.39960-40060). Findings in docs/research/leaf-review-a.md §F.
- `HeckeRest.QMAutCard`, `HeckeRest.ALFixedPoints` (l.98696, 98722; QMStr l.14323, QMIso l.14837, com/HasCM l.14896-14906,
  rep/tt l.56001-56008), `TSHecke.Y3Connected` (l.97457; R1fpProps l.15235), `ThetaPt.ThetaRatiosAlgebraic`
  (l.43206; IsPeriodMatrix l.21096, thetaConst l.21107) read.
