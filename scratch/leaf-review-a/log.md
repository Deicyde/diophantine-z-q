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
- Check file `scratch/leaf-review-a/Check.lean` (imports ZInQKernel.HDecomp.{ModCurves.Leaves, ModCurves.C9,
  Conductor.LadicCond, QM.Leaves, LeafPush2.R3}; seven `#print`s): `lake env lean` exit 0, 0 errors, 133 s
  (load ~10, 146 GB available). Output `check_out.txt`: the printed bodies agree with the HDec copies read in
  Leaves3.lean (R16', CarayolR17', PkgI4.EigenformTwist, R1rec, R5fp, R5fpCount, R03_LinYang). VERIFIED.
- Forks (no Lean) reviewed A-group fields: notes_A1.md (r1r2, r1b, r1rec, r5, r5count, cmOptimalEmbedding),
  notes_A2.md (r3, qmClassNumberOne, qmDenZeroCM3, x6ConicModel, qmHauptmodul second opinion). All CONSEQUENCE.
- `py/hauptmodul_check.py` re-run here (mpmath 1.3.0, 40 digits): Ω(√2+i), Ω(i√(9+6√2)) symmetric, Im Ω ≻ 0;
  j_θ(√2+i) ≈ 1e−162, j_θ(i√(9+6√2)) = −0.592592592592593 (= −16/27); j_θ invariant (≤ 3e−35) under ι(j), ι(2j+ij),
  ι((1+j)/2); near τ₀ = i√3, |Σθ⁸| and |∏θ²| both scale as ε² (orders 2 and 2, so jDen order 10, jNum order 4);
  Σθ⁸(Ω(τ))/((τ−3)(τ+1))⁴ has automorphy factor (cτ+d)⁸ for ι((1+j)/2) at two points (ratio 1.0). VERIFIED (computed).
  Docstring error found: `QMDenZeroCM3` says "zero of order 30 in τ"; it is 10.
- Own verdicts: r14, r15, r16, r17, t24, r4, thetaRatiosAlgebraic, y3Connected, qmAutCard, alFixedPoints: CONSEQUENCE.
