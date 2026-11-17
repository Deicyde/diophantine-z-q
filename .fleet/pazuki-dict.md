# pazuki-dict (fleet summary)

**Verdict: option (b), with the hypothesis direction fixed.** `pazukiCor13Upper` (`ZInQ.HeightSplit.PazukiCor13Upper`,
TailY:778) is not in printed form as stated. It has two steps beyond Pazuki's print:
- **Weak uniformization.** It accepts leaf-push2's weak `IsUniformization` (surjective analytic homomorphism with
  kernel Λ) as the print's uniformization. That is a step under the 11-16 ruling. Fixed, and the step is proved in
  Lean.
- **Analytic polarization.** It quantifies over analytic principal polarizations (`IsSiegel Ω ∧ IsPeriodMatrix Λ Ω`),
  while the print is about algebraic `(A, L)`. The consumers need analytic ⇒ algebraic: their Ω is the QM period
  matrix Ω(τ).

**Main result (VERIFIED, compiled, standard axioms).** `ZInQKernel/Contrib/OneProof/PazukiCor13Upper.lean`:

    PazukiDict.pazukiCor13Upper_of_printed :
      UniformizationLeafAll → AnalyticPPAlgebraic → PazukiCor13UpperPP → ZInQ.HeightSplit.PazukiCor13Upper

- `uniformizationLeafAll` is an existing textbook field.
- `PazukiCor13UpperPP` (new **LEAF, printed form**, flag *reading risk*): Pazuki Cor. 1.3(2), upper half, for an
  algebraic `(A_{K'}, L)`:
  - `L` is ample, symmetric, with `h⁰ = 1`;
  - the uniformization is bp-analytic's biholomorphic one;
  - Ω is the period matrix of `(A_σ, L)`, encoded by its theta divisor and the vendored zero locus.

  The Def. 2.6 coordinate risk is unchanged.
- `AnalyticPPAlgebraic` (new **GLUE, composite**): every analytic principal polarization of `A_σ(ℂ)` is the period
  matrix of an algebraic symmetric principal `L` over a number field. Sources: Appell–Humbert/Frobenius, GAGA, NS
  invariance, `Pic⁰[2]`.
  - Proved to split into `ThetaDivisorAlgebraicC` (analytic half) and `SymmPrincipalDescends` (arithmetic half).
- Proved glue: `exists_strong_of_weak`. A weak `Φ` with kernel Λ that contains no complex line equals
  `ptE ∘ φ ∘ proj ∘ D` with `D` a linear isomorphism. Inputs: homlattice lifting, av-split `ptE`, and a countability
  argument; no dimension theory.

**Checks (VERIFIED).**
- Full build of Main, Discharges and the file: OK.
- `#discharges`: `DISCHARGES [OpenResearchLeaves26.pazukiCor13Upper] by PazukiDict.pazukiCor13Upper_of_printed`,
  still assumes `[UniformizationLeafAll, AnalyticPPAlgebraic, PazukiCor13UpperPP]`, standard axioms.
- Verbatim copy of the field checked by `rfl` (`scratch/pazuki-dict/Verbatim.lean`).
- Autofold spec `scratch/pazuki-dict/autofold.json`. The dry run needs `--allow-rise`: 34/11 → 34/12, because
  kinds.tsv still rates the field LEAF; it is neutral against the 11-16 consequence rating. The generated module
  compiles (`FoldCheck.lean`, `sixContactMin_of_open36`, standard axioms).

**What remains.**
- `AnalyticPPAlgebraic` has no Lean proof. It needs analytic divisors or line bundles on `A(ℂ)`, which Mathlib does
  not have.
- Read Pazuki's Def. 2.6, and check whether he assumes `L` symmetric.

Report: docs/research/pazuki-dict.md.
