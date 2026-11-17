# bfh-gamma0 results log

## Setup
- Merged origin/main (2880fef1e) into wip/bfh-gamma0 (merge e4b8cc397). VERIFIED.
- Build tree copied from ~/dzq-check2 (at origin/main 2880fef1e); `lake build ZInQKernel.Contrib.OneProof.BFHKronecker` OK (10121 jobs). VERIFIED.

## Gamma0New.lean (scratch; compiles, one unused-variable lint only) VERIFIED
- `IsGamma0New F`: F ∈ S_k(Γ₀(N)) Petersson-orthogonal to `V_d g` for all g ∈ S_k(Γ₀(M)), dM | N, M ≠ N.
- `restrict_levelRaise_gamma0`: restriction Γ₀(N)→Γ₁(N) commutes with V_d.
- `relIndex_gamma1_gamma0_ne_zero`.
- `isGamma0New_toCuspFormGamma0 (f : Newform N k) (hχ : f.χ = 1) : IsGamma0New (f.toCuspFormGamma0 hχ)`
  (mem_cuspFormsNew_iff + peterssonInnerCosets_restrict_restrict + restrict_toCuspFormGamma0).
- `heckeGamma0 N k`: ℤ-linear extension of Tau Ceti's `heckeSlashGamma0CuspFormEnd` (untwisted Γ₀(N)
  double-coset operators) to the Hecke ring 𝕋(Δ₀(N), Γ₀(N)).
- `coe_heckeGamma0`: on functions, `heckeGamma0 T F` = Tau Ceti's nebentypus action
  `heckeRingHomCuspCharSpace k 1 T` on the restriction of F (via `twistedHeckeSlashSum_eq_heckeSlashSum`).

## Contributor files (VERIFIED: `lake build ZInQKernel.Contrib.OneProof.BFHGamma0` OK, no warnings in the new files)
- `ZInQKernel/Contrib/OneProof/BFHPrinted/Gamma0Newform.lean` (imports Tau Ceti only): `IsGamma0New`,
  `restrict_levelRaise_gamma0`, `relIndex_gamma1_gamma0_ne_zero`, `isGamma0New_toCuspFormGamma0`,
  `heckeGamma0`, `heckeGamma0_single`, `coe_heckeGamma0`, `coeffGamma0`, `IsGamma0Newform`
  (T_n-eigen for (n,N)=1, IsGamma0New, a₁ = 1), `coeffGamma0_toCuspFormGamma0`,
  `isGamma0Newform_toCuspFormGamma0`.
- `ZInQKernel/Contrib/OneProof/BFHGamma0.lean` (imports BFHKronecker + Gamma0Newform): `IsFESignGamma0`,
  `kroneckerTwistCoeffGamma0`, `KroneckerCentralValueNeZeroGamma0`, leaf `BFHClauseIIGamma0`,
  `bfhClauseIIKronecker_of_bfhClauseIIGamma0`, `grossZagierCd_of_bfhClauseIIGamma0`,
  `frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhGamma0`, `fhNonvanishing_of_bfhClauseIIGamma0`.
- `BFHKronecker.lean`: docstring of `BFHClauseIIKronecker` only (weight k, centre L(k/2), statement-check read
  of pp. 543-544, pointer to BFHClauseIIGamma0). Statement unchanged.

## Checks (VERIFIED)
- FoldCheck.lean against main's Main.lean body (2880fef1e: open35, OpenResearchLeaves26, OpenTextbookLeaves12,
  OpenAddedLeaves17, OpenGlue8, six H29Split leaves): `frozenTarget_bfhGamma0`, `frozenTarget_bfhGamma0_allB`,
  axioms [propext, Classical.choice, Quot.sound]. Output FoldCheck-output.txt.
- Discharges.lean: `#discharges: 56 open hypotheses, 3089 theorems checked, 8 discharge one` (none from this
  task; the hFH line is fh-printed's friedbergHoffsteinB_FE_of_printed, transitive). 14 theorems, standard
  axioms. Output Discharges-output.txt.
- autofold.json (hand-fold spec; hFH is a top-level binder, not parsed by autofold.py).
- Statement-copy.lean.txt: verbatim copies of 22 statements/definitions involved.
- Statement-check record for BFH pp. 543-544: not found on this host (grep of docs/, all origin branches'
  docs/one-proof/STATEMENT-CHECKS.md and reviews.tsv). Cited per the task brief.

## Converse (VERIFIED, compiled; standard axioms)
- `cuspFormsOldGamma0`, `levelRaise_mem_cuspFormsOldGamma0`, `isGamma0New_iff` (IsGamma0New ↔ Petersson complement
  of the Γ₀ old subspace).
- `cuspFormsOld_le_comap_trace`: trace Γ₁(N)→Γ₀(N) maps Γ₁-old into Γ₀-old (cuspFormTraceGamma0_levelRaise +
  sum_diamondOpCusp_mem_cuspFormCharSpace_one + cuspFormCharSpace_one_eq_range at level M).
- `restrict_mem_cuspFormsNew_of_isGamma0New`; `IsGamma0Newform.toNewform` (Tau Ceti Newform, χ = 1);
  `IsGamma0Newform.toCuspFormGamma0_toNewform`.
- BFHGamma0.lean: `coeff_toNewform`, `bfhClauseIIGamma0_of_bfhClauseIIKronecker`,
  `bfhClauseIIGamma0_iff : BFHClauseIIGamma0 ↔ BFHClauseIIKronecker`,
  `bfhClauseIIGamma0_iff_bfhClauseII`.
- Discharges rerun: `#discharges: 56 open hypotheses, 3109 theorems checked, 8 discharge one`; 23 theorems,
  all [propext, Classical.choice, Quot.sound], no sorryAx. FoldCheck rerun: standard axioms.
