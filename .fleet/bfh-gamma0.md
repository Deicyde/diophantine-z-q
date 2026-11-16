# bfh-gamma0 (fleet summary)

**Result.** The last gap in BFHClauseIIKronecker is closed. The leaf is now stated over the classical
newform on Γ₀(N), as BFH print it (`ZInQ.BFHPrinted.BFHClauseIIGamma0`), and it is proved equivalent in
Lean to bfh-kronecker's leaf (`bfhClauseIIGamma0_iff`) and to bfh-leaf's (`bfhClauseIIGamma0_iff_bfhClauseII`).
The hFH discharge is rebuilt on it: hFH is replaced by a printed leaf, −1 GLUE on main (hand fold, spec in
scratch/bfh-gamma0/autofold.json).

**What compiles** (standard axioms only; 23 theorems in Discharges-output.txt, no sorry):
- `ZInQKernel/Contrib/OneProof/BFHPrinted/Gamma0Newform.lean`:
  - `IsGamma0New` (Petersson-orthogonal to V_d S_k(Γ₀(M)) for dM | N, M ≠ N), `heckeGamma0` (the Γ₀(N)
    Hecke ring acting on S_k(Γ₀(N))), `IsGamma0Newform` (T_n-eigen for (n, N) = 1, new, a₁ = 1);
  - `isGamma0New_toCuspFormGamma0` (by mem_cuspFormsNew_iff, peterssonInnerCosets_restrict_restrict and
    restrict_toCuspFormGamma0), `isGamma0Newform_toCuspFormGamma0`;
  - the converse, `restrict_mem_cuspFormsNew_of_isGamma0New` and `IsGamma0Newform.toNewform` (through the
    trace Γ₁ → Γ₀ and the diamond sums).
- `ZInQKernel/Contrib/OneProof/BFHGamma0.lean`: the leaf `BFHClauseIIGamma0` at weight k = 2, with centre
  L(k/2) = L(1) and χ_D the Kronecker symbol; the two equivalences;
  `frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhGamma0`; `fhNonvanishing_of_bfhClauseIIGamma0`.
- `BFHKronecker.lean`: docstring fixed (weight k, L(k/2), cites the statement-check read of BFH Invent.
  Math. 102 pp. 543–544). The statement is unchanged.
- The fold check against main's Main.lean body (2880fef1e, open35, 15 binders) passes with standard
  axioms. `#discharges` reports 56 open hypotheses, 3109 theorems checked, 8 discharge one (none from this
  task, as expected for a top-level binder).

**Leaf rating.** Printed form: a direct instance at k = 2, every clause literal over Mathlib, Tau Ceti or
kernel definitions, no stronger than the print.

**What remains.**
- The hand fold itself (Main.lean, kinds.tsv, locators.md, OPEN.md), which the rules forbid here.
- The statement-check record for BFH pp. 543–544 is not on this host. If it is not in the repository,
  flag the row unread.

Report: docs/research/bfh-gamma0.md. Scratch: scratch/bfh-gamma0/.
