# h33-sign (2026-11-15)

**Verdict:** the pending-review flag on `h33 = TYZSplit.TYZThm33` can be removed. The statement is correct and no correction is needed. The kernel's `z_n = (1 − [i]) f₀(P_n)` for n ≡ 5 (mod 8), with `[i]` acting as CM by +I, is TYZ's sign. Three independent arguments:
1. **TYZ's own computation.** α = −i on the identity component (Period7.tex L1564–1566).
2. **Lean.** `scratch/h33-sign/Sign.lean` proves `tyzThm33With_iff_of_reading` with standard axioms only. For any family of CM points of TYZ's shape (either reading of `[i]`, either sign of i₀) that satisfies TYZ's printed Thm 3.6(1) `z̄ = −z + τ(1)`, TYZ's Thm 3.3 for that family is equivalent to the leaf. The other reading would force f₀(P_n) to be torsion (`torsion_of_alt_thm36`). The kernel's `basePt` satisfies the hypotheses (`basePt_reading`).
3. **Computation.** Exact PARI q-expansion checks of the eta model, `τ ↦ τ+1/4` and the Fricke involution, plus 200-digit numerics on 20 values of n: Prop 3.5(2) and Thm 3.6(1) hold with +I and fail with −I.

**Normalizations.** Every other sign and normalization in TYZThm33 was checked against the source lines and agrees; the table is in docs/research/h33-sign.md. `scratch/h33-sign/Iso.lean` (Mathlib only) compiles the algebraic parts: the curve isomorphisms A ≅ curveA and E_n ≅ curveC n, compatibility with `[i]`, the Heegner fixed points and the discriminants.

**Compiles:** Sign.lean and Iso.lean, both with 0 errors and 0 warnings.

**What remains outside Lean (recorded):**
- the shape of TYZ's z_n: this needs i₀ = ±phiC (x0-32's leaf X0AnalyticModel) and the reading X_U ≅ X0(32)_{Q(i)} (L1191–1193);
- TYZ Thm 3.6(1) taken as printed;
- the kernel leaf CMAlgebraic.

There is no human review of TYZ itself. Suggested kinds.tsv update for row h33 is in the report.
