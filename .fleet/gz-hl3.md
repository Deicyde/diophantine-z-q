# gz-hl3 (2026-11-15)

**Result.** `hL3 = ZInQ.GZDecomp.GrossZagierHeegner` is proved in Lean from six leaves stated over genuine
definitions: `ZInQ.GZHL3.grossZagierHeegner_of_leaves`, in `ZInQKernel/Contrib/OneProof/GrossZagierHeegner.lean`.
`#print axioms` gives propext, Classical.choice and Quot.sound only. The six leaves:

- `WeierstrassUniformization`: Silverman VI.5.1, printed form;
- `StrongWeilCurve`: Eichler–Shimura with a rational Manin constant, composite;
- `IsogenyLattice`: Faltings 1983 in analytic form, composite;
- `HeegnerPointRational`: Shimura reciprocity / Gross 1984 §1–3, composite;
- `GrossZagierFormula`: GZ I.6.3 and Ch. V, `L'(E/K,1) = κ ĥ(y_K)` with `κ > 0`; printed form with the
  constant forgotten;
- `GrossConjugation`: Gross 1984 §5, `ȳ_K = −ε y_K` mod torsion, printed form.

The Heegner point is now a Lean object, `Σ_{Q∈S} weierPt E L (c·φ_f(τ_Q))`. It is built from Mathlib's
Weierstrass ℘, the Eichler integral of the Tau Ceti newform, the kernel's `HeegnerForm`, and a complete set of
Γ₀(N)-representatives.

**Glue proved:**

- the representatives exist (`heegnerRepsExist`, via SL₂(ℤ) reduction and the transform of forms);
- `weierPt` lies on E;
- the embedding ℚ(√D) → ℂ;
- `L'(E/K,1) ≠ 0` at a simple zero;
- the Ch. V corollaries: `y_K` has infinite order iff `L'(E/K,1) ≠ 0`, and rank ≥ 1.

**Finding.** With complex or arbitrary `c`, the Heegner-rationality statement would be false for CM curves
(`[i]∘φ` is not defined over ℚ). The leaves therefore use `c ∈ ℚ^×`.

**Cd form.** `Cd.lean` proves `GZStatements.GrossZagierHeegnerCd` from leaves restricted to C_d. Shimura's
theorem on CM curves replaces Eichler–Shimura plus Faltings, so it needs one deep leaf fewer. The Gross–Zagier and
Gross leaves are unchanged.

**What compiles:** both new files (`lake build`). The `#discharges` output is in
`scratch/gz-hl3/discharges-output.txt`.

**Main.lean edit (for the integrator):** replace `hL3` by the six leaves and pass
`ZInQ.GZHL3.grossZagierHeegner_of_leaves hU hSW hI hHP hGZ hGC`. Details are in `docs/research/gz-hl3.md` §7.

**What remains:**

- every locator and printed constant is UNVERIFIED (no papers on this host; `~/tyz-src` is also absent);
- `HeegnerPointRational` could be reduced further to the kernel's `ShimuraReciprocityModFn` / `X0ModuliGalois`
  leaves, plus class-group action glue on Heegner forms (not attempted);
- the TYZ Theorem 3.3 leaf (`h33`) cannot supply `hL3`, because its encoding forgets the coefficient.
