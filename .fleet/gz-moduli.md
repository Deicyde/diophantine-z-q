# gz-moduli (fleet summary)

**Result.** `ZInQ.GZHL3.GrossZagierFormulaCd` (rated consequence: stated for the analytic Heegner point
`Σ weierPt(c φ_f(τ_Q))`) is proved in Lean from one new printed leaf, `ZInQ.GZModuli.GrossZagierModuliCd`: the
Gross–Zagier formula (GZ 1986 Thm I.6.3 / Ch. V Thm 2.1, positive constant forgotten) in its moduli form.
- **Heegner points.** They are cyclic `N`-isogenies `ℂ/Λ₁ → ℂ/Λ₂` with `End = 𝒪_D` and `𝔫 = (N, (−β+√D)/2)`
  killing the kernel, in the lattice model.
- **Parametrization.** `φ : X₀(N) → E` over `ℚ` is a point of `E(ℚ(X₀(N)))`: canonical-model function field,
  nonconstant, `φ(∞) = O`.
- **`y_K`.** It is the sum of `φ` over a complete set of Heegner points.

The proof works for every `E` (`grossZagierFormulaAt_of_moduli`, `grossZagierFormula_of_moduli`). Three things are
proved:
- the analytic parametrization is an algebraic `φ` in this sense (`isModularParam_of`), and its value agrees with the
  moduli definition at every point (`modPt_eq`);
- the classification of Heegner points (adapted basis, the action of `𝒪_D`): the lattice pairs of a complete set of
  Heegner forms are a complete set of Heegner points (`isHeegnerPointReps_of`);
- GAGA is not needed, because gz-heegner already proved that the coordinates of `φ` lie in `ℚ(X₀(N))`.

**Count.** `GrossZagierFormulaCd` (GLUE) becomes `GrossZagierModuliCd` (published, flagged unread): −1 strict GLUE.
With gz-heegner, `hL3` becomes `X0ModuliGaloisMero` (consequence) + `GrossZagierModuliCd` + `GrossConjugationCd`
(`scratch/gz-moduli/MainEdit.lean`, `frozenTarget_gzmoduli`, standard axioms). That is neutral now, and −1 once
`X0ModuliGaloisMero` is printed.

**What compiles.**
- `ZInQKernel/Contrib/OneProof/GrossZagierModuli.lean` and `GrossZagierModuli/NonVacuous.lean` (new files only):
  `lake build` OK, standard axioms (`scratch/gz-moduli/out_check.txt`).
- `#discharges`: `[hL3] by GZModuli.grossZagierHeegner_of_moduli` (the all-`E` form). The `C_d` theorem is not listed
  because `GrossZagierFormulaCd` is not yet a bundle field. `autofold.json` targets the field `grossZagierFormulaCd`,
  for use after the `C_d` split is folded.
- The verbatim target copy is checked by `rfl`.

**Rating.** Printed form (constant forgotten). Reading risk (SPECULATIVE): V.2.1 may be printed only for the strong
Weil parametrization; the leaf quantifies over every nonconstant `φ` with `φ(∞) = O`, which follows from the optimal
case. All locators are UNVERIFIED (no copy of GZ on this host).

**Remains.** A reading of GZ II §1 and V §2 against the leaf. `X0ModuliGaloisMero`. The explicit constant.
Report: `docs/research/gz-moduli.md`.

_Final commit 2026-11-16; all Lean above compiled in this worktree._
