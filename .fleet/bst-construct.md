# bst-construct (2026-11-16)

**Result.** `r11r12` (Pan + Berger) is discharged with Berger's period rings built in Lean inside Mathlib's `B_dR`.
The theorem is `HDec.PkgI4.BergerBst.panBerger_of_printedB_weak`, in `ZInQKernel/Contrib/OneProof/BergerBst.lean`.
It uses two leaves, `BergerPrintedB` (Berger 2002 Thm 0.7) and `PanPrintedB` (Pan 2022 Thm 1.0.4), plus the
bundle's existing fields `dsThm965Weak` and `dsThm966`.

* **The rings.** `A_max = {Σ a_n (ω/p)^n, a_n ∈ A_inf → 0}` ⊆ `B_dR^+`; `B_max = A_max[1/p][1/t]`;
  `B_st = B_max[log [p̃]]`.
* **The definition.** "Semistable" is Fontaine's admissibility, `dim_{B_st^{G_K}} (B_st ⊗ V)^{G_K} = dim V`.
  There is no abstract `B_cris[X]` and no normalization.
* **Ratings.** Both leaves are rated printed form. The remaining flags are reading flags:
  * Berger §1.2's wording of `A_max`, recalled, not read;
  * admissibility over `B_st^{G_K}` rather than over `F`, which agree by Fontaine's theorem;
  * locators;
  * Pan's eigenform reading, unchanged from pb-fix2. `PanPrintedB` is `PanPrintedU` with only the pst predicate
    changed, so any settlement of that reading applies verbatim.
* **Fold.** The dry run gives strict 34/11 → 36/10 and strictest 34/11 → 36/10 (−1 GLUE).

**Proved in Lean (standard axioms, 23 declarations checked):**
* `B_max^+`, `B_max` and `B_st` are `G_{ℚ_p}`-stable, with `σ(log p̃) = log p̃ + log[u_σ]`;
* `log` is additive on `1 + ker θ` (Rees-algebra argument);
* `log[ε] ∈ A_max`;
* `t ≠ 0`, and `ε` exists;
* `A_max` does not depend on the generator of `ker θ`;
* the trivial representation is admissible;
* `B_dR^+ → B_dR` is injective;
* `B_st ≅ B_max[X]`, given the named Prop `LogPTildeTranscendental`;
* admissibility ⇔ pb-fix2's `[K_0:ℚ_p]·dim V` form, given the named Prop `FontaineBstInvariants`.

Neither named Prop is used by the fold.

**What compiles.**
* `lake build +ZInQKernel.Contrib.OneProof.BergerBst` succeeds.
* `#discharges` shows `OpenResearchLeaves26.r11r12` discharged.
* The scan finds 0 hits.
* `scratch/bst-construct/FoldDryRun.lean` (the autofold dry run) compiles, and `sixContactMin_of_open36` uses
  only the standard axioms.

**What remains.**
* Read Berger 2002 §1.2 against `Amax`, `Bmax` and `Bst`.
* The transcendence of `log [p̃]` over `B_max` is not proved. It needs Fontaine's cohomological input, and it is
  isolated as a named Prop.
* Locator rows for the two new leaves.
* The fold itself, from `scratch/bst-construct/autofold.json`.

Report: `docs/research/bst-construct.md`.
