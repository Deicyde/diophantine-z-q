# hcm-printed (fleet note)

**Result: `hCM = T5Glue.ShimuraMainCM` is proved in Lean from printed leaves.** The dictionary step that re-rated it to
GLUE is now Lean. Standard axioms only.

* **New file:** `ZInQKernel/Contrib/OneProof/ShimuraMainCMPrinted.lean` (66 KB). It imports
  `ZInQKernel.Contrib.OneProof.QMRecPrinted`, so it needs qmrec-printed and shimura-split2, both merged into this
  branch. It provides:
  * `HcmPrinted.shimuraMainCM_of_printed : MainTheoremCMArith → WeierstrassUniformization → WeierstrassParam →
    WeierstrassAbVar → HomLatticeCorr → T5Glue.ShimuraMainCM`;
  * `shimuraMainCM_of_textbook`: the same with `HomLatticeCorr` replaced by the current textbook fields
    `uniformizationLeafAll` and `gagaMorphism`.
* **Finding:** qmrec-printed's `MainTheoremCM` has an existential sign (`∃ ε`), which cannot fix `ShimuraMainCM`'s
  arithmetic direction (`s⁻¹𝔞`). The leaf used is `MainTheoremCMArith`, the verbatim body at `ε = 1` (Shimura's
  normalization). It implies `MainTheoremCM`, and `mainTheoremCM_iff` checks the copy by `Iff.rfl`.
* **New leaves:**
  * `MainTheoremCMArith`: printed form; flag: pending reading of the `[s, K]` normalization, which `ShimuraMainCM`
    already assumes.
  * `WeierstrassUniformization`: Silverman VI.5.1, gz-weil's statement verbatim; printed form.
  * `WeierstrassParam`: Silverman VI.3.6 over Mathlib's Weierstrass points; printed form, weaker than the print.
  * `WeierstrassAbVar`: `E_Λ` as a `PkgI3.AbVar` with coordinates and `θ = [℘, ℘', 1]`; printed form; flag: pending
    reading of the AbVar presentation.
* **Glue proved:**
  * `lin`: a holomorphic homomorphism `ℂ/Λ' → ℂ/Λ''` in Weierstrass coordinates is `z ↦ αz`;
  * `A^σ` (points and regular functions), and `σ` on Mathlib points;
  * `core`: Weierstrass coordinates on `A^σ`;
  * ArtinCond → ArtinCondC;
  * the CM type, reflex model and reflex norm of `ℚ(√−m)`;
  * the adelic dictionary (`𝔞 ⊗ ℤ̂` ↔ closure of `𝔞` in `𝔸_{K,f}`);
  * the CM endomorphisms.
* **Checks** (all VERIFIED):
  * `lake build` of Main, Discharges and the new file succeeds (12997 jobs).
  * `#discharges`: `DISCHARGES [hCM]` by both theorems, standard axioms.
  * `autofold.py --dry-run` refuses the spec, because `hCM` is a frozenTarget argument and not a bundle field. The
    fold is manual. `FoldCheck.lean` (frozenTarget with `hCM` replaced by the leaves) compiles.
* **Remains:**
  * a reading of Shimura 1971 §5.2 for the sign;
  * a ruling on `WeierstrassAbVar`;
  * qmrec-printed must reach main first.
* No statement was changed. Report: `docs/research/hcm-printed.md`. Log: `scratch/hcm-printed/log.md`.
