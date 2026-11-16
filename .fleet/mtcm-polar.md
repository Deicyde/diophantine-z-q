# mtcm-polar (fleet note)

**Result: `HcmPrinted.MainTheoremCMArith` and `QMRecPrinted.MainTheoremCM` are proved in Lean** for every lattice,
with no polarization hypothesis. They follow from the strict-reading print (polarized CM abelian varieties, fractional
𝓞_E-ideal lattices), Shimura's existence theorem, and the bundle's textbook fields. Standard axioms only.

* **New file:** `ZInQKernel/Contrib/OneProof/MainCMPolar.lean` (50 KB). It imports `ShimuraMainCMPrinted`, so it needs
  qmrec-printed and hcm-printed, both merged here. It provides:
  * `mainTheoremCMSign_of_polar ε : MainTheoremCMPolSign ε → CMAbVarExists → UniformizationLeafAll → GAGAMorphism →
    MainTheoremCMSign ε`;
  * `mainTheoremCMArith_of_polar` (ε = 1), `mainTheoremCM_of_pol` (existential sign);
  * `qmReciprocityL3_of_pol`, `rayClassCMAb_of_polar`;
  * `shimuraMainCM_of_polar` (this is `hCM`).
* **New leaves:**
  * `MainTheoremCMPol`: printed form. It is `HcmPrinted.MainTheoremCMSign ε` (∃ ε) plus exactly the hypotheses
    `IsOLattice 𝔞` and `∃ ζ, IsRiemannDatum Φ 𝔞 ζ` (`Tr(ζ x ȳ)`, ζ̄ = −ζ, Im φᵢ ζ > 0). Flag, reading risk: is Shimura
    Thm 18.6 / 5.15 printed for non-primitive CM types? The consumers use the induced type on E = K(√2). I believe it
    is general, and Milne's CM notes §9 is an alternative citation; UNVERIFIED.
  * `MainTheoremCMPolMax`: the ε = 1 form, needed for `hCM` only. It keeps hcm-printed's pending reading of the
    normalization.
  * `CMAbVarExists` (Shimura 1998 §6.2; Riemann's theorem plus GAGA): printed form, weaker than the print.
  * The new leaves are implied by the old ones (`mainTheoremCMPol_of_mainTheoremCM`, `mainTheoremCMPolMax_of_arith`).
* **Glue proved:**
  * step (2), `exists_zeta`, by weak approximation at the infinite places;
  * `lattice_of_unif`: N𝓞_E ⊆ 𝔞 ⊆ d⁻¹𝓞_E, by comparison with the full lattice of UniformizationLeafAll;
  * step (3): the isogeny μ : ℂ^g/Φ(N𝓞_E) → A from HomLatticeCorr, its conjugate μ^σ through the pullback square plus
    rigidity, `𝔞̂ = 𝔞 + 𝔟̂`, and the density of E in 𝔸_f ⊗ E.
* **Checks** (all VERIFIED):
  * `lake build` of the module (12231 jobs) succeeds.
  * `#discharges`: `DISCHARGES [hCM] by MainCMPolar.shimuraMainCM_of_polar`, still assuming [MainTheoremCMPolMax,
    CMAbVarExists, the 3 Weierstrass leaves, UniformizationLeafAll, GAGAMorphism]; standard axioms.
  * `FoldCheck.lean` (frozenTarget with `hCM` replaced) compiles.
  * `autofold --dry-run` refuses `hCM` (a frozenTarget argument), so the fold is manual (in the report). Specs for
    after shimura-split2 (`qmReciprocityL3`) and after qmrec-printed (`mainTheoremCM`) are ready but cannot be dry-run
    yet.
  * A read-only adversarial statement review found no soundness issue.
* **Remains:**
  * the primitivity reading, or a Lean reduction from induced to primitive types (not attempted);
  * the ε = 1 normalization reading, for the `hCM` route only;
  * the folds.
* Report: `docs/research/mtcm-polar.md`. Log: `scratch/mtcm-polar/log.md`.
