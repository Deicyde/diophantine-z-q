# pb-fix (fleet summary)

**Result: `r11r12` (`HDec.PkgI4.PanBerger`) is discharged by `panBerger_of_printedT` from two restated leaves,
`PanPrintedT` (Pan 2022, Thm 1.0.4) and `BergerPrintedT` (Berger 2002, Thm 0.7).** It also uses `DSThm965` and
`DSThm966`, which are already leaves of the same bundle. I rate both new leaves printed form; if that holds, the
fold is −1 GLUE (dry run: strict 46/10 → 48/9, strictest 45/11 → 47/10). Report: `docs/research/pb-fix.md`.

**Repairs.**
* **Berger.** "Semistable" is now `IsSemistableOverT`: Fontaine's printed tensor form `(B_st ⊗ V^*)^{G_K}`,
  normalized by the explicit `[K_0 : ℚ_p]`. Here `K0 K = ℚ_p(roots of unity of order prime to p in K)`, which is
  the maximal unramified subextension. So `BergerPrintedT` needs no `B_st^{G_K}` step.
* **Pan.** `PanPrintedT` holds for every `ι_p : ℚ̄_p ≃+* ℂ` and concludes
  `tr ρ(σ_arith) = ψ(σ) ι_p⁻¹(a_q(g))`. It no longer asserts that the coefficients are algebraic. That is now
  glue, proved from `DSThm965`/`DSThm966` via `r14Det_of_printed`, together with a proved `ℂ ≃+* ℚ̄_p`
  (Steinitz).
* **`B_cris ≠ 0`.** Already proved by pb-sanity (merged, `PanBergerSanity.lean`).
* **Wording.** The citation fixes (Brinon–Conrad §5 Thm 5.2.1; Fontaine Exp. III 1.5) are in the new file. For
  pb-bypass's file they are a docstring patch, `scratch/pb-fix/PanBerger-wording.patch`, not applied because the
  rules forbid editing other files under `ZInQKernel/`.

**What compiles (all VERIFIED).**
* `ZInQKernel/Contrib/OneProof/PanBergerFix.lean` builds with no warnings and uses only the standard axioms
  (10 theorems checked). The contribution scan finds 0 hits.
* `#discharges` reports `r11r12` discharged by `panBerger_of_printedT`, still assuming `PanPrintedT`,
  `BergerPrintedT`, `DSThm965` and `DSThm966`.
* The autofold spec is `scratch/pb-fix/autofold.json`; its dry run compiles.
* Also proved:
  * the tensor form agrees with the Hom form (`isSemistableOverT_iff`);
  * pb-bypass's `LocalIsPst` equals `LocalIsPstT` if Fontaine's `dim B_st^{G_K} = [K_0 : ℚ_p]` holds
    (`localIsPst_iff_T`);
  * the trivial character is semistable in the printed sense exactly when that dimension identity holds
    (`isSemistableOverT_trivial_iff`).

**What remains.**
* Fontaine's `B_st^{G_K} ⊆ K_0` is still not in Lean. The leaves no longer need it for their meaning, but no
  representation can yet be shown pst in the printed sense.
* Pan's "comes from a cuspidal eigenform up to twist" is taken in its standard reading: geometric Frobenius,
  cohomological normalization, applied to `ρ^∨`.
* The locators.md rows for the two restated leaves are proposed in the report, not added.
