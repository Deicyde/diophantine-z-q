# pb-fix3 (fleet summary)

**Result: `r11r12 : PanBerger` is discharged with −1 GLUE, from two leaves rated printed form.**
`HDec.PkgI4.PanDict.panBerger_of_printedPV` (new file `ZInQKernel/Contrib/OneProof/PanBergerDict.lean`) takes
`PanPrintedP` (Pan 2022, Thm 1.0.4) and `BergerPrintedV` (Berger 2002, Thm 0.7). It also uses the current bundle's
`dsThm965Printed`, `eigenformCoeffFieldFinite` and `dsThm966Printed`. bst-construct's spec named
`dsThm965Weak`/`dsThm966`, which main no longer has, so this spec supersedes it.

* `PanPrintedP` transcribes Pan's hypotheses and conclusion:
  * Hodge–Tate multiplicity `dim_E (V ⊗ ℂ_p(w))^G`;
  * irreducible as "no stable subspace";
  * "comes from a cuspidal eigenform up to twist": a Tau Ceti `EigenformAwayFromLevel` `g`, a `ρ_g` attached
    through `ι_p` (geometric Frobenius traces), and `ρ ≅ ρ_g ⊗ ψ`.

  The dictionaries to the kernel forms are proved in Lean:
  * `localDistinctHTP_iff`: printed HT ⇔ the finrank form;
  * `isIrreducibleP_of`: Burnside form ⇒ irreducible;
  * `exists_normalized_of_eigenform`: passes to the newform via Tau Ceti's DS 5.8.4, giving the kernel's
    `IsNormalizedEigenform` (converse `exists_eigenform_of_normalized`);
  * `one_le_weight` and `trace_of_twist`.
* `BergerPrintedV` is Berger for one continuous `ρ_E : G_Qp → GL_n(E)`. `bergerPrintedB_of_V` (via
  `continuous_model`) gives bst-construct's form. Otherwise the check against Thm 0.7 found no new issue
  (bst-construct's unread flags on `A_max`/`B_max` wording remain).

**Compiles (VERIFIED):**
* the contribution builds, along with `Main` and `Discharges`;
* 11 declarations use only the standard axioms;
* `#discharges` shows `OpenResearchLeaves31.r11r12` discharged;
* autofold dry run: strict 11/18 → 13/17, i.e. GLUE 18 → 17. Its output compiles, and `sixContactMin_of_open49`
  uses only the standard axioms.

**Remains:**
* read Pan FM.tex L253 for the exact attachment formula (recalled; arithmetic Frobenius would also work via
  `ρ_g^∨`), and the JAMS numbering;
* read Berger §1.2;
* locator rows R11/R12 for the new leaves;
* the fold also needs bst-construct's `BergerBst.lean`, which is on this branch but not yet on main.

Report: `docs/research/pb-fix3.md`. Spec: `scratch/pb-fix3/autofold.json`.
