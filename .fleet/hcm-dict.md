# hcm-dict (fleet summary)

**Result:** Lean now proves frozenTarget hypothesis `hCM : T5Glue.ShimuraMainCM` from one new printed-form leaf,
`ZInQ.Contrib.HCMDict.ShimuraThm54`: Shimura 1971 Thm 5.4 as printed, over Mathlib's Weierstrass curves and
points, with E restricted to short models and uniqueness dropped. The proved theorem is
`shimuraMainCM_of_printed : ShimuraThm54 → T5Glue.ShimuraMainCM`, in
`ZInQKernel/Contrib/OneProof/ShimuraMainCM.lean`. It uses only the standard axioms and has no sorry.

**GLUE count:** the hCM row goes from consequence/GLUE/GLUE to published (unread)/LEAF/LEAF. Strict GLUE goes from
22 to 21 and strictest from 22 to 21. No new GLUE.

**What was checked:**
- Compiled: the contribution module (lake build).
- `#discharges`: `[hCM] by shimuraMainCM_of_printed`, still assumes `[ShimuraThm54]`, standard axioms.
- Compiled, standard axioms only:
  - `FoldCheck.lean`, the manual fold. It has two variants: one calls frozenTarget, the other is the folded Main body.
  - `MainFolded.lean`, Main.lean with the fold applied.

**How the leaf is rated:** printed form. "Analytic isomorphism" is the definition `IsAnalyticUnif`. A Lean theorem
(`isAnalyticUnif_iff` with `exists_lattice_eq`) shows that the maps satisfying it are exactly
z ↦ (℘_{L₀}(αz), ℘'_{L₀}(αz)/2), so the leaf is not stronger than the print.

**What the proof uses:** the vendored FLT theorem `isUniformization_toPoint` (and its surjectivity of j), Mathlib's
℘ analyticity, the inverse function theorem, discreteness of lattices, and `T5Glue.IsScale`.

**Still to do:**
- The Shimura and Lang theorem numbers are UNVERIFIED, so the leaf enters as "unread".
- The integrator adds the locators.md row and the kinds row (`scratch/hcm-dict/kinds-row.tsv`) and applies the
  4-line Main.lean fold (spec in docs/research/hcm-dict.md §4).
- claims.tsv lists hCM as held by cm-primitive; reconcile with that claim.
