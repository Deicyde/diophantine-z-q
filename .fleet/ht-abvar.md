# ht-abvar (2026-11-17)

**Verdict.**
* derham-scholze's leaves (`ScholzeDeRhamAlg` and `T10_TateDuality`) alone do not supply `hodgeTateDecompAbVar`.
  They give de Rham with Hodge jumps in [0, 1], but no dimension of `Fil¹`, so the multiplicities (g, g) stay open.
* The smallest reroute is the manuscript's own (`lem:de-rham-descent`, L10996-10997: the Hodge numbers of
  `H¹_dR(A/F)`, then "Consequently" the weights). It needs one new leaf,
  `DeRhamScholze.HTAbVar.HodgeNumberH1AbVar`: `dim_{ℚ_p} Fil¹ D_dR(H¹_ét(A_{F̄}, ℚ_p)) = [F:ℚ_p]·g`.
  * Tags: ELLIOT for the Hodge numbers (L10996, uncited), through CITED Scholze Cor. 1.8 for the filtered comparison
    (L736-737, L10958-10959).
  * Rating: consequence, not printed form, because Mathlib has no `H_dR`.
* With that leaf, the field is **proved in Lean** with the standard axioms:
  `hodgeTateDecompAbVar_of_scholze : ScholzeDeRhamAlg → T10_TateDuality → HodgeNumberH1AbVar → HodgeTateDecompAbVar`.
  The field's statement is copied verbatim and checked `Iff.rfl`. No Picard scheme, dual abelian variety or Weil
  pairing is used.
* Faltings 1988 III.4.1 is cited only as a remark (L11003-11006). It was not used: it is not the manuscript's use,
  and it would still need the Hodge numbers.

**What compiles** (lake build ok, standard axioms):
* `ZInQKernel/Contrib/OneProof/HTAbVarScholzeDims.lean` (the leaf, plus Fontaine's `gr D_dR ≅ D_HT` with
  dimensions) and `HTAbVarScholze.lean` (the field).
* Dry run `scratch/ht-abvar/HTDryRun.lean`, built on c8-conrad2/3's copy for consumers (i) C8 and (ii) Poincaré,
  with consumer (iii) taken from the new theorem. Top `sixContactMin_of_open73HT` / `frozenTarget_ht`, standard
  axioms.
  * No hypothesis carries a Picard row.
  * The field-taint run finds no reader of `picRepresentableAbVar`, `kleimanPicZeroProper954SiteQ` or
    `hodgeTateDecompOr`. **So the Picard rows, and `hodgeTateDecompOr`, leave the route.**
* `#discharges`: 34 open, 25 discharge one, none from this task. That is expected: the field is not an open field.
  Hand-fold spec: `scratch/ht-abvar/autofold.json`.

**Net change:** kinds.tsv H rows go from 5/24 on 29 to 5/27 on 32, so GLUE is +3, of which (iii) contributes +2.
The target "net GLUE ≤ 0" is not met. The blocker: without `H_dR` in Mathlib, Scholze and the Hodge numbers can
only be consequence leaves, and those always count GLUE. Merging those two leaves, or a reading of Milne, would
bring (iii) to +1.

**What remains:** the fold (integrator; needs `--allow-rise` or a ruling), the Milne reading, a locator for
h^{1,0}(A) = g. Report: `docs/research/ht-abvar.md`.
