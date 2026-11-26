# pb-refereed-fold: `bergerSurveyF` and `panPrintedF` restated from refereed prints

**Correction (2026-11-26).** The `colmezThm01` half was not a restatement. `ColmezThm01` is the basis form `PanDict.BergerSurveyFBasis`: it implies `bergerSurveyF` (`bergerSurveyF_of_colmez`), but the converse is not proved; the tree notes that it needs the `G_K`-regularity of `B_st` (`PanBergerFontaine.lean`, §5 and the docstrings of `IsPstFBasis` and `bergerPrintedVT_of_surveyBasis`). The fold therefore made `frozenTarget`'s hypothesis strictly stronger at the same count, which the fold rule forbids even when the rating improves (the later adversarial reading, docs/research/pb-adversarial-readings.md, rated `colmezThm01` LEAF; that reading stays on record as corroboration). Ruling: `bergerSurveyF` is restored as the field, sourced to Berger, Invent. Math. 148 (2002), the manuscript's own citation (theorem number to be checked), with Fontaine's Astérisque 223 for the definitions; Colmez's theorem stays as an additive record (`PanBergerRefereed.lean`) and as a corroborating flag. Proving the `G_K`-regularity of `B_st` in Lean would make the two forms equivalent. `panThm104F` stays: its statement is `panPrintedF`'s, token for token. Pan's theorem was read in arXiv:1901.07166v2; the numbering in J. Amer. Math. Soc. 35 (2022) is unchecked.

**Result.** `ZInQ.OneProof.frozenTarget` now goes through `HDec.HSyn.sixContactMin_of_open96`
(`ZInQKernel/OneProof/H/TailZ103.lean`). Two fields of the research bundle are replaced by leaves stated from
refereed prints. The open count (24) and the strict and strictest LEAF/GLUE counts (4/17 on the 21 H
hypotheses) do not change: both new leaves are flagged pending reading, so they count GLUE until a person has
read the pages below (ruling 2026-11-17).

Model work, no human review. Every page reference below is an AI reading.

## 1. The fold

| Removed field (rating) | New leaf | Proof of the removed field | Source of the new leaf |
| --- | --- | --- | --- |
| `bergerSurveyF` (GLUE/GLUE: Brinon–Conrad Thm 9.3.5, unrefereed notes) | `colmezThm01` | `PanBergerRefereed.bergerSurveyF_of_colmez` | Colmez, *Espaces vectoriels de dimension finie et représentations de de Rham*, Astérisque 319 (2008), Théorème 0.1, p. 118 |
| `panPrintedF` (GLUE/GLUE: definitions from Brinon–Conrad) | `panThm104F` | `PanBergerRefereed.panPrintedF_of_thm104F` | Pan, J. Amer. Math. Soc. 35 (2022), Theorem 1.0.4 (read in arXiv:1901.07166v2); definitions from Fontaine, Astérisque 223 (1994), Exp. II and III |

The contribution is PR #201 (`Contrib/OneProof/PanBergerRefereed.lean`, `AbstractPstGen.lean`). It builds on
#194, which proved the two steps both old rows named: the image of Fontaine's `A_cris` in `B_dR^+` is `AcrisOf`,
and the images of Fontaine's `B_cris` and `B_st` are `BcrisOf` and `BstFOf`.

* **`colmezThm01`** is Colmez's theorem in its printed form, at `K = ℚ_p`: semi-stable means
  `B_st^+[1/t] ⊗_{ℚ_p} V ≅ (B_st^+[1/t])^d` as a module with semilinear `G_L`-action (§0.2, p. 118; the tree's basis
  form `IsAdmissibleT`), de Rham is taken in the equivalent form `dim_K D_dR(V) = d` that §0.2 prints, and
  `B_st^+ = B_cris^+[u]` (p. 120), so `B_st^+[1/t]` is `BstFOf`. Its statement is the tree's
  `PanDict.BergerSurveyFBasis` (by `rfl`); the dimension form `bergerSurveyF` follows by the existing
  `PanDict.bergerSurveyF_of_basis`.
* **`panThm104F`** has the same statement as `panPrintedF` (by `rfl`). Only the source of the definition of
  "potentially semi-stable in the sense of Fontaine" changes: Fontaine, Exp. III, 5.6.1, p. 166 (potentially
  `B_st`-admissible), in the equivalent form printed in 1.8.5, pp. 134–135 (`V` becomes `B_st`-admissible over a
  finite `L`: `dim_{B_st^{G_L}} D_{B_st,L}(V) = dim V`), with `B_st` identified with its image in `B_dR`
  (Exp. II, 4.2.4–4.2.5, p. 86).

Other prints considered for `bergerSurveyF`: Berger, Invent. Math. 148 (2002), Théorème 0.7, states the theorem for
`B_st = B_max[log [π̄]]` and only asserts (§1.2) that `D_st` is Fontaine's; Fontaine, Astérisque 295 (2004),
mentions it only in the introduction; Colmez's Bourbaki exposé 897 (2003) may not count as refereed.

## 2. Checks

* `lake build +ZInQKernel.OneProof.Main` passes.
* `#print axioms ZInQ.OneProof.frozenTarget` is `[propext, Classical.choice, Quot.sound]`.
* `scratch/one-proof/DumpCompact.lean` with `cmp_hashes.py`: no existing `ZInQKernel.OneProof` constant changed its
  type or value hash except `frozenTarget`.
* `open-statements.json` regenerated (`scripts/one_proof/OpenStatements.lean`); `render_open.py --check` passes.
* PR #201's discharge check: `DISCHARGES [OpenResearchLeaves76.bergerSurveyF] by
  HDec.PkgI4.PanBergerRefereed.bergerSurveyF_of_colmez`, still assuming `ColmezThm01`, and the same for
  `panPrintedF` with `PanThm104F`, axioms standard.

## 3. Pages a person needs to read

1. **Colmez 2008** (numdam `AST_2008__319__117_0.pdf`):
   * p. 118, Théorème 0.1: "Toute représentation de de Rham de 𝒢_K est potentiellement semi-stable."
   * p. 118, §0.2: the definitions of de Rham (with "ce qui équivaut à" `dim_K D_dR(V) = d`), semi-stable
     (`B_st^+[1/t] ⊗_{ℚ_p} V` isomorphic to `(B_st^+[1/t])^d` as a `𝒢_K`-module) and potentially semi-stable
     (semi-stable over a finite `L`); `B_cris^+ ⊂ B_st^+ ⊂ B_dR^+` are Fontaine's rings.
   * p. 120: `B_st^+ = B_cris^+[u]`.
2. **Fontaine, Astérisque 223 (1994)** (numdam `AST_1994__223__113_0.pdf` and `AST_1994__223__59_0.pdf`):
   * Exp. III, 1.8.5, pp. 134–135: "V devient B-admissible sur L" defined by `dim_{F_L} D_{B,L}(V) = dim_E V`,
     and "pour qu'un objet V de Rep(G) soit potentiellement B-admissible, il faut et il suffit qu'il existe une
     extension finie L de K … sur laquelle V devienne B-admissible".
   * Exp. III, 5.6.1, p. 166: "On dit qu'une représentation p-adique V de G est potentiellement semi-stable si elle
     est potentiellement B_st-admissible relativement à H."
   * Exp. II, 3.1.5–3.1.6, p. 81 (`B_st^+ = B_cris^+[X]`, `X ↦ λ(b)`) and 4.2.4–4.2.5, p. 86 (`ι_K` injective;
     `B_st` identified with its image in `B_dR`).
3. **Pan, J. Amer. Math. Soc. 35 (2022), 1031–1169** (doi:10.1090/jams/991): Conjecture 1.0.1 and Theorem 1.0.4
   against arXiv:1901.07166v2, pp. 2 and 5. Check that Conjecture 1.0.1 keeps "continuous, irreducible", A1–A3 and
   "up to twist"; that Theorem 1.0.4 still reads "Let p be an odd prime", with the distinct Hodge–Tate weights
   clause and the `p = 3` condition word for word; and the Notation paragraph (odd `p`, `ι_p`, geometric Frobenius,
   Hodge–Tate weight of the cyclotomic character `−1`).
