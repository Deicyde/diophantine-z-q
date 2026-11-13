# leaf-adopt3: docstring/doc repairs from rv-leaves48 and fact-check w34b

Inputs: `scratch/rv-leaves48/Repairs.md` (items P1-P7, written against Leaves.lean at 01267822) and
`docs/research/factcheck-w34b.md` (items 1-28 and nits; only those that concern
`scratch/h-decomposition/Leaves.lean` or `docs/research/h-decomposition.md` are acted on).
"Extended" means the source names the claim in one place and the same wrong claim also stands in
the file named here; the correction there is the source's own wording.

## 1. Leaves.lean: `scratch/leaf-adopt3/apply_repairs.py`

Usage: `python3 scratch/leaf-adopt3/apply_repairs.py scratch/h-decomposition/Leaves.lean`. It makes 12
exact replacements and checks that every old string occurs exactly once, both before any write
and again after the earlier replacements. On any failure it writes nothing and exits 1. The
anchors were found by content, not by Repairs.md's line numbers.

Test: the script was run on a copy only. Leaves.lean was copied at 01:28 (22455 lines, under
concurrent edit by leaf-adopt3, HEAD 3aab2e70) to `/tmp/leaves_test.lean` and the script was run
on that copy: 12 of 12 applied, exit 0. A second run on the patched copy fails as it should (exit
1, nothing written). `/tmp/leafcheck/strip_compare.py` removes nested `/- -/` blocks, `--` comments
and skips string literals. With it, the code of the original and patched copies is **identical**,
both byte-for-byte and after whitespace normalization. A negative control (one renamed `def`) is
detected. None of the new texts adds or removes a `/-`, `-/` or `--`.

| # | Source | Place (by content) | Change |
|---|---|---|---|
| L1 | rv-leaves48 P1 | `ResearchLeaves.r19` field docstring | "(not yet known non-vacuous: AN3 open)" replaced by P1's text: the value is `⊤` or the stable height, so R19-R21 hold for the definition; a defect would show up as a false `h5` |
| L2 | P1, extended | module header (leaf-adopt2 paragraph) | "height leaves (R18-R22, H5) are not yet known to be non-vacuous" replaced: where `h = ⊤`, R19, R20, R22 are vacuous and R21 is trivial; a defect shows up as a false H5 or a false R18 (R18 asserts `h < ⊤`) |
| L3 | P1, extended | §2 comment "leaf-adopt: the placeholders `R19_GaudronRemond`…" | label "**Not yet known to be non-vacuous**" becomes "**The height may be `⊤`**" (old wording kept in quotes); adds "So R19-R21 are true for the definition…" |
| L4 | rv-leaves48 P3 | `ResearchLeaves.r1r2` field docstring | gives P3's typed premise (characteristic 0, Rosati `x ↦ μ⁻¹x̄μ`, `μ = 2j + ij`, model reviews only) |
| L5 | rv-leaves48 P4 | `T23_FontaineClosure` docstring | "Exact." becomes "Consequence (matrix form of the published statement)." |
| L6 | P4, extended | hsyn-fold comment before `## §3. Glue` | "(exact, matrix form, …)" for T23 becomes "(consequence: matrix form of the published statement, …)" |
| L7 | rv-leaves48 P5 | `PkgI6.LocalReciprocityUpper` (`t16b`) docstring | "The canonical reciprocity map is one such θ" replaced by P5's wording (Serre's arithmetic-Frobenius normalization; the inverse normalization fails clause 3) |
| L8 | fact-check w34b item 1 | `LeafQM.AV.fibre_conjugates_isomorphic` docstring | now describes what the statement says: some `P : QML3 ℚ̄` with all conjugates `Aut(𝒪)`-twists of it. The link to `j₀` is in the proof only. The linked form is `exists_fibre_object` with `conj_twist_of_rational`. The statement is unchanged; see the skipped items |
| L9 | fact-check item 4 (= rv-qm-polar repair 3, retargeted) | R1hecke parenthesis in the `R1fp` docstring | "`λ' = ±λ∘ι(μ⁻¹μ')`, `μ'` rescaled to norm 6" becomes "`λ' = λ∘ι(εv)`, `v = μ⁻¹α(μ) ∈ 𝒪¹` †-symmetric (`twist_type`), `ε = sign trd v`", plus "for the Atkin–Lehner generators `i`, `j + k`, `v = −1` and `λ' = λ`" |
| L10 | fact-check item 3, extended | `R1fp` docstring, "Status of the faithfulness claim" (ii) | the compiled scope of Lemma P is now complete: N5's `μ` on `Λ = 𝒪` only; the `E0R`/`E0` identification, `Λ = 𝒪v`, Riemann forms ↔ polarizations, class number one and the descent are not in Lean |
| L11 | fact-check item 3, extended | `LeafAdopt.R1R2fpRep` docstring (Premise: Lemma P) | the same correction as L10 |
| L12 | fact-check nit ("same four fields") | `DefFaltingsSec` header comment | "same four fields" becomes "same five fields … `X` and four instances" (checked against `structure AbVar`: `X` + `grp`, `proper`, `smooth`, `geomInt`) |

## 2. `docs/research/h-decomposition.md` (edited directly)

Each changed passage carries "(fact-check w34b …)" or "(rv-leaves48 P…)". The diff is +55/−32 lines.
Sections, leaf table structure and counts are unchanged.

| Source | Place | Change |
|---|---|---|
| rv-leaves48 P1 | §0 "What is in Lean today", current-counts sentence | "R18-R22, H5 are not yet known to be non-vacuous" replaced by the ⊤-case description (old wording quoted) |
| P1 | §0 "The exact claim" caveat | replaced by "R18-R22 are consequences only together with H5, where a defect of the definition would surface" |
| P1 | §2.1 R19 *Lean* paragraph | "**Not yet known to be non-vacuous**" replaced: vacuous at an `A` with `h = ⊤`, says something only with H5 |
| P1 | §2.1 R20 *Lean* paragraph | the same |
| P1 | §2.1 R21 *Lean* paragraph | the same (trivial at `⊤`) |
| P1 | §2.1 H5 caveat | "until AN3 is proved no leaf … non-vacuous" replaced by `h = ⊤` ⟺ no metrized model; R19-R21 stay true; a defect shows up as a false H5 (cites `RvLeaves48D.sfh_eq_top_iff`, `H5_forces_metrized_model`) |
| P1 | §2.3 "Premises" bullet (leaf-adopt2) | reworded the same way |
| P1 | §5 WP10 | "(AN3, which make R19-R21, H5 non-vacuous)" becomes "(AN3, needed for H5's finiteness clause; R19-R21 are true for the definition without them)" |
| P1 | "Remaining work after leaf-adopt2" item 2 | "(non-vacuity of R18-R22, H5)" becomes "(H5's finiteness for the definition, on which R18-R22 depend)" |
| P1 | §6 R7(ii) | "no leaf over the height is known to be non-vacuous" replaced by "H5's finiteness clause is not known to hold…; the risk sits in H5" |
| rv-leaves48 P2 | §2.1 R16 *Lean* paragraph | added: T34 is equally vacuous without `X1ModelExists`; it is in neither bundle and is proved by no theorem of Leaves.lean (at 01267822); so the glue for C9, E1, E2 cannot use R16 or T34 yet |
| P2 | §2.2 T34 row, Lean column | "like R16, non-vacuous only with `X1ModelExists` and T33" |
| P4, extended | §2.2 T23 row, Lean column | "the Lean form, on `V^∨`, is a consequence of the published statement, not exact". The E/C column (which refers to the published statement) is kept |
| rv-leaves48 P6 | §2.2 T31 row, reference | "II §3" becomes "I §3.2 (UNVERIFIED, from memory; formerly II §3, glue-descent.md cites I §3)". glue-descent.md is not edited |
| fact-check item 14 | "Changes since hsyn-fold (leaf-adopt)" paragraph | "they import kernel modules" becomes "two of them, QMLeaves.lean and ModCurveLeaves.lean, import kernel modules …; T32a.lean and Faltings.lean import only Mathlib" |
| fact-check nit (h-decomposition.md:306 at 01267822) | hsyn-fold "Still not formalized" bullet | "the 14 placeholder leaves" gets "(the count at hsyn-fold; current counts in §2.3)" |
| fact-check item 5 | leaf-adopt block (leaf-qm-fp bullet) and "Remaining work after leaf-adopt" item 2 | "bp-qmmoduli §2.2" gets "(now Lemma P of rv-qm-polar, leaf-adopt2)". These are the only two of item 5's locations still unannotated; the current-state ones were already rewritten by leaf-adopt2 |
| fact-check item 3, extended | §2.1 R1, R2, R5 "Premise: Lemma P" paragraphs (three identical sentences) | compiled scope corrected as in L10 (N5's `μ` on `Λ = 𝒪` only; `eq_pm_E0_of_principal`, `riemann_sign`, `lemmaP_lattice`; list of what is not in Lean) |
| fact-check item 8 and nit "19.2k lines", extended | §2.3 "Lean check (leaf-adopt)" bullet | "118 `#print axioms`" becomes "115 `#print axioms` lines for 114 declarations (`sixContactMin_of_leaves` printed twice)"; "19.2k lines" becomes "about 19.3k lines: 19350 at 01267822" (verified with `git show 01267822:…`: 19350 lines, 115 `^#print axioms`) |
| fact-check item 18, extended | §3 G2 row | "`[K:ℚ] ≤ 324!`" is qualified: it is the generic `splitting_degree_le` (any separable `f ∈ ℚ[X]` of degree ≤ 324), not a statement about the fibre field (checked: Leaves.lean `splitting_degree_le`) |
| fact-check item 1 | §3 G4 row | added: as stated, `fibre_conjugates_isomorphic` gives only some `P`; the link to `j₀` is in the proof; the linked form is `exists_fibre_object` + `conj_twist_of_rational` |

## 3. Skipped, with reasons

**Rows named in the brief but not in factcheck-w34b.** These are §3 C2 and E1 (rows G8, G17) and
§5 WP3, WP5, WP13. factcheck-w34b has no item about any of them: it never mentions C2, E1, WP3,
WP5 or WP13. Its only h-decomposition.md items are 5, 14, 28 and the line-306 nit. So nothing was
changed under the "(fact-check w34b)" tag. What I found while checking:
- C2/E1 (G8, G17 rows; also §0 lines on `SemisimpleBaseChange`, the §2.3 "Not leaves" bullet, WP3)
  are stale for another reason. glue-ssbc (commit 1dde2937, an ancestor of 01267822) proves
  `SemisimpleBaseChange` in `scratch/glue-ssbc/SSBC.lean`, and C2/E1 without the hypothesis in
  `scratch/glue-ssbc/C2.lean` (docs/research/glue-ssbc.md). leaf-adopt3 seems to be folding it now
  (`scratch/leaf-adopt3/parts/10_ssbc.lean`).
- WP13 lists "QM dichotomy's combined locator", which loc-fix superseded (Chia-Fu Yu 2013 Thm 1.1,
  a single locator; see the T27 row).
- WP5: no stale claim found. R17 is still `opaque` in the current Leaves.lean.
These are left to the caller or the wave-25 pass, with a source tag other than fact-check w34b.

**Repairs.md**
- P2's proposed field `t35 : LeafModCurves.X1ModelExists`: changes a statement (the bundle), so
  not done. The name T35 is also taken now (`UniformizationExists`, leaf-adopt2). Also
  `docs/research/x1-belyi.md` (merged in 017c2b72) proves `X1ModelExists` from five new leaves.
  That is wave-25 material. Only P2's documentation content was applied (§2 above).
- P3's other passages (the "SPECULATIVE premise" docstrings at base 15294, 15625, 18693, 18723):
  already rewritten to Lemma P with its conditions by leaf-adopt2 (current `R1fp`, `QMLeaves`,
  `R1R2fpRep`, `R5fpStrong` docstrings). Nothing to do.
- P6: glue-descent.md's "I §3" is in another file; only h-decomposition.md was changed.
- P7 (two `GaloisRep` structures): a glue note, not a docstring error. h-decomposition.md §6 R4
  already records the two Galois-representation layers.

**factcheck-w34b, items touching Leaves.lean or h-decomposition.md**
- Item 1, the Lean fix (strengthen the conclusion of `fibre_conjugates_isomorphic`): changes a
  statement. Only the documentation fix was applied (L8, G4 row).
- Item 2 (`QML3` docstring without characteristic 0): already fixed in the current Leaves.lean (the
  `QML3` docstring says "in characteristic 0"). The kernel copy and QMLeaves.lean are other files.
- Item 3: rv-qm-polar.md and QMPolar.lean are other files. Applied only by extension (L10, L11,
  R1/R2/R5 paragraphs).
- Item 4: kernel and QMLeaves.lean copies are other files. The Leaves.lean copy was done (L9).
- Item 5: kernel, leaf-qm-fp.md and rv-qm-polar.md are other files. Its h-decomposition.md
  locations were already rewritten by leaf-adopt2, except the two historical ones annotated above.
- Item 8, "optionally drop the duplicate `#print axioms` line": that line is a command, not a
  comment, so the script leaves it. Only the count in h-decomposition.md was corrected.
- Item 28: concerns rv-blueprints.md. h-decomposition.md:765-770 is already corrected (the item
  says so).
- (a) and the remaining items (6, 7, 9-13, 15-17, 19-27 and the other nits) concern other files
  (leaf-adopt.md, leaf-push2.md, hdec-adopt2.md, def-faltings.md, rv-qm-polar.md, rv-jac-ext.md,
  rv-blueprints.md, bp-analytic.md, leaf-qm-fp.md, leaf-modcurves.md, glue-t32a.md, kernel files,
  QMPolar.lean, R16Transfer.lean). I checked them against h-decomposition.md and found no
  restatement, except the ones extended above (items 3, 8, 18 and the "19.2k" nit).
- Historical blocks of h-decomposition.md that still say "not yet known to be non-vacuous" are
  left as written: the superseded leaf-adopt counts in §0, the leaf-adopt def-faltings bullet, and
  the leaf-adopt bullets in §2.3. They describe the state at the time, and their content (`h = ⊤`
  possible, R21 trivial, R19/R20 without instances) is accurate.

## 4. Notes
- While this ran, Leaves.lean was being changed by the leaf-adopt3 fold (HEAD moved to 3aab2e70;
  hodge-lattice and h5-neron are being folded). If `HodgeLatticeTheorem` / AN3 get proved there,
  the P1 wording stays correct, but the wave-25 pass may want to say that H5's finiteness is then
  no longer open. Re-run the script on the final file: it refuses to write if any anchor moved or
  is duplicated.
- Facts in the new text that are not in the sources: R22 vacuous at `⊤` (its hypothesis
  `stableFaltingsHeight A = x`) and R18 false at `⊤` (it asserts `h ≤ bound` in `EReal`). Both
  were read from the current `R22_Pazuki` / `R18_Javanpeykar` definitions. rv-leaves48 compiled
  the ⊤ analysis for R19-R21 and H5 only, and the new text says so.
