# loc-fix: the repairs of rv-loc-leaves and rv-nocm applied

Task loc-fix, 2026-11-12. Base: origin/wip/w32-base (bf1323f9). Inputs: `docs/research/rv-loc-leaves.md`,
`docs/research/rv-nocm.md` (model reviews, not human reviews). Log: `scratch/loc-fix/log.md`.

## Result

No published statement of the project now carries T27 without Yu's hypothesis "indefinite", the
count `#CM(R) = h(R)`, or "indices 4, 6, 2" for the map `X₆ → X₆/W`. The Lean leaf T27 was the only
Lean statement that had to change. It is now the faithful form `QMDichotomyYu`, which is weaker
than the old one. Everything else changed in docstrings and notes only. Every change carries a
dated note saying what changed and why.

1. **T27, Lean (VERIFIED, compiled; see Build).** Changed in `ZInQKernel/HDecomp/Objects.lean` and
   in `scratch/h-decomposition/Leaves.lean`:
   - `PkgI3.QuatIndefinite a b := 0 < a ∨ 0 < b`. This says `ℍ[ℚ,a,b] ⊗ ℝ ≅ M₂(ℝ)`.
   - `PkgI3.QMDichotomyYu` is the leaf: Yu, JPAA (2013) Thm 1.1, with the hypothesis
     `QuatIndefinite a b`. The volume number 217 is from memory and marked UNVERIFIED.
   - `ObjBridge.QMDichotomyYu`, with `ObjBridge.qmDichotomyYu_iff`, is the same leaf over the
     shared layer.
   - Both `I3Leaves` bundles have the field `qmDichotomy : QMDichotomyYu`, and `i3Leaves_iff` is
     re-proved with the new iff. In Leaves.lean the HSyn bundle field is
     `t27 : PkgI3.QMDichotomyYu`.
   - **The old form was removed.** The old `QMDichotomy` Prop, which had no "indefinite", is gone
     from both files, together with `qmDichotomy_iff` and Leaves.lean's `qmDichotomyYu_of_qmDichotomy`.
     The old conclusion survives only at the project's `B = (2,−3)`, as the lemma
     `PkgI3.qmDichotomy_B6`. That lemma is proved from `QMDichotomyYu` and
     `quatIndefinite_two_neg_three`.
   - **Consumers.** The only consumers of the leaf are the two `I3Leaves` structures,
     `i3Leaves_iff` and the HSyn bundle. I checked this by grep over `ZInQKernel/`, `scripts/` and
     Leaves.lean. Nothing else needed re-proving.
   - **Out of scope.** Other tasks' scratch copies still define the old form:
     `scratch/obj-bridge`, `glue-I3-linalg`, `glue-ssbc` and `hsyn/tail.lean`. They are outside
     this task's edit list and were not touched.
2. **R05 and R02 (rv-nocm §3.1, §3.2).** The CM count is now `2^{b(R)} h(R)` on `X₆ = X₀(6,1)`,
   with `b(R) = #{p | 6 inert in k}`. The numbers `(4,6,2)` are now described as orbifold orders of
   `Γ*`. The indices of `Y₃ → P¹_j` are given as glue, from torsion-freeness and normality of `Γ₃`
   (`RvNocm.ramification_eq_orbifold_order`), and `X₆ → X₆/W` has indices `2,2,2`. Applied in:
   - **h-decomposition.md**: R2 and R5 replaced by rv-nocm's exact texts, with the audit details
     and history kept. The §0 list items 2 and 5 were updated, and the §6 R1 and R2 risk entries
     got update notes.
   - **glue-repo.md**: leaf-table rows L2 and L14, the A10 table rows (the count, plus rv-nocm's
     inserted sentence for the case split), and the PR(i) paragraph.
   - **hdec-elementary.md**: row A2, L2(a) (a note that the index clause is glue), L3(i) and the
     Lin–Yang locator.
   - **hdec-faithful.md and hdec-alt.md**: the A2 rows, hdec-faithful's L2 and L5, and hdec-alt's
     L1.
   - **h-trust.md**:
     - A2: the Content line replaced by rv-nocm's text, plus a review note.
     - A5: a review note saying the open neatness question is settled (A5 holds).
     - A10: the supplier's count, plus a review note with rv-nocm's text for the case
       `D(R) ≠ 1` (NoCM holds).
   - **`ZInQKernel/HDecomp/Repo/PRArith.lean`**: the module docstring now gives the source of
     `(4,6,2)`.
   - **Leaves.lean**: rv-loc-leaves' `patch_leaves.py`, all 16 edits. Its output was
     byte-identical to `scratch/rv-loc-leaves/LeavesPatched.lean`, because Leaves.lean had not
     moved since 6988c7fe. The patch covers:
     - the R02, R05, R16, R17 and R22 placeholder docstrings;
     - Pan's `p = 3` proviso and Frobenius convention;
     - Kato for R13;
     - semisimplicity in R15;
     - `CarayolUnramified`;
     - the `GlueRepo.PR` header.

     loc-fix added dated adoption notes on these.
   - **R16, R17, R22**: notes in h-decomposition.md as rv-loc-leaves lists them. In
     `scratch/def-ladic-cond/LadicCond.lean`, the docstrings of `CarayolR17` and `CarayolR17'` now
     state the coverage read by the audit, instead of "content and coverage of `p ∣ N` UNVERIFIED".
     Docstrings only.
3. **Leftover locators (loc-adopt's list).**
   - **Lin–Yang "Example 30" → arXiv v1 Example 29.** Fixed in glue-repo, hdec-elementary,
     hdec-faithful, hdec-alt, pkg-I1, wk-h, rv-leaves-a, h-v14 and h-trust (history item), and in
     Leaves.lean's R03 and QMHauptmodul docstrings.
   - **"indices 4, 6, 2" → orbifold orders.** Fixed in pkg-I1, wk-h, h-v14 and h-b1. M4 is
     replaced by rv-nocm's text.
   - **TYZ `char'` "Lemma 3.8" → Lemma 3.14** in tyz-t1.md, 6 places. I re-checked this in
     `~/tyz-src/Period7.tex`: in §3 the theorem-counter environments are choice, CM point1, GZ,
     congruence, m3, CM point2, coset5, heckeaction5, integral5, coset6, heckeaction6, integral6
     and prop3.9 (3.1-3.13), then `char'` = 3.14 and `multiples1` = 3.15. VERIFIED. None of the
     listed files says "multiples1".
   - h-b1.md had no "Example 30". Its Lin–Yang mention now names v1 Example 29 in M4.

## Build (VERIFIED, 2026-11-12, 11:44-11:50 PST)

- `lake build ZInQKernel`: "Build completed successfully (9952 jobs)", exit 0, warnings only.
- `lake env lean scripts/print_axioms.lean`: exit 0. There are 182 entries: the 180 of the base
  plus the 2 added, `ObjBridge.qmDichotomyYu_iff` and `PkgI3.qmDichotomy_B6`. Every entry lists
  exactly `[propext, Classical.choice, Quot.sound]`, and there is no `sorryAx`. No existing
  entry was renamed: the removed `qmDichotomy_iff` had no entry.
- `lake env lean scratch/h-decomposition/Leaves.lean` (1m34s): exit 0, no errors.
  - It has one `sorry`, the known one in `HSyn.sixContactMin_of_leaves`.
  - It prints 81 axiom lists. 80 are standard; the one with `sorryAx` is that same theorem.
- `lake env lean scratch/def-ladic-cond/LadicCond.lean`: exit 0, 16 entries, all standard.

## Not done / open

- I did not re-read any primary source; I have no network. The readings of Yu, González–Rotger,
  Baba–Granath and Carayol are the audit's, as the reviews report them.
- The scratch copies of the old T27 in other tasks' directories are unchanged (see item 1).
- rv-loc-leaves' optional R22 fold-in (`PazukiLiteral` etc. from `PazukiR22.lean`) was not
  copied into Leaves.lean. The R22 docstring points to it.
