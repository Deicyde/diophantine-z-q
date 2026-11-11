# h-adopt: report

## What was done

1. **docs/research/h-trust.md**: every repair of `docs/research/rv-h-trust.md` §6 is applied
   (S1-S4, O1-O12, R1-R6, D1-D3, N1-N3), with a changelog at the end of the note. Main points:
   - **C8 supplier added.** The 5-adic representation of a weight-`k` eigenform is de Rham
     (Hodge–Tate) at 5 with weights `{0, 1−k}`: Faltings, Math. Ann. 278 (1987); Scholl, Invent.
     Math. 100 (1990), with Faltings 1989 or Tsuji 1999; or Saito, Invent. Math. 129 (1997).
   - **Review attributions fixed.** C3's lemma `lem:de-rham-descent`, A9's Milne paragraph and C9's
     Li–Shimura sentence are new in the 11/5 text and were reviewed only by rv-h-trust, not by
     Astra. C3 is now "[M] (rv-h-trust only)".
   - **Stale statuses fixed.** A4-A6 are [M] (rv-h-b1, whose repairs 1-6 are applied in h-b1).
     The counts are now 7 / 5 / 24 [M], with no [U] step. The status rule says statuses are
     local and that later steps inherit them.
   - **Locators.** Faltings 1983: Hom is Korollar 1 (Satz 3 is semisimplicity, Satz 4
     endomorphisms). Berger: published Thm 0.7 / Cor. 5.22. N5's own Carayol locator (L9778).
     Serre *Corps locaux* VI §2 for D4.
   - **New mark ASTRA-READ.** It covers the locators that the Astra records say were opened
     (Faltings, Silverberg–Zarhin, Berger, Javanpeykar, GR14, Pazuki, the Baba–Granath
     preprint, Pan arXiv v2, Milne ADT, Buzzard).
   - **Residuals added**:
     - polarization uniqueness for A4 (elementary proof recorded, Rotger as an alternative);
     - the four rv-h-b1 §7 inputs for A4;
     - `J(u)` not a branch value (`branch_check.py`);
     - N5's integral-model route as a model-reviewed fallback for A5-A6;
     - twists of eigenforms and Li's newform theorem (C9);
     - Faltings Satz 3 and the Serre–Tate specialization (C10);
     - the Faltings 1984 erratum check;
     - the height normalizations (not a residual) and the vestigial `C_cm`;
     - §2.7 (vii), the three N5-only passages.
   - §2.3 lists nine scripts plus `rv_checks.py` and `branch_check.py`, with the c3_breaks rerun.
     §3 holds the repaired drafts, and §4 says what is left.
2. **ZInQKernel/Hypotheses/Height.lean**: the module docstring and the docstring of
   `ZInQ.SixContactEstimate` are replaced by the repaired drafts of h-trust §3.
   **ZInQKernel/Hypotheses/HeightMin.lean**: a "Trust" paragraph is appended to the module
   docstring (it names the four admissibility facts of `Main.lean:70-73`), and the docstring of
   `ZInQ.SixContactMin` is replaced. The text:
   - names no unpublished upstream supplement as an input;
   - says which arguments rest on model reviews only (rv-h-novel, Astra, rv-h-a011, rv-h-cm,
     rv-h-b1, and rv-h-trust alone for the three N5-only passages);
   - keeps every line at most 100 characters.
3. **KERNEL_PLAN.md**: the H row of the dependency table is replaced by the repaired row. That
   row was the only H trust passage; nothing else changed.
4. **Checks**:
   - `lake build ZInQKernel` succeeds (9919 jobs).
   - `lake env lean scripts/print_axioms.lean`: all 59 entries show exactly
     `[propext, Classical.choice, Quot.sound]` (`scratch/h-adopt/print_axioms.out`).
   - `git diff` of the two Lean files shows only comment changes. With comments stripped
     (`scratch/h-adopt/strip_comments.py`), both files are identical to the previous commit.

No statement, definition or proof was changed. No new Lean declarations.

## What is left (unchanged mathematics; network needed)

The locator checks of h-trust §2.5 remain. The most important are:

- Pan's JAMS text (Thm 1.0.4);
- Carayol's Théorème A at `F = ℚ`;
- the new C8 supplier;
- the hypothesis of Shimura 1973 Thm 1 (Hecke- and Fricke-stable span).

The ASTRA-READ locators were read by a model only.

## Problems / suggestions

- The three passages new in N5 (C3's de Rham descent lemma above all, then A9's Milne paragraph
  and C9's Li–Shimura sentence) have a single model review. A second independent review of C3's
  lemma would remove the thinnest point of the trust statement.
- C8 rests only on Astra's reading of the 11/4 text, which did not name the eigenform input. A
  short focused review of N5 L757-768 with the new supplier would be worthwhile.
- `scratch/rv-h-trust/` has no `reruns/` subdirectory on this branch, although rv-h-trust §7
  mentions one. The rerun outcomes are therefore cited from rv-h-trust §2.3.
