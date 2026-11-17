# pc90b-review: diff-only re-check of draft PR #90 at head a8099a02

Task pc90b-review, 2026-11-17, branch `wip/pc90b-review`, which is exactly a8099a02a with nothing merged. This re-checks the
five commits 517e05cce..a8099a02 (52e113d72, d8b9dd45a, 80020b427, 405c14903, a8099a02a). The previous review is
`docs/research/pc90-review.md` on `origin/wip/pc90`. Log: `scratch/pc90b-review/log.md`. Every claim below is VERIFIED
(compiled, computed or read) unless it is marked otherwise.

## Verdict

**a8099a02 is not clean, for one documentation reason. The Lean, the hKum discharge, the S12 removal and the rename are
clean.**

* **Item (6) fails: the labels.** `Lemma54` is still labelled a *printed leaf*, but it is a lemma of the manuscript.
  `KolyvaginThm1` names the bridge (Shimura's construction plus Faltings' isogeny theorem), but it is still rated
  "printed leaf as cited", not *consequence*. These are docstring edits only; no statement changes. Early notice:
  `.fleet/pc90b-review-verdict.md` (commit b5bf0a745).
* Items (1), (2), (3), (4) and (7) pass. Item (5) passes as far as it can be checked: the five commits touch no Tau Ceti
  file. Pin 86b92544 is not present on this host, so the comparison was made against the pins named in the vendored
  headers (see (5)).
* Still open from pc90-review: S12 stays in the PR's **history** (commit 4b2595108). Removing it at the head does not
  remove it from history. The history must be rewritten (squash) before the PR is merged into any public branch.

## (1) Build: PASS

| command | result |
|---|---|
| `lake build ZInQKernel.OneProof.Main ZInQKernel.MainGreenTao` | success, **16151 jobs**, 0 errors |
| the same plus `PoleS12.Leaves`, `Hypotheses.PoleManuscript`, `PoleCompletenessFromRCGenuineFinal` and the 3 changed vendored AnthropicFLT modules | success, **16151 jobs** (all of them are in Main's closure) |
| all 12 modules that import or are the 3 changed AnthropicFLT modules (`git grep` on their names), including `Thm_*` and `Def_Isogeny_ConditionalCurrency` | success, **9317 jobs** |

Main now imports `PoleCompletenessFromRCGenuineFinal`, which imports Tau Ceti's Weil pairing. That it builds confirms that
the rename removed the clash on `WeierstrassCurve.Affine.divisorSum` that pc90-review reproduced.

## (2) Axioms and forbidden tokens: PASS

`scratch/pc90b-review/Axioms.lean` produced `Axioms-output.txt`. `[propext, Classical.choice, Quot.sound]` only for:
* `ZInQ.OneProof.frozenTarget`;
* the MainGreenTao headline `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness`;
* `ZInQ.Manuscript.PoleS12.kummerSelmerM`, `ZInQ.Manuscript.PoleRC.kummerSelmerM_proof`, and
  `ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_final`;
* every declaration of the six changed modules. A metaprogram (`#scan_modules`) runs `collectAxioms` on each non-internal
  constant. It scanned 1 (Main), 11 (Leaves), 10 (PoleManuscript), 45 (Def_WeierstrassCurve_GenusOnePic0, including
  `WeierstrassCurve.Affine.placeDivisorSum`), 394 and 144 (the two `S_…` modules) declarations; **0 nonstandard**.

None of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` occurs outside comments in the six
changed `.lean` files, and no added line contains one. The same holds for `KummerSelmerMProof.lean` and
`PoleCompletenessFromRCGenuineFinal.lean`. None of the six changed files is pinned by upstream
(`scratch/upstream/baseline-lean-files.txt`).

## (3) The hKum discharge is genuine: PASS

Base 517e05cce (`git show 517e05cce:ZInQKernel/OneProof/Main.lean`):
```
theorem _root_.ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves57) (t : HDec.HSyn.OpenTextbookLeaves18) (l : HDec.HSyn.OpenAddedLeaves27)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (h54 : ZInQ.Manuscript.PoleS12.Lemma54) (hKum : ZInQ.Manuscript.PoleS12.KummerSelmerM)
    (hB : ZInQ.Manuscript.PoleS12.BCDTThmA) (hK : ZInQ.Manuscript.PoleS12.KolyvaginThm1) :
    ZInQ.FrozenTarget
```
Head a8099a02 (`#check`, compiled):
```
ZInQ.OneProof.frozenTarget : HDec.HSyn.OpenResearchLeaves57 → HDec.HSyn.OpenTextbookLeaves18 → HDec.HSyn.OpenAddedLeaves27 →
  ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine → ZInQ.Manuscript.PoleS12.Lemma54 →
  ZInQ.Manuscript.PoleS12.BCDTThmA → ZInQ.Manuscript.PoleS12.KolyvaginThm1 → ZInQ.FrozenTarget
```
* The only signature change is that `hKum` is gone. The other seven hypotheses keep their types and their order.
* The proof term now uses `poleCompleteness_of_restrictedConverseGenuine_final hRC h54 hB hK`, whose body
  (`PoleCompletenessFromRCGenuineFinal.lean:31-36`) passes `ZInQ.Manuscript.PoleS12.kummerSelmerM` to `…_mw`.
* `kummerSelmerM : ZInQ.Manuscript.PoleS12.KummerSelmerM` (compiled `#check`): its type is the same constant the
  hypothesis had. The five commits do not change the body of `KummerSelmerM` (the hunks in `Leaves.lean` are docstrings
  only). Its definition (`#print`): `∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → Nat.card (selmerAt (curve ↑ℓ) 1) = (SelM ℓ).ncard`.
* It is a theorem, proved as `fun ℓ h1 h2 => PoleRC.kummerSelmerM_proof ℓ h1 h2`, with standard axioms (item 2).

## (4) No S12: PASS

* `git ls-tree -r a8099a02 | grep -i parity-frozen` prints nothing. The blob hash of the S12 copy (f319c4da) occurs nowhere
  in the tree.
* I grepped the whole tree with fixed strings for all 460 distinct non-comment S12 lines of at least 40 characters. There is
  one hit, a 66-character generic phrase in `ZInQKernel/Contrib/OneProof/PoleS12/Primes.lean`, which none of the five
  commits touches: "remainder theorem gives a reduced residue class, and Dirichlet's". That phrase is not a copy of S12.
* S12 is still in the history (4b2595108). See the verdict.

## (5) Tau Ceti untouched: PASS (by diff); pin 86b92544 UNCHECKED

* `git diff --stat 517e05cce a8099a02 -- ZInQKernel/Contrib/TauCeti ThirdParty` is empty. The five commits change no
  vendored Tau Ceti file.
* The vendored path is `ZInQKernel/Contrib/TauCeti/` (2022 files). **86b92544 is not an object in this repository or in
  any git repository under `~`** (I searched every `.git` to depth 4). The comparison as specified could not be made.
* The vendored headers name the pins 5a01f5fe3621, 97a5b23586f9 and 4d91513e4d30, all present in `~/tcrun/tc`.
  `scratch/pc90b-review/tc_compare.py` strips the leading comment block and maps `ZInQKernel.Contrib.TauCeti.` to
  `TauCeti.`. Result: **1852 files are code-identical** to their pin (1807 at 5a01f5fe, 45 at 97a5b235). **47 differ**:
  24 only in imports (they import `Backport/` copies), 23 also in code, for example `Global/PrescribedInvariant.lean`
  (423 changed lines), `RepresentationTheory/FDRep.lean` and `GroupAction/Stabilizer.lean`. Each of the 47 carries a
  "Modified for the Z-in-Q kernel" note. 123 files have no pin header (121 under `Backport/`, `MathlibBackport`,
  `Notice.lean`). The full lists are `tc_compare.txt` and `tc_codediff.txt`. All of this predates the five commits
  (Tau Ceti is identical at 517e05cce), so it is outside this diff-only check.

## (6) Labels: FAIL

* `Lemma54`. `Leaves.lean:81`: "**Lemma 5.4 (`lem:corank`, tex L1072–1084), printed form over genuine definitions.** …
  A cited leaf here; not proved." Module doc `Leaves.lean:17`: "`Lemma54` (printed leaf, tex `lem:corank`, Cassels–Tate
  via Poonen–Stoll)". `Main.lean:12` and `:137`: "the printed leaves Lemma 5.4, BCDT Theorem A and Kolyvagin's
  Theorem 1". The docstring does say that the manuscript proves it ("Provenance (b)"), but every label calls it a printed
  leaf. Required label: manuscript lemma (`lem:corank`, proved in the manuscript from the Kummer sequence and Cassels–Tate
  via Poonen–Stoll), not a printed leaf.
* `KolyvaginThm1`. `Leaves.lean:52`: "**Kolyvagin, Theorem 1, the case `r = 1`** (printed leaf as cited: …". The step is
  named at `Leaves.lean:58-59`: "this leaf follows from the print only through Shimura's construction and Faltings'
  isogeny theorem (with trivial nebentypus)". So the bridge is named, as required. The rating is not: `Leaves.lean:14`
  ("`KolyvaginThm1` (printed leaf, the `r = 1` case)") and `:52` still say printed leaf. Required: rated **consequence**.
* BCDT (not required, recorded for completeness): `Leaves.lean:40` "printed leaf"; `IsModular` is argued to be a
  consequence of condition (2) of the print, and the docstring says so.

## (7) Rename scope: PASS

* `git diff --stat 517e05cce a8099a02` lists 7 paths: the 3 vendored AnthropicFLT files (`Def_WeierstrassCurve_GenusOnePic0`
  and two `P2M/Sol/S_…`), `PoleS12/Leaves.lean`, `Hypotheses/PoleManuscript.lean`, `OneProof/Main.lean`, and the deletion
  of `scratch/upstream/parity-frozen-4eaee875.tex`.
* Mechanical check: I took the base version of each AnthropicFLT file, replaced the exact token `divisorSum` (no word
  character on either side) by `placeDivisorSum`, and diffed the result against the head. The only differences are the
  4-line "Modified 2026-11-17" header and a `-- [port] renamed from divisorSum` comment on the def line. Nothing else was
  renamed. The derived lemma names (`divisorSum_single`, `divisorSum_pointDivisor`, `divisorSum_eq_zero_of_isPrincipal`,
  …) keep their names, and none of them collides with Tau Ceti's (`divisorSum_apply`, `divisorSum_eq_zero_iff`,
  `divisorSum_ofPoint_sub_ofPoint`, …). The build of (1) confirms this.
* In a8099a02 the bare token `divisorSum` occurs only in Tau Ceti's `Divisor/Sum.lean` and `MulByInt/DivisorPullback.lean`
  and in GreenTao's unrelated `SmoothSieveCutoff.divisorSum`. No Tau Ceti file was touched.

## Known issues

1. **Labels** (item 6): `ZInQKernel/Contrib/OneProof/PoleS12/Leaves.lean:14, :17, :52, :81` and
   `ZInQKernel/OneProof/Main.lean:12, :137`.
2. **Stale docstrings after 405c14903.** `Leaves.lean:20` ("`KummerSelmerM` (textbook GLUE, not proved)") and
   `Leaves.lean:91` ("textbook GLUE, not proved in Lean") predate the proof; `PoleS12.kummerSelmerM` now proves it.
3. **S12 in history**: commit 4b2595108. Squash before merging.
4. Kolyvagin bridge (SPECULATIVE, a remark on completeness and not a fault). Going from `IsModular` (some cusp form on
   Γ₀(N) with the coefficients of `L(E,s)`) to a weak Weil parametrization of level exactly the conductor also uses
   newform theory (Atkin–Lehner, multiplicity one) and conductor = level (Carayol), besides Shimura and Faltings. The
   docstring's "the step BCDT cite for (2) ⇒ (6)" covers this by reference.
5. Pin 86b92544 is not available on this host: item (5)'s comparison with that pin is unchecked.
