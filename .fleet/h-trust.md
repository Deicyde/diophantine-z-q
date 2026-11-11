# h-trust: one trust statement for H with no unpublished supplement (task T3)

Full note: `docs/research/h-trust.md`. Log and script reruns: `scratch/h-trust/`.

**Result.** The note gives a numbered outline of Theorem 4.1, in the form `SixContactEstimate`
uses it, in 36 steps. Each step names its supplier and status. **No unpublished supplement is
used:**

- `direct-p5`: never cited in N5, which applies Pan's Theorem 1.0.4 directly at L756.
- `a001`, `ly-d6`, `igusa-theta`: replaced by Baba–Granath 2008, Lin–Yang 2020, Igusa and
  Lauter–Naehrig–Yang, read through `form_check.py` and `igusa_check.py`.
- `b11` and Buzzard: replaced by h-b1's Lemma PR.
- CM branch: replaced by NoCM.

Status counts:

| Status | Steps | Which |
| --- | --- | --- |
| refereed theorems and verified scripts only | 7 | |
| refereed theorem applied through bookkeeping with a model review only | 5 | |
| model-reviewed arguments only | 21 | reviews: rv-h-novel on N5, Astra on the 11/4 text, rv-h-a011 on Version 14, rv-h-cm |
| **unchecked** | **3** | A4, the moduli identification of N5's `Y₃`; A5-A6, Lemma PR, whose review `wip/rv-h-b1` has no commit yet |

I reran the repository scripts the steps rely on: form, Igusa, `b1_checks`, `rv-h-cm/check.py`,
and rv-h-novel's c1 and c2. Each matched its saved output or its log.

**Two choices that shrink the base (VERIFIED as reasoning).**

- Keep N5's Scholze + Berger route to potential semistability rather than Lemma PG. Both papers
  are refereed, and the route adds no new repository argument.
- Keep Faltings 1983 for the semisimplicity, endomorphism and Hom theorems, rather than
  GR14 + Tate. That makes GR14's non-circularity (W4) irrelevant.

**What remains outside refereed sources (§2):**

- N5's own arguments, reviewed by models only (W1). The weakest-reviewed paragraph is C8, the
  twist and weight step at N5 L757-768.
- NoCM, reviewed by a model only.
- Lemma PR and the moduli identification, not reviewed at all.
- Seven exact scripts.
- Five citation swaps away from unrefereed editions: Milne's notes, Brinon–Conrad, Conrad's
  preprint, and the preprints of Baba–Granath and Lin–Yang.
- About 40 UNVERIFIED locators, with places to check them. The ones that could change a
  statement are Pan's JAMS numbering, Carayol's Théorème (A) at `F = ℚ`, and GR14 Thm 1.4.

**Drafts (§3).** Replacement docstrings for `Hypotheses/Height.lean` (module docstring and
`SixContactEstimate`) and `Hypotheses/HeightMin.lean` (one appended paragraph, and
`SixContactMin`), plus a KERNEL_PLAN H row that names no supplement. The Lean files were not
edited.

**Minor finding.** rv-h-novel's line numbers for its steps 5-8 are about 22 too high. The right
N5 ranges are L796-812, L813-823, L823-846 and L846-857.

**Next.** One review of this outline (`rv-h-trust`), plus the pending review of h-b1. With
network access, the locator checks of §2.5.
