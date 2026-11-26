# Z is Diophantine in Q: status of the Lean formalization (2026-11-23)

The manuscript *Z is Diophantine in Q* (the November 5, 2026 text that the Lean statement was frozen against,
`diophantine_zq.pdf` in the fork; upstream has revised the manuscript since) constructs one polynomial P with integer
coefficients such that a rational number q is an integer exactly when P(q, w) = 0 for some tuple w of rational
numbers. This project checks that proof in the Lean 4 proof assistant, with the Mathlib library.

- Development fork: https://github.com/Deicyde/diophantine-z-q. This file describes the Lean state of fork main
  29bfbc3f (merged 2026-11-22; the Lean is unchanged through 2026-11-23), where a single Lean theorem, `ZInQ.OneProof.frozenTarget`, proves the manuscript's
  Theorem 1.1 from exactly the statements that are still open. The last change to the hypotheses of pole completeness was
  the rank-one fold (fork PR #176, 2026-11-20).
- Upstream: https://github.com/elliotglazer/diophantine-z-q. Its pull request #139 holds this fork as of c1e4ed1b,
  before the switch away from Route K (below).
- Start here to help: https://github.com/Deicyde/diophantine-z-q/issues/14 explains how to pick an open statement,
  claim it and prove it; docs/one-proof/OPEN.md lists every open hypothesis with its Lean statement, its kind, its
  source and who is working on it.
- Blueprint site: https://deicyde.github.io/diophantine-z-q/ (since fork PR #123, redeployed after each passing build
  of main that a push started; on this file's date it showed main at 29bfbc3f).

The open statements of the current proof (generated from docs/one-proof/OPEN.md; the strict count and glue are defined
in the Glossary at the end):

<!-- open-count:begin -->
**19 hypotheses of the H part** (in the bundles `OpenAddedLeaves29`, `OpenResearchLeaves78`), plus three hypotheses outside the H part (`hRC`, `hCT`, `hRank`, from which Lean proves pole completeness, Theorem 5.2 of the 11/5 manuscript), listed at the end of docs/one-proof/OPEN.md.

* **Strict count: 5 published / 14 glue** (the strictest flagged reading; no hypothesis carries a strictest-reading flag).
* By kind: consequence 13, published 6.
* Generated from docs/one-proof/OPEN.md by scripts/one_proof/render_open.py.
<!-- open-count:end -->

## Status in three lines

- **Proved in Lean, with no gaps:** the manuscript's Theorem 1.1, in exactly the form frozen upstream, follows from
  two inputs: H, one instance of the manuscript's six-contact height estimate (Theorem 4.1), and pole completeness
  (Theorem 5.2) for the manuscript's own pole polynomial. Lean proves pole completeness from the restricted converse
  theorem (Theorem 5.3), the Cassels–Tate pairing on its curves (from which Lean proves Lemma 5.4), and the rank-one
  line of Silverman's *The Arithmetic of Elliptic Curves*, 2nd ed., Appendix C, Evidence 16.5.5, p. 453.
  The construction is the manuscript's; the textbook citation replaces the two previous forward-rank inputs.
- **Reduced in Lean:** H follows from 19 statements that are still open, and Lean proves every step from them to H
  (`HDec.HSyn.sixContactMin_of_open98`, the H part of `ZInQ.OneProof.frozenTarget`). By the project's ratings, 7 of
  them are published theorems (some specialized or weakened) and 12 are consequences of published theorems or of the
  manuscript's own text. Under the strict count, which also requires that a reader has checked the statement against
  the printed page, 6 of the 19 count as published statements in their printed form and 13 do not. Since 2026-11-26,
  with no human reader available, an adversarial AI reading stands in for the human one (docs/DECISIONS.md).
- **Open:** the 19 statements behind H and the three inputs of pole completeness: the manuscript's Theorem 5.3,
  the Cassels–Tate pairing, and Silverman's rank-one implication.

These 24 statements are exactly the hypotheses of `ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`).
Folding in a proof can remove a hypothesis from that theorem. The count block above is generated from the Lean type.

## How far to trust each part

| Part | Status |
| --- | --- |
| The construction of P and every finite computation about it (variables, degree, coefficients) | proved in Lean, no hypotheses |
| Theorem 1.1 from H and pole completeness | proved in Lean (`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness`) |
| H, the manuscript's Theorem 4.1 (one instance) | unrefereed; its new arguments reviewed only by AI models; in Lean, derived from 21 open statements (next row) |
| H from 21 open statements | proved in Lean, in the module chain under `ZInQKernel/OneProof/H/` and `ZInQKernel/Contrib/OneProof/` (built with `ZInQKernel/OneProof/Main.lean`, outside the default library target) |
| Pole completeness, the manuscript's Theorem 5.2 | proved in Lean from three hypotheses, with the manuscript's Lemma 5.4 proved from the Cassels–Tate pairing (`ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne`) |
| Theorem 5.3 (restricted converse) of the manuscript | unrefereed; assumed |
| The Cassels–Tate pairing on the curves of Theorem 5.3 | Poonen and Stoll's restatement of Cassels' theorem, specialized to these curves; assumed; classified as glue pending a check against a source that proves it |
| Silverman, Appendix C, Evidence 16.5.5, p. 453 | the analytic-rank-one to Mordell–Weil-rank-one implication, without the finite-Sha conclusion; assumed; recorded as a consequence of Miller's Theorem 4.4, from which Lean proves it; rated by Miller's Theorem 4.4; AI-read only, no human statement check |
| Theorem 1.1 from exactly the statements that are still open | proved in Lean (`ZInQ.OneProof.frozenTarget`) |

"Proved in Lean" means the Lean kernel checked it, with no `sorry` (unproved step), no `native_decide` (trusted
external evaluation), and only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. "Assumed" means stated
in Lean as a proposition and passed as a hypothesis, never as an axiom. A reader therefore needs to trust only the
open statements, not the rest of the manuscript's argument.

## The statement checked

`ZInQ.FrozenTarget` says: there is a polynomial P with integer coefficients in 292,890,231,905 variables, of total
degree below 2↑↑7 and with every coefficient below 2↑↑8 in absolute value, such that a rational number q is an integer
if and only if P(q, w) = 0 for some tuple w of 292,890,231,904 rational numbers. Here 2↑↑n is a tower of n twos
(2↑↑1 = 2 and 2↑↑(n+1) = 2^(2↑↑n)). `scripts/check_target.py` confirms that this statement is textually identical,
up to whitespace, to upstream's frozen statement of Theorem 1.1 in `lean/Frozen/BoundedIntegerPolynomial.lean`.
As a cross-check, `ZInQ.PrintedTheorem11.theorem11_iff_frozenTarget` (fork PR #151,
`ZInQKernel/Contrib/OneProof/PrintedTheorem11.lean`) proves `ZInQ.FrozenTarget` equivalent to Theorem 1.1 as written
from the manuscript's printed text.

The headline Lean theorem is
`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness`
(`ZInQKernel/MainGreenTao.lean`), with the two hypotheses `hH : SixContactMin` and `hPC : PoleCompleteness`.
`ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`) applies it to H and to pole completeness. It takes the
open statements of H as the fields of `HDec.HSyn.OpenResearchLeaves76` and `HDec.HSyn.OpenAddedLeaves28` (the third
bundle, `HDec.HSyn.OpenTextbookLeaves18`, has no open field left), and the three inputs of pole completeness as the
hypotheses `hRC` (Theorem 5.3), `hCT` (the Cassels–Tate pairing on the curves of Theorem 5.3, from which Lean proves
Lemma 5.4), and `hRank` (Silverman's forward rank-one implication), and nothing else.

## The open statements

### H, the six-contact height estimate (21)

docs/one-proof/OPEN.md gives each statement's Lean form, source, rating and holder. They come from these areas:

- the Shimura curve of discriminant 6 with level-three structure: Deligne's canonical model and an integral model over
  Z[1/30] (Lean derives the map to the projective line from these two);
- complex multiplication: the degree of a CM j-invariant, Faltings heights of CM elliptic curves, and Fowler's
  Proposition 2.7;
- abelian varieties: the duality between the Tate module and étale cohomology (Milne, Theorem 12.1(a)); Lean derives
  Faltings' semisimplicity and Tate theorems (1983, §5) from Gaudron–Rémond's Theorem 1.4 and Silverberg–Zarhin's
  Theorem 3.4, through their Theorem 3.5 and the existence of Néron models, which Lean proves (all below);
- Néron models and semistable reduction: Grothendieck's semistable reduction theorem in the form of Silverberg–Zarhin,
  Theorem 3.4; Lean proves their inertia criterion for semistable reduction (Theorem 3.3, fork PR #177), Raynaud's
  criterion in their form (Theorem 3.5) from Theorems 3.4 and 3.3, the existence of Néron models over a Dedekind base,
  and Faltings' extension lemma for semiabelian schemes (1983, Lemma 1) over a discrete valuation ring;
- Faltings heights: Gaudron–Rémond's Theorem 1.4 and the lower bound recorded in their Section 9, Javanpeykar's
  Theorem 1.1.1, and Pazuki's Corollary 1.3;
- p-adic Hodge theory: Berger's p-adic monodromy theorem, Scholze's comparison theorem for the first cohomology of
  abelian varieties, and Conrad's local algebraicity of Hodge–Tate characters;
- modular forms: Shimura's theorem on the factors of the Jacobian of a modular curve (1973, Theorem 1), the Galois
  representations attached to eigenforms (Diamond–Shurman 9.6.5, Deligne–Serre), Carayol's local–global compatibility
  in the form of Darmon–Diamond–Taylor, Pan's theorem on the Fontaine–Mazur conjecture, and the Hodge–Tate weights of
  the Galois representations of modular forms.

Two of them are steps of the manuscript itself rather than citations: the Hodge numbers in its de Rham descent
lemma (part of `scholzeH1AbVar`) are uncited there, and the integral model of the
level-three curve is the manuscript's own argument from cited papers. Each entry's Source line in
docs/one-proof/OPEN.md says which.

AI models have compared most of the statements with their printed sources (rows flagged unread or pending reading in
docs/one-proof/kinds.tsv have had no statement check against the page); several were restated to their printed form
after such a reading (among them Gaudron–Rémond's Theorem 1.4). A statement counts as published under the strict count
only once a reader has checked it against the page. Apart from the AI readings, contributors have posted statement
checks on https://github.com/Deicyde/diophantine-z-q/issues/14, which docs/one-proof/credits.tsv credits; two of them,
of Fowler's Proposition 2.7 (then the field `fowlerProp27`) and of `cmjDegree` against the publisher's PDF
(2026-11-18), were made by a person: an AI model proposed the passages and drafted the reports, and the reader read the
print and checked each quote and step. docs/one-proof/reviews.tsv records these two as human readings, the first ones
recorded; neither changes a count.

### Pole completeness (3)

Pole completeness is the manuscript's Theorem 5.2 for its own pole polynomial (whose solutions give points on its
curves E_ℓ: y² = x(x − ℓ)(x + 3ℓ); `diophantine_zq.tex` lines 976–986 and 1001–1004). Lean proves it from three
statements: `hRC`, the manuscript's Theorem 5.3 (the restricted converse), stated over the genuine 2-primary Selmer
group; `hCT`, the Cassels–Tate pairing on the same curves in Poonen and Stoll's restatement of Cassels' theorem
(Ann. of Math. 150 (1999), Introduction), from which Lean proves Lemma 5.4; and `hRank`, Silverman's forward rank-one
implication (2nd ed., Appendix C, Evidence 16.5.5, p. 453). The last replaces `hB` and `hK` at this root, without
changing the pole construction or using the finiteness of Sha. Its record cites Miller's Theorem 4.4 (LMS J. Comput.
Math. 14 (2011)), from which Lean proves it (`ZInQ.Manuscript.ForwardRankLiterature.silvermanRankOne_of_miller`);
an AI reading found the Lean form of Miller's theorem faithful to the print. `hRank` is rated by Miller's Theorem 4.4;
AI-read only, no human statement check.
Fork PR #110 reduces Theorem 5.3 in Lean to step-level hypotheses along the manuscript's
Sections 7–9 and Appendices E–G (`ZInQ.Manuscript.RC.Wiring.restrictedConverseGenuine_of_leaves`); `frozenTarget`
still takes it as one hypothesis, because some of those steps still state their conclusions directly.

## What is proved in Lean with no hypotheses

The construction of the polynomial and every finite computation about it run in the kernel. Two steps of the
manuscript are replaced by proved ones: - route AP replaces the manuscript's Proposition 6.2: Szemerédi's theorem in
the primes (Vasily Ilin's Apache-2.0 Lean proof of Green–Tao, vendored and extended to dense subsets of the primes)
together with a density theorem for the good primes (Proposition D, proved with Mathlib's Chebyshev bounds and a
Selberg sieve vendored from the PrimeNumberTheoremAnd project); - the catalogue bound is proved in the weaker form
CAT₈, which suffices.

Deriving H from the literature also re-sources some steps of the manuscript's Section 4 and replaces its last step;
docs/research/h-trust.md, a note from 2026-11-11 on an earlier route, follows the proof of Theorem 4.1 step by step.

An earlier proof, Route K, replaced pole completeness by an argument through Tian–Yuan–Zhang and Gross–Zagier for a
different pole polynomial. It is retired and kept at the tag `route-k-final` (bf691da2); docs/research/rs-pole.md
explains why it existed. No TYZ or Gross–Zagier hypothesis remains. About 80 modules of that development still compile
in the tree, because the H chain imports their Shimura and complex-multiplication results (docs/research/lane74.md;
docs/research/lane74b.md, items 2 and 7).

## How to help

Start at https://github.com/Deicyde/diophantine-z-q/issues/14, which a coding agent can follow as written to prove
exactly the Lean statement of an open hypothesis and open a pull request against the fork's main, where the proof is
folded into `ZInQ.OneProof.frozenTarget`. docs/one-proof/OPEN.md lists every open hypothesis of that theorem with its
exact Lean statement, its kind, its source and who is working on it; CONTRIBUTING.md is the guide for contributors,
and docs/one-proof/CONTRIBUTING.md the short contract for a proof, which `#discharges` checks. Claim a statement
before starting, in one place: comment `Claiming <field> at <commit>` on
https://github.com/Deicyde/diophantine-z-q/issues/14 (older claims on the upstream topic issues stay valid). To check
a statement against its printed source without Lean, see docs/one-proof/STATEMENT-CHECKS.md, and
docs/one-proof/pages-wanted.md for the pages to read. The status column of docs/one-proof/OPEN.md shows who holds each
statement. To build and check: `lake exe cache get`, then `lake build ZInQKernel +ZInQKernel.OneProof.Main`; the build
prints the axioms of `ZInQ.OneProof.frozenTarget`, which must be the three standard axioms; then `lake env lean
scripts/print_axioms.lean` (463 declarations: the headline
`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness` and its variants, the
theorems that replace former hypotheses, and the glue lemmas of the decomposition of H; every one must depend only on
the three standard axioms) and `python3 scripts/check_target.py`.

## Verification

Every Lean change is built before it reaches main. GitHub's hosted runners also build the theorem after each push to
main that changes Lean files or the Lake configuration, in the main build cache workflow
(.github/workflows/main-build-cache.yml). The job fails unless the build finishes and the axioms of
`ZInQ.OneProof.frozenTarget` are among `propext`, `Classical.choice` and `Quot.sound`; any other axiom, `sorryAx`
included, fails it. The first such build finished on 2026-11-18 (run 44219370755, at be73b91c). After the run at
3078ae6a (run 44513481236, 2026-11-19), the runs on main failed or were cancelled by the next landing until
2026-11-20; every failure, the last at 8579961f (run 44725033802), stopped at the workflow's disk-space guard,
because the restored build nearly filled the runner. Fork PR #171 fixed this: the workflow now deletes Lake's
per-module setup files, which were 48 of the build's 53 GB. Its merge at 75c937b0 passed (run 44739014494,
2026-11-20), and so has every later run that a push to main started, except one that was cancelled (run 44745750741,
at c5c66ded). The latest is run 45030880796 at 29bfbc3f (2026-11-22): the build completed (19,897 jobs) and
`frozenTarget`, with its 24 open hypotheses, depended only on the three standard axioms. A cold build takes more than
one job, so each run saves its progress and the next one resumes from it.

When the headline from H and pole completeness landed (lane74, fork main d435851d; docs/research/lane74b.md, section
6), all 463 declarations of `scripts/print_axioms.lean` depended only on the three standard axioms, with no `sorry`,
and `scripts/check_target.py` confirmed the statement. Since then the fold reports record a build and an axiom check
of `ZInQ.OneProof.frozenTarget` (docs/research/fold-b112.md, fold-b115.md, fold-b116.md, fold-c8.md, fold-cm.md,
nos-narrow-fold.md and cm-serre-tate-fold.md); hecke-sqrt.md, cm-port2.md, lem54-ct-check.md, faltings-dict2.md,
fowler-unique.md, cmj-bridges.md and j-descent5.md record dry runs or previews, and the landings of fork PR #133, of the
cmj-close fold, of fork PR #142 (BCDT Theorem A as printed) and of the outside-discharges fold of fork PRs #152, #153,
#155, #156 and #157 have no build record in a report. Nor do the later folds (fork PRs #176, #177 and #180, and the
swap to Silverberg–Zarhin's Theorem 3.4); the main build cache's passing runs are their build records.

## AI caveat

The manuscript was written with AI models and audited by an AI model, and the project's Lean was written by AI coding
agents. The ratings of the open statements are by AI models, and so are the readings of their printed sources, apart
from the contributors' statement checks on issue #14 that docs/one-proof/credits.tsv credits (two of them, of
2026-11-18, made by a person with AI drafting the reports, and recorded in docs/one-proof/reviews.tsv as human
readings). A person's reading of a statement against its source counts for more: see
docs/one-proof/STATEMENT-CHECKS.md.

## Where the details are

- README.md: the one-page summary, with a dated status block.
- `ZInQKernel/OneProof/Main.lean`: the whole proof in one theorem, `ZInQ.OneProof.frozenTarget`, whose hypotheses are
  exactly the open statements, with the history of the folds in its docstring.
- docs/one-proof/OPEN.md: every open hypothesis, with its Lean statement, kind, source and status, and the rule for
  counting a statement as published; docs/one-proof/kinds.tsv: the rating of each; CONTRIBUTING.md and
  docs/one-proof/CONTRIBUTING.md: how to prove one and check it.
- docs/research/lane74.md and docs/research/lane74b.md: the switch to the manuscript's route;
  docs/research/rs-pole.md: why Route K existed; docs/research/selmer-2infty.md: Theorem 5.3 over the genuine
  2-primary Selmer group; docs/research/cassels-tate-pairing.md, lemma54-ct.md and lem54-ct-check.md: Lemma 5.4 from
  the Cassels–Tate pairing; docs/research/fold-b112.md, fold-b115.md, fold-b116.md, fold-c8.md, fold-cm.md,
  hecke-sqrt.md, nos-narrow-fold.md, cm-port2.md, faltings-dict2.md, fowler-unique.md, fowler-bridges.md,
  bsh-family.md, cmj-bridges.md and j-descent.md to j-descent5.md: the folds since, with a check of the manuscript
  steps they touch; cm-serre-tate-fold.md records fork PR #132 without such a check, and the fold of fork PR #133,
  which replaced the triviality of wild inertia by Silverberg–Zarhin's Theorem 3.3, has no report there.
- blueprint/roadmap/height-decomposition/: the blueprint chapter with one article per open statement of H, giving
  its statement in mathematical terms, how it differs from the print, and its source.
- docs/research/h-trust.md: a dated note (2026-11-11, on an earlier route) that follows the proof of Theorem 4.1 step
  by step.
- docs/research/frontier.md: the project's dated survey of the open statements, with sources, ratings and history.
- docs/research/locators.md: the audit of the literature citations against primary sources.

## Glossary

- **Kernel-checked / proved in Lean:** accepted by Lean's kernel, with no `sorry` and only the axioms `propext`,
  `Classical.choice`, `Quot.sound`.
- **Hypothesis (assumed):** a Lean proposition passed as an argument to a theorem; nothing is added as an axiom.
- **Frozen statement:** upstream's quarantined copy of Theorem 1.1 in `lean/Frozen/`, which the project must not
  change.
- **H:** the instance of the manuscript's six-contact height estimate (Theorem 4.1) that the proof uses,
  `ZInQ.SixContactMin`.
- **Pole completeness:** the manuscript's Theorem 5.2 for its own pole polynomial, `ZInQ.PoleCompleteness`; Lean
  proves it from the manuscript's Theorem 5.3, the Cassels–Tate pairing (from which it proves the manuscript's Lemma
  5.4) and the rank-one line of Silverman's *The Arithmetic of Elliptic Curves*, 2nd ed., Appendix C, Evidence
  16.5.5, p. 453.
- **Published / consequence:** a statement printed in the literature, possibly specialized, or one that follows from a
  printed theorem, or from the manuscript's own text, by an argument not yet in Lean.
- **Strict count:** counts a statement as published only if it is a refereed theorem in its printed form (or a direct
  instance of it) and a reader has checked it against the printed page.
- **Glue:** in the strict count, every statement not counted as published (docs/one-proof/kinds.tsv, column `strict`);
  as a kind, an argument connecting statements, which the project must prove in Lean (no open statement has this kind
  now).
