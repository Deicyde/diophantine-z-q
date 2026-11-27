# ℤ is Diophantine in ℚ: the Lean proof

## Contributors

- **Elliot Glazer** ([@elliotglazer](https://github.com/elliotglazer)): the manuscript and the upstream repository.
- **Jack McCarthy** ([@Deicyde](https://github.com/Deicyde)): this fork, with AI agents working for him.
- **Contributed work on `main`:** loning ([@loning](https://github.com/loning)),
  Chey Loveday ([@CheyLoveday](https://github.com/CheyLoveday)),
  Carlos Toledo ([@carlostoledo1891](https://github.com/carlostoledo1891)),
  Cameron Freer ([@cameronfreer](https://github.com/cameronfreer)),
  Junyan Xu ([@alreadydone](https://github.com/alreadydone)),
  Ryan McCorvie ([@mccorvie](https://github.com/mccorvie)) and
  Zach Baugher ([@zachbaugher](https://github.com/zachbaugher)).
- **The October 11 manuscript:** Sohail Farhangi.
- **Credited by the upstream project for its collective notes:** Stefan Baranczuk, Jose Brox
  ([@JoseBrox](https://github.com/JoseBrox)), Gabe Conant, Sohail Farhangi, Cameron Freer, James Freitag, Elliot
  Glazer, Jennifer Park and Caroline Terry.

What each person did is in [CONTRIBUTORS.md](CONTRIBUTORS.md).

This fork formalizes in Lean 4 the main theorem of the manuscript
[*ℤ is Diophantine in ℚ*](diophantine_zq.pdf) (November 5, 2026, Theorem 1.1): there is a polynomial `P` with
integer coefficients such that a rational number `q` is an integer exactly when `P(q, w) = 0` for some
`w ∈ ℚ^292,890,231,904`. Lean states it as `ZInQ.FrozenTarget` ([`ZInQKernel/Target.lean`](ZInQKernel/Target.lean)).
The Lean result is conditional: it proves the theorem from the open hypotheses counted below, and those are not
proved in Lean.

**Reference text.** The Lean follows Elliot Glazer's original manuscript, the November 5, 2026 text kept here as
[`diophantine_zq.tex`](diophantine_zq.tex), and deviates from it only when it has to, for example when a step
cannot be formalized as written. Each deviation is recorded with its reason in
[`KERNEL_PLAN.md`](KERNEL_PLAN.md#reference-text-and-deviations)
([#95](https://github.com/Deicyde/diophantine-z-q/issues/95)).

**Two routes.** The project has two proofs of the theorem, and they are means to the same end. Both use the
six-contact height estimate (the manuscript's Theorem 4.1). They differ in how they obtain pole completeness
(Theorem 5.2).

- **Elliot's route**, the proof on `main`, uses the manuscript's own pole polynomial, with
  curves y² = x(x − ℓ)(x + 3ℓ), and proves pole completeness from three statements:
  - the manuscript's restricted converse theorem (Theorem 5.3);
  - the Cassels–Tate pairing on the curves of Theorem 5.3 (Poonen–Stoll's statement of Cassels' theorem, the print
    the manuscript cites for its Lemma 5.4; Lean proves Lemma 5.4 from it);
  - the forward rank-one implication in Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Appendix C,
    Evidence 16.5.5, p. 453. This supplies just the Mordell–Weil rank conclusion of Lemma 5.5. It replaces the
    two previous modularity and Kolyvagin inputs; the pole construction and the restricted converse are unchanged.

  Theorem 5.3 stays one hypothesis of the main theorem. Separately,
  [#110](https://github.com/Deicyde/diophantine-z-q/pull/110) reduces it, along the manuscript's Sections 7–9 and
  Appendices E–G, to step-level hypotheses (`ZInQ.Manuscript.RC.Wiring.restrictedConverseGenuine_of_leaves`). Some
  of those still state their step's conclusion directly and are being restated over the manuscript's objects.
  Proving the steps in Lean is [#83](https://github.com/Deicyde/diophantine-z-q/issues/83).
- **The congruent-number route** uses the congruent-number curves y² = x(x − ℓ)(x + ℓ) in place of the
  manuscript's. The manuscript's soundness lemma (Lemma 5.1) holds for both families. Pole completeness for these
  curves is proved from a narrow rank hypothesis on an explicit 2-Selmer system. The project derived that hypothesis
  from Tian, Yuan and Zhang's theorem on congruent numbers and the Gross–Zagier formula. The two pole polynomials
  cannot both be the kernel's at once, so this route is not in `main`'s build. Its last build on this fork is the tag
  [`route-k-final`](https://github.com/Deicyde/diophantine-z-q/tree/route-k-final).
  [nasqret/z-in-q-lean](https://github.com/nasqret/z-in-q-lean) builds on it, and the plan is to bring the two
  projects together upstream ([#104](https://github.com/Deicyde/diophantine-z-q/issues/104)).
  [`docs/research/rs-pole.md`](docs/research/rs-pole.md) explains how the route arose. Older documents call it
  "Route K".

Apart from its hypotheses, Elliot's route departs from the manuscript in two smaller steps, both proved: route AP
replaces Proposition 6.2 by Szemerédi's theorem in the primes together with a density theorem for the good primes
(Proposition D), and the catalogue bound is proved in the weaker form CAT₈. Deriving the height estimate from the
literature also re-sources some steps of the manuscript's Section 4 and replaces its last step.

nasqret/z-in-q-lean also has a weaker, qualitative theorem that replaces the height estimate by von Känel's bound,
whose constant is not explicit. That bound is ineffective: it shows that a polynomial exists but gives none of
Theorem 1.1's numbers, such as the count of variables. Neither route above uses it.

## Roadmap

The [roadmap](blueprint/roadmap/README.md) writes the proof out as a book, with a page for each statement in the
proof's outline: what it says, how the Lean statement differs from the manuscript's, its Lean name, and whether it
is proved, cited from the literature or open. It opens with a diagram of the proof and a status table for each route,
and then has one part for each piece of the proof:
- [the construction](blueprint/roadmap/construction.md): the polynomial and why its zeros project to ℤ;
- [the height input](blueprint/roadmap/height-input.md): the minimal height hypothesis, from the open statements of
  [the height decomposition](blueprint/roadmap/height-decomposition/README.md);
- [the pole input](blueprint/roadmap/pole-input.md): pole completeness, by Elliot's route from
  [Theorem 5.3, the restricted converse](blueprint/roadmap/restricted-converse/README.md), whose proof in the
  manuscript's Sections 7–9 and Appendices E–G has a page for each numbered statement, or by the congruent-number
  route.

The [blueprint site](https://deicyde.github.io/diophantine-z-q/) renders the roadmap with its dependency graph. The
height-decomposition chapter is generated from the Lean and the ratings in `docs/one-proof/`.
`python3 scripts/roadmap/check_current.py` checks the roadmap against the tree: that every Lean name it cites exists,
that the generated chapter is current (`--fix` regenerates it), and that every field of Theorem 5.3's remaining
hypotheses it names exists.

## Status (fork `main` at `43c4d0da`, 2026-11-27)

- **One theorem, [`ZInQ.OneProof.frozenTarget`](ZInQKernel/OneProof/Main.lean), proves `ZInQ.FrozenTarget` from 29
  open hypotheses, statements not yet proved in Lean.** Lean's kernel checks it with no `sorry` and only the standard
  axioms `propext`, `Classical.choice` and `Quot.sound`. Everything else, including every finite computation, is
  proved in Lean. Since 2026-11-18 GitHub's hosted runners run this check too: the [main build
  cache](.github/workflows/main-build-cache.yml) workflow builds the theorem after a push to `main` that changes Lean
  and fails unless its axioms are among these three. Its [first passing
  run](https://github.com/Deicyde/diophantine-z-q/actions/runs/44219370755) was at `be73b91c`. After its run at `3078ae6a` (2026-11-19)
  its runs on `main` failed, each at the workflow's disk-space guard, or were cancelled by the next landing, until
  [#171](https://github.com/Deicyde/diophantine-z-q/pull/171) made it delete Lake's per-module setup files (48 of the build's
  53 GB). Every run a push started since has passed, except one that was cancelled; the [latest
  passing run](https://github.com/Deicyde/diophantine-z-q/actions/runs/45030880796) is at `29bfbc3f`, with 24 open hypotheses,
  and the [run list](https://github.com/Deicyde/diophantine-z-q/actions/workflows/main-build-cache.yml) shows the other
  commits it has passed on ([#62](https://github.com/Deicyde/diophantine-z-q/issues/62)). The [build-cost
  table](docs/one-proof/CONTRIBUTING.md#what-it-costs-to-build) has no build by anyone outside the project yet.
- **The hypotheses are premises, not axioms:** Lean proves "if they all hold, then ℤ is Diophantine in ℚ". 26 belong
  to the six-contact height estimate (the manuscript's Theorem 4.1). The other three supply pole completeness
  (Theorem 5.2): the manuscript's Theorem 5.3, the Cassels–Tate pairing on its curves `E_ℓ` (from which Lean proves
  Lemma 5.4), and Silverman's forward rank-one implication. Of the 26, 14 are classed as published theorems and
  12 as consequences of a published theorem or of the manuscript's text. Under the strict
  count (a refereed theorem as printed, checked against the page), 9 qualify; the other 17 still need an argument or a
  reading. AI raters assigned these classes. The live list, with each statement's source, rating and holder, is
  [`docs/one-proof/OPEN.md`](docs/one-proof/OPEN.md).
- **Progress:** 65 open hypotheses on 2026-11-15, 30 on 2026-11-17, 33 on 2026-11-18, 31 on 2026-11-19, 25 on 2026-11-20, 24
  on 2026-11-21, 22 on 2026-11-26, 29 now. The count falls when a hypothesis is proved, can rise or fall when one is
  restated as printed statements, and changes when the proof follows the manuscript more closely: the switch away from
  Route K removed five hypotheses and added pole completeness, following the manuscript's complex-multiplication
  argument in Section 4 added four, deriving pole completeness from its Section 5 replaced one by four, and proving the
  manuscript's integral model of the level-three Shimura curve from the printed statements it uses replaced one by
  eight. So it does not measure proved content.
- **AI caveat.** The manuscript was written with AI models and audited by an AI model, and the project's Lean was
  written by AI coding agents. Published hypotheses have been compared with their printed sources by AI readers, and
  those flagged `unread` on OPEN.md have had no statement check against the page yet. Contributors have also posted
  statement checks on [#14](https://github.com/Deicyde/diophantine-z-q/issues/14), credited in
  `docs/one-proof/credits.tsv`; two of them (2026-11-18) were made by a person against the publisher's PDF, with AI
  drafting the reports, and `docs/one-proof/reviews.tsv` records them as the first human readings.

## Upstream

Elliot Glazer's repository, [elliotglazer/diophantine-z-q](https://github.com/elliotglazer/diophantine-z-q), plans
to take this work in as staged pull requests once its Lean CI is fixed; [#139](https://github.com/elliotglazer/diophantine-z-q/pull/139)
holds this fork as of `c1e4ed1b`, which predates the switch away from Route K. Its topic issues
[#81](https://github.com/elliotglazer/diophantine-z-q/issues/81) to
[#86](https://github.com/elliotglazer/diophantine-z-q/issues/86), indexed in
[#37](https://github.com/elliotglazer/diophantine-z-q/issues/37), list the open statements of the height estimate by
area. Its issues [#74](https://github.com/elliotglazer/diophantine-z-q/issues/74) and
[#76](https://github.com/elliotglazer/diophantine-z-q/issues/76) concern Route K's inputs from Tian–Yuan–Zhang and
Gross–Zagier, which the theorem no longer uses.

## Contribute

Start at [issue #14](https://github.com/Deicyde/diophantine-z-q/issues/14); a coding agent can follow it as written.

- **Prove a hypothesis in Lean:** pick an `open` row on [OPEN.md](docs/one-proof/OPEN.md), claim it on #14, follow
  [CONTRIBUTING.md](docs/one-proof/CONTRIBUTING.md), and open a pull request against this fork's `main`.
- **Check a statement against its printed source** (no Lean needed): follow
  [STATEMENT-CHECKS.md](docs/one-proof/STATEMENT-CHECKS.md); [pages-wanted.md](docs/one-proof/pages-wanted.md) lists
  the pages to read. A person's reading counts for more than an AI's: apart from `unread`, only a person's reading
  clears a statement's flags.

## Check it yourself

Lean `v4.35.0`, Mathlib `56a00585`:

```
lake exe cache get
lake build +ZInQKernel.OneProof.Main
```

Then run `#print axioms ZInQ.OneProof.frozenTarget` in a file that imports `ZInQKernel.OneProof.Main`. Its output
lists axioms only: the open hypotheses are premises in the theorem's statement, so they do not appear there.
[`scripts/one_proof/check_axioms.py`](scripts/one_proof/check_axioms.py) checks that output.

A cold build is long. The default `lake build` does not build this theorem, so name the target as above. On a
12-core, 18 GB machine, 694 of the 5,225 project modules built in 41 minutes. On GitHub's hosted runners the first
cold build, of this target and the discharges target, took about seven and a half hours of build time over two
runs (16,331 Lake jobs); a run that starts from the previous build of `main` takes 10 to 14 minutes when a push
changes few files. Allow about 60 GB of disk: a finished build is about 53 GB for this repository, plus 6.7 GiB for
Mathlib. Of the 53 GB, 48 GB are Lake's per-module setup files, a file of several megabytes per module; the hosted
workflow deletes them from its restored build, which leaves about 8 GB
([#171](https://github.com/Deicyde/diophantine-z-q/pull/171)). Use a short checkout path, because the setup files
embed absolute paths. Clone with `git clone --depth 1 --single-branch`: the fork has several hundred branches.

## More

- [STATUS.md](STATUS.md): the detailed status. Its count block is regenerated after each landing; its prose is
  dated and describes the commit it names.
  [docs/research/frontier.md](docs/research/frontier.md): the project's dated survey of the open statements, with
  sources, ratings and history.
- The manuscripts: [diophantine_zq.pdf](diophantine_zq.pdf) ([TeX](diophantine_zq.tex)) and the earlier conditional
  [October 11 manuscript](October%2011%20Manuscript/README.md); the polynomial and its checks are in
  [construction/](construction/README.md). The copy here is the November 5 text that `ZInQ.FrozenTarget` was frozen
  against. Upstream has revised the manuscript since (version 20 as of 2026-11-18), with corrections listed in
  its README.
- The previous, longer README, with the earlier five-hypothesis theorem and its trust statements, is
  [here](https://github.com/Deicyde/diophantine-z-q/blob/222c98bfaaade688e1c0afdef7c857ce59ab6081/README.md).
- [Blueprint site](https://deicyde.github.io/diophantine-z-q/) (redeployed after each main build cache run that
  passes on `main`).
- Licence: the fork's own material is under the Apache License 2.0 ([LICENSE](LICENSE)). It does not cover the
  manuscripts, `construction/` and `lean/`, which came from upstream, or the vendored libraries
  ([NOTICE](NOTICE), [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md)).
- Credits: the November 5 manuscript was produced by Elliot Glazer with Astra 6, Sol 6.1 and Opus 5.5, with auditing
  from Fable 5.1. Vendored libraries are credited in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md), and contributed
  proofs in the [credits section of OPEN.md](docs/one-proof/OPEN.md#credits). Everyone who contributed is listed in
  [CONTRIBUTORS.md](CONTRIBUTORS.md).
