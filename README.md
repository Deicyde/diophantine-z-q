# ℤ is Diophantine in ℚ: the Lean proof

## Contributors

- **Elliot Glazer** ([@elliotglazer](https://github.com/elliotglazer)): the manuscript and the upstream repository.
- **Jack McCarthy** ([@Deicyde](https://github.com/Deicyde)): this fork, with AI agents working for him.
- **Contributed work on `main`:** loning ([@loning](https://github.com/loning)),
  Chey Loveday ([@CheyLoveday](https://github.com/CheyLoveday)),
  Carlos Toledo ([@carlostoledo1891](https://github.com/carlostoledo1891)),
  Cameron Freer ([@cameronfreer](https://github.com/cameronfreer)) and
  Junyan Xu ([@alreadydone](https://github.com/alreadydone)).
- **Claims and discussion:** zachbaugher ([@zachbaugher](https://github.com/zachbaugher)).
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

The proof follows the manuscript's route. Its hypotheses fall into two groups. The first is the statements from
which Lean derives the instance of the six-contact height estimate (the manuscript's Theorem 4.1) that the proof
uses. The second is four statements from which Lean proves pole completeness (Theorem 5.2) for the manuscript's own
pole polynomial, as the manuscript's Section 5.1 does:
- the manuscript's restricted converse theorem (Theorem 5.3);
- the Cassels–Tate pairing on the curves of Theorem 5.3 (Poonen–Stoll's statement of Cassels' theorem, the print
  the manuscript cites for its Lemma 5.4; Lean proves Lemma 5.4 from it);
- consequences of the two printed theorems behind its Lemma 5.5: the modularity theorem of Breuil, Conrad, Diamond
  and Taylor (Theorem A), and Kolyvagin's Theorem 1.

Theorem 5.3 stays one hypothesis of the main theorem. Separately,
[#110](https://github.com/Deicyde/diophantine-z-q/pull/110) reduces it, along the manuscript's Sections 7–9 and
Appendices E–G, to step-level hypotheses (`ZInQ.Manuscript.RC.Wiring.restrictedConverseGenuine_of_leaves`). Some of
those still state their step's conclusion directly and are being restated over the manuscript's objects. Proving the
steps in Lean is [#83](https://github.com/Deicyde/diophantine-z-q/issues/83).
Apart from these hypotheses, the main theorem departs from the manuscript in two smaller steps, both proved: route AP
replaces Proposition 6.2 by Szemerédi's theorem in the primes together with a density theorem for the good primes
(Proposition D), and the catalogue bound is proved in the weaker form CAT₈. Deriving the height estimate from the
literature also re-sources some steps of the manuscript's Section 4 and replaces its last step. An earlier proof,
Route K, replaced pole completeness by an argument through Tian–Yuan–Zhang and Gross–Zagier for a different pole
polynomial. It is retired and kept at the tag
[`route-k-final`](https://github.com/Deicyde/diophantine-z-q/tree/route-k-final);
[`docs/research/rs-pole.md`](docs/research/rs-pole.md) explains why it existed.

## Status (fork `main` at `e1dddb4d`, 2026-11-18)

- **One theorem, [`ZInQ.OneProof.frozenTarget`](ZInQKernel/OneProof/Main.lean), proves `ZInQ.FrozenTarget` from 33
  open hypotheses, statements not yet proved in Lean.** Lean's kernel checks it with no `sorry` and only the standard
  axioms `propext`, `Classical.choice` and `Quot.sound`. Everything else, including every finite computation, is
  proved in Lean. Since 2026-11-18 GitHub's hosted runners run this check too: the [main build
  cache](.github/workflows/main-build-cache.yml) workflow builds the theorem after a push to `main` that changes Lean
  and fails unless its axioms are among these three. Its [first passing
  run](https://github.com/Deicyde/diophantine-z-q/actions/runs/44219370755) was at `be73b91c`, it [passed at this
  commit](https://github.com/Deicyde/diophantine-z-q/actions/runs/44447567722), and its [run
  list](https://github.com/Deicyde/diophantine-z-q/actions/workflows/main-build-cache.yml) shows the other commits it
  has passed on ([#62](https://github.com/Deicyde/diophantine-z-q/issues/62)). The [build-cost
  table](docs/one-proof/CONTRIBUTING.md#what-it-costs-to-build) has no build by anyone outside the project yet.
- **The hypotheses are premises, not axioms:** Lean proves "if they all hold, then ℤ is Diophantine in ℚ". 29 belong
  to the six-contact height estimate (the manuscript's Theorem 4.1). The other four are the inputs from which Lean
  proves pole completeness (the manuscript's Theorem 5.2), as the manuscript does: its Theorem 5.3, the Cassels–Tate
  pairing on its curves E_ℓ: y² = x(x − ℓ)(x + 3ℓ) (from which Lean proves its Lemma 5.4), and consequences of the
  modularity theorem of Breuil, Conrad, Diamond and Taylor and of Kolyvagin's Theorem 1. Of the 29, 11 are classed as
  published theorems and 18 as consequences of a published theorem or of the manuscript's text. Under the strict count
  (a refereed theorem as printed, checked against the page), 5 qualify; the other 24 still need an argument or a
  reading. AI raters assigned these classes. The live list, with each statement's source, rating and holder, is
  [`docs/one-proof/OPEN.md`](docs/one-proof/OPEN.md).
- **Progress:** 65 open hypotheses on 2026-11-15, 30 on 2026-11-17, 33 now. The count falls when a hypothesis is
  proved, can rise or fall when one is restated as printed statements, and changes when the proof follows the
  manuscript more closely: the switch away from Route K removed five hypotheses and added pole completeness, following
  the manuscript's complex-multiplication argument in Section 4 added four, and deriving pole completeness from its
  Section 5 replaced one by four. So it does not measure proved content.
- **AI caveat.** The manuscript was written with AI models and audited by an AI model, and the project's Lean was
  written by AI coding agents. Published hypotheses have been compared with their printed sources by AI readers, and
  those flagged `unread` on OPEN.md have had no statement check against the page yet. Contributors have also posted
  statement checks on [#14](https://github.com/Deicyde/diophantine-z-q/issues/14), credited in
  `docs/one-proof/credits.tsv`; two of them (2026-11-18) were made by a person against the publisher's PDF, with AI
  used only for drafting. `docs/one-proof/reviews.tsv` does not record them as readings yet.

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
changes few files. Allow about 50 GB of disk: the finished hosted build is 37 GiB for this repository and 6.7 GiB
for Mathlib. Use a short checkout path, because Lake writes a file of several megabytes per module that embeds
absolute paths. Clone with `git clone --depth 1 --single-branch`: the fork has several hundred branches.

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
