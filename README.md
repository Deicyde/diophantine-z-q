# ℤ is Diophantine in ℚ: the Lean proof

This fork formalizes in Lean 4 the main theorem of the manuscript
[*ℤ is Diophantine in ℚ*](diophantine_zq.pdf) (November 5, 2026, Theorem 1.1): there is a polynomial `P` with
integer coefficients such that a rational number `q` is an integer exactly when `P(q, w) = 0` for some
`w ∈ ℚ^292,890,231,904`. Lean states it as `ZInQ.FrozenTarget` ([`ZInQKernel/Target.lean`](ZInQKernel/Target.lean)).

## Status (fork `main` at `0be76f13`, 2026-11-17)

- **One theorem, [`ZInQ.OneProof.frozenTarget`](ZInQKernel/OneProof/Main.lean), proves `ZInQ.FrozenTarget` from
  39 open hypotheses, statements not yet proved in Lean.** Lean's kernel checks it with no `sorry` and only the
  standard axioms `propext`, `Classical.choice` and `Quot.sound`. Everything else, including every finite
  computation, is proved in Lean.
- **The hypotheses are premises, not axioms:** Lean proves "if they all hold, then ℤ is Diophantine in ℚ". 34 belong
  to the six-contact height estimate (the manuscript's Theorem 4.1) and 5 to the positive-rank part
  (Tian–Yuan–Zhang and Gross–Zagier). Each is a published theorem (27), a consequence of one (9) or a combination of
  several (3). Under the project's strict count, 17 are published theorems in their printed form; the other 22 still
  need an argument or a reading. The live list, with each statement's source, rating and holder, is
  [`docs/one-proof/OPEN.md`](docs/one-proof/OPEN.md).
- **Progress:** 65 open hypotheses on 2026-11-15, 39 on 2026-11-17.
- **AI caveat.** The manuscript was written with AI models and audited by an AI model, and the project's Lean was
  written by AI coding agents. Published hypotheses have been compared with their printed sources only by AI readers,
  and the newest (flagged `unread` on OPEN.md) not at all; no person has confirmed one yet.

## Upstream

Elliot Glazer's repository, [elliotglazer/diophantine-z-q](https://github.com/elliotglazer/diophantine-z-q), plans
to take this work in as staged pull requests once its Lean CI is fixed; [#139](https://github.com/elliotglazer/diophantine-z-q/pull/139)
holds this fork as of `c1e4ed1b`. Its topic issues
([#74](https://github.com/elliotglazer/diophantine-z-q/issues/74),
[#76](https://github.com/elliotglazer/diophantine-z-q/issues/76),
[#81](https://github.com/elliotglazer/diophantine-z-q/issues/81) to
[#86](https://github.com/elliotglazer/diophantine-z-q/issues/86), indexed in
[#37](https://github.com/elliotglazer/diophantine-z-q/issues/37)) list the open statements by area.

## Contribute

Start at [issue #14](https://github.com/Deicyde/diophantine-z-q/issues/14); a coding agent can follow it as written.

- **Prove a hypothesis in Lean:** pick an `open` row on [OPEN.md](docs/one-proof/OPEN.md), claim it on #14, follow
  [CONTRIBUTING.md](docs/one-proof/CONTRIBUTING.md), and open a pull request against this fork's `main`.
- **Check a statement against its printed source** (no Lean needed): follow
  [STATEMENT-CHECKS.md](docs/one-proof/STATEMENT-CHECKS.md); [pages-wanted.md](docs/one-proof/pages-wanted.md)
  lists the pages to read. A person's reading counts for more than an AI's: it is what clears a statement's flags.

## Check it yourself

Lean `v4.35.0`, Mathlib `56a00585`:

```
lake exe cache get
lake build +ZInQKernel.OneProof.Main
```

Then run `#print axioms ZInQ.OneProof.frozenTarget` in a file that imports `ZInQKernel.OneProof.Main`. Its output
lists axioms only: the open hypotheses are premises in the theorem's statement, so they do not appear there.

## More

- [STATUS.md](STATUS.md): the detailed status, rebuilt after each landing.
  [docs/research/frontier.md](docs/research/frontier.md): the project's dated survey of the open statements, with
  sources, ratings and history.
- The manuscripts: [diophantine_zq.pdf](diophantine_zq.pdf) ([TeX](diophantine_zq.tex)) and the earlier conditional
  [October 11 manuscript](October%2011%20Manuscript/README.md); the polynomial and its checks are in
  [construction/](construction/README.md).
- The previous, longer README, with the earlier five-hypothesis theorem and its trust statements, is
  [here](https://github.com/Deicyde/diophantine-z-q/blob/222c98bfaaade688e1c0afdef7c857ce59ab6081/README.md).
- [Blueprint site](https://deicyde.github.io/diophantine-z-q/) (a snapshot from 2026-11-13).
- Credits: the November 5 manuscript was produced by Elliot Glazer with Astra 6, Sol 6.1 and Opus 5.5, with auditing
  from Fable 5.1. Vendored libraries are credited in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md), and contributed
  proofs in the [credits section of OPEN.md](docs/one-proof/OPEN.md#credits).
