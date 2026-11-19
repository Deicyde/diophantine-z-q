# Where is “ℤ is Diophantine in ℚ” formalized?

*Unreviewed machine audit. AI agents produced every verdict; no mathematician has checked any of it.*

Made for the [Deicyde/diophantine-z-q](https://github.com/Deicyde/diophantine-z-q) project. It is not reviewed by
the manuscript's author or by the maintainer of [nasqret/z-in-q-lean](https://github.com/nasqret/z-in-q-lean).
Corrections are welcome as issues.

**Scope.** [M] is *ℤ is Diophantine in ℚ*, the manuscript dated November 5, 2026, in
[elliotglazer/diophantine-z-q](https://github.com/elliotglazer/diophantine-z-q), 148 pages. For each of its 71
numbered statements, 132 numbered displays and 127 further passages that [F]'s blueprint cites, agents searched
two Lean repositories separately, [F] (Deicyde/diophantine-z-q) and [N] (nasqret/z-in-q-lean), compared the
statements, and recorded each declaration's standing: proved, assumed, a definition, or `sorry`. They read both
repositories' source at the pins and built nothing. Each annotation records how its link was made and that no
person reviewed it.

## Pins

| | |
|---|---|
| [M] | `97cec7fdd757d9a8e4f468151a47a6d3610fb2f2` |
| `diophantine_zq.pdf` sha256 | `dfe8f60c88a6e7a05d0f16ee46063eb6b30163dd238670beca5147bf898abb15` (892,753 bytes, 148 pages) |
| [F] (FORK_PIN) | `f81ade8be515a0864bab15aacb80ffdbfd923d5d` |
| [N] (NASQRET_PIN) | `de33a32dc47dfdb1efa6c70d0b837bc6a5c9a2c6` |
| [N]'s dependency | elliotglazer/diophantine-z-q at `2358394558aafae202a1ce6d3bd1b536b79ad3d0`, an earlier state of [F]'s kernel |

This folder sits in [F]. Its verdicts are about [F] at the pin above, not at the commit you are reading.

## Viewing it

On the project's site: <https://deicyde.github.io/diophantine-z-q/companion/pdf-overlay/viewer/index.html>. The
site holds no copy of the manuscript. The page fetches the PDF from `raw.githubusercontent.com` at [M]'s pin, in
your browser, and checks its sha256 before showing it (`"remote": true` in `pdf-overlay/overlay.config.json`). The
site is rebuilt when a Lean change on `main` passes its hosted build, so a change here shows up with the next one.

On your own machine:

```sh
cd docs/companion/manuscript
python3 pdf-overlay/tools/serve.py --build
```

then open <http://127.0.0.1:8000/pdf-overlay/viewer/index.html>. `serve.py` fetches the PDF from the same
address, checks its sha256 and keeps it in a local cache; the PDF is not in this
folder. A card's kind names its repository (`theorem · fork`, `def · nasqret`, `… · nasqret dependency`) and
any standing short of proved (`conditional`, `assumed`, `sorry`). The panel shows one note per item, from the
item's first record; every record's note, naming its repository and standing, is in its file under
`manuscript/annotations/` ([Literature Links](https://github.com/mathlib-initiative/literature-links) 1.0.1).

## The answer

Both repositories state most of [M]'s items in Sections 1–6, 10–12 and Appendix C. Neither formalizes
Sections 7–9 or Appendices E–G, where [M] proves Theorem 5.3, nor Appendix H, part of the proof of Theorem 4.1:
a search of each found there only (RC), a few displays of Appendices E and F, and, in [F], Lemma H.1. Neither proves Theorem 1.1 unconditionally.

The 71 numbered statements. Subject [M], object the repository; relations are those of each verdict's key links.

| | [F] | [N] |
|---|---:|---:|
| stated and proved | 4 | 4 |
| stated, proved only from assumed hypotheses | 6 | 2 |
| stated and assumed | 1 | 0 |
| stated, neither proved nor assumed | 2 | 3 |
| partly stated, or stated differently | 2 | 5 |
| absent (checked) | 56 | 57 |
| `exactMatch` / `closeMatch` / `broadMatch` | 12 / 1 / 0 | 5 / 2 / 2 |
| `narrowMatch` / `relatedMatch` (differs) | 2 / 0 | 1 / 4 |
| `noMatch` | 56 | 57 |

All 660 verdicts (330 items × 2 repositories) are complete; none is "Not yet judged". The only numbered
statements absent outside Sections 7–9 and Appendices E–H are Corollaries 13.1–13.3, in both.

### The five headline statements

- **Theorem 1.1**: [F] exact, proved only from `SixContactMin` and `PoleCompleteness` (or the open rows of
  `OPEN.md`); [N] exact, conditional: its headline `bounded_from_height_tian_gross_zagier` proves it from
  `SixContactMin`, `PublishedTian47` and `SimpleZeroRank`.
- **Lemma 1.2**: [F] close, conditional, with a slope-representation hypothesis [M] does not list; [N] differs,
  conditional: other height and rank hypotheses, and a polynomial defining ℤ never identified with [M]'s P_*.
- **Theorem 4.1**: [F] exact (`SixContactEstimate`), stated, neither proved nor assumed; the headline assumes its
  instance `SixContactMin`. [N] stronger (`HeightInstance`, no condition on S), conditional.
- **Theorem 5.2**: [F] exact (`PoleCompleteness`), assumed by the headline; proved only conditionally
  (in `frozenTarget`'s route, from four assumed inputs: Theorem 5.3, the Cassels–Tate pairing, BCDT Theorem A and
  Kolyvagin's Theorem 1); [N] exact, stated, neither proved nor assumed, and its proofs use the dependency's pole polynomial instead.
- **Theorem 5.3**: [F] exact (`RestrictedConverseGenuine`), assumed; [N] close, stated only, with the Selmer
  corank and analytic order as arbitrary arguments.

Details: [`docs/headlines.md`](docs/headlines.md).

### Confirmed findings

Each survived two skeptics, each reading [M]'s LaTeX and the repository's source. None is a typo.

- **[N], 23 items** (Proposition 6.1, Lemmas 11.1 and 11.2, Eqs (8), (9) and 18 passages): the dependency's pole
  polynomial uses the curves y² = x(x − ℓ)(x + ℓ), where [M] has y² = x(x − ℓ)(x + 3ℓ), so its slope predicate,
  height certificate, local congruence, test relation and specification are of another polynomial. The
  dependency does this on purpose: its source marks these templates as its Route K variant and names [M]'s form.
- **[N], Theorem 4.1**: `HeightInstance` fixes R = D with no condition on S, claiming a smaller constant when S has
  a prime above D.
- **[N], Lemma 5.1** and its passage: `polePredicate_sound` holds for every prime p > 3 and any finite multiplier
  set.
- **[N], Lemma 1.2** and its passage: hypotheses outside [M]'s list, and no theorem identifies [M]'s P_*; neither
  statement implies the other.
- **[N], Lemma 5.5**: only that a simple zero gives a point of infinite order.
- **[N], three Section 6 passages** (formal conventions, local conventions, Silverman): `Sun28.ShortFormal` proves
  less than [M]'s inverse exponential.
- **[N], the j-form passage**: its first display only at S = S_mul.
- **[F] and [N], Section 12 size, catalogue, cutoff and the C.2 recipe counts**: a weaker prime bound, the cutoff
  c_* < 2^2^4617, and an upper bound only for the counts.
- **[F], Lemma 5.5**: only r = 1, through the assumed `KolyvaginThm1`.
- **[F], four Section 6 passages** (multiplication template, formal and local conventions, Silverman): as for
  [N], the formal logarithm's inverse exponential is not stated.
- **[F], Lemma H.1**: only K = ℚ_ℓ with F Galois, conditional.
- **[F] and [N], Step F4**: stronger, [F] 12 h(u) ≤ h(J(u)) + 450 and [N] h(u) ≤ h(J(u)) + 50.
- **[F] and [N], (K6)**: stronger ([F] for every e ≥ 1, odd n and f; [N] through its dependency).
- **[F], (K7)**: stronger, the vendored Tau Ceti Mackey formula.
- **[N], (O.10)**: stronger, `HeckeShell.divided_shell` for odd p and k.
- **[F] and [N], Eq (6)**: stronger, `Density.card_TL_le` bounds a set of bad primes containing [M]'s, uniformly in
  L and with a smaller error ([N] through its dependency).

55 in all (14 [F], 41 [N]); the list with declarations is `python3 -I scripts/mapping/stats.py findings`, run in this folder.

## What was checked and what was not

Checked: every item's region against `diophantine_zq.pdf` itself; every declaration named against an index built
from its repository's source at its pin, with its standing; each verdict by a mapper and an independent verifier, a
judge where they disagreed, two skeptics for each claimed finding and one for each absence in Sections 7–9 and
Appendices E–H; the annotations by the Literature Links scan and `check_generated.py` (also in CI).

Not checked: whether anything is proved in Lean's sense (nothing was built, no axioms were inspected; `proved`
means no `sorry` in the declaration's own text); non-findings, which no skeptic tested; the dependency's
declarations beyond their statements. No person reviewed any verdict.

A review after the mapping found five blocking and three major defects, among them conditional results recorded
as proved and false details in ten notes. A last pass fixed them. Nothing re-reviewed that pass, except its new
verdict on Eq (6), which two skeptics tested. One status remains in doubt: Section 12 size [N] may be `differs`
rather than `weaker`, because the dependency's bounds are for a polynomial built from other pole templates.

## License

Apache-2.0 (`LICENSE`, `NOTICE`). [M]'s PDF and TeX state no licence and are not in this folder. The repository's own `NOTICE` says how it holds them.
