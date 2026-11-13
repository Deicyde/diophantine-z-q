# Z is Diophantine in Q

**Blueprint site: https://deicyde.github.io/diophantine-z-q/**

Browse every statement of the formal proof there: its informal statement and proof sketch, the
statements it depends on, its Lean declarations with links into the source, and whether it is
proved. The site is rebuilt from `main` after each passing verification run.

> **This fork** proves the 11/5 manuscript's Theorem 1.1 in Lean from five explicit hypotheses,
> stated as `Prop`s, not axioms. The first is the six-contact height estimate (the manuscript's
> Theorem 4.1), in the one instance `SixContactMin` from which both of the proof's uses follow. Its
> proof combines refereed theorems and exact computations with new arguments, the manuscript's and
> this repository's, that have been reviewed only by AI models. The other four are statements
> about L-functions of elliptic curves over ℚ (Mathlib's `WeierstrassCurve.LSeries`), three of them
> only about the congruent number curves `C_d : y² = x³ − d²x`. From them Lean derives the
> positive-rank statement that the proof needs:
>
> - `Literature.GrossZagier`: if the L-function of an elliptic curve over ℚ has a simple zero at
>   `s = 1`, the curve has a rational point of infinite order. This is Gross–Zagier (1986), with an
>   auxiliary quadratic twist (Bump–Friedberg–Hoffstein 1990) and modularity
>   (Breuil–Conrad–Diamond–Taylor 2001).
> - `Literature.FunctionalEquation5`: for squarefree `d ≡ 5 (mod 8)`, the functional equation of
>   `L(C_d, s)` with conductor `32d²` and root number `−1` (Deuring, Hecke; Birch–Stephens 1966),
>   stated on the strip `0 < Re s < 2`.
> - `Literature.HeckeContinuation`: for every positive integer `d`, `L(C_d, s)`, defined by its
>   Euler product for `Re s > 3/2`, extends to an entire function (Deuring, Hecke: `C_d` has
>   complex multiplication by `ℤ[i]`, so `L(C_d, s)` is the L-function of a Hecke character of
>   `ℚ(i)`; standard, but the locator audit cited below did not read an original source).
> - `Literature.TYZThm35ReadingA`: for squarefree `d ≡ 5 (mod 8)`, if `L(C_d, s)` vanishes to order
>   at least 2 at `s = 1`, then the genus sums `T5aCl d` and `T5bCl d` are both `0` in `ℤ/2`. Both
>   are sums over set partitions of the primes of `d`, of the products over the blocks `B` of
>   `#2Cl(ℚ(√−d_B))`, the order of the subgroup of squares in the class group, where `d_B` is the
>   product of the primes in `B`; `T5aCl d` runs over the partitions with one block `≡ 5` and all
>   others `≡ 1 (mod 8)`, and `T5bCl d` over those with one block `≡ 7`, one `≡ 3` and all others
>   `≡ 1 (mod 8)`.
>
>   This is a consequence of Theorem 3.5(2) of Tian–Yuan–Zhang (TYZ), *Genus periods, genus points
>   and congruent number problem* (arXiv:1411.4728v1; Asian J. Math. 21 (2017), 721–774), for
>   `n = d ≡ 5 (mod 8)`, under one reading of its genus sums. TYZ write the decompositions of `n` as
>   `n = d₀d₁⋯d_ℓ`; in reading A they are set partitions of the primes of `n`, each counted once,
>   with a trivial factor `d₁ = 1` allowed. In that reading TYZ's two sums are `T5aCl d` and
>   `T5aCl d + T5bCl d`, so their evenness is the conclusion above
>   ([docs/research/nt-tyz.md](docs/research/nt-tyz.md) §1.3). `TYZThm35ReadingA` needs the
>   theorem only when `𝓛(n) = 0`: the paper defines its invariant `𝓛(n)` from `L(C_n, 1)` or
>   `L′(C_n, 1)` and sets it to `0` exactly when the order of vanishing at `s = 1` is at least 2.
>   The printed hypothesis is a condition on TYZ's genus point `P(n)`, followed by an "i.e." that
>   restates it as the evenness of `2^{−ρ(n)}𝓛(n)` and is not proved in the paper. When
>   `𝓛(n) = 0`, the condition on `P(n)` follows directly from the first assertion of the paper's
>   Theorem 3.5 and its Lemma 3.18 (nt-tyz.md §2.2, F6), so the "i.e." is not needed.
>
>   **No refereed text found by the project's literature search, which AI agents carried out,
>   states reading A explicitly** (the one statement found, Smith, arXiv:1603.08479, Theorem 2.1,
>   is unrefereed). TYZ's introductory theorem stating the same parity criteria (Theorem 1.2 of the
>   arXiv version, Theorem 1.4 of the journal version) requires every factor `d_i > 1`, and read
>   that way it is false: `d = 26565` and `d = 33117` are counterexamples, in both versions (exact
>   class-group computations and explicit points giving rank at least 3, not checked in Lean;
>   nt-tyz.md §1.4). The paper's proof of Theorem 3.5(2) passes through its Proposition 3.4,
>   whose proof is only a sketch in the arXiv version; the journal's proof was not assessed on
>   this point. The comparison of the arXiv and journal versions, including these theorem numbers,
>   was an audit by AI agents with web access
>   ([docs/research/locators.md](docs/research/locators.md)), not a check by a human.
>
>   As supporting evidence, not as a hypothesis: Proposition N (nt-tyz.md §4; a new argument
>   reviewed twice by AI models and never by a human) proves `TYZThm35ReadingA` without
>   Proposition 3.4, from unambiguous results of the paper, among them the convolution identity of
>   its Lemma 2.9 (which the repository's notes and Lean names call Lemma 2.8). Lean checks that
>   proof from `PropN.TYZInputs`, a hand encoding of those results in
>   `ZInQKernel/Hypotheses/TYZInputs.lean` (`PropN.tyzThm35ReadingA_of_tyzInputs`); Lean does not
>   check that the encoding matches the paper.
>
> From `Literature.TYZThm35ReadingA` and `Literature.HeckeContinuation`, Lean derives
> (`Literature.tyzRow5b_of_readingA`) the intermediate statement `Literature.TYZRow5b`: for
> squarefree `d ≡ 5 (mod 8)` with `T5bCl d` odd, `L(C_d, s)` vanishes to order at most 1 at
> `s = 1`.
>
> `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier`
> (`ZInQKernel/MainLiterature.lean`) has no `sorry`, uses no `native_decide`, and depends only on
> the axioms `propext`, `Classical.choice` and `Quot.sound`; so does the intermediate form
> `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzRow5b_functionalEquation5_grossZagier`,
> with `Literature.TYZRow5b` in place of `Literature.TYZThm35ReadingA` and
> `Literature.HeckeContinuation`. Trust statements list every step, published or not, with its
> source and how it was checked:
> [docs/research/h-trust.md](docs/research/h-trust.md) for H, and
> [docs/research/cr3-trust.md](docs/research/cr3-trust.md) for `CertifiedRankTYZClRk`, the
> positive-rank statement that Lean derives from the L-function statements;
> [docs/research/wk-cr3.md](docs/research/wk-cr3.md) §3 (reviewed in
> [docs/research/rv-lit.md](docs/research/rv-lit.md)) checks `GrossZagier`, `FunctionalEquation5`
> and `TYZRow5b` against their sources (the locator audit found that the original source of the
> conductor and functional equation in `FunctionalEquation5` has not been fully read).
> `CertifiedRankTYZClRk` itself, and weaker forms down to positive rank on the two curves per input
> that the proof uses, give variants of the theorem ([KERNEL_PLAN.md](KERNEL_PLAN.md)).
>
> Everything else is proved in Lean, and every finite computation is checked by the kernel. That
> includes every step from the four L-function statements, through `CertifiedRankTYZClRk`, to the
> certified-rank statement CR₃ that the construction uses (`ZInQ.CertifiedRank`: when the explicit
> 2-Selmer system of `C_d` has 8 elements and contains a class `a` with `|a| ≡ 7 (mod 8)`, `C_d` has
> a rational point with `x ∈ aℚ*²`): Rédei's formula, Theorem 3.6 and Corollary 4.4 of
> [docs/research/tyz-5b.md](docs/research/tyz-5b.md), Proposition 0
> ([docs/research/descent-alt.md](docs/research/descent-alt.md) §4.1), the complete 2-descent and
> Mordell–Weil for the curves `C_d`. Three more inputs started as hypotheses and are proved:
> Mordell–Weil for the generator curve; the catalogue bound, by an effective Dirichlet theorem
> ([docs/effective-dirichlet-plan.md](docs/effective-dirichlet-plan.md)); and pole completeness,
> by an explicit 2-descent from CR₃ ([docs/research/slot-k.md](docs/research/slot-k.md)). For
> that step the polynomial's pole template uses the congruent number curves
> `y² = x(x − ℓ)(x + ℓ)` where the manuscript has `x + 3ℓ`; the statement proved, with its
> variable count and bounds, is the manuscript's. A fourth, the twenty-two-prime pattern, is not
> needed: a change in a completeness proof ([docs/research/nt-22p.md](docs/research/nt-22p.md))
> uses long progressions of good primes instead, which come from Szemerédi's theorem in the primes
> (Vasily Ilin's Lean proof of the Green–Tao theorem, vendored in `ThirdParty/GreenTao/` and
> extended to dense sets of primes) and a density theorem for those primes
> ([docs/research/pd-paper.md](docs/research/pd-paper.md)). The theorem from `SixContactMin` and
> CR₃ itself is `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank`
> (`ZInQKernel/MainGreenTao.lean`), and the three-hypothesis version that keeps the manuscript's
> prime pattern and none of the vendored code is
> `ZInQ.exists_bounded_integer_polynomial_defining_integers_of` (`ZInQKernel/Main.lean`); both have
> the same axioms. See [KERNEL_PLAN.md](KERNEL_PLAN.md), the
> [final audit](docs/kernel-audits/final-audit-2026-11-07.md) of the earlier version with
> hypotheses H, PC, 22P and CAT, the [blueprint site](https://deicyde.github.io/diophantine-z-q/)
> and its sources in
> [blueprint/](blueprint/README.md). The rest of this README is upstream's.

This repository contains the November 5, 2026 manuscript **Z is Diophantine in Q**, the October 11, 2026 manuscript **A conditional Diophantine definition of Z in Q from four arithmetic inputs**, and comparison notes. A research archive preserves the constructions, computations, proof drafts, reviews, and partial Lean formalization developed for the 11/5 manuscript.

## Start here

| To… | Open… |
| --- | --- |
| Read the 11/5 argument | [11/5 manuscript PDF](diophantine_zq.pdf) |
| Inspect or edit the 11/5 manuscript | [11/5 TeX source](diophantine_zq.tex) |
| Read the 10/11 manuscript and compare the constructions | [October 11 Manuscript](October%2011%20Manuscript/README.md) |
| Browse the polynomial and run its checks | [Curated construction](construction/README.md) |
| Build the 11/5 manuscript or accepted Lean modules | [Build instructions](docs/building.md) |
| Inspect the formalization | [Accepted Lean helper snapshot](lean/README.md) |
| Find the construction, supporting calculations, or earlier approaches | [Research guide](docs/research-guide.md) |
| Audit exact theorem applications, conventions and repairs | [Theorem application inventory](docs/theorem-application-audit/README.md) |
| Download the saved research history | [Research handoff zip, 340 MB](https://github.com/elliotglazer/diophantine-z-q/releases/download/research-handoff-2026-11-04-r2/z-in-q-research-handoff-2026-11-04-r2.zip) |
| Check a download | [SHA-256 checksums](SHA256SUMS) and [verification instructions](docs/research-guide.md#verify-and-restore-the-archive) |
| Report a mathematical or implementation issue | [Contribution guide](CONTRIBUTING.md) |
| Cite the 11/5 manuscript or research archive | [BibTeX entries](CITATION.bib) |

The current 11/5 TeX source and PDF, together with the dated research handoff snapshot, are also available from the [current research release](https://github.com/elliotglazer/diophantine-z-q/releases/tag/research-handoff-2026-11-04-r2).

## The 11/5 manuscript's result

To say that the integers are **Diophantine in the rationals** is to say that being an integer can be expressed by one polynomial equation with rational auxiliary variables. The 11/5 manuscript presents a construction of a fixed polynomial with integer coefficients such that

$$
q\in\mathbb Z
\quad\Longleftrightarrow\quad
\exists\,\mathbf w\in\mathbb Q^{292\,890\,231\,904},\quad P(q,\mathbf w)=0,
\qquad q\in\mathbb Q.
$$

The input is the ordinary rational number $q$. The witnesses are rational numbers as well. The same polynomial must work for every input.

The stated bounds for this polynomial are:

| Quantity | Bound |
| --- | --- |
| Total ambient variables, including the input | 292,890,231,905 |
| Total degree | Less than $2\uparrow\uparrow 7$ |
| Absolute value of each coefficient | Less than $2\uparrow\uparrow 8$ |

Here $2\uparrow\uparrow n$ is a right-associated tower of $n$ twos: $2\uparrow\uparrow 1=2$ and $2\uparrow\uparrow(n+1)=2^{2\uparrow\uparrow n}$. The variable count is an ambient bound; it does not assert that every variable occurs essentially. The construction is specified through finite formulas and substitutions, rather than an expanded list of monomials.

The 11/5 manuscript derives three consequences:

- A refutation of Mazur's finite-connected-components conjecture for the closure of rational points in the real locus.
- A universal rational Diophantine polynomial with ordinary integer program and input parameters.
- Many-one equivalence of $\operatorname{HTP}(\mathbb Q)$ with the halting set $0'$.

The bounds above concern the integer-defining polynomial $P$. They do not automatically apply to the universal polynomial or its specializations.

## Relation to earlier work

The 11/5 construction builds on OpenAI's preprint [*Hilbert's tenth problem over the rational numbers*](https://github.com/openai/math/blob/main/preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026/main.pdf), dated October 6, 2026. The 11/5 manuscript concerns a Diophantine definition of the ordinary embedded integers and its stated quantitative bounds. Undecidability of the existential theory of the rationals is not presented here as a new corollary of this project.

The 11/5 manuscript's bibliography and source-application appendices identify its other mathematical inputs. The [research guide](docs/research-guide.md#map-of-the-argument) connects the 11/5 arguments to their supporting files.

## Comparison with the 10/11 manuscript

The [10/11 manuscript](October%2011%20Manuscript/ZIsDiophantineInQBySohailsGPT-6.pdf) and the 11/5 manuscript use the same elliptic curve and share a strategy: build arithmetic on integer labels, control the height of a candidate rational scalar, and force it to equal its labelled integer by sufficiently accurate approximation. The 10/11 manuscript uses congruence at the fixed prime $3$; the 11/5 manuscript uses real approximation with an auxiliary shift.

The 10/11 argument is explicitly conditional on four OpenAI arithmetic inputs. The 11/5 manuscript presents an unconditional argument and gives simultaneous numerical bounds for its specified polynomial. The 10/11 manuscript does not give a numerical variable count or coefficient bound. Its degree-four conversion is also available for the 11/5 polynomial, with additional variables, so degree alone does not establish a smaller construction. See the [full comparison notes](October%2011%20Manuscript/README.md) for the interfaces, qualifications, and source references.

## Verification status

The [November 5 theorem application inventory](docs/theorem-application-audit/README.md) records 82 scoped review decisions, 147 citations and 443 anchored contexts, with exact source versions, maps, hypotheses and convention changes. The identified source-application obligations have been reviewed and their repairs integrated, including the de Rham comparison and local cochain arguments. [Explicit internal premises remain](docs/theorem-application-audit/DEPENDENCIES.md). These AI reviews do not independently certify every internal lemma or the main theorem.

The 11/5 manuscript presents an unconditional proof. Revision 2 of the 11/5 manuscript includes the later restricted-converse and theta justifications and replaces the von Känel–Kret height dependency with a direct modularity argument and a CM argument. [Four independent AI reviews](docs/reviews/height-replacement/REPORT.md) found no unresolved gap in the replacement within their stated scopes. The revised 11/5 text includes their requested clarifications. These reviews are distinct from independent human peer review and machine verification. See the [revision notes](docs/revision-2.md).

**The Lean formalization is incomplete.** At the November 4 handoff, the main bounded-polynomial declaration still contains `sorry`. The last accepted production snapshot is integration 31, containing 48 modules and 463 explicit public declarations. These counts include definitions and helper results; they are not a count of completed main-proof obligations. Later accepted work remains outside that integration.

The archive preserves superseded and unsuccessful approaches as well as later work. Start with its `CURRENT_STATE.json`, `START_HERE.md`, and `current/` directory before relying on a historical status report. See [the formalization notes](docs/research-guide.md#lean-formalization) for the remaining groups of obligations.

## Research archive

The handoff indexes 57,450 original file locations. Repeated byte-identical files share stored content. It includes a searchable offline `INDEX.html`, a manifest with hashes, a research timeline, and a utility for restoring the original directory layout. Conversational transcripts and credentials are excluded.

The root-level TeX source is the reviewed revision of the 11/5 manuscript; the matching 148-page PDF was rebuilt from it. The November 4 handoff preserves the first release's research history and adds subsequent sources, manuscript versions, feedback and reviews. The repository offers one current release; earlier research versions remain inside the handoff archive. The November 5 audit and its new sources are documented separately in the repository and its source-restoration manifest; the November 4 handoff is not an updated copy of that audit.

## Reproducible checks

The [curated construction](construction/README.md) provides the finite expression, its pinned input, and executable checks without requiring the historical archive. The [Lean directory](lean/README.md) contains the byte-identical accepted helper snapshot, its dependency pins, and a separate unproved target.

The [CI workflow](.github/workflows/research-checks.yml) checks construction regeneration, finite arithmetic cases and inventory consistency, compiles the 11/5 manuscript, and builds the accepted Lean modules with an axiom audit. See [build instructions](docs/building.md) for local commands and the limits of each check. A green CI run concerns those checks, not completion of the main proof.

## AI usage and attribution

The October 11 Manuscript was produced by Sohail Farhangi with ChatGPT 6. The November 5 Manuscript was produced by Elliot Glazer with Astra 6, Sol 6.1, and Opus 5.5, with auditing from Fable 5.1.

[CITATION.bib](CITATION.bib) supplies citation entries for the 11/5 manuscript and research archive with the author field intentionally omitted. Identify a research artifact by the release tag and file hash as well. [Archival release notes](docs/archiving.md) explain the DOI status.

Licenses for original project material are awaiting the maintainer's selection. [Third-party notices](THIRD_PARTY_NOTICES.md) identify upstream software and mathematical sources; the project's license will not relicense those materials. The historical archive needs a per-source redistribution review before public release.
