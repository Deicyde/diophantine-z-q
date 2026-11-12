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
> - `Literature.HeckeContinuation`: for every `d ≠ 0`, `L(C_d, s)` extends to an entire function
>   (Deuring, Hecke: `C_d` has complex multiplication by `ℤ[i]`, so `L(C_d, s)` is the L-function
>   of a Hecke character of `ℚ(i)`).
> - `Literature.TYZThm35ReadingA`: for squarefree `d ≡ 5 (mod 8)`, if `L(C_d, s)` vanishes to order
>   at least 2 at `s = 1`, then the genus sums `T5aCl d` and `T5bCl d` are both even. (Each is a
>   sum, over certain set partitions of the primes of `d`, of products of the orders of the
>   subgroups of squares `2Cl(ℚ(√−d_B))` in the class groups, where `d_B` is the product of a
>   block's primes.) This is a consequence of Theorem 3.5(2) of Tian–Yuan–Zhang, *Genus periods,
>   genus points and congruent number problem* (arXiv:1411.4728v1; Asian J. Math. 21 (2017),
>   721–774), for `n = d ≡ 5 (mod 8)`, under one reading of its genus sums (reading A: the
>   decompositions of `d` are set partitions of its primes, each counted once, with a trivial
>   factor `d₁ = 1` allowed). It uses only the case `𝓛(n) = 0` of the printed hypothesis. (The
>   paper defines its invariant `𝓛(n)` from `L(C_n, 1)` or `L′(C_n, 1)` and sets it to `0` exactly
>   when the order of vanishing at `s = 1` is at least 2. The printed hypothesis is a condition on
>   a genus point `P(n)`, followed by an "i.e." that restates it as "`2^{−ρ(n)}𝓛(n)` is even" and
>   is asserted without proof; when `𝓛(n) = 0` the condition on `P(n)` follows from results that
>   the paper proves, so the "i.e." is not needed.) **No refereed text that we have read states
>   reading A explicitly.** The introductory theorem that states these criteria (Theorem 1.2 of
>   the arXiv version, Theorem 1.4 of the journal version) requires every factor `d_i > 1`, and
>   read that way it is false: `d = 26565` and `d = 33117` are counterexamples, in both versions.
>   The paper's proof of Theorem 3.5(2) passes through its Proposition 3.4, whose proof is only
>   sketched in the arXiv version ([docs/research/nt-tyz.md](docs/research/nt-tyz.md)). As
>   supporting evidence, Proposition N (same note, §4; a new argument reviewed twice by AI models
>   and never by a human) proves this statement without Proposition 3.4, from unambiguous results
>   of the paper (among them the convolution identity of its Lemma 2.9), and Lean checks that proof
>   (`PropN.tyzThm35ReadingA_of_tyzInputs`, from the encoding `PropN.TYZInputs` of those results in
>   `ZInQKernel/Hypotheses/TYZInputs.lean`). The comparison of the arXiv and journal versions was
>   an audit by AI agents with web access ([docs/research/locators.md](docs/research/locators.md)),
>   not a check by a human.
>
> From the last two, Lean derives (`Literature.tyzRow5b_of_readingA`) the intermediate statement
> `Literature.TYZRow5b`: for squarefree `d ≡ 5 (mod 8)` with `T5bCl d` odd, `L(C_d, s)` vanishes
> to order at most 1 at `s = 1`.
>
> `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier`
> (`ZInQKernel/MainLiterature.lean`) has no `sorry`, uses no `native_decide`, and depends only on
> the axioms `propext`, `Classical.choice` and `Quot.sound`; so does the intermediate form
> `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzRow5b_functionalEquation5_grossZagier`,
> with `Literature.TYZRow5b` in place of the last two hypotheses. Trust statements list every step,
> published or not, with its source and how it was checked:
> [docs/research/h-trust.md](docs/research/h-trust.md) for H, and
> [docs/research/cr3-trust.md](docs/research/cr3-trust.md) for `CertifiedRankTYZClRk`, the
> positive-rank statement that the L-function statements split up;
> [docs/research/wk-cr3.md](docs/research/wk-cr3.md) §3 (reviewed in
> [docs/research/rv-lit.md](docs/research/rv-lit.md)) checks `GrossZagier`, `FunctionalEquation5`
> and `TYZRow5b` against their sources.
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
