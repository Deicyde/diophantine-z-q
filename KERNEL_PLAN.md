# Kernel-checked formalization plan

This fork works toward a Lean proof of the 11/5 manuscript's Theorem 1.1, the statement
frozen upstream as `ZInQ.exists_bounded_integer_polynomial_defining_integers`
(`lean/Frozen/BoundedIntegerPolynomial.lean`), in which every finite computation is
checked by the Lean kernel.

## What can and cannot be formalized

The manuscript assembles Theorem 1.1 from six inputs (Lemma 1.2): **G** (canonical point
codes form `2E(K₀) = ℤP₀`), **M** (multiplication), **H** (the six-contact height
estimate), **PC** (pole completeness), **C** (compiler semantics) and **B** (the literal
specification and its size bounds).

Several of these rest on theorems that Mathlib does not have and that cannot be reduced
to computation:

| Input | Deep dependency |
| --- | --- |
| H (Theorem 4.1) | refereed theorems (Shimura curve: Shimura, Deligne, Kottwitz, Baba–Granath, Lin–Yang, González–Rotger; SGA 1, SGA 7, Serre–Tate; Faltings 1983; Scholze; Berger; Pan's Theorem 1.0.4; p-adic Hodge theory of modular forms in the Tate-module normalization, at every level (Saito 1997, Scholl 1990 with Scholze, or Kato 2004), with Deligne–Serre 1974 for weight one; Li, Shimura 1973, Eichler–Shimura (Shimura 1971); Carayol; Serre's local fields; Silverberg–Zarhin; Javanpeykar; Gaudron–Rémond; Pazuki; Igusa), plus the manuscript's descent, conductor and transfer arguments (model reviews only: [rv-h-novel](docs/research/rv-h-novel.md), Astra), the manuscript's geometric, twist and theta-height bookkeeping (Astra; the twist and weight step also [rv-h-c8](docs/research/rv-h-c8.md); of three passages new in the 11/5 text, the de Rham lemma reviewed in [rv-h-trust](docs/research/rv-h-trust.md) and [rv-h-c3](docs/research/rv-h-c3.md), the other two in rv-h-trust and [rv-h-a9c9](docs/research/rv-h-a9c9.md)), NoCM ([h-cm](docs/research/h-cm.md), [rv-h-cm](docs/research/rv-h-cm.md)), and Lemma PR in place of the integral model ([h-b1](docs/research/h-b1.md); model review [rv-h-b1](docs/research/rv-h-b1.md)). No unpublished upstream proof supplement. Outline: [docs/research/h-trust.md](docs/research/h-trust.md) |
| PC (Theorem 5.2) | the restricted converse (Theorem 5.3): Kato, Waldspurger, Bump–Friedberg–Hoffstein, Nekovář, Gross–Zagier–Kolyvagin, BCDT. Under Route K (pole polynomial with the congruent number curves `x + ℓ`), PC is **proved** from the narrow hypothesis CR₃ (`ZInQ.poleCompleteness_of_certifiedRank`): Tian–Yuan–Zhang with Proposition N ([docs/research/nt-tyz.md](docs/research/nt-tyz.md) §4) and Gross–Zagier with an auxiliary imaginary quadratic field ([docs/research/pc-audit.md](docs/research/pc-audit.md) RK7; Kriz's 2-converse is an alternative that is not needed), for curves `C_d`, `d ≡ 5 (mod 8)`, with a 3-dimensional explicit 2-Selmer system. Outline: [docs/research/cr3-trust.md](docs/research/cr3-trust.md) |
| 22P (Proposition 6.2), used by M | Green–Tao linear equations in primes, Möbius–nilsequences, Green–Tao–Ziegler. **Replaced** by route AP, whose input is proved in Lean: Szemerédi's theorem in the primes (`ZInQ.greenTaoDense`, from a vendored Green–Tao proof) and the weak form of Proposition D (`ZInQ.Density.goodPrimeDensity`) |
| CAT (a step in the proof of Proposition 12.1), used by B | the explicit progression estimate of Bennett–Martin–O'Bryant–Rechnitzer; the weaker form CAT₈ that the proof needs is **proved** (`ZInQ.catalogueBound8`, from an effective Dirichlet theorem) |
| MW, used by G | the Mordell–Weil theorem over `ℚ(√2)`: **proved** (`ZInQ.mordellWeilE`, from the two-isogeny descent and Mathlib's descent theorem) |

Each of these conclusions is an elementary statement about rational numbers, integers or
the explicit curve `E`. They enter the main theorem as **explicit hypotheses** (Lean
`Prop`s in `ZInQKernel/Hypotheses/`), not as `axiom`s, so the trust boundary is visible in
the theorem's type. MW has since been proved in Lean
(`ZInQKernel/Model/Descent/MordellWeil.lean`), and CAT by an effective Dirichlet theorem
(`ZInQKernel/Progressions/`; the proof needs the catalogue only below `2^(W⁸)`, far above
the manuscript's `2^(W³)`). PC, for the Route K pole polynomial, is a theorem from the narrower
hypothesis CR₃ (below). That leaves three hypotheses, H_min, CR₃ and 22P:

```lean
theorem ZInQ.exists_bounded_integer_polynomial_defining_integers_of
    (hH : SixContactMin) (hCR : CertifiedRank)
    (h22 : FixedPrimePattern) : FrozenTarget
```

Route AP (below) replaces 22P with a statement that is proved in Lean, which leaves two:

```lean
theorem ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank
    (hH : SixContactMin) (hCR : CertifiedRank) : FrozenTarget
```

in `ZInQKernel/MainGreenTao.lean`. Apart from the root module `ZInQKernel.lean`, which imports everything,
it is the only module that combines the vendored Green–Tao library or the vendored sieve with the
main construction.

The form of the theorem whose hypotheses are closest to the literature, and the fork's headline,
is

```lean
theorem ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier
    (hH : SixContactMin) (hA : Literature.TYZThm35ReadingA) (hC : Literature.HeckeContinuation)
    (hF : Literature.FunctionalEquation5) (hG : Literature.GrossZagier) : FrozenTarget
```

in `ZInQKernel/MainLiterature.lean`. Its four CR₃ hypotheses are Props over Mathlib's L-series of an
elliptic curve (`ZInQKernel/Hypotheses/CR3Literature.lean`): `Literature.GrossZagier` (for every
elliptic curve over ℚ, a simple zero of `L(E, s)` at `s = 1` gives a point of infinite order),
`Literature.FunctionalEquation5` (the functional equation of `L(C_d, s)` with conductor `32d²` and
root number `−1`, on the strip `0 < Re s < 2`), `Literature.HeckeContinuation` (`L(C_d, s)` has an
entire continuation, `d ≠ 0`) and `Literature.TYZThm35ReadingA` (for squarefree `d ≡ 5 (mod 8)`, if
`L(C_d, s)` vanishes to order at least 2 at `s = 1`, then `T5aCl d` and `T5bCl d` are even). The
first three are textbook theorems. The fourth is a consequence of Tian–Yuan–Zhang's Theorem 3.5(2)
for `n ≡ 5 (mod 8)` (arXiv:1411.4728v1; Asian J. Math. 21 (2017), 721–774) in reading A, where
decompositions are set partitions of the primes, each counted once, with `d₁ = 1` allowed (TYZ's two
sums are then `T5aCl d` and `T5aCl d + T5bCl d`); no refereed text found by the project's literature
search, which AI agents carried out, states reading A explicitly. It uses only the case `𝓛(n) = 0`
of the printed hypothesis, which is covered without the hypothesis's "i.e." clause, asserted in the
paper without proof (`docs/research/nt-tyz.md` §2.2 F6). Theorem 1.2 of the arXiv version, which is
Theorem 1.4 of the journal version, keeps in both versions the restriction that every factor `d_i`
is greater than one; read literally it is false (`d = 26565` and `d = 33117` are counterexamples, in
both versions). The paper's proof of reading A passes through its Proposition 3.4, whose proof is a
sketch in the arXiv version. The journal comparison, including these numbers and the convolution
identity's number, Lemma 2.9 in both versions, is an audit by AI agents with web access
(`docs/research/locators.md`), not a human check. As supporting evidence, not as a hypothesis,
Proposition N proves `TYZThm35ReadingA` from unambiguous results of the paper without Proposition
3.4 (`docs/research/nt-tyz.md` §4; two reviews by AI models, none by a human), and Lean checks that
proof (`PropN.tyzThm35ReadingA_of_tyzInputs` from the encoding `PropN.TYZInputs`,
`ZInQKernel/Hypotheses/TYZInputs.lean`, `ZInQKernel/RouteK/PropN.lean`; Lean does not check that the
encoding matches the paper, whose Lemma 2.9 the encoding calls `LemmaTwoEight`). The plan and its
review are `docs/research/wk-cr3.md` and `docs/research/rv-lit.md`. From `TYZThm35ReadingA` and
`HeckeContinuation` Lean derives (`Literature.tyzRow5b_of_readingA`) the intermediate statement
`Literature.TYZRow5b` (`L(C_d, s)` vanishes to order at most 1 at `s = 1` when `T5bCl d = 1`), the
hypothesis of the intermediate form

```lean
theorem ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzRow5b_functionalEquation5_grossZagier
    (hH : SixContactMin) (hT : Literature.TYZRow5b) (hF : Literature.FunctionalEquation5)
    (hG : Literature.GrossZagier) : FrozenTarget
```

From `TYZRow5b`, `FunctionalEquation5` and `GrossZagier` Lean derives
(`Literature.rootNumberVanishing_of_functionalEquation`, then
`Literature.certifiedRankTYZClRk_of_literature`) the positive-rank form

```lean
theorem ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
    (hH : SixContactMin) (hCR : RouteK.Rank.CertifiedRankTYZClRk) : FrozenTarget
```

in `ZInQKernel/RouteK/RankVariants.lean`. `CertifiedRankTYZClRk` says that for squarefree
`d ≡ 5 (mod 8)` with odd genus sum `T5bCl d`, `C_d(ℚ)` has a point of infinite order. Its premise
has no Selmer condition, and in Lean it implies every other form of CR₃. The forms that assume
least are `CertifiedRankRk` and, for the two curves per input that the proof uses,
`CertifiedRankDLRk` and `CertifiedRankDLAdmRk` (the paragraphs on CR₃'s forms below).
`MainLiterature.lean` also has variants that assume H in its j-form `JHeight.JHeightBound`
(`ZInQKernel/Hypotheses/JHeight.lean`), a bound on the height of the Hauptmodul value `J(u)`. It
implies `SixContactMin` in Lean (step F4 and the final numerics), so its trust statement is steps
A1–F3 of `docs/research/h-trust.md` (reduction: `docs/research/wk-h.md`).
Trust statements, which list every step with its supplier, published or not:
`docs/research/h-trust.md` for H, and `docs/research/cr3-trust.md` for `CertifiedRankTYZClRk`.

H enters in its minimal form `SixContactMin` (`ZInQKernel/Hypotheses/HeightMin.lean`): the one
inequality `h(u) ≤ H₆(D) M_{S_mul}(u)²⁴` for `u ∈ ℚ \ 𝒞` that the proof uses, the instance
`S = S_mul`, `R = D` of Theorem 4.1. The manuscript's form `SixContactEstimate` implies it
(`ZInQ.sixContactMin_of_sixContactEstimate`), and
`exists_bounded_integer_polynomial_defining_integers_of_sixContactEstimate` is the main theorem
with H as stated in the manuscript.

CR₃ (`CertifiedRank`, `ZInQKernel/Hypotheses/CertifiedRank.lean`) replaces pole completeness.
The pole polynomial is the Route K one: its curves are the congruent number curves
`y² = x(x - ℓ)(x + ℓ)` instead of the manuscript's `x + 3ℓ` (Lemma 5.1, soundness, holds for both).
CR₃ says: if `d > 0` is squarefree with `d ≡ 5 (mod 8)`, `a` is a squarefree divisor of `d` with
`|a| ≡ 7 (mod 8)`, and the explicit 2-Selmer system `Σ(𝒞_d)` of `d` (`ZInQKernel/RouteK/System/`,
built from Legendre symbols only) has exactly 8 solutions, one of them with first coordinate the
class of `a`, then `C_d : y² = x³ − d²x` has a rational point with `x ≠ 0` and `x ∈ aℚ*²`. It follows
from Proposition 0 (the system is `Sel₂(C_d)`, `docs/research/descent-alt.md` §4.1) with
Tian–Yuan–Zhang (Theorem 3.5 and the argument of the proof of Theorem 3.5(2), §3.3, as completed in
`docs/research/nt-tyz.md` §4 by Proposition N, which has two model reviews, `rv-nt-tyz.md` and
`rv-prop-n.md`) and Gross–Zagier with an auxiliary imaginary quadratic field
(`docs/research/pc-audit.md` RK7); Kolyvagin's published papers enter only inside Tian–Yuan–Zhang.
Kriz's 2-converse (arXiv:2002.04767, Theorem 10.13, a preprint) with the corank lemma is an
alternative that is not needed. The trust statement, with a supplier and a status for every step
and the residual list, is `docs/research/cr3-trust.md` (reviewed in `docs/research/rv-cr3-trust.md`).
PC is then
a theorem (`ZInQ.poleCompleteness_of_certifiedRank`): the descent lemma DL
(`ZInQ.RouteK.descent_lemma`, `docs/research/slot-k.md` §2, proved in `ZInQKernel/RouteK/`) gives,
for every admissible input `B`, a multiplier `m` and two curves `C_{|n|}`, `C_{|nθ|}` certified for
the class `β = sqf(mB)`; CR₃ gives the points, and these give a zero of the pole polynomial.
`exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness` is the main theorem with
PC (Route K) in place of CR₃.

Two narrower hypotheses are available as variants of the main theorem. Proposition 0 is proved in
Lean (`ZInQKernel/RouteK/Selmer/`, `ZInQ.RouteK.Selmer.prop0Statement`): the explicit system is the
textbook 2-Selmer group, defined through the local solubility of 2-coverings. So CR₃ follows from
CR₃^Sel (`ZInQ.RouteK.Selmer.CertifiedRankSel`): for these `d`, if `Sel₂(C_d)` has 8 elements and
contains a class with `|a| ≡ 7 (mod 8)`, then every Selmer class comes from a rational point, that is
`Ш(C_d)[2] = 0`. `exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel` is the
main theorem with CR₃^Sel. Next, 22P can be replaced by 22P_AP (`ZInQ.GoodPrimeAP`: the good slope
primes above `max S_b` contain arithmetic progressions of every length), through a change in the
completeness proof that leaves the polynomial unchanged (`docs/research/nt-22p.md` §3, Lemma P and
Proposition AP, checked by three model reviews and a model audit of the Lean statements:
`docs/research/rv-nt22p-*.md`, `aud-ap.md`). That variant is
`exists_bounded_integer_polynomial_defining_integers_of_goodPrimeAP`. 22P_AP follows from
Szemerédi's theorem in the primes (`ZInQ.GreenTaoDense`: Green–Tao 2008, Theorem 1.2, proved there
only in outline; Tao–Ziegler, Acta Math. 201 (2008), give a complete proof) and the
positive relative upper density of the good slope primes (`ZInQ.GoodPrimeDensity`: the weak form of
Proposition D of nt-22p §2, proved on paper in `docs/research/pd-paper.md` and checked by a model
review, `docs/research/rv-pd-paper.md`), giving
`exists_bounded_integer_polynomial_defining_integers_of_greenTaoDense` and, with CR₃^Sel as well,
`exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_greenTaoDense`.

Szemerédi's theorem in the primes is proved in Lean. The Lean proof of the Green–Tao theorem for the
set of all primes that Vasily Ilin produced with GPT-5.6 Sol in Codex, as a lean-eval benchmark
submission, is vendored in `ThirdParty/GreenTao/` under the Apache License 2.0 and ported to this
Lean and Mathlib (`ThirdParty/GreenTao/NOTICE.md` lists the changes).
`ZInQ.greenTaoDense` (`ZInQKernel/External/GreenTaoDense/`) extends that proof to every set of
primes of positive relative upper density, following `docs/research/gt-dense.md`.
The weak form of Proposition D is proved in Lean as well: `ZInQ.Density.goodPrimeDensity`
(`ZInQKernel/Density/`) follows `pd-paper.md`, with Arend Mellendijk's Selberg sieve from
PrimeNumberTheoremAnd vendored, unchanged except its import lines, under the Apache License 2.0 in
`ZInQKernel/Sieve/`. `ZInQKernel/MainGreenTao.lean` discharges both statements:
`exists_bounded_integer_polynomial_defining_integers_of_goodPrimeDensity` assumes 6C_min, CR₃ and
GoodPrimeDensity, `exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_goodPrimeDensity`
assumes 6C_min, CR₃^Sel and GoodPrimeDensity, and
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank` and
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankSel` assume only
6C_min and CR₃, respectively CR₃^Sel. `ZInQKernel/Main.lean`, and with it the three-hypothesis main
theorem, does not import the vendored library.

On the CR₃ side, Theorem 4.3 of `docs/research/tyz-5b.md` is proved in Lean
(`ZInQKernel/RouteK/Rank5b/`, `ZInQ.RouteK.Rank5b.det_M5b_eq_dot`): on a Selmer-minimal curve the
determinant of Smith's matrix `M_5b` is the parity of the number of primes `≡ 3 (mod 4)` dividing
the first coordinate of a non-torsion Selmer class. So CR₃^Sel follows from `CertifiedRank5b` (if `Sel₂(C_d)` has 8 elements
and `det M_5b = 1`, every Selmer class comes from a rational point;
`ZInQ.RouteK.Rank5b.certifiedRankSel_of_certifiedRank5b`). `CertifiedRank5b` implies CR₃^Sel, so as a
hypothesis it is at least as strong, but it is stated in the terms of Smith's table, the step toward
Tian–Yuan–Zhang's own statement (`tyz-5b.md` §3).
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank5b`
(`RouteK/Rank5bSec3.lean`) takes only SixContactMin and `CertifiedRank5b`; the older variant
`exists_bounded_integer_polynomial_defining_integers_of_certifiedRank5b` also takes 22P.

That step is done: sections 2 and 3 of `tyz-5b.md` are proved in Lean (`ZInQKernel/RouteK/Rank5b/Sec3/`),
including the forest lemma and Theorem 3.6, `det M_5b = T_5b(d)` (`ZInQ.RouteK.Rank5b.det_M5b_eq_T5b`),
where `T_5b(d)` is Tian–Yuan–Zhang's `(7, 3)` genus sum with Rédei's `g` written in Legendre symbols.
`CertifiedRankTYZ` (for squarefree `d ≡ 5 (mod 8)` with `#Sel₂(C_d) = 8` and `T_5b(d)` odd, every
Selmer class comes from a rational point) is the hypothesis in their own terms; it is equivalent to
`CertifiedRank5b` and gives
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZ`. Its trust
statement names Tian–Yuan–Zhang (Proposition N of `docs/research/nt-tyz.md`), Rédei's formula and
Gross–Zagier; one model review found it faithful after docstring repairs, with a numerical check
against PARI on 30 values of `d` (`docs/research/rv-cr5b-sec3.md`). Rédei's formula is proved in
Lean: the Prop `ZInQ.RouteK.Rank5b.RedeiFormula` is the theorem `ZInQ.RouteK.Redei.redeiFormula`
(`ZInQKernel/RouteK/Redei/`, the eight steps of `docs/research/redei-plan.md` §3.2: ambiguous
classes, genus characters and their surjectivity by Dirichlet's theorem, genus theory
`Cl² = ⋂ ker χ_q` by counting, the 4-rank statement, and the 𝔽₂ linear algebra that matches
Rédei's matrix with the bits). So `CertifiedRankTYZCl`, the hypothesis with Tian–Yuan–Zhang's own
`g(d) = #2Cl(ℚ(√−d))` (class groups of `ℚ(√−d)` from Mathlib), is equivalent to `CertifiedRankTYZ`
(`certifiedRankTYZ_iff'`), and
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZCl` takes only
SixContactMin and `CertifiedRankTYZCl`.

These hypotheses all conclude that every 2-Selmer class of `C_d` comes from a rational point, while
the published theorems give only that `C_d(ℚ)` has positive rank. The step between them
(`docs/research/pc-audit.md` RK9) is proved in Lean: the complete 2-descent map is a homomorphism
with kernel `2C_d(ℚ)` and image in `Sel₂(C_d)` (`RouteK/Rank/`), and `C_d(ℚ)` is finitely generated
for every `d ≠ 0` (`ZInQ.RouteK.Rank.fg_points`, `RouteK/RankMW/`, from the two-isogeny descent and
Mathlib's descent theorem), so a point of infinite order and `#Sel₂(C_d) = 8` give every Selmer
class (`loc_of_mem_sel2_of_infinite_order`). Each hypothesis therefore has a positive-rank form,
"`C_d(ℚ)` has a point of infinite order" (equivalently, `d` is a congruent number):
`CertifiedRankRk`, `CertifiedRankTYZRk` (squarefree `d ≡ 5 (mod 8)` with `T_5b(d)` odd; no
condition on `Sel₂`) and `CertifiedRankTYZClRk`, with main-theorem variants in
`RouteK/RankVariants.lean`. `RouteK/RankInf.lean` states the same four hypotheses (with
`CertifiedRankDLRk` below) with the conclusion "`C_d` has infinitely many rational points", the
classical statement that `d` is a congruent number, and proves each equivalent to its positive-rank
form (`exists_infinite_order_iff_infinitelyManyPoints`, from `fg_points`), so the trusted text can
be read without Mathlib's group law. `CertifiedRankTYZClRk` implies `CertifiedRankTYZRk`
(`certifiedRankTYZRk_of_certifiedRankTYZClRk`, by Rédei's formula), which implies `CertifiedRankRk`
(`certifiedRankRk_of_certifiedRankTYZRk`, by Corollary 4.4 and Theorem 3.6), so of these three
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankRk` assumes the
least. `CertifiedRankTYZClRk` is the form whose content is literally Tian–Yuan–Zhang's
Proposition N and Gross–Zagier, with no condition on `Sel₂`; its main-theorem variant
(`…_sixContactMin_certifiedRankTYZClRk`) takes only SixContactMin and `CertifiedRankTYZClRk`.
Lean derives every other form of CR₃ from `CertifiedRankTYZClRk`, including the forms with the
premise `#Sel₂(C_d) = 8` (`certifiedRankTYZ_of_certifiedRankTYZRk'`,
`certifiedRankTYZCl_of_certifiedRankTYZClRk'`, `certifiedRank5b_of_certifiedRankTYZ`) and
`CertifiedRankDLAdmRk`; `docs/research/cr3-trust.md` §0 lists the 14 forms and the implications.

The proof applies CR₃ at only two curves, `C_{d₁}` and `C_{d₁|θ|}`, where `d₁ = D.d₁` comes from a
slot choice `D : RouteK.Slots β θ p₀` (`RouteK/RankDL.lean`). `RouteK.Rank.CertifiedRankDLRk` says
that for all `β, θ, p₀` with `RouteK.Inputs β θ p₀` some slot choice gives two curves with rational
points of infinite order. Lean proves `CertifiedRankRk → CertifiedRankDLRk`
(`certifiedRankDLRk_of_certifiedRankRk`), so this variant assumes no more than the `CertifiedRankRk`
one, and `CertifiedRankDLRk → PoleCompleteness`, hence the main theorem from SixContactMin and
`CertifiedRankDLRk`
(`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLRk`);
`CertifiedRankDLAdmRk` quantifies only over admissible `B`
(`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLAdmRk`). These forms rest on the same literature
as `CertifiedRankRk`. What they add is a smaller target for partial results, such as explicit
points on the curves of some slot choice (`poleSoluble_of_slots_infinite_order`). They depend on the
internal definitions `Inputs` and `Slots`, so a change to the slot construction changes their
meaning.

`scripts/check_target.py` checks that `FrozenTarget` is upstream's frozen statement token
for token. Removing another hypothesis means formalizing its source theorem or finding a
cheaper route to it; MW and CAT were within reach of current Mathlib.

## The polynomial is constructed in Lean

`FrozenTarget` asserts that a suitable polynomial *exists*. The development therefore
defines the polynomial by construction in Lean, mirroring upstream's generators: each
template and recipe is a Lean term, and the natural precision polynomial is the output of a
Lean compiler applied to a Lean description of the precision program. Witness-block
disjointness and the variable count are proved by construction, and the degree and
coefficient bounds compositionally. The saved files `construction/ordinary-integer-definition.json`
and `construction/precision-natural-polynomial.json` are cross-checks for an external
script, not inputs to the proof. The finite computations left in the proof are mathematical
certificates (the generator descent and height search, point counts, explicit comparisons).

## Milestones

1. **Reduction to finite computations.** Prove the main theorem from the hypotheses
   and a conjunction of finite, decidable statements. Everything else (the elliptic
   model and generator descent, multiplication, the compiler, the variable-shift bridge,
   the literal specification and the size bounds) is proved in Lean. The finite
   statements are first checked by `native_decide` or by external scripts, in a separate
   library outside the audited root package.
2. **Kernel certificates.** Replace each trusted computation by a certificate checked in
   the kernel, in the style of `AxiomMath/CFSG`: an external tool emits witness data,
   pinned data files become `Nat` literals, Boolean checkers built from the kernel's
   GMP-accelerated `Nat` operations are proved by `Eq.refl true`, and soundness lemmas
   connect each checker to the mathematical statement. The final build uses no
   `native_decide`.
3. **Classical inputs.** Formalize any classical input that milestone 1 states as a
   hypothesis. The Mordell–Weil theorem for `E/K₀` is done, and so is CAT, through an
   effective Dirichlet theorem ([docs/effective-dirichlet-plan.md](docs/effective-dirichlet-plan.md)).

Status (2026-11-07):

- Milestones 1 and 2 are done. `ZInQ.exists_bounded_integer_polynomial_defining_integers_of`
  (`ZInQKernel/Main.lean`) proves `FrozenTarget` from three hypotheses (H_min, CR₃, 22P; CAT is the
  theorem `ZInQ.catalogueBound8`, and PC, for the Route K pole polynomial, the theorem
  `ZInQ.poleCompleteness_of_certifiedRank`) with no `sorry` and
  no `native_decide`; `#print axioms` lists only `propext`, `Classical.choice` and
  `Quot.sound`.
- The last finite computation was the node statistics of the universal halting circuit. The
  proof needs only upper bounds on its addition and multiplication nodes
  (`ZInQ.Compiler.NodeCheck.haltingAddMulBound`), and these are proved by an upper-bound
  judgment over the construction monad that counts requested nodes and subtracts requests
  whose node is already present (`ZInQKernel/Compiler/NodeBound/`); the program-dependent part
  is four small `decide +kernel` computations (about 25 s).
- The exact node counts, which no theorem uses, are kernel proofs too
  (`ZInQ.Compiler.NodeCheck.haltingAddMulCheck`, `ZInQKernel/Compiler/NodeSkeleton/`): the
  run of the construction is split into 89 `decide +kernel` checks of a builder without a
  hash-consing table, guided by pinned oracle data, and a simulation proof relates it to the
  fast builder (about 10 min in all). No library in the repository uses `native_decide`.

## Finite computations

Every finite computation the proof needs (audit of 2026-11-06, updated as the formalization
landed). All of them are checked by the kernel; the audited library `ZInQKernel` uses no
`native_decide`.

| Status | Computations |
| --- | --- |
| Checked by the kernel | the small-height search (`ZInQ.Search.searchCheck_eq_true`: `Nat.rec` loops over Boolean tests built from the kernel's GMP `Nat` operations, closed by `decide +kernel` in about 60 s); the 324-primorial literal (a Boolean trial-division checker with a soundness lemma); the point counts modulo 17 and 23; the node statistics of the power template (about 35 s) and its translation statistics (about 1 min); the template parameter and witness tables; the shape of the 1,399-instruction universal interpreter and its equality with the compiled structured interpreter (a few seconds each); the size and validity of the wrapper program; the witness-count arithmetic; the closed comparisons and small constant bounds of the size chapter; the integer inequalities behind the height constants; the clearing arithmetic; the congruences of P₀ modulo 7; the height comparisons and the small residue and sign tables |
| Node statistics of the halting circuit | the bounds the proof uses (at most 125,307 additions and 98,361 multiplications among the 293,568 hash-consed nodes of the universal halting circuit) are kernel proofs, by the presence-only upper-bound judgment of `ZInQKernel/Compiler/NodeBound/`; the variable count, the constants and the call count are proved symbolically. The exact counts, used by no theorem, are kernel proofs as well (`ZInQKernel/Compiler/NodeSkeleton/`, 89 chunked `decide +kernel` checks) |
| Replaced by symbolic proofs | the other counts of the halting and precision circuits (from the counting lemmas of the packed compiler and the construction), the scope of the precision circuit, every statement about the astronomically large constants, the guard product over the false triples |
| Not computable, proved instead | the catalogue bound CAT, a closed statement about φ(4·324#) ≈ 7.5·10¹²⁹ residue classes; with the cutoff raised to 2^(W⁸) it follows from an effective Dirichlet theorem (`ZInQKernel/Progressions/`) |

The saved JSON constructions are compared with the Lean construction only by external
scripts; they are not inputs to the proof.

## Layout

| Path | Contents |
| --- | --- |
| `lean/` | Upstream's accepted helper snapshot, unchanged, required as the Lake package `z_in_q` |
| `ZInQKernel/` | This fork's Lean development (library `ZInQKernel`, namespace `ZInQ`) |
| `ZInQKernel/Hypotheses/` | The explicit hypotheses, and the statement of MW (now proved) |
| `blueprint/` | The Autoform blueprint: the informal dependency graph and its Lean status |
| `scripts/check_target.py` | Identity check between `FrozenTarget` and the frozen upstream statement |
| `scripts/print_axioms.lean` | `#print axioms` for the main theorems, their variants and the theorems that replace former hypotheses |

## Build

```sh
lake exe cache get
lake build
python3 scripts/check_target.py
lake env lean scripts/print_axioms.lean
```

The `autoform verify` workflow builds the project, validates the blueprint and audits
every root-package declaration for axioms beyond `propext`, `Quot.sound` and
`Classical.choice`.
