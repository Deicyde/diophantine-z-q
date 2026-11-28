# Upstream Version 22 against the open hypotheses of the single proof

What the 175-variable theorem of upstream's Version 22 uses, set against the 33 open hypotheses of `ZInQ.OneProof.frozenTarget`.

**Fork.** `Deicyde/diophantine-z-q` at `d415070d4` (2026-11-28): 30 hypotheses on the height side, plus `hRC`, `hCT`, `hRank` (`docs/one-proof/OPEN.md`).

**Upstream.** Release `quartic-175-version-22` (2026-11-28). `manuscripts/quartic_v22.tex`, 57,375 lines, SHA-256 `15576881d6ff053e…`. Line numbers below are in this file.

**Outside paper.** M. Bhargava and A. Burungale, *A Diophantine definition of Z in Q*, arXiv:2611.16130v2 (19 November 2026), called BB below. It is unrefereed.

This note records what is used where. It does not propose a change of route: the fork's reference text stays the 5 November manuscript (#95).

A note on names: `openai-pointwise-catalogue.md` cites page numbers of a PDF dated 20 November that was also called Version 22. That PDF had 918 pages and was not on the upstream repository; the published Version 22 has 856 (`research/version22/BUILD.json`), so those page numbers do not apply to it.

## Summary

- The 175-variable theorem (`v22:175-fixed`, line 1888) is a different construction from Theorem 1.1 of the 5 November manuscript. It uses neither `PoleCompleteness` nor `SixContactMin`.
- `hRC`, `hCT` and `hRank` are not used. One outside statement takes their place: the rational-point conclusion of BB Theorem 2.3.
- Of the 30 height-side rows, 8 are the same printed result in Version 22's height chain, 9 are the same work but a different result, and 13 are not used.
- Version 22 needs two large results of its own that the fork has no statement for: a discriminant-210 height theorem with explicit constants, and a theorem on simultaneous primes of the form u + c·w².
- One retained input is already proved in the fork's Lean: the generator certificate for the curve over Q(√2).
- `FrozenTarget` asks for a polynomial in 292,890,231,905 variables of degree below 2↑↑7 with coefficients below 2↑↑8. A 175-variable quartic with coefficients below 2^802 meets those bounds after padding with unused variables. This is an inference of this note and is not checked in Lean.

## 1. The interface statements

| Fork (5 November manuscript) | Version 22, 175-variable theorem | BB's own proof |
|---|---|---|
| **`PoleCompleteness`** (Theorem 5.2). Pole polynomial on y² = x(x−e)(x+3e). Proved in Lean from `hRC`, `hCT`, `hRank`. | Not used. Replaced by Lemma `v22:native-pole` (lines 181–241): the equations e²+dp²=1, UV=e(1−d), U²−V²=dq². Soundness is an elementary valuation argument. Completeness uses the point conclusion of BB Theorem 2.3. | Lemma 2.2, from Theorem 2.3. |
| **`SixContactMin`** (an instance of Theorem 4.1). Discriminant-six Shimura curve, contacts {0, −15, −20, −24, −30, −60}, exponent 24. Proved in Lean from the 30 height-side rows. | Not used. Soundness consumes equation `v21:height-input` (line 2672): quaternion discriminant 210, five contact forms (s, r, r−s, r−2401s, 32r+343s), bound c₀C₀R²E(R)log R with explicit constants. Line 19377 says the discriminant-six constructions must not be substituted for it. | Proposition 3.1: discriminant six, sextic (X²−1)(X²−9)(X²−25), exponent 24, constant not computed. Its six contact points are not projectively equivalent to the fork's (checked by computing all cross-ratio normal forms), so it is not `SixContactMin` in other coordinates. |
| **Prime supply.** `greenTaoDense` and `goodPrimeDensity`, both proved in Lean (`ZInQKernel/MainGreenTao.lean`). | Not enough. Completeness uses `thm:v5-simultaneous-primes` (line 39943): primes u + c_j·w² with congruence conditions on Gaussian generators. | Green–Tao 2008, Theorem 1.2. The docstring of `GreenTaoDense` describes the same theorem; the two statements were not compared word for word. |
| **Elliptic model.** `generator_certificate` (`ZInQKernel/Model/Generator/Certificate.lean`), proved in Lean: P₀ has infinite order and 2E(K₀) = Z·P₀ for d = 75 − 53√2. | Same statement, retained as `prop:generator` (line 22556) and transported to d₀ = 3 − √2 (lines 145–148). | Different curve, over Q(√13). |

## 2. The three hypotheses outside the height side

| Hypothesis | In the 175-variable theorem | Note |
|---|---|---|
| `hRC` (Theorem 5.3, restricted converse) | Not used | No reference to `hyp:RC`, `hyp:PC` or `sec:rc` in lines 90–1960. The retained-input list (lines 113–141) omits the older pole route. The restricted converse stays in the retained body, where it still carries the older constructions, including the 292,890,231,905-variable theorem. |
| `hCT` (Cassels–Tate, via Poonen–Stoll) | Not used | Cited only in the older pole section (line 24054). |
| `hRank` (Silverman C.16.5.5, via Miller) | Not used | Version 22 says it uses only the point conclusion of BB Theorem 2.3, not its analytic-rank or Tate–Shafarevich assertions (lines 216–218). |

What replaces them is one theorem of an unrefereed preprint. BB prove Theorem 2.3 from:

- a consequence of the Tian–Yuan–Zhang genus-point criterion, their display (2.4), taken from the proof of TYZ Theorem 3.5(2) and stated in that form by Smith (arXiv:1603.08479, Table 2, row 5(b));
- a 2-descent (Heath-Brown 1994 with Monsky's appendix) and Rédei's formula for the genus sum;
- Gross–Zagier and Kolyvagin, for the rank-equality and Tate–Shafarevich assertions only, which Version 22 does not use.

The kernel still has the Route K statement `TYZRow5b` (`ZInQKernel/Hypotheses/CR3Literature.lean`), proved in Lean from `TYZInputs` by `ZInQKernel/RouteK/PropN.lean`. Both it and BB's (2.4) are described as Smith's row 5(b). BB's conclusion is stronger (positive rank and L′ ≠ 0, against analytic order at most one). The two genus sums were not compared term by term.

## 3. The 30 height-side rows

"Chain" means Version 22's discriminant-210 height chain: sections `q214:geometry-carry` to `q214:primary-source-bridges` (lines 19368–20381), the retained proof at 20753–21195, and the older discriminant-210 proof they point to (29982–31128).

| Row | In Version 22's chain | Detail |
|---|---|---|
| `dsThm966Printed` | Same result | Deligne–Serre Theorem 4.1 (line 19615). |
| `gaudronRemondSec9LowerGR1Weak` | Same result | Comment. Math. Helv. 2014, Cor. 8.4 (lines 20277, 20369). |
| `milneCanonicalModelPrint` | Same result, overlapping locator | Milne 2005, pp. 354–355 (line 30279). |
| `milneShimuraFamilyPrint` | Same result | Milne 2005, Theorem 14.8 (line 30264). |
| `milneTorsionCount` | Same result | Milne 1986, Theorem 8.2 and Remark 8.4 (line 30093). |
| `modularHTCoeff` | Same result, Kato part only | Kato 2004 §9.2, §9.4 (lines 19605–19617). |
| `silverbergZarhinThm34` | Same result | Theorem 3.4 (lines 19525, 19665); Theorem 3.5 is also applied. |
| `panThm104F` | Same result, indirectly | Named as the proof source; the statement invoked is Calegari's ICM 2022 chapter, p. 624 (line 19609). |
| `buzzardLemma22Full5` | Same work, different result | Buzzard §1 only (lines 30070, 30248); Lemma 2.2 not used. |
| `buzzardXDV15Lit` | Same work, different result | As above; Theorem 2.1 and Cor. 2.3 not used. |
| `javanpeykarThm111An` | Same work, different result | Theorem 1.1.1 is replaced. §2.3, Lemma 2.3.1 and §4.1 are used (lines 19764, 19883, 19991). |
| `milneProp207At3` | Same work, different result | Milne 1986 is used for other results; Prop. 20.7 never. |
| `milneProp207At5` | Same work, different result | As above. |
| `milneThm125Pts` | Same work, different result | Only Remark 8.4 overlaps. |
| `milneZeroPreservingHomLN` | Same work, different result | Cor. 20.2(a) not used. |
| `milneThm71Projective` | Same work, different result | Projectivity comes from Stacks Project tags (line 30160). |
| `voightQMComplexModuliPrint` | Same work, different result | Voight 13.3.4, 13.3.11, Cor. 7.1.5 (lines 30106, 30389); §43.6 not used. |
| `afCharpolyDS965` | Not used | Shimura 1973 Theorem 1 with Li's Fricke formula instead (line 19707). |
| `bergerSurveyF` | Not used | |
| `boutotCarayolPolarizationPrint` | Not used | "Boutot" does not occur in the file. |
| `boutotCarayolRepresentabilityPrint` | Not used | Representability from Yuan 2024 §2.1 and Stacks tags. |
| `carayolThmAFrob` | Not used | A different Carayol paper (Astérisque 147–148, 1987) is used (line 19649). |
| `egaIV1757SmoothNormal` | Not used | |
| `egaIV_9_7_7_OL` | Not used | |
| `fowlerProp27PrintCanonical` | Not used | |
| `gaudronRemondThm14GR1` | Not used | The 2023 memoir's Theorem 1.9(1) is used instead. |
| `pazukiCor13Upper` | Not used | The metric comparison is done through Yuan 2024 (line 30459). |
| `raynaudLNM119Normal` | Not used | |
| `colmez1992DeRhamAbVarModel` | Not used | De Rham property from Scholze 2013 (line 19605). |
| `fontaine1982HTAbVar` | Not used | As above. |

BB's own height proof (their Section 3) overlaps the fork's rows in two places. It cites Buzzard §1, Theorem 2.1, Lemma 2.2 and Cor. 2.3, which is what the two Buzzard rows record, and it uses Pazuki 2012 (Definition 2.6 and §2.3, not Cor. 1.3). Its Faltings-height bound comes from von Känel–Kret, arXiv:2307.06944, equation (7.1), in place of the modularity, Javanpeykar and Gaudron–Rémond rows.

## 4. What Version 22 needs that the fork has no statement for

**Completeness**

- BB Theorem 2.3, point conclusion (unrefereed; Version 22's release page says so).
- `thm:v5-simultaneous-primes`. Its proof is in the manuscript (lines 39922–43079). It rests on Green–Tao, *Linear equations in primes* (2010), the two Green–Tao 2012 nilsequence papers, Tao–Ziegler (2018), Bienvenu (2017), Mitsui (1956), Browning–Loughran, Browning–Heath-Brown, Williams and Kopp–Lagarias, and on an inverse theorem for the Gowers norms proved inside the manuscript (lines 46554–47507). That part cites Candela–Szegedy (2022) and replaces a step of Green–Tao–Ziegler's Appendix C with its own construction (lines 47490–47499).
- Real-return lemmas (`v15:dependencies`, compact neighbourhoods): no outside citations.

**Soundness**

- The discriminant-210 height theorem. Beyond the eight shared rows it uses González–Rotger (2006), Yuan (2024), Gaudron–Rémond's 2023 memoir (Theorem 1.9(1), Lemma 16.2(1)), Carayol (1987), Scholze (2013), Calegari's ICM 2022 chapter, Shimura (1973), Li (1975), Faltings (1986), Deligne (1979), von Känel (2021), Fröhlich and Serre on local fields, and many Stacks Project tags.
- Three inputs to that theorem are the project's own: the modular-Jacobian height bound "(H0.3)" (line 20134), which replaces Javanpeykar's Theorem 1.1.1; the conductor and small-prime support arguments the text calls private#8 and private#9; and the discriminant-210 moduli construction.
- Formal-group comparison, weighted height sums and a Lucas-sequence lemma, all proved in the text with no outside theorem.

**Finite checks**

- The 147 rows, their expansion (3,196 monomials, coefficients below 2^802) and the "331 anchor" residues. The text calls the row check a finite author verification by script (lines 869–875). No proof-assistant check is claimed.

## 5. What the fork already has

- `generator_certificate`, the same statement Version 22 retains.
- `greenTaoDense`, which is the Green–Tao input of BB's own proof, though not of Version 22's.
- The Route K files (`ZInQKernel/RouteK/`, `ZInQKernel/Hypotheses/TYZInputs.lean`), whose `TYZRow5b` matches BB's (2.4) as described in section 2. What else those files prove was not traced.

## How this was made, and its limits

- Three AI readers each traced one chain of the TeX (height, completeness, elliptic model) and reported with line numbers. Their main claims were checked against the text by search and by reading the cited lines. No person has checked the result.
- "Same result" means the text names the same theorem number. The Lean statement of a row was not compared with what Version 22 needs from that theorem.
- Whether the 175-variable theorem's proof is correct was not examined. Upstream's release page says its acceptance was by AI review with an owner override and is not independent human review.
- BB's paper was read for what it cites, not checked. None of the other cited literature was opened.
- No Lean was built.


_Written by Claude Code at the repository owner's request. This is an AI reading of the two texts; nothing here has been confirmed by a person._
