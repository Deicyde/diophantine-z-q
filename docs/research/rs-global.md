# The architecture of the construction: which roles force which deep inputs

Every claim carries one of three marks.

- **VERIFIED**: checked against the cited text (the 11/5 manuscript, the 10/11 manuscript, the
  Lean sources or the audit files) or by a computation whose script is in `scratch/rs-global/`.
- **STANDARD**: a published theorem, with a reference.
- **SPECULATIVE**: an idea or an expectation that is not proved.

Conventions.

- Line numbers refer to `diophantine_zq.tex`, the 11/5 manuscript (SHA-256 `cb1148cd…`, the
  version against which the theorem-application audit was taken).
- "10/11, p. n" is page n of the 25-page PDF in `October 11 Manuscript/`.
- A001–A082 are the records of `docs/theorem-application-audit/applications.json`.
- Lean declarations are in the namespace `ZInQ`.
- The per-hypothesis analyses are the companion notes `rs-height`, `rs-pole` and `rs-pattern`
  (`docs/research/rs-height.md`, `rs-pole.md`, `rs-pattern.md`). This note builds on them,
  rechecks the facts it uses, and adds the comparison across hypotheses and across the three
  constructions.

Notation.

- `K₀ = ℚ(s)`, `s² = 2`; `E : y² = x³ − d²x` with `d = 75 − 53s`; `P₀` the generator of
  `2E(K₀)` (line 261); `ι(n)` the code of `[n]P₀`.
- `𝒞 = {0, −15, −20, −24, −30, −60}` and `F(u) = ∏_{c∈𝒞}(u − c)`.
- `M_S(u)` is the product of the primes `p ∉ S` at which some `v_p(u − c)` is positive and odd.
- `Φ(B)` is the rational solubility of the pole polynomial (line 983).
- The hypotheses are H (`SixContactEstimate`), PC (`PoleCompleteness`), 22P (`FixedPrimePattern`)
  and CAT / CAT₈ (`CatalogueBound`, `CatalogueBound8`). RC is the restricted converse
  (Theorem 5.3, line 1005).

## 1. The statement and every use

### 1.1 Three constructions and their inputs

**The OpenAI preprint.** The 11/5 manuscript cites it at line 53 (bibliography entry at line 11228,
dated October 6, 2026). The 10/11 manuscript cites a September 24 version checked on October 11
(10/11, p. 25, ref. [1]). The preprint is not in the repository, so everything said here about it
comes from the 10/11 manuscript (VERIFIED against the 10/11 text only). The 10/11 manuscript
imports four of its results (10/11, pp. 2–4):

- **pole parity** (`par:pole-parity`, its §3): a positive existential formula `Φ` with `Φ(t)` true
  for every `t ∈ ℤ`, and no odd negative valuation outside a finite set `S_Φ` (10/11 (2.1), (2.2));
- **rank one** (`ell:rank`, §5): `mE(F) = ℤP` for the same curve over `F = ℚ(√2)` (10/11 (2.3));
- **a five-point height estimate** (`hei:height`, §4): five rational contact points including `∞`,
  and `h(s) ≤ H·M_S(s)^c` (10/11 (2.6));
- **compatible prime patterns** (`pri:pattern`, §6): every integer `A` has `Av = u₁ + u₂ + u₃` with
  `v` and the twelve finite contact values `L_b(u_i, v)` all of the form `±κr`, where `κ` lies in a
  fixed finite set and `r` is a large split prime with `gcd(d₁, d₂) | 4` (10/11 (2.10)–(2.12)).

From these the preprint obtains a Turing reduction of `H10(ℤ)` to `H10(ℚ)`. It explicitly does not
claim a many-one reduction (10/11, p. 2, citing [1, §7]). Its arguments used an "all-ring
pole-parity closure", "quotient-field localization" and a search for a failed rational test (10/11,
Remark 8.2, p. 12).

**The 10/11 manuscript.** Its Theorem 1.1 (p. 1) is conditional on exactly these four inputs. The
classical results it adds are:

- the Davis–Putnam–Robinson–Matiyasevich theorem, for computably enumerable relations on labels
  (Corollary 9.3);
- Koenigsmann's existential definition of `ℤ_(3)` by quaternion trace sums (§13.1; Koenigsmann,
  Ann. of Math. 183 (2016), Observation 5, Proposition 6, Remark 8);
- formal groups (Silverman IV).

The new mathematics consists of:

- finite guarded localization certificates (§4), which give a many-one reduction (Theorem 1.2);
- the Diophantine model of `ℤ` on labels (Corollary 9.2);
- the scalar bridge `Eval` (Theorem 10.1), built from a support relation `Supp` (§12) and a 3-adic
  congruence `Cong₃` of variable precision (§13).

The final contradiction is `K(n) log 3 ≤ h(x − n) < K(n)` (§14). The manuscript gives no numerical
bounds.

**The 11/5 manuscript.** Theorem 1.1 (line 60) comes with explicit size bounds. The assembly lemma
(line 110) derives it from six statements, G, M, H, PC, C and B (lines 87–100). The deep inputs
are:

- H, Theorem 4.1 (line 404);
- PC, Theorem 5.2 (line 1001), derived from RC, Theorem 5.3 (line 1005);
- 22P, Proposition 6.2 (line 1267), used only for M;
- CAT, Proposition 12.1 (line 6285), used only for B.

**Lean.** `exists_bounded_integer_polynomial_defining_integers_of` (`ZInQKernel/Main.lean`) proves
`FrozenTarget` from `SixContactEstimate`, `PoleCompleteness`, `FixedPrimePattern` and
`CatalogueBound8`.

- Statement G is proved: Mordell–Weil is the theorem `mordellWeilE`, and the generator certificate
  is checked in the kernel (KERNEL_PLAN.md).
- C, B, the assembly and both directions of M are proved, modulo the hypotheses.
- CAT₈ is being replaced by an effective Dirichlet theorem (`docs/effective-dirichlet-plan.md`;
  `ZInQKernel/Progressions/`).

After that replacement the trust boundary is {H, PC, 22P}.

The inputs correspond as follows (VERIFIED by reading both manuscripts and the Lean statements).

| Input | Preprint (via 10/11) | 10/11 | 11/5 | Lean |
| --- | --- | --- | --- | --- |
| rank-one label group | `ell:rank` | Input E | G (Prop. 3.1, line 268) | proved |
| denominator control, soundness | `par:pole-parity`, (2.2) | Input P, (2.2) | Lemma 5.1 (line 988), elementary | proved (`Assembly.poleSoluble_no_negative_odd`) |
| denominator control, completeness | `par:pole-parity`, (2.1): `Φ(t)` for **all** `t ∈ ℤ` | Input P, (2.1) | PC: only `B` with square denominator, `0 < B < 1/2`, `v_p(B) ≥ 4` on `S₀` | hypothesis |
| height | `hei:height`, five points with `∞` | Input H | H, six finite contacts, explicit constants | hypothesis |
| prime patterns | `pri:pattern`, 13 forms | Input R | 22P, 22 forms | hypothesis |
| catalogue size | — | — | CAT | hypothesis, effective Dirichlet in progress |
| approximation | — | 3-adic (Koenigsmann's `ℤ_(3)`) | real, elementary | proved |
| c.e. relations on labels | — | DPRM | explicit compiler | proved |

Two of the 10/11 inputs have become cheaper in 11/5:

- rank one is now a theorem, and a Lean theorem;
- the completeness of the pole predicate is required only on a narrow, locally prepared set of
  inputs, not on all integers.

The other two, the height estimate and the prime patterns, kept their nature: a uniform height
bound and a Green–Tao–Ziegler pattern.

### 1.2 Two layers and their roles

Both manuscripts build the definition in two layers (VERIFIED: 10/11, Appendix B, p. 24; 11/5,
lines 6591–6605).

**Layer A: arithmetic on labels.**

- (A1) The label group `ℤP₀` with membership and addition, which are algebraic (lines 350–375).
- (A2) Multiplication: a certificate whose soundness yields a finite box of possible false
  triples, excluded by a finite guard (lines 1225–1259). Its completeness requires witnesses for
  every true triple (lines 1705–1758).
- (A3) Computably enumerable relations on labels. In 11/5 these are the natural predicate (four
  squares, line 369) and the compiled precision program (Section 10, line 5745). In 10/11 they come
  from DPRM (Corollary 9.3).

**Layer B: identification of the rational scalar with its label.**

- (B1) Support: local tests tie the odd contact primes of `t` to the label. In 11/5 this is
  Lemma 11.1, `M_{S_ht}(t) | κF(n)` (line 6151); in 10/11, Proposition 12.2.
- (B2) Size: a height bound from the support.
- (B3) Approximation to a precision computed in Layer A: `|t − n| < e^{−B(n,κ)}` (line 6112), or
  `v₃(x − n) ≥ K(n)` in 10/11.
- (B4) Completeness of B1 for `t = n`: one suitable shift `κ`, found by the compact-local-group
  argument (Lemma 11.2, line 6202; 10/11, Proposition 12.3).

The deep inputs enter the roles as follows (VERIFIED: Lean consumers found by `grep`, listed in
§1.3).

| Role | Direction | Deep input | Lean consumer |
| --- | --- | --- | --- |
| A2, finite box | soundness | H at `S_mul`; shape polynomial in `M` | `Mult.sixContact_at_Smul` → `Mult.slope_height_le_of` → `Mult.finite_box` → `Mult.multiply_sound` |
| A2, slopes exist | completeness | 22P | `Mult.pattern_slopes` ← `slopes_of_int` ← `completeness_core` ← `Mult.multiply_complete` |
| A2, pole witnesses of slopes | completeness | PC | `Mult.slope_complete` |
| A2, local congruences | soundness | none (Lemma 5.1, formal groups) | `Soundness/LocalCongruence.lean` |
| B1, test divisibility | soundness | none (Lemma 5.1, formal groups) | `Assembly.test_dvd` |
| B2, height of `t` | soundness | H at `S_ht`; any effective shape | `Compiler.Precision.sixContact_at_heightPrimes` → `Assembly.ratHeight_le_bound_of_test` → `Assembly.eq_of_close_of_test` |
| B3, precision | both | none beyond Layer A | `Assembly.close_sound`, `Assembly.close_complete` (both take `MultiplicationExact`) |
| B4, test completeness | completeness | PC | `Assembly.test_complete` |
| size bounds | — | CAT₈ | `Size/Constants/*`, `Syntax/Constants/{Catalogue,Relations}.lean` |

So soundness uses only H (beyond elementary local algebra), completeness uses PC in both layers
and 22P in Layer A, and CAT enters only through the numerical bounds.

### 1.3 Every use in Lean

`grep` of the four hypothesis names in `ZInQKernel/`, outside `Hypotheses/` (VERIFIED):

- **`SixContactEstimate`** is applied at exactly two leaves:
  - `Compiler.Precision.sixContact_at_heightPrimes` (`Compiler/Precision/HeightConstant.lean:170`),
    with `S = S_ht`, `R = D`;
  - `Mult.sixContact_at_Smul` (`Multiplication/Certificate/ConstantsProperties.lean:133`), with
    `S = S_mul`, `R = Syntax.R`.

  Every other occurrence threads it through (`Main.lean`, `Assembly/Top/*`,
  `Multiplication/Top/Exact.lean`, `FiniteBox.lean`, `ContactSupport.lean`, `MultiplySound.lean`).
- **`PoleCompleteness`** is applied at exactly two leaves:
  - `Mult.slope_complete` (`Multiplication/Completeness/SlopeCompleteness.lean:75`);
  - `Assembly.test_complete` (`Assembly/Local/TestCompleteness.lean:35`).
- **`FixedPrimePattern`** is destructured at one place only, `Mult.pattern_slopes`
  (`Multiplication/Completeness/PatternSlopes.lean:262`). Its caller `slopes_of_int`
  (`Completeness/Core.lean:16`) uses it with `B₀ = 0`.
- **`CatalogueBound8`** is used only in the size chain:
  - `Size/Constants/{Catalogue,Cutoff,FormalMultiple,T}.lean`;
  - `Size/Majorants/{Bound,Cutoff}.lean`;
  - `Syntax/Constants/{Catalogue,Relations}.lean`;
  - and in `Assembly.Pstar_spec_of` for the bounds.

**Layer B consumes Layer A in both directions** (VERIFIED). `Assembly.value_relation_iff_of`
(`Assembly/Top/ValueRelation.lean`) takes `hM : SpecMultiplicationExact`. `close_sound` and
`close_complete` each take `MultiplicationExact`. The template table (lines 6739–6772) lists
`value.test` with 35,282 = 35,134 + 148 witnesses: the test makes one `multiply` call, which forms
the code of `κn` (line 6131). Hence 22P is needed for the value relation, although
`ValueRelation.lean` never opens it. It enters through `Mult.multiplication_exact hH hPC h22`.

### 1.4 Uses in the manuscript

- **H**: lines 1225–1245 (finite box, Layer A) and 6243–6252 (height of `t`, Layer B). The proof
  of Theorem 1.1 invokes it "for each of the two sets of constants" (lines 125–126); the sets are
  distinguished at lines 966–970.
- **PC**: line 1751 (completeness of multiplication) and line 6233 (Lemma 11.2). Both sound
  directions use only Lemma 5.1 (lines 1196 and 6167); line 1259 records that multiplication
  soundness does not use PC.
- **22P**: applied once, at lines 1705–1758.
- **CAT**: Proposition 12.1, lines 6285–6360.
- **Layer A inside Layer B**: the product `κn` (line 6131), the natural predicate (line 369) and
  the compiled precision relation (lines 5745–5790, used by `Close` at lines 6102–6128).
