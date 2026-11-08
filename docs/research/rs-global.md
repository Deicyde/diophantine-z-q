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

## 2. The weakest form the proof needs

### 2.1 The weakest interface, hypothesis by hypothesis

The companion notes determine, for each hypothesis, exactly what its consumers extract. I rechecked
the facts used below against the Lean consumers listed in §1.3 (VERIFIED unless marked).

| Hypothesis | What the consumers use | Weakest sufficient form | Quantitative slack |
| --- | --- | --- | --- |
| H | two instances; from the witness `t` only `t ∉ 𝒞` and a divisibility `M_S(t) ∣ m` | **H_min**: `h(u) ≤ A₀·M_{S_mul}(u)^24` for all `u ∉ 𝒞` (one inequality; [rs-height §2.1]) | Layer B: any effective monotone bound the precision program can evaluate. Layer A: `A·M^e` with `e` below the test valuation `k = 25`, and `log₂log₂log₂ T < 65 535` for `T = (48A)^{k/(2(k−e))+1}`; today `T < 2^(2^(2^9013))` (`Size.T_lt`), against `deg < 2↑↑7 = 2^(2^(2^65536))` |
| PC | two instances; input `B = R₀·s(q)²` with `R₀` fixed by the slope or by `n`, and `q` free in an open set | **PC⁻**: one good `q` per instance; and **RC∃**: for each admissible `(β, θ)` some `n` with `E_n`, `E_{nθ}` of positive rank; only the abscissa class `β` matters [rs-pole §2] | thresholds: `v₂(B/m) ≥ 3`, `v_p(B/m) ≥ 1` on `S₀` and `B < 1` would do; rank `≥ 1` suffices once `Sel₂` is minimal |
| 22P | one instance (`B₀ = 0`): three good slopes summing to each `A` | **(SR)**, or the pattern form **22P₂**: a homothetic copy of a 12-point set in the good primes, common difference `8P_s w` [rs-pattern §2.5] | 18 of the 22 forms; no catalogue, no `B₀`, no `p ∤ d₁d₂`; `gcd(d₁,d₂) ∣ c_*` suffices; **no** slack in "at most six good primes per slope" |
| CAT | literal constants of the size chain | **CAT₈** (cutoff `2^(W^8)`), or nothing if the catalogue is removed [rs-pattern R2] | any cutoff `2^(2^K)` with `K ≤ 7485` |

### 2.2 Which roles force which inputs

**F1. Soundness uses H only; completeness uses PC and 22P** (VERIFIED, from the table of §1.2).
The soundness of both layers rests on elementary local algebra (Lemma 5.1, the formal-group
congruences, the finite guard) together with H. Completeness rests on PC in both layers and on 22P
in Layer A only. CAT is used by neither direction; it enters only the numerical bounds.

**F2. Layer B needs label multiplication** (VERIFIED). There are two separate reasons.

1. The precision must beat the height bound: `−log ε > B(n, κ) = A₀|κF(n)|^24` (lines 6102–6118).
   That is the exponential of a polynomial in two labels. Only the compiled program, an
   instance of A3, can certify it.
2. The test uses the code of `κn` (line 6131).

Hence Layer B inherits every input of Layer A, and 22P is a hypothesis of the value relation
(§1.3). The 10/11 bridge has the same dependence. Its `Supp` relation calls `Mul_G(T, J, R)`, and
`Cut` and `b = 16·3^k` are c.e. relations on labels (10/11, §§12–14).

**F3. The variable shift keeps prime patterns out of Layer B** (VERIFIED as an argument, from
lines 6151–6234). Consider a test with a *fixed* shift `c`, with `V₀ = H − [c]P₀` and
`V₁ = U − [c]ι(n)`; it would need only addition.

- Its honest witnesses at a prime `p | F(n)` would need `h ≡ 0` modulo the order `e₁` of `P₀` at
  one place above `p`, and `h ≡ c` modulo the order `e₂` at the other place. That requires
  `gcd(e₁, e₂) | c`, the same compatibility as in multiplication (lines 1706–1716).
- This would be needed at every odd contact prime of `F(n)`. For general `n` some prime of `F(n)`
  fails it, so completeness would fail.

Lemma 11.2 avoids the problem by taking the shift `κ` to be a common multiple of the local indices
at all primes of `F(n)` (lines 6207–6214). The price is the product `κn`.

Layer B thus trades a prime pattern for every integer `n`, which no theorem supplies, for label
multiplication. The completeness of label multiplication needs prime patterns only for slopes
that the honest prover chooses.

**F4. In Layer A the shift must be fixed, which forces 22P** (VERIFIED as an argument; it agrees
with [rs-pattern R8]).

- At an odd contact prime `p ∤ c_*`, soundness obtains `n_i ≡ A_i (mod p^25)` from
  `c_*(n_i − A_i) ≡ 0` (lines 1206–1212).
- A shift `κ` supplied as a witness gives only `κ(n_i − A_i) ≡ 0`, which is empty when `κ ≡ 0`
  (mod `p`).
- Forcing `p ∤ κ` locally needs the valuation of `z([κ]J)` for a point `J` that is formal at `p`.
  That is a product of two labels, the very relation being defined.
- Making a witness shift harmless through a `κ`-dependent bound, as in Layer B, would need an order
  relation on labels. Order needs squares, i.e. multiplication.

So the shift is fixed, and then each odd contact prime of each slope must be good individually
(split, two good reductions, `gcd(e₁, e₂) | c_*`). With six test groups per slope (§2.4), a slope
has at most six such primes. Its six contact values are therefore essentially primes, which is a
linear prime pattern.

**F5. The two uses of H need different shapes** (VERIFIED; [rs-height §§2.2–2.3]). The finite
box needs a bound polynomial in `M`, with exponent below the test valuation. The precision step
accepts any effective function. The freedom in Layer B does not help Layer A.

**F6. Effectivity comes from the size bounds, not from definability** (VERIFIED as a reading of
Proposition 6.1, lines 1225–1245, and of `Close`, lines 6102–6128).

- In `FrozenTarget` the constants must be explicit: `A_ht` fixes `T` and hence the literal guard,
  and `A₀` is computed by the precision program.
- For the bound-free statement "ℤ is Diophantine in ℚ" an ineffective constant would do in both
  uses. Proposition 6.1 needs some constant in order to produce some finite box, and the program
  can carry any fixed literal.

So effectivity of H is forced by the bounds of Theorem 1.1. Uniformity in the twist and the
polynomial shape are forced by definability itself. No ineffective bound that is uniform in the
twist and polynomial in `M` is known either (SPECULATIVE assessment: Faltings' finiteness holds
twist by twist, and gives no height bound).

**F7. CAT is forced only by literal constants** (VERIFIED, §1.3). It has a textbook replacement
(the effective Dirichlet plan), and the catalogue itself can be dropped from the construction
[rs-pattern R2].

### 2.3 Structural constraints on any variant of this architecture

These constraints explain why the three deep inputs are of the kinds they are. Each follows from
the definitions by an elementary argument, stated here once.

**C1. Full valuation control is the theorem itself** (VERIFIED as an argument; compare
[rs-height R2]). Suppose some Diophantine set `Ψ` satisfies `ℤ ⊆ Ψ ⊆ ℤ[1/S]` for a finite set
`S`. Then `ℤ = Ψ ∩ ⋂_{p∈S} ℤ_(p)` is Diophantine, because each `ℤ_(p)` is Diophantine in `ℚ`
(STANDARD; e.g. Koenigsmann 2016, Proposition 6, which the 10/11 manuscript applies to `ℤ_(3)`).
So no cheap predicate can see all valuations at all primes. Any architecture of this kind controls
valuations modulo some `m` only, and needs a separate bound that turns support information into
size: an input of the type of H.

**C2. The parity device needs curves of genus at least one** (VERIFIED; elementary, with a
numerical check in `parity_device.py`). Let `f_n(x, e) = x·∏_{i=1}^{n}(x − a_i e)` with integers
`a_i`. Let `p` be odd and prime to `∏ a_i ∏ (a_i − a_j)`, and suppose `v_p(e)` is even and `v_p(x)`
is odd. Then:

- if `v(x) < v(e)`, every factor has valuation `v(x)`, so `v(f_n) = (n + 1)v(x)`;
- if `v(x) > v(e)`, then `v(f_n) = v(x) + n·v(e) ≡ v(x)` (mod 2), since `v(e)` is even.

So `v(f_n)` is odd for all such `x, e`, which makes `y² = f_n(x, e)` insoluble, exactly when `n`
is even. With `n = 0` there is no parameter. The smallest device with a free parameter is `n = 2`,
the genus-one curves `y² = x(x − a₁e)(x − a₂e)`; the manuscript uses `a₁ = 1`, `a₂ = −3`
(line 980).

- The conic (`n = 1`) fails exactly when the parameter is `p`-adically smaller than the abscissa.
  The script finds even valuations in 1459 of 3000 random trials for `n = 1`, and in none for
  `n = 2` or `n = 4`.
- The asymmetry between poles and zeros comes from `H = A(A − B²)`. Its valuation is `3v(B)` when
  `v(B) < 0` and `2v(B)` when `v(B) > 0` (checked in the same script). At an odd pole, therefore,
  the parameters `e` and `eH` have opposite parities, one of them is even, and the device applies
  (Lemma 5.1). At an odd zero both may be odd.

The same computation applies to any homogeneous `y² = g(x, e)`, with `g(x, 0)` a unit multiple of
`x^{deg g}`. Parity control at every prime then needs `deg g` odd and `x` dividing `g` exactly
once. With a parameter this means `deg g ≥ 3`, so genus at least one.

Consequently every predicate built from this device asks, for completeness, for rational points on
genus-one curves with a prescribed abscissa class. This is [rs-pole, Proposition 1]: a point on
`E_ℓ` with `x ∈ βℚ*²`.

**C3. A fixed curve cannot supply these points** (STANDARD). On an elliptic curve with a rational
2-torsion point at `(0, 0)`, the map `P ↦ x(P) mod ℚ*²` is the connecting map of the 2-isogeny
descent. It is a homomorphism with finite image (Silverman, *AEC*, X.4.9). The inputs of PC fall
into infinitely many square classes, `[ηF(t)]` and `[η·2730⁶F(n)]` [rs-pole §2.1(a)]. So the curve
must vary through a family of twists, and PC is a statement about rational points on infinitely
many twists, each with a prescribed Kummer class.

In the manuscript's descent `dim Sel₂ = 3` is forced. For these curves, rank `≥ 1` is then
equivalent to finiteness of `Ш[2^∞]` [rs-pole §2.3]. That is known only through Gross–Zagier and
a converse theorem: RC for the curves `E_ℓ`, or Kriz's theorem for congruent number curves
[rs-pole §4.1].

**C4. Witnesses cannot be algebraic** (VERIFIED, elementary). Let `V → 𝔸¹_t` be the variety of a
Diophantine definition of `ℤ`. A rational section over a dense open set `U` would give rational
points above the non-integers in `U(ℚ)`, which is impossible. So the witnesses for integers are
not rational functions of `t`; [rs-pole §4.3] proves a sharper `p`-adic form of this for the pole
witnesses. Completeness therefore needs arithmetic existence theorems (positive rank, prime
patterns), not explicit formulas.

**C5. Multiplication of labels is not algebraic** (VERIFIED as an argument; it uses only STANDARD
facts).

- Rigidity: a morphism of abelian varieties `A × B → C` sending `0` to `0` is a sum of
  homomorphisms (Mumford, *Abelian Varieties*, §4, Corollary 1). So `([n]P₀, [m]P₀) ↦ [nm]P₀` is
  not a morphism.
- Moreover the set `{([n]P₀, [m]P₀, [nm]P₀)}` is Zariski dense in `E³`.
  - For fixed `m`, its closure contains `{(x, [m]P₀, [m]x) : x ∈ E}`, because `ℤP₀` is dense in
    `E`.
  - For a point `x` independent of `P₀`, the multiples of `(P₀, x)` are dense in `E²`.

So no algebraic condition on the three points cuts out the multiplication graph. A multiplication
certificate needs auxiliary witnesses, whose existence for every true triple is an arithmetic
theorem. In both manuscripts that theorem is a prime pattern.

**C6. At least five contacts; five suffice for the Shimura mechanism** (the lower bound is
[rs-height R7], [rs-pattern R8]; the rest is VERIFIED by `five_contact_j.py`).

- With four or fewer contacts the twists have genus at most one. Positive-rank twists then give
  unbounded heights at bounded `M`, so no height bound of type H can hold.
- The 11/5 contacts form one orbit of a dihedral group of order 12 in `PGL₂(ℚ)`, and `J` is the
  quotient map onto the Shimura orbifold `X⁶/W = ℙ¹_j(4, 6, 2)` [rs-height §3.3]. No rational
  group can do this for five points. The finite subgroups of `PGL₂(ℚ)` are cyclic of order 1, 2,
  3, 4 or 6, or dihedral of order 4, 6, 8 or 12 (STANDARD; Beauville, *Finite subgroups of
  PGL₂(K)*, Contemp. Math. 522 (2010)), and an orbit has size dividing the group order.
- But the proof of H uses `J` only through its ramification over the three special values
  `0, ∞, −16/27` (lines 545–563: indices `2, 6, 2`, normalized to `2, 1, 1`). A non-Galois `J`
  with the right ramification serves as well. For five cone points of order 2 the orbifold Euler
  characteristic forces degree 6 (`−1/2 = 6·(−1/12)`). The four possible ramification passports
  give three-point covers, which the script solves exactly:
  - `[2,2,2] [3,3] [2,2,2]`: with the two points over `∞` at `0` and `∞`, `J = kA²/u³` and
    `kA² − j₁u³ = kB²` force `A = (α + βu³)/2`, so the three contacts over `0` are cube roots of
    one number and never all rational;
  - `[2,2,2] [6] [2,2,1,1]` reduces to the polynomial Pell equation, whose cubic solution `T₃` has
    irrational roots;
  - `[2,4] [6] [2,1,1,1,1]` has an irreducible cubic among its contacts;
  - `[2,4] [3,3] [2,2,1,1]` has exactly one solution with rational contacts, namely

    `J₅(u) = 4(u − 1)² / (u³(2 − u)³)`,
    `J₅(u) + 16/27 = −4(u − 3)(u + 1)(2u² − 4u + 3)² / (27u³(2 − u)³)`.

    The pulled-back orbifold has index 2 exactly at `u = 1` (over `0`), at `u = 0, 2` (over
    `∞`, ramification 3) and at `u = −1, 3` (over `−16/27`, unramified), and index 1 elsewhere.
- So the five integers `𝒞₅ = {−1, 0, 1, 2, 3}`, five consecutive terms of an arithmetic
  progression, are a contact set for which the 11/5 proof of H should go through with `J₅` (degree
  6) in place of the degree-12 `J`. This is SPECULATIVE until the proof is rechecked with `J₅`;
  the rational point `u = ∞` above the elliptic value `0` is one point and does not affect a
  height bound. The preprint's height estimate also has five contact points, one of them `∞`
  (10/11 (2.6)), which is consistent with this count; `u ↦ 1/u` moves `𝒞₅` to
  `{∞, 1/2, 1, −1, 1/3}`. Section 4, route A3, weighs what five contacts would buy.

**C7. Cusps break the step from parity to good reduction; isotrivial families lose the height**
(the first part is [rs-height R4]; the second is VERIFIED as an argument). The mechanism of H needs
a family `A_u` over the `u`-line whose reduction at `p` is good whenever all contact valuations
are even (lines 545–563).

- A non-isotrivial family of elliptic curves has cusps. There the reduction is potentially
  multiplicative whatever the parity.
- An isotrivial family, the twists `E^{(f(u))}` of one curve, does have the parity property: good
  reduction after scaling wherever `v_p(f(u))` is even. But its moduli point is constant. An
  effective Shafarevich theorem then bounds only the twist class, which is already known to be
  supported on `S ∪ supp M`, and says nothing about `h(u)`.

What is needed is a non-isotrivial family with potentially good reduction everywhere, i.e. a
family over a compact Shimura curve: abelian surfaces with quaternionic multiplication, as in
Section 4 (lines 409–563). Bounding their Faltings heights polynomially in the conductor needs
modularity of the attached 2-dimensional Galois representations (lines 753–775; Pan, A011) and
effective Arakelov estimates. This is why H rests on modularity.

### 2.4 The variable budget

`FrozenTarget` fixes the number of variables: `P` may ignore variables, but cannot use more than
292,890,231,904 witnesses. The construction uses all of them (`Syntax.witness_count_arith`). The
script `budget.py` reproduces the count from the template table (lines 6739–6772) and the
recipe identity, and splits it by role (VERIFIED).

| Item | Count | Share of witnesses |
| --- | --- | --- |
| multiplication-template instances | 8,332,156 (3,108,932 direct, 5,223,224 inside 1,305,806 natural predicates) | 99.95% |
| witnesses inside slope predicates | — | 99.70% |
| witnesses inside test groups | — | 74.66% |
| the value relation's own test (`value.test`) | 35,282 | 1.2·10⁻⁷ |

Consequences:

- **The multiplication template is the unit of cost.** One extra witness in it costs 8,332,156
  variables. One extra test group per slope costs 3.64·10¹⁰ variables, which do not exist. Hence
  the cap of six primes per slope [rs-pattern §2.3].
- **The cap can only be relaxed by savings inside the template.** Two slopes per quantity
  [rs-pattern R3] would save 9.73·10¹⁰ variables. That is enough for four more test groups on each
  of the remaining 18 slopes, i.e. ten primes per slope.
- **Layer B is free.** Changes to the value relation's tests cost nothing measurable.

## 3. The manuscripts' proofs and their trust leaves

### 3.1 The audit, sorted by role

`audit_roles.py` assigns each of the 82 audit records to the roles of the construction, according
to the manuscript lines its anchors cite. The audit was taken against the present manuscript
(every record carries the SHA-256 `cb1148cd…` of `diophantine_zq.tex`). VERIFIED.

| Role (manuscript lines) | Records only there | Shared records | Status in Lean |
| --- | --- | --- | --- |
| G: generator, Mordell–Weil (254–376) | A058, A059, A060 (3) | A055 (four squares) | proved |
| H: six-contact height (377–972, 10936–11250) | A001–A018, A061–A064, A078, A079 (24) | A065, A066, A071 | hypothesis |
| PC from RC (973–1122) | A019 (1) | A020, A082 (with RC); A057, A065, A066 | hypothesis |
| RC (1760–5744, 6825–10935) | A022–A045, A049–A054, A067–A070, A073–A075, A080, A081 (39) | A020, A076, A082, A057, A065, A066, A071 | hypothesis (inside PC) |
| M and 22P (1123–1759) | A021, A072 (2) | A057, A065, A071 | 22P hypothesis; the rest proved |
| compiler (5745–6093) | A077 (1) | — | proved |
| value relation (6094–6271) | — | A071, A076 | proved |
| size and CAT (6272–6442) | A046 (1) | A071 | CAT₈ hypothesis, effective Dirichlet in progress |
| corollaries (6443–6590) | A047, A048 (2) | — | outside `FrozenTarget` |

Two thirds of the external applications serve PC: 39 records only in RC, plus A019, A020 and A082.
A further 24 serve H. 22P has two records of its own and CAT one. The elementary inputs (formal
groups A071, Dirichlet A057, four squares A055, division polynomials A056, the AFP exponential
relation A077, Mordell–Weil A058–A060) are all proved in Lean, or replaced there by Lean proofs.

### 3.2 The deep leaves of the three hypotheses

The complete leaf tables are in [rs-height §3.2], [rs-pole §3.2] and [rs-pattern §3.2]. Here I
record, for each hypothesis, only the leaves that carry the depth, with their exact use.

**H** (proof at lines 409–964; STANDARD theorems, audit records as listed).

| Leaf | Statement used | Use |
| --- | --- | --- |
| Baba–Granath; Lin–Yang (A001) | moduli of principally polarized QM abelian surfaces for the algebra of discriminant 6; the normalizer quotient is `ℙ¹_j` with branch data `0, ∞, −16/27` of indices `4, 6, 2` | the compact Shimura family (C7) |
| Buzzard (A002) | integral models of Shimura curves with level structure (Theorem 2.1, Corollary 2.3) | good reduction of the cover outside `S` (lines 441–544) |
| Faltings 1983 (A008, A063) | semisimplicity and the Tate conjecture for abelian varieties over number fields | the Hom field and the transfer to `J₁(N)` |
| Pan (A011) | Fontaine–Mazur for odd 2-dimensional de Rham representations of `G_ℚ` at `ℓ = 5` (residually reducible case) | modularity of `r₅` (lines 753–775) |
| Gaudron–Rémond (A005, A015) | explicit isogeny estimates | CM case and transfer |
| Javanpeykar (A014) | `h_F(J₁(N)) ≤ 1.3·10⁷N^12`-type Arakelov bound for Belyi curves | the polynomial dependence on `M` (exponent 24) |
| Fowler; CM heights (A003, A004, A065) | class number bound and the CM Faltings height formula | CM branch |
| Lin–Yang, Lauter–Naehrig–Yang; Pazuki (A017, A018) | theta formula, theta versus Faltings height | back from `A` to `u` |

**PC** (lines 1019–1121, then RC).

| Leaf | Statement used | Use |
| --- | --- | --- |
| Poonen–Stoll (A019) | the Cassels–Tate pairing is alternating on `Ш` modulo its divisible part | `dim Sel₂ = 3 ⇒ corank 1` (line 1072) |
| Kolyvagin, Gross–Zagier, Kato (A020, A082) | analytic rank `≤ 1` implies equal algebraic rank and finite `Ш` | the forward lemma (line 1086) |
| BCDT (A066) | modularity of elliptic curves over `ℚ` | the forward lemma; replaceable by `X₀(24)` plus twisting [rs-pole §2.3] |
| RC (Theorem 5.3, 39 records, about 8,000 lines) | `corank Sel_{2^∞}(E_ℓ) = 1 ⇒ ord_{s=1} L(E_ℓ, s) = 1` for squarefree `ℓ ≡ 11 (mod 12)` | applied to `E_n` and `E_{nθ}` |

The leaves of RC include Kato's Euler system (A023, A049–A051), Waldspurger (A029–A031),
Bump–Friedberg–Hoffstein (A025), the explicit Gross–Zagier formula of Cai–Shu–Tian (A027),
Nekovář's Selmer complexes and duality (A036–A045, A075, A080, A081), and Dokchitser–Dokchitser
parity (A022). RC itself is a new, unrefereed 2-converse: Kriz–Li (arXiv:1606.03172, Remark 1.6)
note that the 2-converse was open in 2018, as [rs-pole §3.1] records. RC is the largest single
trust leaf of the construction.

**22P** (lines 1291–1704).

| Leaf | Statement used | Use |
| --- | --- | --- |
| Green–Tao, *Linear equations in primes*, Ann. of Math. 171 (2010), Main Theorem (A021) | the asymptotic for a finite-complexity system of affine forms, conditional on GI(s) and MN(s) | the lower count for the 22 forms |
| Green–Tao, Ann. of Math. 175 (2012), Theorem 1.1 (A021) | MN(s) for all s | same |
| Green–Tao–Ziegler, Ann. of Math. 176 (2012), Theorem 1.3 (A021) | GI(s) for all s | same |
| Williams 1974; Silverman III, V (A021, A072) | Mertens in progressions; CM reduction identities | sieve; identifying the good primes |

**CAT** (lines 6285–6360): Bennett–Martin–O'Bryant–Rechnitzer, Theorem 1.2 and Corollary 6.17
(A046). It is being replaced by a textbook effective Dirichlet theorem.

### 3.3 The 10/11 manuscript and the preprint

The 10/11 manuscript assumes the four preprint inputs and adds three leaves (VERIFIED against the
10/11 text):

- Koenigsmann's quaternionic description of semilocal rings (Ann. of Math. 183 (2016),
  Observation 5, Proposition 6, Remark 8), for `ℤ_(3)` (§13.1). Its proof rests on Hilbert
  reciprocity and Hasse–Minkowski for quaternary forms (STANDARD; neither is in Mathlib v4.35 as
  far as I know, see §4, A2).
- DPRM (Davis, Amer. Math. Monthly 80 (1973), Theorem 8.1), for c.e. relations on labels.
- Poonen's rank-one lemmas (ANTS-V, 2002, Lemmas 5, 6, 10, 11), cited as motivation; the needed
  local facts are reproved (10/11, Lemma 3.1).

Its scalar bridge uses no prime pattern (10/11, p. 13: "the new scalar bridge does not use it
again"). This matches F3: the bridge's `Supp` relation, like the 11/5 test, puts the variable
label inside a product (`Mul_G(T, J, R)`, 10/11 Definition 12.1).

What the four preprint inputs rest on cannot be checked here: the preprint and its companion
papers are not in the repository. The 11/5 manuscript replaces each of them by its own proof
(G, Lemma 5.1 with PC, H, 22P). One of these, G, is now a Lean theorem.

### 3.4 The kinds of depth, by role

Combining §2.2 and §2.3, every deep input of the 11/5 construction belongs to one of three kinds.
Each kind is tied to one role.

| Kind | Role | Why this kind (§2.3) | Present leaf |
| --- | --- | --- | --- |
| **K1. Points on infinitely many genus-one twists** with a prescribed Kummer class | completeness of denominator control (A2 and B4) | C2: the parity device needs genus `≥ 1`. C3: a fixed curve has finitely many abscissa classes. C4: no algebraic witnesses | PC ← RC (or Kriz, Route K) |
| **K2. A uniform effective height bound on twists of a curve of genus `≥ 2`** | soundness (A2 and B2) | C1: only valuations mod `m` can be seen. C6: at least 5 contacts. C7: compact Shimura family plus modularity | H ← Pan, Faltings, Javanpeykar, … |
| **K3. Primes in a linear pattern, with a Chebotarev condition on each prime** | completeness of multiplication (A2) | F4: fixed shift, one test group per prime, six groups per slope. C5: multiplication is not algebraic | 22P ← Green–Tao–Ziegler |

Theorem 1.1 refutes Mazur's conjecture on the topology of rational points (lines 79–82; Mazur,
Experiment. Math. 1 (1992), Conjecture 3, A047; that a Diophantine model of `ℤ` in `ℚ` contradicts
it is Cornelissen–Zahidi, *Topology of Diophantine sets: remarks on Mazur's conjectures*, Contemp.
Math. 270 (2000), STANDARD). So some input must produce rational points that are discrete in a
way no previously known variety exhibits. The construction does this by coupling K1, which makes
points exist on infinitely many fibres, with K2, which forces points over non-integers to have
bounded height and hence, by the real approximation, not to exist. That pairing of an existence
theorem with a uniform size theorem is what any architecture must reproduce.

- Plausibly unavoidable in kind: K1 and K2, for every architecture whose denominator control comes
  from parity (C1, C2). SPECULATIVE beyond such architectures.
- Specific to the multiplication mechanism: K3 (F4). No alternative mechanism is known (§4).
