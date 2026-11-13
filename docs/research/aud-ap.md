# Audit of the progression variant of the main theorem: the statements

Subject: the Lean theorem `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_goodPrimeAP`
(`ZInQKernel/Main.lean`), its new hypothesis `ZInQ.GoodPrimeAP`
(`ZInQKernel/Hypotheses/PrimeAP.lean`) and the definitions of the new modules
`ZInQKernel/Multiplication/Completeness/AP/*.lean`, compared with `docs/research/nt-22p.md` §3
(Lemma P, field 2′, the hypothesis 22P_AP, Proposition AP), with the referee reports
`rv-nt22p-proof.md` and `rv-nt22p-ap.md`, and with Green–Tao 2008, Theorem 1.2. The kernel checks
the proofs; this audit concerns what the statements say.

Each examined step is marked CORRECT (checked here), GAP (missing or wrong) or UNCHECKED.

## Verdict

**The statements are faithful as written.**

- `GoodPrimeAP` is the hypothesis 22P_AP of nt-22p §3.3, with the same quantifiers, `x ≥ 1`,
  `v ≥ 1`, the same lower bound `max S_b` (written "larger than every element of `S_b`", an
  equivalent form), and the same set of good slope primes `G`. It follows from Green–Tao 2008,
  Theorem 1.2, and the positive relative upper density of `G` (Proposition D) with no further
  condition. I proved this implication in Lean against the branch, from a Lean form of each of
  the two statements.
- The variant has the main theorem's conclusion `FrozenTarget` (the frozen statement, checked
  token for token) and its two other hypotheses `SixContactMin` and `CertifiedRank`, which the
  branch does not touch. Its axioms are `propext`, `Classical.choice`, `Quot.sound`.
- The new definitions (`PoleAbsorbHyp`, `OldBounds`, `GoodSlopeAP`, `SlopeRepresentationAP`, the
  repeated completeness chain) match nt-22p §3.2 and the referees' corrections. They occur only in
  intermediate statements, so they cannot weaken what the variant proves.

The findings (§5) concern the trust statement: Proposition D is still a sketch (moderate), and two
citations or docstrings need small corrections (minor).

## 1. The hypothesis `GoodPrimeAP`

### 1.1 The Lean statement

```lean
def GoodPrimeAP : Prop :=
  ∀ K : ℕ, ∃ x v : ℕ, 1 ≤ x ∧ 1 ≤ v ∧
    ∀ j ≤ K, GoodSlopePrime (x + j * v) ∧ ∀ q ∈ Mult.S_b, q < x + j * v
```

with

- `GoodSlopePrime p := p.Prime ∧ ∃ r : ZMod p, r² = 2 ∧ 75 − 53r ≠ 0 ∧ 75 + 53r ≠ 0 ∧
  gcd(#E_r(𝔽_p), #E_{−r}(𝔽_p)) = 4`, where `#E_r(𝔽_p)` (`pointCount p (−(75 − 53r)²)`) is the
  number of affine solutions of `y² = x³ − (75 − 53r)²x` over `ZMod p`, plus one;
- `Mult.S_b = S_ht ∪ catalogue`, with `S_ht = {p prime : p ≤ 324}` (a filter of `range 325`) and
  `catalogue = catalogueFinset W 22 324`, a `Finset` equal to the set `𝓗` of the first
  twenty-two primes above `324` in each unit class modulo `W = 4·324#` (`coe_catalogue`, a proved
  theorem).

### 1.2 Comparison with 22P_AP (nt-22p §3.3)

The note states: *for every `K` the set `G′ = {p ∈ G : p > max S_b}` contains an arithmetic
progression `x, x + v, …, x + Kv` with `x ≥ 1` and `v ≥ 1`*, where `G` is the set of good slope
primes, `S_b = S_ht ∪ 𝓗`.

| Item | Note | Lean | Verdict |
| --- | --- | --- | --- |
| quantifiers | `∀ K ∃ x, v` | `∀ K : ℕ, ∃ x v : ℕ` | CORRECT |
| length | `K + 1` terms `x + jv`, `0 ≤ j ≤ K` | `∀ j ≤ K` | CORRECT |
| `x ≥ 1`, `v ≥ 1` | yes | `1 ≤ x ∧ 1 ≤ v` | CORRECT |
| goodness | `p ∈ G` | `GoodSlopePrime (x + j * v)` | CORRECT (see 1.3) |
| lower bound | `p > max S_b` | `∀ q ∈ S_b, q < p` | CORRECT: equivalent, since `S_b` is a non-empty `Finset` (it contains `2`) |
| `S_b` | `S_ht ∪ 𝓗` | `S_ht ∪ catalogue` | CORRECT: same set, finite, primes only |

Junk values. `K = 0` asks for one good prime above `max S_b` and an arbitrary `v ≥ 1`; this is
implied by the infinitude of `G`, which Proposition D gives. The arithmetic is in `ℕ` with only
additions and multiplications, so there is no truncated subtraction. `S_b` takes no junk value: it is
the full set of the note, not an empty or truncated one (which would only weaken the hypothesis,
and the proof of Proposition AP would then fail to typecheck), and it is a finite set, so the
hypothesis is not false for a trivial reason (an infinite `S_b` would make it false and the variant
vacuous). `x ≥ 1` is redundant (`x` is a prime) and harmless. CORRECT.

### 1.3 The definition `GoodSlopePrime` is the set `G` of Proposition D

`GoodSlopePrime` is not new on this branch (it is in `PrimePattern.lean` on `main`, consumed by
field 3 of `GoodSlope`). I checked that it defines the set whose density Proposition D computes:

- by hand: for `p` odd with `2` a square mod `p` and `d(r) = 75 − 53r ≠ 0`, the curve
  `y² = x³ − d(r)²x` has discriminant `64 d(r)⁶ ≠ 0` mod `p`, so it is the good reduction of
  `E : y² = x³ − (75 − 53√2)²x` at the place `√2 ↦ r`, and `pointCount` (affine solutions plus the
  point at infinity) is its order. The two roots `±r` give the two places; the condition is
  symmetric in them. At `p = 2` the root `r = 0` gives two curves with `3` points each, so `2` is
  not good. At `p = 7` both roots kill `d` or `d̄` (`75 − 53·3 = −84`). CORRECT.
- by an independent computation: a literal transcription of the Lean definition (point counts
  over `𝔽_p`, existential over the roots) agrees with the CM description of nt-22p §2.1
  (`p ≡ 1 mod 8`, `(7/p) = −1`, no odd `ℓ | gcd(a, p + 1)` for `p = a² + b²`, `a` odd) at every
  prime `324 < p < 20000` (240 good primes, no mismatch). The relative density of the CM set in
  `(324, 2·10⁶)` is `15821/148867 = 0.1063`, against the Euler product
  `(1/8)∏_{ℓ ≡ 1 (4)}(1 − 2/(ℓ − 1)²) = 0.1060`. The good primes below `324` are
  `17, 41, 73, 97, 241, 257, 313`. As a sanity check against a hidden local obstruction, the good
  primes in `(324, 3·10⁵)` contain a ten-term progression (`53681 + 9240j`, `0 ≤ j ≤ 9`).
  CORRECT.

### 1.4 What Green–Tao 2008 and Proposition D give

**Green–Tao 2008, Theorem 1.2.** I read the statement in the TeX source of arXiv math/0404188v6
(the second theorem of §1, label `sz-primes`, numbered 1.2): *let `A` be any subset of the primes
of positive relative upper density, `limsup_{N→∞} π(N)^{−1}|A ∩ [1, N]| > 0`; then `A` contains
infinitely many arithmetic progressions of length `k` for all `k`.* The progressions are
non-trivial (common difference `d ≠ 0`; with `d = 0` the theorem would be empty). The docstring of
`GoodPrimeAP` quotes this correctly, with the right theorem number. Its proof in the paper is an
outline: the section "Further remarks" (§11 of the arXiv source; the docstring says §10) says
that the method "also extends" to Theorem 1.2, the one significant change being a pigeonholed
residue class `b mod W`, and "we leave the details to the reader". The Conlon–Fox–Zhao
exposition (arXiv:1403.2957) proves Theorem 1.1 in full and lists the dense-subset form only as
an extension. The docstring records this caveat (from `rv-nt22p-ap`, F3). CORRECT as a citation;
the caveat stands (finding F2 below).

**Proposition D** (nt-22p §2.2): `G` has natural density `(1/8)∏_{ℓ ≡ 1 (4)}(1 − 2/(ℓ − 1)²)`
in the primes. Only its weakest consequence is used: `G` has positive relative upper density.
It is a proof sketch (Hecke's theorem for `ℚ(i)` or the prime number theorem in progressions, plus
the two-dimensional sieve of the manuscript, lines 1600–1642); `rv-nt22p-ap` finds it correct as a
sketch and lists what the write-up must contain (its F5). UNCHECKED here beyond the numerical
agreement of 1.3; it is the one unwritten step between the published theorem and `GoodPrimeAP`
(finding F1 below).

**The derivation.** Write, in Lean,

```lean
def GreenTaoDense : Prop :=
  ∀ A : Set ℕ, (∀ p ∈ A, p.Prime) →
    (∃ δ : ℝ, 0 < δ ∧ ∃ᶠ N in atTop,
      δ * (Nat.primeCounting N : ℝ) ≤ (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)) →
    ∀ k : ℕ, ∃ x d : ℤ, d ≠ 0 ∧ ∀ j : ℕ, j < k → ∃ p ∈ A, (p : ℤ) = x + j * d

def PropDUpper : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ N in atTop,
    δ * (Nat.primeCounting N : ℝ) ≤
      (((Finset.range (N + 1)).filter ZInQ.GoodSlopePrime).card : ℝ)

theorem goodPrimeAP_of_greenTao_propD (hGT : GreenTaoDense) (hD : PropDUpper) :
    ZInQ.GoodPrimeAP
```

`GreenTaoDense` is Theorem 1.2 with "infinitely many progressions" weakened to "one", and with
`limsup > 0` written as "`δπ(N) ≤ |A ∩ [0, N]|` for infinitely many `N`, for some `δ > 0`". The two
forms are equivalent: the ratio lies in `[0, 1]` because `A` consists of primes, so a positive
limsup `λ` gives the second form with `δ = λ/2`, and the second form gives `limsup ≥ δ`; and
`0 ∉ A`. `PropDUpper` is implied by the natural-density statement of Proposition D. The
derivation: put `M = max S_b` and `A = {p ∈ G : p > M}`. Then
`|A ∩ [0, N]| ≥ |G ∩ [0, N]| − (M + 1)`, and `π(N) → ∞` (`Nat.tendsto_primeCounting`), so `A`
satisfies the density hypothesis with `δ/2`. Theorem 1.2 with `k = K + 1` gives `x, d ∈ ℤ`,
`d ≠ 0`, and primes `p_j = x + jd ∈ A` for `j ≤ K`. If `d > 0`, take `x′ = p₀` and `v = d`; if
`d < 0`, reverse: `x′ = p_K`, `v = −d`, and `x′ + jv = p_{K−j}`. Then `x′ ≥ 2`, `v ≥ 1`, and every
term is in `G` and exceeds every element of `S_b`. No condition beyond the two inputs is used.

I compiled this derivation against the branch, outside the repository's library: it is accepted
with the axioms `propext`, `Classical.choice`, `Quot.sound` (§4). So `GoodPrimeAP` follows from
Theorem 1.2 and Proposition D with no hidden condition. CORRECT.

A complete proof of the form used is available: the main theorem of Tao–Ziegler, *The primes
contain arbitrarily long polynomial progressions* (Acta Math. 201 (2008); arXiv math/0610050),
states that a set of primes of positive relative upper density contains infinitely many
configurations `x + P₁(m), …, x + P_k(m)` with `m > 0`, for integer polynomials vanishing at `0`.
With `P_i = (i − 1)m` this is Theorem 1.2 with a positive common difference. Its proof treats a
general dense set (the residue class `b mod W` is chosen by pigeonhole in §2 there). I checked the
statement in the TeX source, not the proof.

## 2. The statement of the variant

```lean
theorem exists_bounded_integer_polynomial_defining_integers_of_goodPrimeAP
    (hH : SixContactMin) (hCR : CertifiedRank) (hAP : GoodPrimeAP) : FrozenTarget
```

- **Conclusion.** `FrozenTarget`, the same proposition as in the main theorem
  `exists_bounded_integer_polynomial_defining_integers_of` (same constant, not a copy). The check
  that `FrozenTarget` is token for token the frozen upstream statement passes (§4). The proof
  term is `Assembly.assembly_AP haltingAddMulBound hH (poleCompleteness_of_certifiedRank hCR)
  (slopeRepresentationAP_of_goodPrimeAP hAP)`, and `assembly_AP` produces the witness
  `specPstar c₃`, the same polynomial `P_*` as `Assembly.assembly`. CORRECT.
- **The other hypotheses.** `SixContactMin` and `CertifiedRank` are the constants used by the main
  theorem. Between the merge base with `main` and the branch, the only changes under
  `ZInQKernel/`, `lean/` and `scripts/` are new files (`Hypotheses/PrimeAP.lean`,
  `Multiplication/Completeness/AP.lean` and `AP/*.lean`), one import in `ZInQKernel.lean`, and in
  `Main.lean` two imports, one docstring bullet and the new theorem. No existing definition or
  statement changed, so `SixContactMin`, `CertifiedRank`, `PoleCompleteness`, `FrozenTarget`,
  `GoodSlopePrime`, `S_b` and the catalogue are those of `main`. CORRECT.
- **No hidden hypothesis.** The variant takes no further argument; the halting-circuit bound is
  the theorem `Compiler.NodeCheck.haltingAddMulBound`, as in the main theorem. Its axioms are the
  standard three (§4). CORRECT.

## 3. The definitions of the new modules

A remark on scope first. The variant's statement mentions only `SixContactMin`, `CertifiedRank`,
`GoodPrimeAP` and `FrozenTarget`, and `GoodPrimeAP` mentions only `GoodSlopePrime`, `S_b`,
`pointCount` and the catalogue, all from `main`. The definitions introduced by the branch
(`PoleAbsorbHyp`, `OldBounds`, `GoodSlopeAP`, `SlopeRepresentationAP`) occur only in intermediate
statements. However they are chosen, they cannot weaken what the variant proves; a vacuous or
too-weak intermediate definition could only make some proof fail, and the kernel accepts all of
them. I still compared them with the note, since they are the Lean form of its argument and
other work may cite them.

| Definition | Note / referees | Verdict |
| --- | --- | --- |
| `PoleAbsorbHyp ℓ t`: `1 ≤ v_ℓ(t.den)`, `ℓ = 2 → 3 ≤ v_ℓ(t.den)`, `ℓ ∤ t.num − c·t.den` for `c ∈ 𝒞 ∪ {1}` | Lemma P: `t = u/v` lowest terms, `e = v_ℓ(v) ≥ 1`, the seven `u − cv`, `u − v` prime to `ℓ`, `ℓ` odd or `e ≥ 3` | CORRECT. Lowest terms by `num/den`. The seven clauses are redundant (`rv-nt22p-proof` finding 6), cosmetic. `F(t) > 0` is carried by field 2′ instead, which is equivalent where it is used. Primality of `ℓ` is not in the definition; it is used only at `ℓ ∈ S_b`, all prime. |
| `OldBounds p t` | field 2 of `GoodSlope` at one prime | CORRECT: verbatim copy of the field `old` of `GoodSlope` (`PatternSlopes.lean:29`). |
| `GoodSlopeAP B₀ t` | `GoodSlope` with field 2 replaced by 2′: "either the bounds of field 2 hold at `ℓ`, or `F(t) > 0` and Lemma P's hypotheses hold at `ℓ`" | CORRECT: fields `not_mem_contactSet`, `ne_one`, `contact`, `few` are verbatim; `old` is `OldBounds p t ∨ (0 < contactPoly t ∧ PoleAbsorbHyp p t)`. `GoodSlope → GoodSlopeAP` is proved. |
| `SlopeRepresentationAP` | slope representation with 2′ | CORRECT: `SlopeRepresentation` with `GoodSlope 0` replaced by `GoodSlopeAP 0` (same `B₀ = 0`, three slopes, sum `A`). |

Non-vacuity. `GoodSlopeAP` is not trivially satisfiable: fields 3 and 4 are those of
`GoodSlope`, and the second alternative of 2′ still requires a pole of the right order with
`F(t) > 0`. `SlopeRepresentationAP` is weaker than `SlopeRepresentation` (proved), and that is the
point of the route; the kernel-checked `slope_complete_AP` shows it still suffices.

The repeated completeness chain (`slopes_of_int_AP`, `completeness_core_AP`,
`multiply_complete_AP`, `multiplication_exact_AP`, `exists_value_relation_iff_AP`,
`assembly_AP`) has the statements of the originals with `h22 : SlopeRepresentationAP` in place of
`SlopeRepresentation`; the conclusions (`SlopePred t ell (certShifts …)`, the multiplication
relation, `MultiplicationExact`, the value relation, `FrozenTarget`) are unchanged. CORRECT.

Intermediate lemmas, read against the note (statements only):

- `lemmaP_one`, `lemmaP_two`, `lemmaP_two_ball`: Lemma P(1), (2), with `v_ℓ(1 − R₀q²) ≥ N`
  written `‖1 − R₀q²‖ ≤ ℓ^{−N}` in `ℚ_ℓ`. CORRECT.
- `lemmaP_three`: Lemma P(3), with `e : ℕ` (also `e = 0`), test integrality at every prime of
  `ℤ[√2]` above `p`, `v_p(ℓ₀) ≥ 0`, `v_p(a) ≥ 23e + v_p(12) + 2`; conclusion `v_p(B) ≥ 4`. CORRECT.
- `pole_input_valuations_AP`: concludes `v_p(B) ≥ 4` on `S_b` where the original concludes
  `≥ 103C_p + 8`. Pole completeness needs `≥ 4` on `S₀ ⊂ S_b` only. CORRECT (a weaker
  intermediate conclusion that is still sufficient).
- `weak_approx_targets`: assumes `S ∩ S′ = ∅`, which holds in the application (`S_b` and the
  selected contact primes outside `S_b`). CORRECT.
- `slope_complete_AP`: same conclusion as `slope_complete`, hypothesis `GoodSlopeAP`. CORRECT.
- `slopeRepresentationAP_of_goodPrimeAP`: Proposition AP with `max S_A⁺ = max(1, A′ + 60)`,
  `min S_A⁺ = min(−60, A′ − 1)`, `K = max − min`, `u = x + (max S_A⁺)v`, slopes
  `u/v`, `(A′v − u)/v`, `−10`. These are the note's choices, with the referees' corrected `K_A`.
  CORRECT.

## 4. Checks run

| Check | Outcome |
| --- | --- |
| `lake build ZInQKernel` on the branch | success, 9593 jobs, no `sorry` warning |
| `python3 scripts/check_target.py` | "FrozenTarget matches lean/Frozen/BoundedIntegerPolynomial.lean" |
| `#print axioms` of the variant | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms` of `Mult.slopeRepresentationAP_of_goodPrimeAP` | `[propext, Classical.choice, Quot.sound]` |
| `#check` of the variant and of the main theorem | `SixContactMin → CertifiedRank → GoodPrimeAP → FrozenTarget` and `SixContactMin → CertifiedRank → FixedPrimePattern → FrozenTarget` |
| `#print GoodPrimeAP`, `#print FrozenTarget` | as quoted in §1.1 and as in `Target.lean` |
| grep of `PrimeAP.lean`, `AP.lean`, `AP/*.lean` for `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `set_option`, `unsafe`, `partial`, `opaque`, `csimp`, `macro`, `elab`, `run_cmd`, `#eval` | no occurrence in code (one match of the word "Lean." in a docstring); none in the lines added to `Main.lean` |
| `goodPrimeAP_of_greenTao_propD` (§1.4) | compiles; axioms `[propext, Classical.choice, Quot.sound]` |
| literal `GoodSlopePrime` vs the CM description, `324 < p < 20000` | 240 good primes, no mismatch |
| relative density of `G` in `(324, 2·10⁶)` | `0.1063` (Euler product `0.1060`) |

## 5. Findings

No finding is critical or major. None concerns a Lean statement; F1–F3 concern the trust
statement attached to `GoodPrimeAP` and its documentation.

**F1 (moderate; trust base, not a defect of the statement). Proposition D is still a sketch.**
`GoodPrimeAP` follows from Green–Tao 2008, Theorem 1.2, and the positive relative upper density
of `G` (§1.4, kernel-checked). The second input is Proposition D of nt-22p §2.2, which is a proof
sketch: a transposition of the manuscript's sieve (lines 1600–1642) from prime values of a form
to primes up to `N`, plus Hecke's theorem for `ℚ(i)` or the prime number theorem in progressions.
The referee `rv-nt22p-ap` (its F5) finds the sketch correct and lists the two points the write-up
must make explicit: the upper bound `≪ N/(ℓ² log N)`, uniform in `ℓ`, for `L < ℓ ≤ N^{1/8}`
(trivial lattice counting is not enough there), and the tail `ℓ > N^{1/8}`. My computation agrees
numerically (density `0.1063` against `0.1060`) but is no proof. Until Proposition D is written
out, the docstring's "it follows from the theorem of Green and Tao" rests on an unwritten step.
The docstring says so ("Proposition D is a sketch that still has to be written out"), so the
documentation is accurate; the gap is in the supporting mathematics. Repairable: write out
Proposition D in its weakest useful form, positive relative upper (or lower) density, by the
"Hecke avoided" route of nt-22p §2.2.

**F2 (minor; citation). The dense-subset form of Green–Tao is proved there only in outline, and
the section is misnumbered.** The docstring correctly records that Green–Tao prove Theorem 1.2
only in outline and asks for a complete proof to be cited, without naming one. In the arXiv v6
source the outline is in §11 ("Further remarks"), not §10 as the docstring and `rv-nt22p-ap` say
(I did not check the numbering of the published version). A complete proof of exactly the form
needed is the main theorem of Tao–Ziegler 2008 with linear polynomials (§1.4), which gives a
positive common difference directly. Repair: cite it in the docstring of `GoodPrimeAP`.

**F3 (minor; documentation). The module docstring of `Main.lean` names only Green–Tao.** The new
bullet calls `GoodPrimeAP` "a consequence of Green–Tao 2008, Theorem 1.2". It is a consequence
of Theorem 1.2 *and* Proposition D (F1). The docstring of `GoodPrimeAP` itself is complete.
Repair: add "and Proposition D (positive density of the good slope primes)" to the bullet.

**F4 (cosmetic). Redundant clauses.** `PoleAbsorbHyp` keeps the seven non-divisibility clauses,
which follow from `1 ≤ v_ℓ(t.den)` and lowest terms (`rv-nt22p-proof` finding 6); `GoodPrimeAP`
keeps `1 ≤ x`, which follows from primality. Both are harmless: the first is in an intermediate
definition, and the second is implied by the inputs (§1.4). No repair needed.

**F5 (observation). The hypothesis asks for more than Proposition AP uses.** `GoodPrimeAP`
asks for `K + 1` terms for every `K`; Proposition AP uses at most fourteen terms of a progression
of length `K_A + 1` (`K_A = A + 130` or `−A − 8`). This is the form Green–Tao provides, and a
weaker hypothesis (a homothetic copy of the fourteen-point set `max S_A⁺ − S_A⁺`) would not have a
simpler proof. No repair needed.

## 6. Repairs

1. (F1) Write out Proposition D, at least in the form "the good slope primes have positive relative
   upper density in the primes", following nt-22p §2.2 and `rv-nt22p-ap` F5.
2. (F2) In the docstring of `GoodPrimeAP`, cite Tao–Ziegler, Acta Math. 201 (2008), main theorem
   with `P_i = (i − 1)m`, as a complete proof of the dense-subset form, and correct "§10" to the
   section of the cited version ("Further remarks", §11 of arXiv v6).
3. (F3) In the module docstring of `Main.lean`, add Proposition D next to Green–Tao 2008.
4. Optional: add the derivation of §1.4 (`GreenTaoDense`, `PropDUpper`,
   `goodPrimeAP_of_greenTao_propD`) to the repository next to `GoodPrimeAP`. It makes the trust
   statement precise: the hypothesis is then a named consequence of two named statements, one
   published and one to be written out.
