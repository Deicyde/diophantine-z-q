# Referee report on `nt-22p.md`: Proposition AP, Proposition D and the Green–Tao step

Scope: §2 (Proposition D and the CM description of the good slope primes), §3.3 (the
hypothesis 22P_AP and Proposition AP), §3.4 (Green–Tao 2008 and the trust-base table) of
`docs/research/nt-22p.md`, compared with `ZInQKernel/Hypotheses/PrimePattern.lean`,
`ZInQKernel/Multiplication/Completeness/{PatternSlopes,TwoSlope,SlopeCompleteness,PoleValuations,Core}.lean`,
`ZInQKernel/Hypotheses/Pole.lean` and the TeX source of Green–Tao, arXiv math/0404188v6.
Lemma P and the modified slope-completeness argument of §3.2 are outside this report. I checked
Lemma P(1), which Proposition AP feeds directly, and I take the rest of §3.2 as given.

Notation is that of the note: `𝒞 = {0, −15, −20, −24, −30, −60}`, `T = 𝒞 ∪ {1}`, `A′ = A + 10`,
`S_A⁺ = T ∪ (A′ − T)`, `M = max S_A⁺`, `K_A = M − min S_A⁺`, `G` the good slope primes
(`ZInQ.GoodSlopePrime`), `G′ = {p ∈ G : p > max S_b}`, `B_ℓ = 4` on `S_ht` and `1` on the
catalogue.

## Verdict

**Proposition AP is proved as written**, given the modified slope completeness of §3.2 (field 2′
in place of field 2), which this report does not referee. Every step of §3.3 is correct. The one
numerical slip (the size of `K_A`) does not affect the argument.

**Proposition D is correct** as a proof sketch. Its two analytic inputs (Hecke's prime ideal
theorem for `ℚ(i)`, or only the prime number theorem in progressions, and a two-dimensional upper
bound sieve uniform in `ℓ`) are standard, and the sieve is the manuscript's own (lines 1600–1642),
transposed from prime values of a form to primes up to `N`. It still has to be written out.

**The Green–Tao step is correct.** Theorem 1.2 of Green–Tao 2008 is quoted correctly: it
concerns positive *relative upper* density among the primes, and its progressions are genuine,
non-constant progressions of primes. After reversal they give `x ≥ 1`, `v ≥ 1`, and `x > N` for
any prescribed `N` once the theorem is applied to `G ∩ (N, ∞)`.

**The trust-base claim is right in substance, with qualifications.** The deep input of the
hypothesis drops from the Green–Tao–Ziegler machinery to Green–Tao 2008. But (i) the Lean main
theorem rests on 22P_AP only after the Lean work of Route 1 (field 2′, the Lemma P branch, the
residue-class weak approximation). Until then, the kernel-checked derivation of the slope
representation from 22P₂ is traded for unformalized elementary steps. (ii) Proposition D is still
a sketch. (iii) Green–Tao 2008 prove Theorem 1.2 only in outline (their §10 leaves the details to
the reader), and the exposition the note proposes to follow proves only Theorem 1.1.

No finding is critical or major. Section 2 lists the findings; Section 7 lists the repairs.

## 1. Summary of the steps examined

| Step | Verdict |
| --- | --- |
| §2.1 CM description of `G` for `p > 324` | CORRECT (by hand, and by computation for all `325 ≤ p ≤ 2·10⁵`) |
| §2.2 Euler product and natural density | CORRECT (sketch; computation to `3·10⁷`) |
| §2.2 sieve for `ℓ > L` | CORRECT (it is the manuscript's sieve, transposed) |
| §2.2 positivity without Hecke | CORRECT |
| density of `G′` is relative to the primes | CORRECT |
| §3.3 the set `S_A⁺`, indexing in a progression of length `K_A + 1` | CORRECT |
| §3.3 lowest terms | CORRECT |
| §3.3 field 1 | CORRECT |
| §3.3 signs `F(t₁) > 0`, `F(t₂) > 0` for every integer `A` | CORRECT (including `A′ = −59, −60`) |
| §3.3 field 2′ | CORRECT (case split checked; Lemma P(1) checked) |
| §3.3 fields 3 and 4 | CORRECT (same argument as `goodSlope_of_primeValues`) |
| §3.3 the constant slope `−10` | CORRECT (kernel-checked `goodSlope_neg_ten`) |
| §3.3 remark 1 (every small prime divides `v`) | CORRECT; the size `K_A ≈ |A| + 71` is wrong |
| §3.3 remark 3 (Lemma P needed only on `S₀`) | CORRECT |
| §3.4 statement of Green–Tao 2008, Theorem 1.2 | CORRECT (checked against the TeX source) |
| §3.4 22P_AP from Theorem 1.2 and Proposition D | CORRECT |
| §3.4 trust-base table | CORRECT in substance; incomplete (findings F3–F5) |
| §3.2 Lemma P(2), P(3) and the modified slope completeness | UNCHECKED here (outside this report) |

## 2. Findings

**F1 (minor, cosmetic).** §3.3, remark 1, says `K_A ≈ |A| + 71`. In fact
`max S_A⁺ = max(1, A′ + 60)` and `min S_A⁺ = min(−60, A′ − 1)`, so

- `K_A = A′ + 120 = A + 130` for `A′ ≥ −59`,
- `K_A = 2 − A′ = −A − 8` for `A′ ≤ −60`,

with minimum `61` at `A′ = −59`. Only the qualitative statement (`K_A → ∞`) is used, so nothing
breaks. A useful consequence the note does not state: every progression used has at least 62
terms, so `v` is divisible by every prime `≤ 61`. In particular `8 | v`, since all terms are
`≡ 1 (mod 8)`. So the delicate case `ℓ = 2`, `v₂(v) ≤ 2` of Lemma P never occurs in
Proposition AP.

**F2 (minor, wording).** "All fourteen numbers `u − c′v` are primes of `G′`": `S_A⁺` has fewer
than fourteen elements when `T` and `A′ − T` meet (for instance `A′ = 0`). Then the two variable
slopes share a contact prime. This is harmless: `GoodSlope` is a condition on each slope
separately, and the consumer (`slope_complete`, `Core.lean:17`) treats the three slopes
independently, with private groups. The Lean proof from 22P₂ already allows such coincidences.

**F3 (minor, trust base: the reference for Theorem 1.2).** In the TeX source, Theorem 1.2
(`sz-primes`) is stated in §1, but §10 says only that "our method also extends to prove
Theorem 1.2"; the one change is a pigeonholed residue class `b mod W`, and "we leave the details to
the reader". The Conlon–Fox–Zhao exposition (arXiv:1403.2957), which the note names as the route a
formalization would follow, gives a complete proof of Theorem 1.1 only. It lists Theorem 1.2 among
the "extensions". The modification is routine and Theorem 1.2 is universally accepted. Still,
the trust-base table should cite it as "Green–Tao 2008, Theorem 1.2 (proof outlined in §10)" and
add a source with a complete proof of the dense-subset form, or note that the relative Szemerédi
theorem of Conlon–Fox–Zhao (arXiv:1305.5440, Theorem 1.1 there) plus the `W`-trick with a
pigeonholed class gives it. The note's §3.1 still calls the theorem number UNCHECKED while §3.4
says VERIFIED. The number is 1.2: the theorem counter is tied to subsections, and none precedes it
in §1.

**F4 (moderate, trust base: formalization status).** The table at the end of §3.4 lists
"Lemma P and the modified choice of `q`" and "Proposition AP" as "elementary, VERIFIED by hand".
For the Lean main theorem the comparison should be stated as follows.

- Today `Main.lean` derives `SlopeRepresentation` from 22P₂ in the kernel
  (`slopeRepresentation_of_twoSlopePattern`) and from 22P (`slopeRepresentation_of_fixedPrimePattern`).
- From 22P_AP, `SlopeRepresentation` (with field 2′) needs three new Lean pieces. First, field 2′
  in `GoodSlope`. Second, a new `part1` in `pole_input_valuations`: field `old` is used only there,
  at `PoleValuations.lean:126`, and `GoodSlope.old_le_Cp` has no consumer. Third, a weak
  approximation that hits a residue class at the primes of `S_pole`.

So the hypothesis becomes cheaper only once these pieces are kernel-checked. Before that, the
step from the hypothesis to the slope representation is paper mathematics. The note's Route 1
plans exactly this work; the table should say that its rows for Lemma P and Proposition AP are
"to be formalized", not part of the trust base.
