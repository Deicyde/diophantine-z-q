# rv-tyz-inputs: adversarial review of the Tian–Yuan–Zhang inputs of Proposition N

Scope: the seven inputs I1–I7 (`docs/research/nt-tyz.md` §4.2) from which Proposition N (nt-tyz §4.1) is
proved: for squarefree `n ≡ 5 (mod 8)`, `𝓛(n) = 0 ⟹ T_5a(n) ≡ T_5b(n) ≡ 0`, hence `T_5b(n)` odd ⟹
`ord_{s=1} L(E_n, s) = 1`. For each input this note reads TYZ's printed proof in the arXiv source
(`~/tyz-src/Period7.tex`, arXiv:1411.4728v1, read-only; line numbers `Lnnnn`) down to the published results it
cites, and tests what can be tested numerically. Earlier reviews: rv-nt-tyz compared the quotations of I1–I7
with the source; rv-prop-n checked the deduction from I1–I7. Neither re-derived the proofs of the inputs (§5).
Scripts and outputs: `scratch/rv-tyz-inputs/`; step log: `scratch/rv-tyz-inputs/log.md`.

Marks: **VERIFIED** (re-derived here by hand from the cited statements, or established by a computation whose
script is named), **STANDARD** (a published theorem whose hypotheses hold as used), **SPECULATIVE** (an argument
or expectation not proved here). TYZ's numbering follows nt-tyz (one counter per section); where it matters the
LaTeX label is given.

> **Locator correction (2026-11-12, loc-adopt).** The convolution lemma of input I2 (L1062–1066),
> called "Lemma 2.8" when this review was written, is printed as **Lemma 2.9**; the symmetry lemma
> (`lem2.6`, L1009), called "Lemma 2.7", is **Lemma 2.8**. nt-tyz's count of the shared §2 counter
> skipped Definition 2.7 (L842). VERIFIED for arXiv v1 by recounting `Period7.tex`; the journal has
> the same numbers per the locator audit `docs/research/locators.md` (AI agents, 2026-11-12). The
> numbers below are corrected in place. The same audit read the typeset journal text: arXiv
> Theorem 1.2 is journal **Theorem 1.4**, still with "all `d_i > 1`". Line numbers are unchanged
> and no verdict of this review changed.
> Also corrected 2026-11-12 (loc-adopt, by the same recount of `Period7.tex`'s §3 counter, VERIFIED; not in the audit): `char'` (L1868) is **Lemma 3.14** and `multiples1` (L1919) is **Lemma 3.15**; this note formerly called them Lemma 3.8 and Lemma 3.9. Proposition 3.8 (`heckeaction5`) and Corollary 3.9 (`integral5`) are unchanged. `docs/research/tyz-t1.md` (outside this task's scope) still calls `char'` "Lemma 3.8".

## Verdict

| input | TYZ result | verdict |
|---|---|---|
| I1 | recursion of §3.1 (L1320–1327); `ε`-classes of Theorem 3.3 | **holds as printed** (the `ε`-classes are proved by Lemma 3.15 (`multiples1`), re-derived here) |
| I2 | Lemma 2.9 with Proposition 2.3 | **holds with repairs**: quote it modulo 2 (factor `w_K = 3` at `m = 3`, rv-nt-tyz B1, confirmed); Theorem 2.1 is false for ordered pairs at `m ≡ 3`, harmless for Lemma 2.9 (new) |
| I3 | Theorem 3.5, first assertion (L2343–2380) | **holds as printed, modulo one unprinted computation** in Theorem 3.3 (the explicit Gross–Zagier constant, "computations similar to … Theorem 2.1"). Proposition N needs only part of that constant (§2.3); doubtful only to the extent that this computation is unwritten |
| I4 | Lemmas 3.16, 3.18 | **holds as printed**; proofs re-derived; verified numerically on 8 fields up to degree 64 |
| I5 | Lemma 3.21(1), (4) | **holds as printed**, with two harmless imprecisions; its proof cites Theorem 3.6, whose explicit 2-adic matrix computations were verified by computer (one sign misprint, harmless) |
| I6 | Proposition 3.2(1) | **holds as printed**; re-derived, and verified on 8 fields |
| I7 | definition of `𝓛(n)` (L338–345), root number (Birch–Stephens) | **holds** (STANDARD); consequence verified on 41 samples, `ω(n)` up to 7 |

**Overall.** Proposition N depends on TYZ only through statements whose printed proofs are complete and correct
as far as this review can judge, with one exception of exposition: the exact constant in Theorem 3.3
(`P_χ = ε 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)`) is asserted after "computations similar to that in the proof of
Theorem 2.1", which are not printed (L2014–2015). Proposition N is insensitive to most of that constant: any
factor depending on `d₀` alone, and the uniform factor `2^{h₂(n)}`, drop out (§2.3, VERIFIED). What it needs is
that the factor attached to `d₁` is `𝓛(d₁)` up to a 2-adic unit, and that factor comes from the same
power-of-2 bookkeeping that Theorem 2.1 prints in full and that the numerics of I2 confirm (§3.1). Neither the
false convention of Theorem 1.2 (journal Theorem 1.4; the trivial factor `d₁ = 1`) nor the sketched Proposition 3.4 enters the proof
of any input (§1.8). Misprints found here, all harmless: the sign in one matrix decomposition of
Proposition 3.8 (`heckeaction5`), `(4P)^c = 4P` for `−4P` in Lemma 3.15 (`multiples1`), the factor `w_K` in
Lemma 2.9, and Theorem 2.1 read for ordered pairs at `n ≡ 3`.

**What would settle the residual doubt.** Write out the explicit Gross–Zagier computation for
`(E_{K_n}, χ_{d₀,d₁})` with TYZ's Theorem A.9 (`EGZ`, L3062) and check that the constant is uniform in `χ`;
or read the journal version (Asian J. Math. 21 (2017)) to see whether the referee asked for it (§6).

## 1. The inputs, one by one

### 1.1 I1: the recursion and the `ε`-classes

*As used.* `P(n) := Z(n) − Σ ε(d₀, d₁)𝓛(d₁)P(d₀)` over `n = d₀d₁`, `d₀ ≡ 5, 6, 7`, `d₁ ≡ 1, 2, 3 (mod 8)`,
`d₁ > 1` (L1320–1327), with `ε(d₀, d₁) ≡ 1 (mod 2ℤ[i])` on the classes `(5, 1)`, `(7, 1)`, `(7, 3)` (the value at
`(5, 3)` is not used; rv-prop-n §4.3).

*Status of the text.* The recursion is a definition. Its two ingredients are proved elsewhere:

- `𝓛(d₁) ∈ ℤ` (Theorem 1.1, i.e. I2's recursion; see §1.2).
- The `ε`-classes are part of Theorem 3.3. Its proof (L1865–2023): Lemma 3.14 (`char'`) restricts `χ` to
  `χ_{d₀,d₁}`; Lemma 3.15 (`multiples1`) shows `4P(d₀, d₁) ∈ A(ℚ(√−d₀))^−` except for `(5, 3)`, where
  `4P(d₀, d₁) ∈ A(ℚ(√d₀))^− = [i]A(ℚ(√−d₀))^−`; then Gross–Zagier and Kolyvagin make `E(K_{d₀})^−` of rank 1 when
  `L′ ≠ 0`, so `ε̄P_χ` and `𝒫(d₀)` are proportional, and equal heights fix the proportionality constant up to
  sign. Hence `ε ∈ {±1}`, resp. `{±i}`.

*Checked here* (VERIFIED by hand): the case analysis of Lemma 3.14 (for `n ≡ 5` only `(5, 1)`, `(7, 3)` occur;
for `n ≡ 7` only `(7, 1)`, `(5, 3)`); in Lemma 3.15, the fields `K_{d₀,d₁}`, the actions of `c`, `τ`, `cτ` on
them, `χ(σ_ϖ) = −1 ⟺ d₁ ≡ 3` for `n ≡ 7`, and the identity `[i]A(ℚ(√d₀))^− ⊂ A(ℚ(√−d₀))^−` (Galois
equivariance of `[i]P`, case by case). One misprint: in the case `d₁ = 1` the proof says `(4P)^c = 4P`;
the preceding lines give `(4P)^c = −4P`, which is what the conclusion `4P ∈ A(K_n)^−` needs (new, harmless).

The inclusion `Z(d₀), P(d₀) ∈ A(ℍ′_n)` for `d₀ | n` (rv-prop-n's correction 3) holds (VERIFIED). For
`d₀ ≡ 5`, `Z(d₀) ∈ A(H′_{d₀})`, and `H′_{d₀}` is one of the factors of `ℍ′_n` (L1320). For `d₀ ≡ 7`,
`H′_{d₀} = H_{d₀}` is not a factor, but `σ = 1` and `Φ₀ = 2Cl_{d₀}`, so `Z(d₀)` is fixed by `Gal(H_{d₀}/L_{d₀})`
and lies in `A(L_{d₀}) ⊂ A(L_n(i))`.

When `𝓛(d₁)𝒫(d₀) = 0`, Theorem 3.3 does not determine `ε`. Any choice in the stated class keeps I3 true,
since `P(d₀)` is then torsion and changing `ε` changes `P(n)` by torsion (VERIFIED). Lemma N2 uses only the class.

*`d₁ = 1` / Proposition 3.4.* The recursion writes `d₁ > 1` explicitly and its factors are ordered by class.
Not touched.

**Verdict: holds as printed.**

### 1.2 I2: Lemma 2.9 with Proposition 2.3

*As used* (Lemma N1, modulo 2). For odd squarefree `m ≡ 1, 3 (mod 8)`:
`Σ 𝓛(d₁)𝓛(d₂) ≡ g(m) (mod 2)` over non-ordered `m = d₁d₂` with `d₂ ≡ 1 (mod 8)` (each unordered pair once
when `m ≡ 1`), and `𝓛(1) = 1`.

*TYZ's proof* (L990–1077): the character formula `Σ′ χ_{d₁,d₂}(t) = 2^{h₂(m)} δ_{2Cl}(t)` gives
`Σ′ P(d₁, d₂) = 2^{h₂(m)} Q(m)` (L1001), the sum being over ordered decompositions for `m ≡ 1` and non-ordered
ones for `m ≡ 3`; for `m ≡ 1` the symmetry `P(d₁, d₂) = P(d₂, d₁)` (Lemma 2.8, `lem2.6`) halves it; then
Theorem 2.1 (`P(d₁, d₂) = ±2^{k−a} w_K 𝓛(d₁)𝓛(d₂)`, from the explicit Waldspurger formula, Theorem 4.2) gives the
lemma. Proposition 2.3: `f_m` takes odd values on `(B̂^×)²`, and `t ∈ 2Cl_m` gives `f_m(t) = f_m(s²)`, so
`Q(m) ≡ #2Cl_m = g(m)`.

*Checked here* (VERIFIED by hand):

1. The character count: for `m ≡ 1`, the `2^k` ordered decompositions give `2^k = 2^{h₂}` distinct characters
   (`d₁*d₂* = m`, so `χ_{d₁,d₂} = χ_{d₂,d₁}χ₀`); for `m ≡ 3`, `d₁*d₂* = −m`, so `χ_{d₁,d₂} = χ_{d₂,d₁}` and there are
   `2^{k−1} = 2^{h₂}` characters.
2. The powers of 2: `m ≡ 1`: `h₂ = k`, halving gives `2^{k−1}`; `m ≡ 3`: `h₂ = k − 1`. Theorem 2.1 gives
   `2^{k−1}w_K`. Its own exponent bookkeeping (`|P|² = 2^{4+c}w_K²(L₁/Ω₁)(L₂/Ω₂)` against
   `𝓛(d)² = L/(2^{2k(d)−2−a(d)}Ω_d)`) gives `2^{2k−2}` for odd `m` (`c = 0`) and `2^{2k}` for even `m` (`c = 1`).
   So Lemma 2.9 holds with `w_K` on the left. It is printed without `w_K`, which matters only at `m = 3`
   (`w_K = 3`) and at `m = 1`, where the derivation gives `2^{−1}` and the lemma is not used. This is
   rv-nt-tyz's B1, confirmed. Modulo 2 in `ℤ_(2)` the odd factor is harmless.
3. Lemma 2.8 (symmetry, `m ≡ 1`): `g₀ = ai + bj + (c + √m)k` conjugates `τ(√−m)/√m` to `k`
   (`v g₀ = −m + √m vk = √m g₀ k`); `Nrd g₀ = 2(m + c√m)` with `m + c√m ≡ 1 (mod 4)`, so `χ₀(g₀) = 1`; the other
   solutions are `g₀(u + vk)` with norms `u² + v²`. Correct.
4. *New, harmless.* The proof of Theorem 2.1 says that `χ_{d₁,d₂}` is trivial on `K_{m,2}^×` iff `d₂* ≡ 1 (mod 8)`.
   For `m ≡ 3`, `K_{m,2} = ℚ₂(√5)` also contains `√d₂*` when `d₁* ≡ 1 (mod 8)`. So Theorem 2.1 is false read
   for ordered pairs at `m ≡ 3`: `P(1, 3) = P(3, 1) ≠ 0` (it is `χ = 1`), although `d₂ = 3 ≢ 1`. It is true for
   the non-ordered pair, with the factor `≡ 1` put second, and that is how Lemma 2.9 uses it.

*Not re-derived:* Theorems 2.4 and 2.6 (explicit primitive test vectors; `f_δ = ±1` on `1 + 2O_{B,2}`), the
explicit Waldspurger formula (Theorem 4.2, from Yuan–Zhang–Zhang's Theorem 1.4 and local computations in §4)
and the Petersson-norm constants. A wrong power of 2 anywhere in them would break the integrality of `𝓛` or
the congruence of Lemma N1. The computation of §3.1 tests both, on 30 values.

*`d₁ = 1` / Proposition 3.4.* Lemma 2.9 says `d₁, d₂ > 0` and includes `d₂ = 1` explicitly; the meaning of
"non-ordered" is forced by the derivation (halving by symmetry). Theorem 1.1's sentence "`d_i > 1`" agrees
with the set-partition reading (Lemma N1). Not touched.

**Verdict: holds with the repair "quote Lemma 2.9 modulo 2 (in `ℤ_(2)`)"**, plus the remark on Theorem 2.1.

### 1.3 I3: Theorem 3.5, first assertion

*As used.* `P(n)` and `𝒫(n)` are equal in `A(ℍ′_n) ⊗ ℚ`; in particular `𝓛(n) = 0 ⟹ P(n)` is torsion.

*TYZ's proof* (L2343–2380). Summing `P_χ` over the characters of `Cl_n` gives `2^{h₂(n)} Z(n)` (character
formula; `Φ₀ = Φ ∩ 2Cl′_n`); only the `χ_{d₀,d₁}` contribute modulo torsion (Theorem 3.3, first part);
substituting `P_χ = ε2^{h₂(n)}𝓛(d₁)𝒫(d₀)` gives the recursion for `𝒫(n)`, the same as for `P(n)`; induction.
Correct given Theorem 3.3 (VERIFIED). Implicit conventions: `ε(n, 1) = 1` (choose the sign of `α_n`) and
`𝓛(1) = 1`.

*The gap.* Theorem 3.3's constant is proved by reducing to the height identity
`ĥ(R_χ) = L′(E_{K_n}, χ, 1)/(2^{2k(n)−2h₂(n)−2−a(n)} Ω_{d₀}Ω_{d₁})` and then: "Apply Theorem A.9 … The proof is
finished by computations similar to that in the proof of Theorem 2.1" (L2014–2015). The reduction itself is
correct (VERIFIED: it needs `ĥ(β_{d₀}) = R_{d₀}/2`, consistent with "`R_n` is twice the Néron–Tate height").
The final computation is not printed. Section 2.3 shows how much of it Proposition N needs.

*`d₁ = 1` / Proposition 3.4.* The proof sums over `d₁ > 0`, including `d₁ = 1`, explicitly. Proposition 3.4
is not used. Not touched.

**Verdict: holds as printed, modulo the unprinted computation in Theorem 3.3.** That computation is routine
and of the same kind as Theorem 2.1, which is printed and checked (§3.1). SPECULATIVE until written out.

### 1.4 I4: Lemmas 3.16 and 3.18

*As used.* `A(ℍ′_n)_tors = A[(1+i)³] = A(ℚ(i))` for odd `n`.

*Lemma 3.16* (L2182–2214). The CM description `F^×\F̂^× ≅ (1 + (1+i)³Ô_F)^×` (`F = ℚ(i)`, class number 1,
the units cover `(O/(1+i)³)^×`); `F(A[4])` is the fixed field of `(1 + 4Ô_F)^×`, a quadratic extension of `F`,
hence `ℚ(ζ₈)`. (TYZ call it the ring class field of conductor 4; it is the ray class field modulo 4. Only the
wording is off.) `A(ℚ(i))` is torsion (`A` and its twist by `−1` have rank 0 over `ℚ`); the stabiliser of a
point of `A[4] ∖ A[(1+i)³]` is `1 + 4Ô_F`. The odd part follows from the argument of Lemma 3.18, Step 1.
VERIFIED.

*Lemma 3.18* (L2230–2342), three steps, each re-derived (VERIFIED):

- Step 1 (no odd torsion). `ℍ′_n` is abelian over `L_n(i)` (which contains every `K_{d₀}`) and unramified
  outside 2 over it. `L_n(i)` is multiquadratic and tamely ramified, so `e_p(ℍ′_n/ℚ) ≤ 2`. But `F(x)/F` is
  totally ramified at `℘` with `e = N℘ − 1 ≥ 4` for `0 ≠ x ∈ A[℘]`.
- Step 2 (`|A(ℍ′_n)[2^∞]| ≤ 16`). Take `p ≡ 3 (mod 8)` inert in every `K_{d₀}` (`d₀ ≡ 5, 6`). Conditions (a)–(c)
  give `(d₀/p) = 1`, checked for `d₀ ≡ 5` (an even number of prime factors `≡ 3 (mod 4)`) and `d₀ ≡ 6`
  (`(2/p) = −1`, `(m/p) = −1`). `p` splits completely in `H_{d₀,4}`. So the residue field is `𝔽_{p²}`, and
  `A(𝔽_{p²}) = A[p+1] ≅ (ℤ/(p+1))²`, whose 2-part is `(ℤ/4)²`.
- Step 3 (`√2 ∉ ℍ′_n`, `n` odd). Locally at 2, `ℚ₂(√−d₀) = ℚ₂(√−5)` as subfields (`d₀/5 ≡ 1 (mod 8)`), and
  `1 + 2ϖ_{d₀} ≡ 1 + 2ϖ₅ (mod 4O)`. So every `(H′_{d₀})_v` lies in an unramified extension of the same field
  `N_{5,4}`, while `N_{5,4}(√2) = M_{5,4}` is ramified over `N_{5,4}`. If no `d₀ ≡ 5` divides `n`, then
  `ℍ′_n = L_n(i)`, whose conductor `4n` is not divisible by 8, the conductor of `ℚ(√2)`.

*Numerics* (VERIFIED, `torsion_H.py`, `out_torsion_H.txt`). `H′_{d₀}` was built as TYZ define it, as the
fixed field of `σ_{1+2ϖ}` in the ring class field of conductor 4. `A(ℍ′_n)_tors ≅ ℤ/4 × ℤ/2` (order 8)
for `n = 5, 7, 13, 15, 21, 39, 85, 165`; the last two have two divisors `d₀ ≡ 5`, and `[ℍ′_n : ℚ] = 32, 64`.
Also `√2 ∉ ℍ′_n` and `i ∈ ℍ′_n`. As a control, `A(H_{d₀,4})_tors = (ℤ/4)²` (order 16), where `√2` is present.

*`d₁ = 1` / Proposition 3.4.* Not involved.

**Verdict: holds as printed.**

### 1.5 I5: Lemma 3.21(1), (4)

*As used.* With one lift `β′` of `β₁ = r_∞(−1)r₂(−2)`: `Z(e)^{β′+1} ∈ g(e)τ((1−i)/2) + ℤτ(1)` for `e ≡ 5`, and
`Z(e)^{β′+1} = g(e)τ(1/2)` for `e ≡ 7`.

*TYZ's proof* (L2504–2560). The fixed field of `2Cl′_n` in `H′_n` is `L_n` (`n ≡ 5, 7`). `β_j` acts on `L_n(i)`
as `σ_ϖ ∘ c`. Hence `α = σ_ϖ c β′^{−1} ∈ 2Cl′_n`, and `Z(n)^α − Z(n) ∈ ℤτ(1)` because `z_n^σ ∈ z_n + {0, τ(1)}`.
The value of `Z(n)^{σ_ϖ∘c+1}` is then "checked easily by Theorem 3.6".

*Checked here* (VERIFIED by hand):

- `σ_ϖ|_{ℚ^ab} = r₂(Nϖ) = r₂(n + 1)`; `(n+1)/(−2) ≡ 1 (mod 4)`, and every quadratic subfield of `L_n(i)` has
  2-conductor dividing 4, so `σ_ϖ = r₂(−2)` on `L_n(i)`. Likewise `6/(−2) = −3 ≡ 1 (mod 4)` for `β₂`.
- `α ∈ Gal(H′_n/K_n)` needs `H′_n/ℚ` Galois (nt-tyz F5, from I6).
- The unprinted last step, for (1): `c` inverts `Cl′_n`, so `c(Z) ≡ −Z + gτ(1)`. `σ_ϖ` sends `z_n` to
  `z_n + τ((1+i)/2)` (Theorem 3.6(1)), and `t ∈ Φ₀ ⊂ 2Cl′_n` fixes `i ∈ L_n`. So
  `Z^{σ_ϖ c} + Z ≡ −gτ((1+i)/2) ≡ gτ((1−i)/2) (mod ℤτ(1))`, in either order of composition. For (4):
  `Φ₀ = 2Cl_n`, and conjugating Theorem 3.6(3) gives `(z^{σ_{ϖ⁵}})‾ = τ(1/2) − z`, so `Z^{σ_{ϖ⁵}c} + Z = gτ(1/2)`.
- Imprecisions (new, harmless): in (1) the equality `Z^{β′₁+1} = Z^{β′₂+1}` is proved only modulo `ℤτ(1)`, and
  only membership is used. For `n ≡ 7`, "`β_j` acts on `L_n(i)` as `σ_ϖ ∘ c`" holds on `L_n` for every `ϖ`,
  which is what the proof uses; on `L_n(i)` it holds only for `ϖ` with unit part `≡ −1 (mod 4)`.

*Theorem 3.6(1), (3) and Proposition 3.2(1), (4)* (L1433–1683, L1788–1859). The chain is: Lemma 3.7
(`coset5`) and Proposition 3.8 (`heckeaction5`), a list of explicit 2-adic matrix decompositions and cusps;
then Corollary 3.9 (`integral5`), `π(ϖ)f_n = f_n + τ((1+i)/2)` and `π(1+2ϖ)f_n = f_n`; then Shimura reciprocity
on `P_n = [h, 1]`; then complex conjugation via `j = [[1,0],[8,−1]]`. The hand steps re-derived here
(VERIFIED): Corollary 3.9 from Proposition 3.8; `z̄_n = −z_n + τ(1)`; `μ₄`-coefficients `α, β, γ` uniquely
determined by one cusp; Proposition 3.2(1), with `Gal(H_{n,4}/H_n) ≅ (ℤ/2)²`, `z^{σ_ϖ²} = z + τ(1)` (`σ_ϖ` negates
`i`), `√2 ∈ H_{n,4}`, `σ_{1+2ϖ}(√2) = −√2`; for `n ≡ 7`, the `W`-eigenvalue `−1` from root number `+1` of `A`,
`[∞]^W = [0]`, and the conjugation step.

*Computations* (VERIFIED, `hecke_matrices.py`, `out_hecke_matrices.txt`, exact sympy, symbolic in
`n = 5 + 8m`). All six decompositions of Proposition 3.8 hold, with right factors in `U` (`32 | c`, `4 | a − d`),
middle factors in `SL₂(ℤ)` and left factors upper triangular. The resulting cusps are `Γ₀(32)`-equivalent to
the printed ones. `ϖ` switches the two components of `X_U` and `1 + 2ϖ` does not; `j² = 1` and `jxj = x̄`.
`ϖ, 1+2ϖ, j, ε` normalise `U₂` (Lemma 3.7(2), "explicit calculations" in TYZ). For `n ≡ 7` (16 values),
`M² = −n`, `O_K ⊂ M₀(32)`, `64 | α − δ`, `ϖ⁵ = (32, 1)` and `W^{−1}jϖ⁵ ∈ U₀(32)₂`. **One misprint**:
`w₀ϖε = D₃G₃(−R₃)`, not `D₃G₃R₃`; since `−R₃ = R₁ ∈ U` and `−I ∈ U`, the cusp `[0]^{ϖε} = [−1/8]` is unchanged.

*External inputs of I5:* facts (1)–(3) at L1383–1404, taken from Tian (Cambridge J. Math. 2 (2014)): the
uniformisation `τ`, the CM Galois action on `A[2^∞]` (main theorem of CM, STANDARD) and the cusp dictionary
(verified in §1.5a); Shimura reciprocity (STANDARD).

*`d₁ = 1` / Proposition 3.4.* Not involved (I5 is about single `Z(e)`).

**Verdict: holds as printed** (with the two imprecisions and the misprint, none affecting the statement).

### 1.5a The cusp dictionary

Fact (3) of L1393–1404, quoted from Tian (2014), says how `i₀ : X₀(32) → A` sends the cusps to
`A[(1+i)³] = τ(½ℤ[i]/(1+i)ℤ[i])`. It fixes the translations `R, S, T` in Proposition 3.8, and hence the
torsion points `τ((1±i)/2)`, `τ(1/2)`, `τ(1)` in Theorem 3.6 and in I5.

*Check* (VERIFIED, `cusp_dictionary.py`, `out_cusp_dictionary.txt`). `A ≅ E = 32a1 : Y² = X³ + 4X` over `ℚ`
(`X = 2x`, `Y = 4y`). `E` is the optimal curve, i.e. `X₀(32)` itself (Manin constant 1, STANDARD). Over `ℚ`,
`i₀` is the modular parametrisation `φ(z) = 2πi∫_{i∞}^z f`, unique up to sign. `Λ_E = c(1+i)ℤ[i]` with
`c = Ω⁺/2`, so `τ(x) = φ`-image of `cx`, and `R/2ℤ` maps onto `E(ℝ)`. PARI's exact modular symbols give
`φ(a/c) = x⁺Ω⁺ + x⁻iΩ⁻`. The resulting `τ`-coordinates `2x⁺ + 2ix⁻` are `[0] ↦ 1/2`, `[1/2] ↦ −1/2`,
`[1/16] ↦ 1`, `[±1/4] ↦ ±i/2`, `[±1/8] ↦ (1±i)/2`. This is TYZ's table exactly, with `τ` (no sign change
needed). The images are the points `(2, ∓4)`, `(0, 0)`, `(−2, ∓4i)` and `(∓2i, 0)` of `E(ℚ(i))`. So the external
input behind Proposition 3.8 holds.

### 1.6 I6: Proposition 3.2(1)

*As used* (for nt-tyz F5, and in Lemma 3.21). For `d ≡ 5`, `H′_d` is the fixed field of `⟨σ_{1+2ϖ}⟩` in the ring
class field `H_{d,4}`, hence Galois over `ℚ` (generalized dihedral, Cox Lemma 9.3, STANDARD).

*Proof* re-derived in §1.5 (VERIFIED). *Numerics*: for every `d₀` of §1.4, `[H_{d₀,4} : ℚ] = 2[H′_{d₀} : ℚ]`,
`√2 ∈ H_{d₀,4}` and `√2 ∉ H′_{d₀}` (`out_torsion_H.txt`). Not touched by `d₁ = 1` or Proposition 3.4.

**Verdict: holds as printed.**

### 1.7 I7: the definition of `𝓛(n)` and the root number

`𝓛(n) = 0` exactly when `ord_{s=1} > 1` (definition, L338–345). The rank-one case of the definition uses
`R_n`, which presupposes `rank E_n(ℚ) = 1` when `ord = 1` (Gross–Zagier–Kolyvagin, quoted by TYZ, STANDARD).
The root number `−1` for `n ≡ 5, 6, 7` is Birch–Stephens (STANDARD). So `𝓛(n) ≠ 0` gives `ord ≤ 1`, and the
order is odd, hence 1.

*Numerics* (VERIFIED, `propn_check.py`). See §3.2.

**Verdict: holds** (STANDARD).

### 1.8 Where the two known problems could enter

- *The convention for `d₁ = 1`* (Theorem 1.2 false as printed). The inputs that involve decompositions are I1
  (`d₁ > 1` written, factors ordered by class), I2 (`d₂ > 0` written, `d₂ = 1` included, "non-ordered"
  forced by the derivation) and I3 (`d₁ > 0` written). None uses Theorem 1.2 or its convention. Theorem 1.1's
  "`d_i > 1`" is consistent with Lemma N1 (set partitions). VERIFIED by reading.
- *Proposition 3.4* (sketched proof). Its proof (L2024–2163) sits between the proof of Theorem 3.3 and the
  torsion lemmas. None of the proofs of Theorem 3.3, Lemmas 3.16–3.18, Lemma 3.21, Theorem 3.6, Proposition 3.2
  or the first assertion of Theorem 3.5 cites it. VERIFIED by reading. The only place TYZ use it is the proof
  of Theorem 3.5(2), which Proposition N replaces by Lemma N2.

## 2. Remarks on the deduction (beyond rv-nt-tyz and rv-prop-n)

### 2.1 Lemma 3.21 needs only one lift for all `e`

rv-prop-n's correction 2 (one `β′` for all `e | n`) is consistent with the source: L2495–2500 allow any lift
to `Gal(ℚ̄/ℚ)`.

### 2.2 The single place where the size of a constant enters

Lemma N2 is a statement modulo 2. Changing the recursion's coefficient `ε𝓛(d₁)` by an even factor changes the
coefficients `c_n(e)`. So Proposition N needs the coefficient exactly as defined, and I3 for that recursion.

### 2.3 What Proposition N needs from Theorem 3.3's constant (VERIFIED)

Suppose Theorem 3.3 held in the form `P_χ = ε 2^{h₂(n)} 𝓛(d₁) λ(d₀) 𝒫(d₀)`, with `λ(d) ∈ ℚ^×` depending on `d`
alone (for example, a different normalisation of `𝒫` through `ρ`). Then, as in TYZ's proof of I3,
`Z(n) = Σ_{d₁>0} ε𝓛(d₁)𝒫′(d₀)` with `𝒫′ = λ𝒫`, and the same recursion shows that `P(n)` represents `𝒫′(n)`.
`𝒫′(n) = 0` iff `𝓛(n) = 0`, so Proposition N is unchanged. The uniform factor `2^{h₂(n)}` cancels the
`2^{h₂(n)}` of the character formula, whatever its origin, provided it is the same for every `χ` of a given
`n`. What remains is the dependence on `d₁`, which must be `𝓛(d₁)` times a 2-adic unit of the stated
`ε`-class. In the height identity this dependence enters only through `L(E_{d₁}, 1)/Ω_{d₁}` and the factor
`2^{2k(d₁)−2−a(d₁)}` of the normalisation of `𝓛(d₁)`. Since `k(d₀) + k(d₁) = k(n)` and `a(d₀) + a(d₁) − a(n)` is
constant (`= 1`), both combine into factors depending on `n` only, exactly as in the proof of Theorem 2.1. The
local factor at 2 of the explicit Gross–Zagier formula depends on `χ₂`, which is trivial for every `χ` that
contributes (Theorem 3.3, first part). So the uniformity in `χ` is structural (SPECULATIVE until the
computation of TYZ's Theorem A.9 is written out; it is the same mechanism that the printed proof of
Theorem 2.1 exhibits and that §3.1 confirms numerically).

## 3. Numerical checks

All PARI 2.17.2 via cypari2; one computation at a time, at most 30 inputs per check.

### 3.1 I2 on samples (`i2_check.py`, `tyzcalc.py`, `out_i2_check.txt`; VERIFIED)

30 odd squarefree `m ≡ 1, 3 (mod 8)` (seeded random, `ω(m) = 1..6`, `m < 3·10⁶`, including `m = 3, 11`). For
every divisor `d ≡ 1, 3 (mod 8)` of every `m` (about 200 values), `𝓛(d)² = L(E_d, 1)/(2^{2k−3}Ω_d)` from
`lfun` is the square of an integer (TYZ Theorem 1.1's integrality, which pins the powers of 2 of Theorem 2.1
and Lemma 2.9). Lemma 2.9 modulo 2 (`Σ 𝓛(d₁)𝓛(d₂) ≡ g(m)`, with 1 to 16 pairs per `m`) and Lemma N1
(`𝓛(m) ≡ Λ(m)`) hold on all 30. `g` was computed independently by Rédei's 4-rank formula (unconditional) and
by `quadclassunit`, and the two agree on every argument. The integer identity with `Q(m)` cannot be tested
without the test vector `f_m`.

### 3.2 I7 consequence: Proposition N on samples (`propn_check.py`; VERIFIED)

*Small `n`, full check* (`out_propn_full.txt`, 30 values chosen by their genus sums only: the 12 smallest with
only `T_5b` odd, 6 small ones with `T_5a` odd, and 12 random ones with `k ≥ 3` in `[6005, 40000)`). All 30 have
`ord_{s=1} = 1`. For 25 of them a generator was found (`ellrank`/`ellheegner` + `ellsaturation`), and
`𝓛(n)² = L′(E_n,1)/(2^{2k−3}Ω_n R_n)` is an integer square with `R_n` = PARI's `ellheight`. With twice that,
`𝓛² = 1/2` on every sample, so TYZ's "twice the Néron–Tate height" is PARI's BSD normalisation. `𝓛(n) = 1` on
24 of them and `𝓛(21885) = 3`. `ρ(n)` was computed from the 2-isogeny `φ_n` of L381–388 (`ρ = 0` for 85 and 365,
otherwise 1). Reading A of Theorem 3.5(2), `v₂(𝓛(n)) ≤ ρ(n)` when `T_5a` or `T_5b` is odd, holds on all 25.
This is a weak test, since `𝓛` is odd throughout.

*Large `ω(n)`* (`out_propn_rank.txt`): the pure row 5b (`T_5b = 1`, `T_5a = 0`, the case CR₃
uses): 11 random squarefree `n ≡ 5 (mod 8)` below `4·10⁷`, 6 with `ω(n) = 6` and 5 with `ω(n) = 7` (largest
`39303381 = 3·13·19·29·31·59`; values used by rv-prop-n excluded). All 11 have `ord_{s=1} = 1` (15–350 s each).
Together with §3.2's first part, 41 samples, none inconsistent with Proposition N. `ω(n) ≥ 8` was not tried
(`n > 10⁸`, conductor `> 3·10¹⁷`).

## 4. Summary of findings

| # | where | finding | effect on Proposition N |
|---|---|---|---|
| T1 | Thm 3.3 proof, L2014–2015 | the explicit Gross–Zagier constant is "computations similar to … Theorem 2.1", not printed | Proposition N needs only its `χ`-uniformity (§2.3); residual doubt, settle by writing the computation |
| T2 | Lemma 2.9 | factor `w_K` missing (rv-nt-tyz B1, confirmed) | none modulo 2 in `ℤ_(2)` |
| T3 | Thm 2.1 and its proof | "trivial on `K₂^×` ⟺ `d₂* ≡ 1 (mod 8)`" incomplete at `n ≡ 3`; the theorem is false for ordered pairs (`P(1,3) ≠ 0`) | none: Lemma 2.9 uses non-ordered pairs |
| T4 | Lemma 3.15 (`multiples1`), case `d₁ = 1` | `(4P)^c = 4P` should be `−4P` | none |
| T5 | Prop 3.8 (`heckeaction5`) | `w₀ϖε = D₃G₃(−R₃)`, sign misprint | none (`−I ∈ U`) |
| T6 | Lemma 3.21 | equality in (1) shown only mod `ℤτ(1)`; for `n ≡ 7`, `β_j = σ_ϖ c` on `L_n` only; last step "checked easily", re-derived here | none |
| T7 | Lemma 3.16 | "ring class field of conductor 4" of `ℚ(i)` should read ray class field mod 4 | none |

No finding affects the statement of any input.

## 5. What the earlier reviews did with these inputs

- **rv-nt-tyz** compared the quotation of each input with the source (all correct, with B1 for I2) and read
  the proofs of Theorem 3.3, Theorem 3.5 (first assertion), Lemma 3.18 and Lemma 3.21, but "not re-verified"
  them (its B4). It computed `𝓛(1) = 𝓛(3) = 1` numerically. So it took I1, I3, I4, I5 as given.
- **rv-prop-n** had no access to the source. It took I1, I3 and I5 as quoted, modelled I2 only modulo 2 in
  its abstract tests, and checked Lemma 3.16 numerically (`A(ℚ) ≅ ℤ/4`, `A(ℚ(i))` of order 8, `A(ℚ(ζ₈)) ≅ (ℤ/4)²`).
  It did not check Lemma 3.18. Its numerics (§5) test the consequence of I1–I7, not the inputs.
- This review is the first to re-derive the proofs of I1–I6 against the source and to test I2, I4 (over the
  fields `ℍ′_n` themselves), I6, and the explicit computations behind I5, by computer.

## 6. Refereed status, and what the arXiv text leaves open

- The journal version (Asian J. Math. 21 (2017), no. 4, 721–774) is refereed. Its text was not read here. Only
  arXiv:1411.4728v1 was read, and every statement above is a statement about that text.
- External inputs of I1–I7 and their status: Waldspurger's formula and the Gross–Zagier formula in the form of
  Yuan–Zhang–Zhang (Annals of Math. Studies 184, 2013; refereed book), used through TYZ's explicit versions
  Theorems 4.2 and A.9 (appendix, proved in TYZ); Gross–Zagier (Invent. Math. 1986) and Kolyvagin (published
  1989/1990), cited by TYZ in published form; Tunnell and Saito (multiplicity one, refereed); Birch–Stephens
  (refereed); Tian, Cambridge J. Math. 2 (2014) (refereed) for the facts (1)–(3) about `X₀(32)`; Rédei
  (refereed).
- Open from the arXiv text alone: (a) whether the journal version prints the computation behind Theorem 3.3's
  constant (T1); (b) whether it corrects T2–T7 and the last sentence of Theorem 1.2; (c) the numbering, since
  Zhang cites "Corollary 1.3" for what is Corollary 1.4 in v1 (nt-tyz §3). Only (a) bears on Proposition N, and
  only through §2.3. (2026-11-12: the AI locator audit `locators.md` read the journal text. On (b), the last
  sentence of Theorem 1.2, now journal Theorem 1.4, is not corrected: "all `d_i > 1`" is kept; on (c), §1 is
  renumbered (1.2 → 1.4) while the convolution stays Lemma 2.9. (a) and T2–T7 were not checked by the audit.)

## 7. Ranking of next steps

1. **Write out Theorem 3.3's constant from TYZ's Theorem A.9.** *Payoff:* removes the residual doubt T1, the
   only gap in the inputs. *Obstacle:* the explicit Gross–Zagier formula has many local factors (Petersson
   norms of `2f_n` on `X_U`, the degree of `φ ∘ f_n`). *First test:* redo the bookkeeping of Theorem 2.1 for
   `|P(d₁, d₂)|²` and check that each factor is uniform in `χ`, then do the same for A.9. *Chance: high*, since
   the structure is the same.
2. **Read the journal version** (or Tian's ICM 2022 survey) for T1–T7. *Chance: medium* (access).
3. **A direct numerical test of Theorem 3.3** on one small `n ≡ 5` with two characters (compute `Z(n)` or
   `P_χ` from the modular parametrisation at CM points). *Payoff:* tests the `χ`-uniformity directly.
   *Chance: medium*; it is a substantial computation (CM points on `X_U` over ring class fields).
