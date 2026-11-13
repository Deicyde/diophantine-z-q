# tyz-t1: the constant of Tian–Yuan–Zhang's Theorem 3.3 (residual doubt T1)

Scope: the residual doubt T1 of `docs/research/rv-tyz-inputs.md` (on branch `wip/rv-tyz-inputs`). Proposition N
(`docs/research/nt-tyz.md` §4) uses TYZ's Theorem 3.5, first assertion (input I3). Its proof rests on the
formula of Theorem 3.3 (`GZ`, L1299–1311):

```
P_χ = ε(d₀, d₁) 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀),      𝒫(d) = 2^{−1−ρ(d)} 𝓛(d) α_d,
```

for the characters `χ = χ_{d₀,d₁}` of Lemma 3.8 (`char'`). TYZ reduce it to a height identity and then write
only that it follows from Theorem A.9 (`EGZ`) by "computations similar to" Theorem 2.1 (L2015). This note
writes that computation out (§2), says what I3 and Proposition N need from it (§1), and tests it numerically
(§3). Source: arXiv:1411.4728v1, `~/tyz-src/Period7.tex`, cited by line `Lnnnn`. Scripts and outputs:
`scratch/tyz-t1/`. Step log: `scratch/tyz-t1/log.md`.

Marks: **VERIFIED** means derived here by hand from the cited statements, or established by a computation
whose script is named. **STANDARD** means a published theorem. **SPECULATIVE** means not proved here.

## Verdict

**T1 is closed, with the explicit constant.** Theorem 3.3 holds as printed.

1. *What is needed* (§1, VERIFIED). Write `P_χ = ε c(d₀, d₁) 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)` with `c ∈ ℚ^×`. Then
   I3 (the recursion `P(n)` represents `c·𝒫(n)`) holds if and only if `c(d₀, d₁) = ±c(d₀, 1)` whenever
   `𝓛(d₁)𝒫(d₀) ≠ 0`. That is, the constant must not depend on `d₁` once `d₀` is fixed. For `n ≡ 5` this
   compares two different modular curves, `X_U` for `n` and `X₀(32)` for `d₀ ≡ 7`. Uniformity in `χ` for a
   fixed `n`, which is what rv-tyz-inputs §2.3 asked for, is not enough on its own. A uniform factor
   `λ(n) ≠ λ(d₀)` would break the induction. Agreement "up to a 2-adic unit" is not enough for I3 as stated
   either.
2. *The constant* (§2, VERIFIED from A.9). For every contributing `χ`,
   `ĥ(P_χ) = (f_n, f_n) · 16 √|D_n| · L′(E_{d₀}, 1) L(E_{d₁}, 1) / Ω²` on `A`. This gives
   `8, 4, 2 × L′L / (Ω_{d₀}Ω_{d₁})` for `n ≡ 5, 6, 7`, which is exactly TYZ's `2^{2h₂(n)+2+a(n)−2k(n)}`.
   No factor depends on `χ`, `d₀` or `d₁` except through the two L-values. The only place where a local
   factor might have depended on `χ` is the odd primes `p | n`, where `χ_p(ϖ_p) = ±1` varies. There the local
   factor is `|D|_p^{1/2}` for both signs (VERIFIED, Macdonald's formula). So `c(d₀, d₁)² = γ₀`, one
   constant for all `n` and `χ`, and condition 1 holds.
3. *Numerics* (§3, VERIFIED). `P_χ` was computed exactly as a point on `A = X₀(32)` from Heegner points of
   discriminant `−64n`. Over 30 values `n ≡ 5 (mod 8)` (`k ≤ 5`, `h(−64n) ≤ 1120`):
   - all 73 contributing pairs give `P_{χ_{d₀,d₁}}(n) = ±2^{h₂(n)−h₂(d₀)} 𝓛(d₁) P_{χ=1}(d₀)` exactly (modulo
     torsion), with `𝓛(d₁) ∈ {0, …, 7}`, `d₀` of both classes and rank-3 cases included;
   - all 102 characters excluded by Lemma 3.8 give torsion.
   On 20 values `n ≡ 5, 7`, the absolute statement `P_{χ=1}(n) = ±2^{h₂(n)}𝒫(n)` (with `ρ(n)`) also holds
   exactly, so `γ₀ = 1`.

No repair is needed. Proposition N's use of I3 is unaffected. One residual dependence remains, and it is
external and STANDARD: Theorem A.9 is the Yuan–Zhang–Zhang formula made explicit, and TYZ omit its deduction
("almost the same as" Theorem 4.2, L3079). The argument of §2 uses only its shape (which local factors occur
and that they do not involve `χ`), and §3 tests the outcome independently of A.9.

## 1. What I3 and Proposition N need (VERIFIED)

TYZ's proof of I3 (L2343–2380) sums `P_χ` over the characters of `Cl_n`. This gives `2^{h₂(n)} Z(n)`.
Substituting Theorem 3.3 gives `Z(n) = Σ_{d₁ ≥ 1} ε 𝓛(d₁) 𝒫(d₀)`, with the term `d₁ = 1` equal to `𝒫(n)`, and
the recursion `P(n) = Z(n) − Σ_{d₁>1} ε 𝓛(d₁) P(d₀)` then represents `𝒫(n)` by induction.

Suppose instead `P_{χ_{d₀,d₁}} = ε c(d₀, d₁) 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)`. The same computation gives

```
P(n) − c(n, 1) 𝒫(n) = Σ_{d₁>1} ε 𝓛(d₁) ( c(d₀, d₁) 𝒫(d₀) − P(d₀) ).
```

With the induction hypothesis `P(d₀) = c(d₀, 1)𝒫(d₀)`, the summands are `ε𝓛(d₁)(c(d₀,d₁) − c(d₀,1))𝒫(d₀)`.
They lie in the distinct eigenspaces `A(K_{d₀})^−` for different `d₀`, which are linearly independent in
`A(ℚ̄) ⊗ ℚ`. So `P(n)` represents `c(n,1)𝒫(n)` for all `n` if and only if `c(d₀, d₁) = c(d₀, 1)` whenever
`𝓛(d₁)𝒫(d₀) ≠ 0`. A sign can be absorbed into `ε`, and Lemma N2 uses only `ε` modulo 2. Then I3 holds with
`𝒫′ = c(·,1)𝒫`, and `𝒫′(n) = 0 ⟺ 𝓛(n) = 0`. This is rv-tyz-inputs §2.3, with the condition stated
precisely:

- A factor depending on `d₀` alone is harmless (rv-tyz-inputs was right about this).
- A factor uniform in `χ` for fixed `n`, i.e. depending on `n = d₀d₁`, is harmless only if it is constant
  along the divisor chains. For `n ≡ 5` the pairs are `(d₀, d₁) ≡ (5, 1)` and `(7, 3)`. So the constant at
  class 5 with test vector `f_n = f₀ − f₀∘[i]` on `X_U` must equal the constant at class 7 with
  `f_{d₀} = i₀` on `X₀(32)`. This is a statement across levels, not about `χ`.
- A factor `u(d₀, d₁) ∈ ℤ_(2)^× ∖ {±1}` would make I3 false as stated. Proposition N would then survive only
  with a recursion whose coefficients carry `u`, in `A ⊗ ℤ_(2)`, which TYZ do not define. This case does not
  occur (§2, §3).

## 2. The constant, written out (VERIFIED from Theorem A.9)

**The reduction** (L2005–2010). TYZ reduce Theorem 3.3 to
`ĥ(R_χ) = L′(E_{K_n}, χ, 1) / (2^{2k(n)−2h₂(n)−2−a(n)} Ω_{d₀}Ω_{d₁})`, with `R_χ = φ(P_χ)`. The power of 2
depends only on `n mod 8`: `h₂ = k` for `n ≡ 5, 6` (discriminant `−4n`), `h₂ = k − 1` for `n ≡ 7`
(discriminant `−n`). So `2^{2h₂+2+a−2k} = 8, 4, 2` for `n ≡ 5, 6, 7`.

**Theorem A.9** (L3062–3077), for `F = ℚ`, unramified `χ` and a Gross–Prasad test vector `f`:

```
ĥ(Σ_{t ∈ Cl_n} f(P)^t χ(t)) / (f, f)  =  κ² [O_K^× : ℤ^×]² · 4 · L′^{(S)}(½, π, χ) / ((f′, f′) |D|_𝔸^{1/2} (4π)³) · loc₂,
```

Each factor, for `n ≡ 5, 6, 7` and `χ` as in Lemma 3.8:

| factor | value | depends on |
|---|---|---|
| `κ`, `[O_K^× : ℤ^×]` | 1, 1 (`n > 3`) | nothing |
| `|D|_𝔸^{1/2}` | adelic (L2777), so `|D|_𝔸^{−1/2} = √|D|`: `2√n, 2√n, √n` | `n` |
| `L′^{(S)}`, `S = (N,D) ∪ {∞}` | removes only the Euler factor at 2, which is 1 (each `E_d` is additive at 2): `L′(E_{d₀},1) L(E_{d₁},1)` | `χ` (the L-values) |
| `loc₂` (`v = 2`, `ord₂ N = 5`) | ramified (`n ≡ 5, 6`): `2(1 − ½) = 1`; split (`n ≡ 7`): no factor | `n mod 8` |
| `(f′, f′)` | `Ω²/(2^8 π³)`, `Ω = Ω_{1,∞}` (L959–975) | nothing |
| `(f, f) = vol(X_V)^{−1} f∘f^∨` (L3018–3021, measure `dxdy/2πy²`) | `1/4, 1/8, 1/8` | `n mod 8` |

The Petersson norms in the last row:

- `vol X₀(32) = 48/6 = 8`.
- `X_U` is two copies of `X₀(32)`: `SL₂(ℤ) ∩ U = Γ₀(32)`, because `ad ≡ 1 (mod 32)` forces `a ≡ d (mod 8)`.
  So `vol X_U = 16`.
- On the component labelled by the embedding `ι` of `ℚ(i)`, `f₀∘[i]` is `[ι(i)]`. So `f_n = f₀ − f₀∘[i]`
  is `(1 − [i], 1 + [i])` and `f_n f_n^∨ = (1−i)(1+i) + (1+i)(1−i) = 4`. For `n ≡ 6`, `f₀∘[i]` gives 2. For
  `n ≡ 7`, `i₀` gives 1.

With `Ω² = √n Ω_{d₀}Ω_{d₁}`:

```
ĥ_A(P_χ) = (f_n, f_n) · 16 √|D_n| · L′L / Ω² · loc₂  =  (8, 4, 2) · L′(E_{d₀},1) L(E_{d₁},1) / (Ω_{d₀}Ω_{d₁}),
```

for `n ≡ 5, 6, 7`. The ratios are TYZ's `2^{2h₂+2+a−2k}`. In PARI's height `h_P` (the BSD normalisation,
which is TYZ's `R_n`: rv-tyz-inputs §3.2), Theorem 3.3 is equivalent to exactly this identity. Use
`R_{d₀} = h_P(g_{d₀})`, `h_P(α_{d₀}) = 4^{ρ} R_{d₀}/2` (§3.2), and the definitions of `𝓛`. So the printed
constant is A.9's, provided A.9's height is `h_P`. §3.2 confirms this numerically: `γ₀ = 1`.

**Dependence on `χ`.** There are three possible sources, and none contributes beyond the L-values:

- *At 2.* Every contributing `χ` has `χ₂ = 1` (Lemma 3.8 (2)). So the `K₂^×`-invariant `f_n` of
  Proposition 3.1 (`choice`) is the Gross–Prasad vector for every such `χ`, and `L(½, π₂, χ₂)` is the same
  for all of them.
- *At odd `p | n`.* Here `K_p/ℚ_p` is ramified, `π_p` is unramified, and `s = χ_p(ϖ_K) = ±1` depends on `χ`.
  Proposition 4.7 claims `β_p = |D|_p^{1/2}` (L2910–2913, "using MacDonald formula"). Check, with
  `Ψ(ϖ_K) = a_p/(p+1)`:

  ```
  β_p = L(1,ad)(1 − p^{−2}) · (1 − s a_p/p + 1/p) · |D|_p^{1/2}(1 + s a_p/(p+1)),
  (1 − s a_p/p + 1/p)(1 + s a_p/(p+1)) = ((p+1)² − a_p²)/(p(p+1)),
  L(1,ad)^{−1} = ((p+1)² − a_p²)(1 − 1/p)/p²,
  ```

  so `β_p = |D|_p^{1/2}(1 − p^{−2}) p/((p+1)(1 − 1/p)) = |D|_p^{1/2}` for both values of `s` (VERIFIED).
- *Elsewhere.* `π_v` and `K_v` are unramified, and `β_v = 1`.

So `c(d₀, d₁)² = γ₀` for all `n ≡ 5, 6, 7` and all contributing `χ`. Here `γ₀` collects the global
conventions: the height normalisation of YZZ and `Ω² = 32π²(φ, φ)`. The latter is VERIFIED
(`petersson.py`: `Ω²/covol(Λ_{32a1}) = 8`, and `covol = 4π²(φ, φ)` by PARI's `mfpetersson`). Hence
`c(d₀, d₁) = ±c(d₀, 1)`, which is the condition of §1. The two sides of Theorem 3.3 are proportional by
Gross–Zagier and Kolyvagin (rank of `E(K_{d₀})^−` is 1 when `L′ ≠ 0`; STANDARD), so the height identity fixes
`c` up to sign.

**Misprint (new, harmless).** In the proof of Theorem 2.1 the intermediate display at L955 omits the factor
`√|D|`, which comes from the adelic `|Dd²|^{1/2}` in Theorem 4.2. The final formula at L979 needs it and is
right.

## 3. Numerical tests (VERIFIED)

### 3.1 The model

**`n ≡ 5`.** TYZ's embedding (`√−n ↦ [[−1, 1/4], [−4(n+1), 1]]`, L1203–1205) has fixed point the root of
`[16(n+1), −8, 1]`. So `f₀(P_n)` is a Heegner point of discriminant `−64n` (order `ℤ[4√−n]`) on `X₀(32)`.

- On `X_U`, `z_n^{σ_t} = (1 − ψ(t) i) x^{σ_t}`, where `ψ` is the character of `K(i)/K = K(√n)/K`, which is
  unramified.
- The fibres of `Pic(ℤ[4√−n]) → Cl_n` are `Gal(H_{n,4}/H_n) = ⟨σ_{1+2ϖ}, σ_ϖ²⟩` (Proposition 3.2). The first
  fixes `z_n` and the second adds the 2-torsion point `τ(1)`. So `4P_χ = S_χ − i S_{χψ}` exactly, with
  `S_χ = Σ_{Cl(−64n)} χ(Q) φ(τ_Q)`.

**`n ≡ 7`.** `P_{χ=1}(n)` is the sum of the Heegner points `[A, δ, C]`, `32 | A`, `δ² ≡ −n (mod 128)`, of
discriminant `−n`.

**Implementation.** `φ` is the modular parametrisation of `32a1` (Manin constant 1). Points are compared as
elliptic logarithms modulo `Λ`. `heeg.py` picks one form `[32p, B, C]` per class (`p` = 1 or a split prime),
checks that every class is hit, and checks that the q-series has converged. Genus characters are evaluated
at a represented odd `m`.

**The sign of `i`.** There are two candidate vectors, `f₀ ∓ f₀∘[i]`. Only `f₀ − f₀∘[i]` (relative to the
component of `P_n`) makes the characters excluded by Lemma 3.8 vanish (`t21.py`, `out_t21.txt`). That is the
`K₂^×`-invariant vector of Proposition 3.1, and it is used throughout.

### 3.2 Results

**Cross-level identity** (`tmany.py`; `out_tmany1.txt`, `out_tmany2.txt`, `out_tmany3.txt`). The 30 values
of `n ≡ 5 (mod 8)` were 21, 85, 77, 69, 93, 205, 165, 357, 285, 861, 1005, 1365, 221, 445, 365, 141, 237,
213, 253, 301, 565, 2149, 2165, 3269, 8749, 645, 2373, 12597, 23205, 44285. For every `e | n`:

- `e ≡ 5, 7`: Lemma 3.8 excludes `χ_e`. All 102 such `P_χ` are torsion.
- `e = d₁ ≡ 1, 3`, `d₁ > 1`: the unique `m ∈ [−4m₀ − 64, 4m₀ + 64]` with `16 P_χ(n) ≡ m P_{χ=1}(d₀)` modulo
  `Λ` is `m = ±m₀`, where `m₀ = 16 · 2^{h₂(n)−h₂(d₀)} 𝓛(d₁)`. This holds for all 73 pairs. They include:
  - `𝓛(d₁) = 1, …, 7` (`d₁ = 43, 113, 307, 433, 467, 673`) and `𝓛(d₁) = 0` (`d₁ = 41, 65, 323, 1105, 1785, 4641`);
  - `2^{h₂(n)−h₂(d₀)} = 2, …, 32`;
  - `d₀` of both classes, prime and composite;
  - `d₀ = 4199, 2605` of rank 3, where `P_{χ=1}(d₀)` and `P_χ(n)` are torsion.

  `𝓛(d₁)²` was computed from `lfun` and asserted to be an integer square.

**Absolute constant** (`tabs.py`, `out_tabs.txt`). For `d₁ = 1`, Theorem 3.3 says
`P_{χ=1}(n) = ±2^{h₂(n)} 2^{−1−ρ(n)} 𝓛(n) α_n`. The script computes the index of `4P_{χ=1}(n)` over a
generator `α_n` of `A(K_n)^− ≅ A_n(ℚ)`. It gets `ρ` from `4^ρ = 2h(α_n)/h(g_n)` and
`𝓛(n)² = L′(E_n,1)/(2^{2k−3}Ω_n h_P(g_n))`. On `n = 5, 13, 21, 29, 37, 53, 61, 85, 93, 101, 109, 165` and
`7, 15, 23, 31, 39, 47, 55, 71`, the index equals the predicted `2^{h₂+1−ρ}|𝓛(n)|` in all 20 cases (`ρ = 1`
at 21, 93, 165). So `γ₀ = 1`.

**Limits.** The tests are samples of the statement, and the proof for all `n` is §2. `𝓛(n) = 1` on all 20
absolute samples, so the absolute test does not exercise `𝓛(n) > 1`. The cross-level test does exercise
`𝓛(d₁)` up to 7, and that is the part Proposition N uses.

## 4. Consequences for the notes

- rv-tyz-inputs T1: closed. I3 holds as printed, with Theorem 3.3's constant derived (§2) and tested (§3).
- rv-tyz-inputs §2.3 should read as in §1. The needed property is that `c` is independent of `d₁` for fixed
  `d₀`, a statement across levels. Uniformity in `χ` alone, or "up to a 2-adic unit", would not suffice for
  I3. Both properties hold in fact.
- What remains external is Theorem A.9 itself (YZZ's Gross–Zagier formula, refereed, in TYZ's explicit form,
  whose deduction arXiv v1 omits). It is used only for its shape. The numerics of §3 check
  the resulting identity directly, independently of A.9's constant.
