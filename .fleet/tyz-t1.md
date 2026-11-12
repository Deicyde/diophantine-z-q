# tyz-t1: the constant of TYZ Theorem 3.3 (residual doubt T1 of rv-tyz-inputs)

**Verdict: T1 is closed, with the explicit constant. Theorem 3.3 holds as printed, and I3 and Proposition N
are unaffected.** Full note: `docs/research/tyz-t1.md`. Scripts and outputs: `scratch/tyz-t1/`.

- **What is needed** (VERIFIED). Write `P_χ = ε c(d₀,d₁) 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)`. The recursion represents
  `c𝒫` if and only if `c(d₀,d₁) = ±c(d₀,1)`, i.e. the constant does not depend on `d₁` once `d₀` is fixed.
  For `n ≡ 5` and the pair `(7,3)` this compares two levels: `X_U` with `f₀ − f₀∘[i]`, and `X₀(32)` with
  `i₀`. This is sharper than rv-tyz-inputs §2.3. Uniformity in `χ` for fixed `n` would not be enough, and
  neither would "up to a 2-adic unit".
- **The constant** (VERIFIED from A.9). `ĥ_A(P_χ) = (f_n,f_n)·16√|D|·L′(E_{d₀},1)L(E_{d₁},1)/Ω²`
  `= 8, 4, 2 × L′L/(Ω_{d₀}Ω_{d₁})` for `n ≡ 5, 6, 7`. This is exactly TYZ's `2^{2h₂+2+a−2k}`. The inputs are
  `(f_n,f_n) = 1/4, 1/8, 1/8` (`vol X_U = 16`, `vol X₀(32) = 8`), the adelic `|D|` (so `√|D|`), and local
  factor 1 at 2. At odd `p | n`, where `χ_p(ϖ) = ±1` varies, the local factor is `|D|_p^{1/2}` for both signs
  (Macdonald). So no factor depends on `χ`, `d₀` or `d₁` beyond the L-values, and `c² = γ₀` is a single
  global constant. `Ω² = 32π²(φ,φ)` was checked with PARI's `mfpetersson`.
- **Numerics** (VERIFIED, PARI). `P_χ` was computed exactly from Heegner points of discriminant `−64n` on
  `X₀(32)`, after reducing TYZ's CM point on `X_U` to such points.
  - On 30 values `n ≡ 5 (mod 8)` (`k ≤ 5`, `h(−64n) ≤ 1120`): all 73 pairs satisfy
    `P_{χ_{d₀,d₁}}(n) = ±2^{h₂(n)−h₂(d₀)}𝓛(d₁)P_{χ=1}(d₀)` exactly. This covers `𝓛(d₁)` from 0 to 7, both
    classes of `d₀`, and rank-3 `d₀`.
  - All 102 characters excluded by Lemma 3.8 give torsion.
  - On 20 values `n ≡ 5, 7`, the absolute `d₁ = 1` statement (with `ρ(n)`) holds exactly, so `γ₀ = 1`.
- **New misprint, harmless.** The intermediate display at L955 (proof of Theorem 2.1) drops `√|D|`. The final
  formula is right.
- **What remains external.** Theorem A.9, i.e. YZZ's Gross–Zagier formula made explicit by TYZ, whose
  deduction v1 omits. It is used only for which factors occur, and the numerics test the resulting identity
  independently of it.
