# t30-adelic (fleet report)

**Verdict: both targets proved in Lean. No `sorry`; every main theorem uses only the axioms
`propext`, `Classical.choice`, `Quot.sound` (VERIFIED with `#print axioms`).**

- **T30** (`scratch/t30-adelic/SqrtCrit.lean`):
  `T30.leafSqrtCrit_of_localKroneckerWeber : (∀ p : Nat.Primes, PkgI6.LocalKroneckerWeber p) →
  GlueDescent.B2Q.LeafSqrtCrit`. It also comes in HSyn's `t16a` form (`T30.leafSqrtCrit_of_t16a`)
  and in a per-prime form (`T30.sqrtCrit_at`). So leaf L-B2c (HSyn field `t30`) follows from T16,
  and T30 drops off the list of literature theorems.
  - "If" direction: needs no Kronecker–Weber. The character is inflated from
    `ℚ_p(μ_{p^{k+1}(p^{2f}-1)})`; an element of order ≤ 2 restricts to `1` or `τ₋₁`; then a
    square-root lemma for ℂ^× (ℂ^× is divisible, so Baer's criterion applies).
  - "Only if" direction: the fixed field of `ker φ` is finite and abelian. T16 places it inside a
    cyclotomic field. A lift `σ` of `τ₋₁` satisfies `σ² ∈ ker φ` and `cyc_N(σ) = u`.
- **G1-adelic** (`scratch/t30-adelic/Adelic.lean`, `G1Count.lean`):
  - Objects: `B̂ = Πʳ_p [B_p, 𝒪_p]` (Mathlib's `RestrictedProduct`); `N` = the normalizer of `𝒪̂`
    in `B̂^×`; `K₀ = 𝒪̂^×`; `K₃`; `𝔸_f^×` and `ℤ̂^×` as central scalars.
  - Components of `N` normalize `𝒪_p`, and `x ∈ 𝔸_f^×K₀ ⇔ ∀p, x_p ∈ ℚ_p^×𝒪_p^×`.
  - `N/(𝔸_f^×K₀) ≃* B_2^×/ℚ_2^×𝒪_2^× × B_3^×/ℚ_3^×𝒪_3^×`, so the index is 4. This is the
    restricted product of the local quotients, which are trivial at `p ∤ 6`.
  - `𝔸_f^× ∩ K₀ = ℤ̂^×`, `[K₀ : ℤ̂^×K₃] = 36`, and **`|Γ'| = [N : 𝔸_f^×K₃] = 4·36 = 144`**
    (`G1Adelic.gamma_order`, `gamma_count_Zint`).
  - Generic count lemma: `G1Count.index_count`.
- **What compiles:** all three files with `lake env lean`, in 8–14 s each. They need these modules
  built first: `HDecomp.Sqrt.Disj`, `Descent.B2Glue`, `Vigneras.Local`, `Repo.A1Quaternion`.
- **What remains:**
  - Identifying `B̂` and `𝔸_f^×` with Mathlib's `𝔸ᶠ[ℤ,ℚ]` is not done. Two attempts were stopped
    by Mathlib obstacles: an instance mismatch in `PadicInt.adicCompletionIntegersEquiv`, and kernel
    timeouts when unfolding `Padic.adicCompletionEquiv`. Both are in the log.
  - The rest of A3 (the Hecke action of `Γ'` on `Y₃` over ℚ, and `deg ≤ |Γ'|`) was outside this
    task.
  - Integration: replace HSyn's `t30` with `T30.leafSqrtCrit_of_t16a`. The files can go into
    `ZInQKernel/Contrib/` as new files.
- **Report:** `docs/research/t30-adelic.md`. **Log:** `scratch/t30-adelic/log.md`.
