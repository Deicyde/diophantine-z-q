# t30-adelic (fleet report)

**Verdict: both targets proved in Lean, no `sorry`, standard axioms only.**

- **T30** (`scratch/t30-adelic/SqrtCrit.lean`): `T30.leafSqrtCrit_of_localKroneckerWeber :
  (∀ p : Nat.Primes, PkgI6.LocalKroneckerWeber p) → GlueDescent.B2Q.LeafSqrtCrit`. The leaf
  L-B2c (HSyn field `t30`) follows from T16 (`t16a`), so T30 leaves the literature list. The
  "if" direction needs no Kronecker–Weber (inflation from `ℚ_p(μ_{p^{k+1}(p^{2f}-1)})`, ℂ^× divisible);
  "only if": the fixed field of `ker φ` is finite abelian, T16 puts it in a cyclotomic level, a lift
  of `τ₋₁` has `σ² ∈ ker φ` and `cyc_N(σ) = u`.
- **G1-adelic** (`scratch/t30-adelic/Adelic.lean`, `G1Count.lean`): `B̂ = Πʳ_p [B_p, 𝒪_p]`
  (Mathlib `RestrictedProduct`), `N` = normalizer of `𝒪̂` in `B̂^×`, `K₀ = 𝒪̂^×`, `K₃`, `𝔸_f^×`,
  `ℤ̂^×`. Proved: components of `N` normalize `𝒪_p`; `x ∈ 𝔸_f^×K₀ ⇔ ∀p, x_p ∈ ℚ_p^×𝒪_p^×`;
  `N/(𝔸_f^×K₀) ≃* B_2^×/ℚ_2^×𝒪_2^× × B_3^×/ℚ_3^×𝒪_3^×` (index 4); `𝔸_f^× ∩ K₀ = ℤ̂^×`;
  `[K₀ : ℤ̂^×K₃] = 36`; **`|Γ'| = [N : 𝔸_f^×K₃] = 4·36 = 144`** (`G1Adelic.gamma_order`,
  `gamma_count_Zint`); generic count lemma `G1Count.index_count`.
- Compiles: all three files with `lake env lean` (after building `HDecomp.Sqrt.Disj`,
  `Descent.B2Glue`, `Vigneras.Local`, `Repo.A1Quaternion`), ~8-14 s each.
- Remains: identification of `B̂` with `ℍ[𝔸ᶠ[ℤ,ℚ],2,0,-3]` over Mathlib's `FiniteAdeleRing`
  (reindexing + `Padic.adicCompletionEquiv`; not done); the rest of A3 (Hecke action of `Γ'` on
  `Y₃` over ℚ, `deg ≤ |Γ'|`) is outside this task. Integration: replace HSyn's `t30` by the theorem.
- Report: `docs/research/t30-adelic.md`; log: `scratch/t30-adelic/log.md`.
