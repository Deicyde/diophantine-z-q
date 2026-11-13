# g1-adelic2 (fleet note)

**Main result.** `G1Adelic.FA.gamma_order_AF : (ZAF ⊔ K3AF).relIndex NAF = 144`, i.e. |Γ'| = 144, stated over
Mathlib's `𝔸ᶠ[ℤ,ℚ] = FiniteAdeleRing ℤ ℚ`. Here N is the normalizer of 𝒪̂ = 𝒪 ⊗ ℤ̂ in `ℍ[𝔸ᶠ[ℤ,ℚ],2,0,-3]ˣ`,
ZAF = 𝔸ᶠ^× (central scalars) and K3AF = {u ∈ 𝒪̂^× : u ≡ 1 mod 3𝒪̂}. Axioms: [propext, Classical.choice, Quot.sound].

**Compiles (VERIFIED, lake build).** Two new files:
- `ZInQKernel/Contrib/G1Adelic/FiniteAdele.lean`: `Theta : BA ≃+* ℍ[𝔸ᶠ[ℤ,ℚ],2,0,-3]` (t30-adelic's B̂ = Πʳ_p[B_p,𝒪_p]),
  `quatRP`, `map_Nhat/K0/Zhat/K3`, `relIndex_eq_four_AF` (= 4), `relIndex_K3_AF` (= 36), `gamma_order_AF` (= 144).
- `ZInQKernel/Contrib/G1Adelic/Complements.lean`: `baseChange A : A ⊗[ℚ] ℍ[ℚ,2,0,-3] ≃ₐ[A] ℍ[A,2,0,-3]`,
  `tensorEquivBA : 𝔸ᶠ[ℤ,ℚ] ⊗[ℚ] ℍ[ℚ,2,0,-3] ≃+* BA`, `quotEquivAF : N/(𝔸ᶠ^×K₀) ≃* B_2^×/ℚ_2^×𝒪_2^× × B_3^×/ℚ_3^×𝒪_3^×`,
  `ZAF_inf_K0AF : 𝔸ᶠ^× ∩ K₀ = ℤ̂^×`, `gamma_count_Zint_AF` (144 = 4·36), `OhatAF_eq_span` (𝒪̂ = 𝒪⊗ℤ̂),
  `ZhatAF_eq_range_structureMap`.
Both import main's `ZInQKernel.HDecomp.Textbook.G1Adelic` (no copied scratch code). No sorry, no axiom.

**Route.** Index by `HeightOneSpectrum ℤ`, use Mathlib's `adicCompletion.padicEquiv` behind `irreducible_def`
(no `Padic.adicCompletionEquiv` / `PadicInt.adicCompletionIntegersEquiv`), reindex with `mapAlongRingHom` along
`primesEquiv`, and hide the reindexed witness behind `∃` so that the kernel never sees the cast. No Tau Ceti code was used.

**Remains.** Nothing in scope. No leaf Prop is stated over `FiniteAdeleRing`, so no leaf is closed. G1's `Y₃/Γ' = P¹_j` still needs R1.
Details: docs/research/g1-adelic2.md; log: scratch/g1-adelic2/log.md.
