# glue-vigneras (task report)

**Main result.** Vignéras' local normalizer facts used by A3(a) are proved in Lean
(`scratch/glue-vigneras/Local.lean`, compiles, no sorry, axioms propext/Classical.choice/Quot.sound),
over Mathlib's `ℍ[ℚ_[p], 2, 0, -3]` and N5's concrete order `𝒪_p` = ℤ_p-span of (1, i, (1+j)/2, (i+ij)/2):

- p = 2, 3: `𝒪_p = {x : nrd x ∈ ℤ_p}` (`mem_Op_iff_nrd_two/three`; so N5's 𝒪 is the valuation ring, maximal at 2, 3),
  the normalizer of `𝒪_p` is all of `B_p^×` (`normalizerOp_eq_univ`), and `[B_p^× : ℚ_p^×𝒪_p^×] = 2`
  (`index_scalOpUnits`, `vigneras_local`).
- every prime p, every n: `N_{GL_n(ℚ_p)}(M_n(ℤ_p)) = ℚ_p^× GL_n(ℤ_p)` (`split_normalizer_iff`).

Proofs are elementary (anisotropic binary forms mod p + valuation parity; for split primes,
conjugating E_ij after scaling by the largest entry). Published form stated in
docs/research/glue-vigneras.md §2 (Vignéras LNM 800 Ch. II; Voight GTM 288 Ch. 13, 23; numbers UNVERIFIED).

**Remains (open glue, elementary):** (1) `𝒪_p ≅ M₂(ℤ_p)` at p ∤ 6 (explicit Hensel splitting, three
cases) to apply the split theorem to N5's order; (2) the adelic product formula
`|N/(𝔸_f^*K₀)| = ∏_p local index = 4` over `FiniteAdeleRing`; (3) the global index
`[N_B(𝒪) : ℚ^×𝒪^×] = 4` (not on A3's critical path). Deliverables: docs/research/glue-vigneras.md,
scratch/glue-vigneras/{Local.lean, log.md}.
