# glue-vigneras (task report)

**Main result.** Every normalizer fact that A3(a) uses for N5's maximal order `𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩`
in `B = (2,−3)` is proved in Lean. No sorry; axioms are only propext, Classical.choice and Quot.sound. The
statements are over Mathlib's `ℍ[ℚ, 2, 0, -3]` and `ℍ[ℚ_[p], 2, 0, -3]` and N5's concrete lattice:

- **Global** (`scratch/glue-vigneras/Global.lean`), `normalizer_index_four`: `[N_B(𝒪) : ℚ^×𝒪^×] = 4`.
  `ℚ^×𝒪^×` is the kernel of the surjection `N_B(𝒪) → (ℤ/2)²`, `x ↦ (v₂, v₃)(nrd x) mod 2`, with coset
  representatives 1, i, j, ij. The finite computation behind it (`nrd_dvd_six`): a primitive `x ∈ 𝒪` that
  normalizes `𝒪` has `nrd x ∣ 6`. This comes from a ℤ[1/6] certificate (`cert.py`): `6·nₐn_b` is an integer
  combination of the coordinates of `x eₖ x̄`. No class number, strong approximation or local–global step is used.
- **Local** (`scratch/glue-vigneras/Local.lean`): at p = 2, 3, `𝒪_p = {nrd ∈ ℤ_p}`, `N(𝒪_p) = B_p^×` and
  `[B_p^× : ℚ_p^×𝒪_p^×] = 2` (`vigneras_local`). At every p ≠ 2, 3, `N(𝒪_p) = ℚ_p^×𝒪_p^×`
  (`unramified_normalizer`, on N5's order with no splitting needed). For every p and n,
  `N_{GL_n(ℚ_p)}(M_n(ℤ_p)) = ℚ_p^×GL_n(ℤ_p)` (`split_normalizer_iff`).

The published forms are stated in docs/research/glue-vigneras.md §2: Vignéras LNM 800 Ch. II and III, and
Voight GTM 288 Ch. 13 and 23 (theorem numbers UNVERIFIED). L3 is no longer needed as a leaf.

**Remains (open glue):** the adelic bookkeeping of A3: identifying `N/(𝔸_f^*K₀)` with the product of the local
quotients (or, via class number one, with the global quotient proved here), and glue-repo's finite group theory
`|Γ'| = |N/𝔸_f^*K₀|·|K₀/ℤ̂^*K₃|`. A3(b)-(d) are outside this task.

Deliverables: docs/research/glue-vigneras.md; scratch/glue-vigneras/{Local.lean, Global.lean, cert.py,
cert.output.txt, gen_global.py, log.md}.
