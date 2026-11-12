# glue-I6-rest (fleet report)

**Main result.** Three of the six glue items left open by pkg-I6 and glue-conductor are proved in
Lean over pkg-I6's definitions, with no `sorry`. `#print axioms` shows only `propext`,
`Classical.choice` and `Quot.sound` (VERIFIED, `lake env lean`, 22:28-22:34 PST). A fourth item is
proved in its group-theoretic core. Report: `docs/research/glue-I6-rest.md`.

- **D4 `artinConductor_le_of_upper`** (`scratch/glue-I6-rest/Conductor.lean`). If `G^v` acts
  trivially for every `v > U ≥ 0`, then `f(V) ≤ dim V·(1+U)`. This is pkg-I6's statement, with
  fewer hypotheses (no DVR is needed). The proof computes on the integral definition of `φ`:
  the integrand is antitone, `G^{φ(b)} = G_b`, and `Σ_{i≤b} |G_i|/|G_0| ≤ 1 + φ(b)`.
- **D3 `sq_principalUnits`** (`I6Base.lean`). Adopted from glue-conductor's Dyadic.lean
  (Hensel).
- **D1 (a), `e ≤ a!`** (`I6Base.lean`). `[SplittingField f : K] ≤ (deg f)!` for separable `f`,
  `e(P) ≤ [L:ℚ]`, hence `e(P) ≤ (deg f)!` when `L` is the splitting field of `f` over `ℚ`. That
  is the hypothesis of glue-conductor's `D1_genuine`. **Caveat:** this is the global form.
  Glazer bounds only the local degree `[F:ℚ_p] ≤ a`, so the local version still needs
  `D_P ≅ Gal(L_P/ℚ_p)` or a Krasner choice of a global field (report §2.2).
- **B2 square-root criterion, core** (`SqrtChar.lean`, `exists_half_iff`). A character
  `Γ → ℚ/ℤ` of any abelian group is twice a character iff it kills `Γ[2]` (Baer injectivity of
  `ℚ/ℤ`).

**What remains (with reason):**
- **The square-root criterion's local part.** It needs `Gal(ℚ_p(μ_{p^k m})/ℚ_p)`, that is, the
  irreducibility over `ℚ_p` of the cyclotomic polynomial, which Mathlib has only over `ℚ`, plus
  the 2-torsion of `ℤ_p^× × ℤ̂`. About 500-1000 lines (SPECULATIVE).
- **`[ε]_p = 0` (cyclic inflation).** Step (b), that the inflated carry cocycle is a coboundary
  on `ℤ/2f`, is explicit and was checked by brute force for `f ≤ 12`. Step (a) is that every
  2-cocycle of `ℤ/f` is cohomologous to the carry cocycle; Mathlib has no inhomogeneous-cochain
  form of it. About 200-400 lines.
- **Frobenius density in `G_ℚ`.** Lifting Frobenius elements to `G_ℚ` needs decomposition
  groups in `\bar ℚ/ℚ`. Recommended instead: state C10 on finite quotients, where the leaf
  `ChebotarevExists` suffices.

Files: `scratch/glue-I6-rest/{I6Base,Conductor,SqrtChar}.lean` and `log.md`.
