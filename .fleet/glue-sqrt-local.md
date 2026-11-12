# glue-sqrt-local (final note)

**Main result.** Both Galois-theoretic halves of B2's local square-root criterion are proved in Lean,
and so is the group-theoretic step for every prime `p`, including 2. No `sorry`; `#print axioms`
shows only `propext`, `Classical.choice`, `Quot.sound`. Report: `docs/research/glue-sqrt-local.md`.

What compiles (`lake env lean`, 2026-11-12 ~00:06 PST):
- `scratch/glue-sqrt-local/SqrtLocal.lean` (ramified half and finite model):
  - `cyclotomic_prime_pow_irreducible_padic`: `Φ_{p^{n+1}}` is irreducible over `ℚ_p` (Eisenstein over
    `ℤ_p`, then Gauss).
  - `galEquivUnits`: `Gal(L/ℚ_p) ≃* (ℤ/p^{n+1})ˣ`. `finrank_eq_totient`.
  - `tauNeg`: `τ₋₁`, acting by `ζ ↦ ζ⁻¹`.
  - `gal_sqrt_criterion` (`p` odd): a character is `2ψ` iff it kills `τ₋₁`.
  - `gal_sqrt_criterion_lower` (every `p`): the same for characters factoring through `μ_{p^n}`.
  - `sqrt_criterion_finite` (every `p`): the criterion on the model `(ℤ/p^{k+1})ˣ × ℤ/2f → (ℤ/p^k)ˣ × ℤ/f`.
- `scratch/glue-sqrt-local/Unramified.lean` (unramified half; `L/ℚ_p` finite Galois):
  - `isLocalRing_integralClosure`: the integral closure of `ℤ_p` in `L` is local (Mathlib's spectral norm).
  - `exists_frobenius`: there is `σ` with `σζ = ζ^p` on roots of unity of order prime to `p`
    (Mathlib's `IsArithFrobAt`).
  - `pow_frobenius`: every element acts as `ζ ↦ ζ^{p^n}` on those roots of unity.
  - `range_autToPow_eq_zpowers'`: the image in `(ℤ/m)ˣ` is `⟨p⟩`.
  - `finrank_eq_orderOf`: `[ℚ_p(μ_m):ℚ_p] = ord_m(p)`. `isCyclic_gal`: its Galois group is cyclic.

What remains (not proved):
1. Disjointness: `Gal(ℚ_p(μ_{p^k m})/ℚ_p) ≅ (ℤ/p^k)ˣ × ⟨p⟩`, that is, the degree bound
   `≥ φ(p^k)·ord_m(p)`. It needs `e ≥ φ(p^k)` for `ζ_{p^k} − 1`, plus `e·f = [L:ℚ_p]`
   (Mathlib `sum_ramification_inertia`; `S` local is now proved). SPECULATIVE: 150-250 lines.
2. Plumbing from `G_{ℚ_p}` to a finite quotient: factoring a continuous character through
   `Gal(M/ℚ_p)` and inflating `ψ` back.
3. The level change `m → p^{2f} − 1` in the unramified part.

With item 1, `sqrt_criterion_finite` applies to the genuine Galois group, and items 2-3 assemble
pkg-I6's B2 statement from leaf I6.3 (local Kronecker-Weber). No special-casing to quadratic or
quartic characters was needed.
