# glue-t32a results log

## Setup
- scratch/glue-t32a/T32a.lean = scratch/glue-b3b/B3b.lean verbatim (glue-b3-unram + glue-conj + glue-b3b),
  followed by the glue-t32a sections (proof of `LeafPush.T32a_TameQuadratic`).

## Proof plan (no finite-level ramification theory)
For odd p, w over p, χ : I_w → ℤˣ continuous:
1. (Kummer generator) ∃ β ≠ 0 with τβ = χ(τ)β for all τ ∈ I_w (ker χ open ⇒ contains
   I_w ∩ Stab(γ) for a primitive element γ of a finite extension; β = Σ_{y ∈ roots} c(y) y^j,
   some j by Vandermonde).
2. (Values) every v(x), x ∈ ℚ̄^×, satisfies v(x)^n = v(p)^m, n ≥ 1 (Newton polygon of minpoly).
3. g = √p; glue-b3b's `exists_inertia_neg` gives τ₀ ∈ I_w with τ₀g = -g.
4. Least n with v(β)^n ∈ v(g)^ℤ is odd (else β^n/g^k is a unit negated by τ₀; inertia acts
   trivially mod w and 2 is a unit).
5. For τ ∈ I_w: β^n/g^k is a unit, so χ(τ) = (τg/g)^k. Hence χ ∈ {1, η_g}. η_g ≠ 1 and continuous.
