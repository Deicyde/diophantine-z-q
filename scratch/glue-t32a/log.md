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

## Results (all VERIFIED by `lake env lean scratch/glue-t32a/T32a.lean`, Lean 4.35.0 / Mathlib v4.35.0,
## 2026-11-12 16:53 PST: 0 errors, no `sorry`, no `axiom`, ~21 s)
- `inertia_val_sub_lt_one`: τ ∈ I_w, z ∈ w ⇒ v(τz − z) < 1.
- `not_inertia_neg`: p odd, τ ∈ I_w, v(z) = 1 ⇒ τz ≠ −z.
- `val_int_eq_pow`, `val_rat_eq_zpow`: v(r) = v(p)^e (r ∈ ℤ∖0), v(q) = v(p)^m (q ∈ ℚ^×).
- `val_pow_eq_zpow`: x ∈ ℚ̄^× ⇒ ∃ n > 0, m ∈ ℤ, v(x)^n = v(p)^m (Newton polygon of minpoly).
- `exists_kummer`: χ : I_w →* ℤˣ continuous ⇒ ∃ β ≠ 0, ∀ τ ∈ I_w, τβ = χ(τ)β.
  (Krull basis `krullTopology_mem_nhds_one_iff`, `Field.exists_primitive_element`, roots of
  minpoly, `Matrix.det_vandermonde_ne_zero_iff`, `Matrix.eq_zero_of_mulVec_eq_zero`.)
- `char_eq_sgn_zpow`: p odd, g² = p, τ₀ ∈ I_w with τ₀g = −g ⇒ every continuous χ equals
  τ ↦ (τg/g)^k for some k ∈ ℤ.
- `etaG`, `etaG_continuous`: η_g(τ) = τg/g as a continuous I_w →* ℤˣ.
- `t32a : LeafPush.T32a_TameQuadratic` (statement `diff`-identical to Leaves.lean L11927-11932; defs
  GQ, IsAtPrime, inertiaQ identical too).
- `leafB3a : LeafB3a`, `unramified_outside_noLeaf` (= `unramified_outside_t32a t32a`).
- `#print axioms` for exists_kummer, val_pow_eq_zpow, char_eq_sgn_zpow, t32a, leafB3a,
  unramified_outside_noLeaf: [propext, Classical.choice, Quot.sound]. The 14 inherited lines unchanged.
- Not used: higher ramification groups, structure of tame inertia, finite-level e/f, Gauss sums.
