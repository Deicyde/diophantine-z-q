# glue-sqrt-local: the local part of B2's square-root criterion

Status: research note (task glue-sqrt-local, 2026-11-11). Lean: `scratch/glue-sqrt-local/SqrtLocal.lean`
(the main file, self-contained), plus its two earlier pieces `CycloPadic.lean` and `SqrtFinite.lean`.
Results log: `scratch/glue-sqrt-local/log.md`. No file under `ZInQKernel/`, `blueprint/`, or another
task's notes or scratch was edited.

Marks: **VERIFIED** means compiled or read in a source. **STANDARD** means a published theorem.
**SPECULATIVE** means an assessment. Locators from memory are UNVERIFIED.

## Main result

**The totally ramified (`p`-power) half of the local square-root criterion is proved in Lean, and
so is the whole group-theoretic step, for every prime `p` including `p = 2`.** The
unramified (prime-to-`p`) half is not proved. It needs `Gal(ℚ_p(μ_m)/ℚ_p) = ⟨Frob_p⟩` for `p ∤ m`
and the linear disjointness of `ℚ_p(μ_{p^k})` and `ℚ_p(μ_m)`. See §3 for what Mathlib offers.

All theorems below compile with no `sorry`. `#print axioms` shows only `propext`,
`Classical.choice` and `Quot.sound` (VERIFIED: `lake env lean scratch/glue-sqrt-local/SqrtLocal.lean`,
2026-11-11 23:50 PST).

| Statement | Lean name (namespace `GlueSqrtLocal`) | Status |
| --- | --- | --- |
| `Φ_{p^{n+1}}(X+1)` is Eisenstein at `(p) ⊂ ℤ_p` | `cyclotomic_prime_pow_comp_isEisensteinAt_padicInt` | VERIFIED |
| `Φ_{p^{n+1}}` is irreducible over `ℚ_p`, for every prime `p` | `cyclotomic_prime_pow_irreducible_padic` | VERIFIED |
| `Gal(L/ℚ_p) ≃* (ℤ/p^{n+1})ˣ` for every `p^{n+1}`-th cyclotomic extension `L` of `ℚ_p` | `galEquivUnits` | VERIFIED |
| `[L:ℚ_p] = φ(p^{n+1})` | `finrank_eq_totient` | VERIFIED |
| `τ₋₁ := galEquivUnits⁻¹(−1)` acts by `ζ ↦ ζ⁻¹` on `μ_{p^{n+1}}(L)`; `τ₋₁² = 1` | `tauNeg`, `tauNeg_mul_self`, `tauNeg_sq` | VERIFIED |
| **`p` odd: a `ℚ/ℤ`-character `χ` of `Gal(L/ℚ_p)` is `2ψ` for some character `ψ` iff `χ(τ₋₁) = 0`** | `gal_sqrt_criterion` | VERIFIED |
| `p` odd: `u² = 1` in `(ℤ/p^k)ˣ` forces `u = ±1` | `units_sq_eq_one_odd` | VERIFIED |
| any `p`: `u² = 1` in `(ℤ/p^{k+1})ˣ` forces `u ≡ ±1` in `(ℤ/p^k)ˣ` | `redU_sq_eq_one` | VERIFIED |
| **any `p`, `k`, `f`: a character `χ` of `(ℤ/p^k)ˣ × ℤ/f` becomes `2ψ` on `(ℤ/p^{k+1})ˣ × ℤ/2f` iff `χ(−1, 0) = 0`** | `sqrt_criterion_finite` | VERIFIED |
| a character of an abelian group is `2ψ` iff it kills the 2-torsion (copied from glue-I6-rest) | `exists_half_iff` | VERIFIED |

## 1. What is proved, and how

1. **Irreducibility over `ℚ_p`.** Mathlib proves that `Φ_{p^{n+1}}(X+1) ∈ ℤ[X]` is Eisenstein at
   `(p)` (`cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt`). That gives the coefficient
   conditions in `ℤ_p[X]` after mapping. The constant term is `Φ_{p^{n+1}}(1) = p`
   (`eval_one_cyclotomic_prime_pow`), and `p ∉ (p²)` because `p` is not a unit of `ℤ_p`. Then
   `IsEisensteinAt.irreducible` applies over `ℤ_p`. Gauss's lemma for monic polynomials over the
   integrally closed `ℤ_p` (`Monic.irreducible_iff_irreducible_map_fraction_map`) moves this to
   `ℚ_p`. The substitution `X ↦ X − 1` is removed through the algebra automorphism
   `algEquivAevalXAddC 1`. Mathlib had this only over `ℚ` (`cyclotomic.irreducible_rat`).
2. **Galois group.** With irreducibility, Mathlib's `IsCyclotomicExtension.autEquivPow` gives
   `Gal(L/ℚ_p) ≃* (ℤ/p^{n+1})ˣ`, and `IsCyclotomicExtension.finrank` gives the degree. Any `L`
   works, for example `CyclotomicField (p^(n+1)) ℚ_[p]` or the subfield of `PadicAlgCl p` generated
   by the `p^{n+1}`-th roots of unity.
3. **The criterion on `Gal(L/ℚ_p)` for odd `p`.** Apply `exists_half_iff` to
   `Additive Gal(L/ℚ_p)`. The group is commutative because it embeds in `(ℤ/p^{n+1})ˣ`
   (`galCommGroup`). Its 2-torsion is `{1, τ₋₁}` by `units_sq_eq_one_odd`, an integer argument:
   `p^k ∣ (x−1)(x+1)`, and `p` odd cannot divide both factors.
4. **The finite model for every `p` (`sqrt_criterion_finite`).** With an unramified part, or at
   `p = 2`, the 2-torsion of a finite quotient of `G_{ℚ_p}^{ab}` is bigger than `{1, τ₋₁}`. So one passes to
   the next level. The 2-torsion of `(ℤ/p^{k+1})ˣ × ℤ/2f` maps into `{(1,0), (−1,0)}` in
   `(ℤ/p^k)ˣ × ℤ/f`. At `p = 2` this uses `2^{k+1} ∣ x² − 1 ⇒ 2^k ∣ x ∓ 1`; in `ℤ/2f`, `2a = 0`
   implies `a ↦ 0` in `ℤ/f`. So `χ ∘ proj` is a square iff `χ(−1, 0) = 0`. This is the pkg-I6
   statement once one knows that `Gal(ℚ_p(μ_{p^k m})/ℚ_p) ≅ (ℤ/p^k)ˣ × ℤ/f`, compatibly in the
   levels, with `τ₋₁ ↔ (−1, 0)` and Frobenius `↔ (1, 1)`. There `f = ord_m(p)`, and at the next
   level `m'` one needs `ord_{m'}(p) = 2f`; for example `m' = p^{2f} − 1`, which `m` divides.

## 2. How B2 uses it (glue, unchanged from pkg-I6 §B2)

A finite-order character `χ` of `G_{ℚ_p}` factors, by I6.3 (`LocalKroneckerWeber`, a leaf),
through `Gal(ℚ_p(μ_n)/ℚ_p)` with `n = p^k m`, `p ∤ m`. Enlarge `n` to `p^{k+1} m'` with
`ord_{m'}(p) = 2 ord_m(p)`. Then `sqrt_criterion_finite` produces `ψ` on the bigger Galois group
when `χ(τ₋₁) = 1`. `ψ` is continuous on `G_{ℚ_p}` because it factors through a finite quotient.
The converse holds because `τ₋₁² = 1`. When `m = 1` and `p` is odd, `gal_sqrt_criterion` is
already the statement over the genuine Galois group, and no enlargement is needed.

## 3. What remains (not proved), with the Mathlib inputs located

1. **The unramified Galois group.** For `p ∤ m`, the claim is that `autToPow` maps
   `Gal(ℚ_p(μ_m)/ℚ_p)` onto `⟨p⟩ ⊆ (ℤ/m)ˣ`.
   - `⊇`: a Frobenius `σ` with `σζ = ζ^p` exists by Mathlib's
     `IsArithFrobAt.exists_of_isInvariant` (finite group acting on `S` with invariants `R`,
     `S/Q` finite) and `IsArithFrobAt.apply_of_pow_eq_one` (`σζ = ζ^{#(R/Q∩R)}` when
     `m ∉ Q`) (VERIFIED: the names were read in `Mathlib/RingTheory/Frobenius.lean`). The setup is:
     `R = ℤ_p`, `S` = the integral closure of `ℤ_p` in `L`, `Q` a prime over `(p)`. One also
     needs `Algebra.IsInvariant ℤ_p S Gal(L/ℚ_p)`, finiteness of `S/Q`, and `#(ℤ_p/(p)) = p`.
     SPECULATIVE: 100-200 lines.
   - `⊆`: the inertia group at `Q` is trivial, because distinct `m`-th roots of unity stay
     distinct mod `Q` when `m ∉ Q`. The decomposition group then embeds in the cyclic group
     `Gal((S/Q)/𝔽_p)`, which Frobenius generates. Equality `D = G` needs a unique prime of `S`
     over `(p)`, that is, `S` local (`ℤ_p` henselian, Mathlib `IsAdicComplete.henselianRing`).
     The step from henselian `ℤ_p` to local `S` was not located in Mathlib (SPECULATIVE:
     200-300 lines).
2. **Disjointness.** The claim is `Gal(ℚ_p(μ_{p^k m})/ℚ_p) ≅ (ℤ/p^k)ˣ × ⟨p⟩`: the image of `autToPow`
   in `(ℤ/p^k)ˣ × (ℤ/m)ˣ` (CRT) is the full product. The degree is at least `φ(p^k)·f`, since
   `e ≥ φ(p^k)` from the Eisenstein subfield and `f_res ≥ f` from `μ_m` in the residue field
   (Mathlib `Ideal.sum_ramification_inertia`, `inertiaDeg`). That degree bound is what proves
   disjointness. SPECULATIVE: 150-300 lines on top of item 1.
3. **`p = 2` over the genuine Galois group.** `sqrt_criterion_finite` covers `p = 2` on the model.
   The genuine form also needs restriction `Gal(L_{k+1}/ℚ_2) → Gal(L_k/ℚ_2)` to be compatible with
   `redU`. That is routine (`autToPow` and `ζ_{2^{k+1}}² = ζ_{2^k}`), but it was not written.
4. **From `G_{ℚ_p}` to the finite quotient.** Continuity, and factoring a finite-order character
   through `Gal(M/ℚ_p)` for a finite Galois `M` inside `PadicAlgCl p`, use Mathlib's infinite
   Galois theory (`InfiniteGalois`, `Field.absoluteGaloisGroup`). This is plumbing; it was not
   written.

No special-casing to quadratic or quartic characters was needed: the proved parts hold for all
finite-order characters (in `ℚ/ℤ`-valued form).
