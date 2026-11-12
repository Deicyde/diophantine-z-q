# glue-sqrt-local: the local part of B2's square-root criterion

Status: research note (task glue-sqrt-local, 2026-11-11/12). Lean: `scratch/glue-sqrt-local/SqrtLocal.lean`
(ramified half and finite model) and `scratch/glue-sqrt-local/Unramified.lean` (unramified half). Both
are self-contained; `CycloPadic.lean`, `SqrtFinite.lean`, `Frob.lean` and `Local.lean` are the pieces
they merge.
Results log: `scratch/glue-sqrt-local/log.md`. No file under `ZInQKernel/`, `blueprint/`, or another
task's notes or scratch was edited.

Marks: **VERIFIED** means compiled or read in a source. **STANDARD** means a published theorem.
**SPECULATIVE** means an assessment. Locators from memory are UNVERIFIED.

## Main result

**Both halves of the Galois-theoretic input to B2's local square-root criterion are proved in Lean.
So is the group-theoretic step, for every prime `p` including `p = 2`.**

- Totally ramified half: `Φ_{p^{n+1}}` is irreducible over `ℚ_p`, and `Gal(ℚ_p(μ_{p^{n+1}})/ℚ_p) ≅ (ℤ/p^{n+1})ˣ`.
  The square-root criterion holds on this genuine Galois group for every `p`: for odd `p`
  directly (`gal_sqrt_criterion`), and for all `p`, including `2`, for characters factoring
  through the action on `μ_{p^n}` (`gal_sqrt_criterion_lower`).
- Unramified half, for `p ∤ m`:
  - `Gal(L/ℚ_p)` maps onto `⟨p⟩ ⊆ (ℤ/m)ˣ`, by the Frobenius `ζ ↦ ζ^p`. This holds for every
    finite Galois `L/ℚ_p` containing a primitive `m`-th root of unity.
  - `[ℚ_p(μ_m):ℚ_p] = ord_m(p)`, and the Galois group is cyclic.
  - On the way: the integral closure of `ℤ_p` in a finite extension of `ℚ_p` is a local ring
    (through Mathlib's spectral norm).

**Not proved:**
- the linear disjointness of `ℚ_p(μ_{p^k})` and `ℚ_p(μ_m)`, that is,
  `Gal(ℚ_p(μ_{p^k m})/ℚ_p) ≅ (ℤ/p^k)ˣ × ⟨p⟩`. It needs the fundamental inequality `e·f ≤ [L:ℚ_p]`.
- the plumbing from `G_{ℚ_p}` to finite quotients. See §3.

All theorems below compile with no `sorry`. `#print axioms` shows only `propext`,
`Classical.choice` and `Quot.sound` (VERIFIED, 2026-11-11/12):
- `lake env lean scratch/glue-sqrt-local/SqrtLocal.lean`, 00:06 PST;
- `lake env lean scratch/glue-sqrt-local/Unramified.lean`, 00:00 PST.

Files (each self-contained; scratch files cannot import each other):
- `SqrtLocal.lean`: the ramified half and the finite model. It merges `CycloPadic.lean` and `SqrtFinite.lean`.
- `Unramified.lean`: the unramified half. It merges `Frob.lean` and `Local.lean`.

### Ramified half and finite model (`SqrtLocal.lean`, namespace `GlueSqrtLocal`)

| Statement | Lean name | Status |
| --- | --- | --- |
| `Φ_{p^{n+1}}(X+1)` is Eisenstein at `(p) ⊂ ℤ_p` | `cyclotomic_prime_pow_comp_isEisensteinAt_padicInt` | VERIFIED |
| `Φ_{p^{n+1}}` is irreducible over `ℚ_p`, for every prime `p` | `cyclotomic_prime_pow_irreducible_padic` | VERIFIED |
| `Gal(L/ℚ_p) ≃* (ℤ/p^{n+1})ˣ` for every `p^{n+1}`-th cyclotomic extension `L` of `ℚ_p` | `galEquivUnits` | VERIFIED |
| `[L:ℚ_p] = φ(p^{n+1})` | `finrank_eq_totient` | VERIFIED |
| `τ₋₁ := galEquivUnits⁻¹(−1)` acts by `ζ ↦ ζ⁻¹` on `μ_{p^{n+1}}(L)`; `τ₋₁² = 1` | `tauNeg`, `tauNeg_mul_self`, `tauNeg_sq` | VERIFIED |
| **`p` odd: a `ℚ/ℤ`-character `χ` of `Gal(L/ℚ_p)` is `2ψ` for some character `ψ` iff `χ(τ₋₁) = 0`** | `gal_sqrt_criterion` | VERIFIED |
| `actLower : Gal(L/ℚ_p) → (ℤ/p^n)ˣ` (`L` of level `p^{n+1}`) is the action on `μ_{p^n}`: `g x = x^{actLower g}` | `actLower`, `apply_eq_pow_actLower` | VERIFIED |
| **every `p`, including `2`: for a character `χ₀` of `(ℤ/p^n)ˣ`, `χ₀ ∘ actLower` is `2ψ` for a character `ψ` of `Gal(L/ℚ_p)` iff `χ₀(−1) = 0`** | `gal_sqrt_criterion_lower` | VERIFIED |
| `p` odd: `u² = 1` in `(ℤ/p^k)ˣ` forces `u = ±1` | `units_sq_eq_one_odd` | VERIFIED |
| any `p`: `u² = 1` in `(ℤ/p^{k+1})ˣ` forces `u ≡ ±1` in `(ℤ/p^k)ˣ` | `redU_sq_eq_one` | VERIFIED |
| **any `p`, `k`, `f`: a character `χ` of `(ℤ/p^k)ˣ × ℤ/f` becomes `2ψ` on `(ℤ/p^{k+1})ˣ × ℤ/2f` iff `χ(−1, 0) = 0`** | `sqrt_criterion_finite` | VERIFIED |
| a character of an abelian group is `2ψ` iff it kills the 2-torsion (copied from glue-I6-rest) | `exists_half_iff` | VERIFIED |

### Unramified half (`Unramified.lean`)

`L` is a finite Galois extension of `ℚ_p`. The file's ambient hypotheses are
`[Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]`.

| Statement | Lean name | Status |
| --- | --- | --- |
| `y ∈ L` is integral over `ℤ_p` iff its spectral norm is `≤ 1` | `isIntegral_iff_spectralNorm_le_one` | VERIFIED |
| **the integral closure of `ℤ_p` in `L` is a local ring** | `isLocalRing_integralClosure` | VERIFIED |
| `#(ℤ_p/(p)) = p` | `card_quotient_maximalIdeal` | VERIFIED |
| **Frobenius: there is `σ ∈ Gal(L/ℚ_p)` with `σζ = ζ^p` for every root of unity `ζ ∈ L` of order prime to `p`** | `exists_frobenius` | VERIFIED |
| **every `τ ∈ Gal(L/ℚ_p)` acts as `ζ ↦ ζ^{p^n}` on those roots of unity, for one `n`** | `pow_frobenius` (from `pow_frobenius_of_isLocalRing`) | VERIFIED |
| in a domain, `m`-th roots of unity congruent mod a prime `Q ∌ m` are equal | `eq_of_pow_eq_one_of_sub_mem` | VERIFIED |
| `p ∤ m`, `ζ ∈ L` a primitive `m`-th root: the image of `Gal(L/ℚ_p) → (ℤ/m)ˣ` is `⟨p⟩` | `range_autToPow_eq_zpowers'` | VERIFIED |
| `p ∤ m`, `L` an `m`-th cyclotomic extension: `[L:ℚ_p] = ord_m(p)` | `finrank_eq_orderOf` | VERIFIED |
| same: `Gal(L/ℚ_p)` is cyclic | `isCyclic_gal` | VERIFIED |

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

5. **Locality of `S = integralClosure ℤ_p L` (`isLocalRing_integralClosure`).** Mathlib's
   spectral norm `‖·‖_sp` on `L` (`spectralNorm ℚ_[p] L`) is multiplicative because `ℚ_p` is
   complete (`spectralMulAlgNorm`), and it is nonarchimedean (`isNonarchimedean_spectralNorm`).
   - `y` is integral iff `‖y‖_sp ≤ 1`. The forward direction: the minimal polynomial over `ℚ_p` has
     `ℤ_p` coefficients (`minpoly.isIntegrallyClosed_eq_field_fractions'`), and
     `spectralValue_le_one_iff` applies. The converse: lift the minimal polynomial to `ℤ_p[X]`
     (`lifts_and_natDegree_eq_and_monic`).
   - So the units of `S` are the elements of norm `1`. The nonunits have norm `< 1`, so they are
     closed under addition (`IsLocalRing.of_nonunits_add`).
6. **Frobenius (`exists_frobenius`).** The setup:
   - `IsGaloisGroup Gal(L/ℚ_p) ℤ_p S` (`IsGaloisGroup.of_isFractionRing`);
   - `S` finite over `ℤ_p` (`IsIntegralClosure.finite`);
   - a maximal `Q` over `(p)` (`exists_maximal_ideal_liesOver_of_isIntegral`);
   - `S/Q` finite.

   Then Mathlib's `IsArithFrobAt.exists_of_isInvariant` gives `σ`, and
   `IsArithFrobAt.apply_of_pow_eq_one` gives `σζ = ζ^{#(ℤ_p/(p))} = ζ^p`, since `m` is a unit
   of `ℤ_p`.
7. **Every element is a Frobenius power (`pow_frobenius_of_isLocalRing`).** Since `S` is local,
   every `τ` stabilizes `Q`. Its image under `Ideal.Quotient.stabilizerHom` lies in
   `Gal((S/Q)/𝔽_p)`, which is generated by `x ↦ x^p`
   (`FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow`). So `τζ ≡ ζ^{p^n} (mod Q)`.
   Distinct `m`-th roots of unity stay distinct mod `Q`, because `Σ_i x^i y^{m−1−i} = 0` and
   `x ≡ y` would force `m ∈ Q`. Hence `τζ = ζ^{p^n}`.
8. **Corollaries.** `autToPow σ = k` whenever `σζ = ζ^k`. So the image of `autToPow` is `⟨p⟩`.
   It is injective for a cyclotomic extension (`autToPow_injective`), and
   `|Gal| = [L:ℚ_p]` (`IsGalois.card_aut_eq_finrank`) gives `[L:ℚ_p] = ord_m(p)`.

## 2. How B2 uses it (glue, unchanged from pkg-I6 §B2)

A finite-order character `χ` of `G_{ℚ_p}` factors, by I6.3 (`LocalKroneckerWeber`, a leaf),
through `Gal(ℚ_p(μ_n)/ℚ_p)` with `n = p^k m`, `p ∤ m`. Enlarge `n` to `p^{k+1} m'` with
`ord_{m'}(p) = 2 ord_m(p)`. Then `sqrt_criterion_finite` produces `ψ` on the bigger Galois group
when `χ(τ₋₁) = 1`. `ψ` is continuous on `G_{ℚ_p}` because it factors through a finite quotient.
The converse holds because `τ₋₁² = 1`. When `m = 1` and `p` is odd, `gal_sqrt_criterion` is
already the statement over the genuine Galois group, and no enlargement is needed.

Identifying `Gal(ℚ_p(μ_{p^k m})/ℚ_p)` with the model `(ℤ/p^k)ˣ × ℤ/f` uses three things:
- `galEquivUnits` for the `p`-power part;
- `range_autToPow_eq_zpowers'` and `isCyclic_gal` for the prime-to-`p` part (`ℤ/f ≅ ⟨p⟩`,
  `1 ↦ Frobenius`);
- disjointness (§3, item 1). This is the one Galois-theoretic input still missing.

## 3. What remains (not proved)

1. **Disjointness:** `Gal(ℚ_p(μ_{p^k m})/ℚ_p) ≅ (ℤ/p^k)ˣ × ⟨p⟩` through `autToPow` and CRT.
   - The image lies inside `(ℤ/p^k)ˣ × ⟨p⟩`, by `pow_frobenius`. Since `autToPow` is injective,
     equality is the degree bound `[ℚ_p(μ_{p^k m}):ℚ_p] ≥ φ(p^k)·ord_m(p)`.
   - The standard proof of that bound uses the fundamental inequality `e·f ≤ [L:ℚ_p]`, with:
     - `e ≥ φ(p^k)`: `‖ζ_{p^k} − 1‖_sp = p^{−1/φ(p^k)}`, from the product of the conjugates,
       `Φ_{p^k}(1) = p`, and the Galois invariance `spectralNorm_eq_of_equiv`;
     - `f ≥ ord_m(p)`: `μ_m` injects into `S/Q`, by `eq_of_pow_eq_one_of_sub_mem`.
   - Mathlib's `Ideal.sum_ramification_inertia` (for Dedekind domains, so it applies to `S`)
     gives `e·f = [L:ℚ_p]` once `S` is known to have one prime, which is now proved. What is left
     is the computation of `e` for `ζ_{p^k} − 1` (`(p) = (ζ−1)^{φ(p^k)}` in `S`) and the residue
     degree bound.
   - SPECULATIVE: 150-250 lines. Mathlib proves the global analogues in
     `NumberTheory/NumberField/Cyclotomic/Ideal.lean` (`ramificationIdx_eq_of_prime_pow`,
     `inertiaDeg_eq_of_prime_pow`), which may be adaptable.
2. **`p = 2` over the genuine Galois group: done** (`gal_sqrt_criterion_lower`, with
   `apply_eq_pow_actLower` identifying the level change with the action on `μ_{2^n}`).
3. **From `G_{ℚ_p}` to finite quotients.** Factoring a finite-order continuous character
   through `Gal(M/ℚ_p)` for a finite Galois `M ⊂ PadicAlgCl p`, and inflating `ψ` back to
   `G_{ℚ_p}`, uses Mathlib's infinite Galois theory. This is plumbing; it was not written.
4. **The level change in the unramified part.** Moving from `m` to `m' = p^{2f} − 1`, where
   `ord_{m'}(p) = 2f` and `m ∣ m'`, together with compatibility of restriction with
   `ZMod (2f) → ZMod f`. Elementary, but not written.

With item 1, the Galois group of `ℚ_p(μ_{p^k m})` becomes the model `(ℤ/p^k)ˣ × ℤ/f` of
`sqrt_criterion_finite`. Items 3-4 then assemble pkg-I6's statement from I6.3.

No special-casing to quadratic or quartic characters was needed: the proved parts hold for all
finite-order characters (in `ℚ/ℤ`-valued form).
