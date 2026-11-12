# glue-sqrt-disj: disjointness and the level change for B2's local square-root criterion

Status: research note (task glue-sqrt-disj, 2026-11-12). Lean: `scratch/glue-sqrt-disj/Disj.lean`
(self-contained; it merges glue-sqrt-local's `Unramified.lean`, part of its `SqrtLocal.lean`, and this
task's `Ram.lean` and `Level.lean`). Results log: `scratch/glue-sqrt-disj/log.md`. No file under
`ZInQKernel/`, `blueprint/`, or another task's notes or scratch was edited.

Marks: **VERIFIED** means compiled or read in a source. **STANDARD** means a published theorem.
**SPECULATIVE** means an assessment. Locators from memory are UNVERIFIED.

## Main result

**Items (1) and (3) of glue-sqrt-local §3 are proved in Lean. So is the local square-root criterion
over the genuine finite Galois groups `Gal(ℚ_p(μ_N)/ℚ_p)`, for every prime `p` including `2`, with the
level change built in.** Item (2), the passage from `G_{ℚ_p}` to a finite quotient (where I6.3 enters),
is not written; §3 lists exactly what it needs.

1. **Disjointness (item 1).** Let `p ∤ m` and let `L` be a `p^k m`-th cyclotomic extension of `ℚ_p`.
   Then `Gal(L/ℚ_p) ≃* (ℤ/p^k)ˣ × ⟨p⟩ ⊆ (ℤ/p^k)ˣ × (ℤ/m)ˣ` through the action on `μ_{p^k}` and on
   `μ_m`, and `[L:ℚ_p] = φ(p^k) · ord_m(p)`.
2. **Degree bound, from Mathlib's fundamental identity.** For every finite Galois `L/ℚ_p` containing a
   primitive `p^k`-th and a primitive `m`-th root of unity: `φ(p^k) · ord_m(p) ≤ [L:ℚ_p]`. This is the
   input glue-sqrt-local lacked. The fundamental inequality `e·f ≤ [L:ℚ_p]` is already in Mathlib, in
   its Galois form (`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`). Only `e` and `f`
   had to be bounded.
3. **Level change (item 3).** `ord_{p^n−1}(p) = n`, and `m ∣ p^{t·ord_m(p)} − 1`.
   `galToProd` is compatible with restriction: on the Galois groups it becomes reduction mod
   `p^{k'}` and mod `m'`.
4. **The criterion at a finite level, for every `p`.** Let `K = ℚ_p(μ_{p^k m}) ⊆ L = ℚ_p(μ_{p^{k+1} m'})`
   with `m ∣ m'` and `ord_{m'}(p) = 2·ord_m(p)` (for example `m' = p^{2f} − 1`). Let `τ ∈ Gal(K/ℚ_p)` act by
   `ζ ↦ ζ⁻¹` on `μ_{p^k}` and trivially on `μ_m`. Then a `ℚ/ℤ`-character `χ` of `Gal(K/ℚ_p)`,
   inflated to `Gal(L/ℚ_p)`, is twice a character of `Gal(L/ℚ_p)` iff `χ(τ) = 0`.

Everything below compiles with no `sorry`. `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound` for every listed theorem (VERIFIED: `lake env lean scratch/glue-sqrt-disj/Disj.lean`,
00:53 PST, 2026-11-12; `Ram.lean` 00:44 and `Level.lean` 00:45 also compile standalone).

### Statements (`Disj.lean`, namespace `GlueSqrtDisj`)

Ambient hypotheses on `L` (as in glue-sqrt-local): `[Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
[IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]`. For the disjointness
section also `[NeZero m] (hcop : p.Coprime m) [IsCyclotomicExtension {p ^ k * m} ℚ_[p] L]`.
Here `u = ZMod.unitOfCoprime p hcop`, that is, `p` as a unit mod `m`.

| Statement | Lean name | Status |
| --- | --- | --- |
| In a domain `R`, with `Q` prime, `p ∈ Q` and `z` a primitive `p^k`-th root: `p ∈ Q^φ(p^k)` | `prime_mem_pow_totient` | VERIFIED |
| **`φ(p^k) · ord_m(p) ≤ [L:ℚ_p]`** for `L ∋ ζ_{p^k}, ζ_m`, `p ∤ m` | `totient_mul_orderOf_le_finrank` | VERIFIED |
| `galToProd k m : Gal(L/ℚ_p) →* (ZMod p^k)ˣ × (ZMod m)ˣ` (autToPow on `ζ^m` and on `ζ^{p^k}`) | `galToProd` | definition |
| `galToProd` is injective | `galToProd_injective` | VERIFIED |
| **range of `galToProd` = `⊤ × zpowers u`** | `range_galToProd` | VERIFIED |
| **`Gal(L/ℚ_p) ≃* (⊤ : Subgroup (ZMod p^k)ˣ).prod (zpowers u)`** | `galEquivProd` | VERIFIED |
| **`[L:ℚ_p] = φ(p^k) · ord_m(p)`** | `finrank_eq_totient_mul_orderOf` | VERIFIED |
| `g x = x^a` for `x^{p^k} = 1`; `g y = y^b` for `y^m = 1`, where `(a, b) = galToProd g` | `galToProd_fst_spec`, `galToProd_snd_spec` | VERIFIED |
| **restriction ↔ reduction:** for `K` of level `p^{k'} m'` inside `L`, `k' ≤ k`, `m' ∣ m`: `galToProd (g|_K) = (a mod p^{k'}, b mod m')` | `galToProd_restrict` | VERIFIED |
| `p` is prime to `p^n − 1`; **`ord_{p^n−1}(p) = n`** (`p ≥ 2`, `n ≥ 1`) | `coprime_pow_sub_one`, `orderOf_unit_pow_sub_one` | VERIFIED |
| `m ∣ p^{t·ord_m(p)} − 1` | `dvd_pow_orderOf_sub_one` | VERIFIED |
| `Gal(L/ℚ_p)` is commutative | `galCommGroup` | VERIFIED |
| `τ` exists: `galToProd τ = (−1, 1)` for some `τ` | `exists_tau` | VERIFIED |
| **every `p`: `(∃ ψ, ∀ g, 2•ψ(g) = χ(g|_K)) ↔ χ(τ) = 0`** for `K ⊆ L` of levels `p^k m`, `p^{k+1} m'`, `m ∣ m'`, `ord_{m'}(p) = 2 ord_m(p)` | `sqrt_criterion_level` | VERIFIED |
| same with `m' = p^{2f} − 1`, `f = ord_m(p)`, side conditions discharged | `sqrt_criterion_level_pow` | VERIFIED |

`sqrt_criterion_level` states the characters as `Additive Gal(K/ℚ_[p]) →+ AddCircle (1 : ℚ)` and
`Additive Gal(L/ℚ_[p]) →+ AddCircle (1 : ℚ)`, and restriction as `AlgEquiv.restrictNormal`. `K` and
`L` are any fields with the cyclotomic instances and `[Algebra K L] [IsScalarTower ℚ_[p] K L]`. They
need not be subfields of a fixed algebraic closure.

## 1. How the proofs go

1. **Degree bound (`totient_mul_orderOf_le_finrank`).** Let `S` be the integral closure of `ℤ_p` in `L`.
   - `S` is Dedekind (`integralClosure.isDedekindDomain ℤ_[p] ℚ_[p] L`), finite and flat over `ℤ_p`.
     `Gal(L/ℚ_p)` is a Galois group for `S/ℤ_p` (`IsGaloisGroup.of_isFractionRing`).
   - Mathlib's fundamental identity gives `g · e · f = |Gal(L/ℚ_p)| = [L:ℚ_p]`, so `e·f ≤ [L:ℚ_p]`.
     The locality of `S` (glue-sqrt-local) is not needed for this bound.
   - **`e ≥ φ(p^k)`.** `e = multiplicity Q (pS)` (`Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity`).
     Also `p = Φ_{p^k}(1) = ∏_μ (1 − μ)` over the primitive `p^k`-th roots `μ ∈ S`.
     Since `Q` is prime, some `1 − μ₀ ∈ Q`. Every `μ` is a power of `μ₀`, so `1 − μ₀ ∣ 1 − μ`.
     Hence `p ∈ Q^φ(p^k)`, and `Q^φ(p^k) ∣ pS`.
   - **`f ≥ ord_m(p)`.** `#(S/Q) = p^f` (`Ideal.cardQuot_pow_inertiaDeg`), so `η^{p^f} ≡ η (mod Q)`.
     Two `m`-th roots of unity that agree mod `Q` are equal (`eq_of_pow_eq_one_of_sub_mem`, from
     glue-sqrt-local). So `η^{p^f − 1} = 1`, `m ∣ p^f − 1`, and `ord_m(p) ≤ f`.
2. **Disjointness.** `galToProd` is injective by Bezout. Write `1 = mA + p^k B`. Then
   `ζ = (ζ^m)^A (ζ^{p^k})^B`, so an element fixing `ζ^m` and `ζ^{p^k}` fixes `ζ`, and
   `autToPow_injective` applies. The image lies in `⊤ × ⟨p⟩` by glue-sqrt-local's
   `range_autToPow_eq_zpowers'`. It has size `|Gal| = [L:ℚ_p] ≥ φ(p^k)·ord_m(p) = |⊤ × ⟨p⟩|`
   (item 1). Hence equality.
3. **Restriction.** `galToProd_fst_spec` and `galToProd_snd_spec` describe `galToProd` by its action
   on the whole of `μ_{p^k}` and `μ_m`, not just on the chosen generator. The restriction formula then
   follows from `AlgEquiv.restrictNormal_commutes` and `autToPow_eq_of_apply`.
4. **Criterion.** Apply `exists_half_iff` (glue-I6-rest) to `χ ∘ res` on `Additive Gal(L/ℚ_p)`.
   - Let `g ∈ Gal(L/ℚ_p)` with `g² = 1`, and write `galToProd g = (a, b)`.
   - `a² = 1` in `(ℤ/p^{k+1})ˣ`, so `a ≡ ±1 (mod p^k)` (`redU_sq_eq_one`, any `p`, including 2).
   - `b = u'^j` with `u'^{2j} = 1`. So `2f ∣ 2j`, hence `f ∣ j`, and `b ↦ u^j = 1` in `(ℤ/m)ˣ`.
   - By `galToProd_restrict` and injectivity on `K`, `g|_K ∈ {1, τ}`.
   - Conversely, `g₀ = galToProd⁻¹(−1, 1)` has order dividing 2 and restricts to `τ`.

## 2. How this connects to glue-sqrt-local and to B2

- glue-sqrt-local proved the two halves separately: `galEquivUnits` (level `p^{n+1}`) and
  `range_autToPow_eq_zpowers'` / `finrank_eq_orderOf` (level `m`). It also proved the abstract model
  `sqrt_criterion_finite` on `(ℤ/p^k)ˣ × ℤ/f`. `Disj.lean` uses its `range_autToPow_eq_zpowers'` (whose
  proof rests on the locality of `S` and on Frobenius) and its `redU_sq_eq_one` and `exists_half_iff`.
  It does not need the abstract model, because `sqrt_criterion_level` runs the same argument on the
  genuine Galois groups.
- **B2's local criterion from I6.3.** Let `χ` be a finite-order character of `G_{ℚ_p}`. I6.3
  (`LocalKroneckerWeber`, the leaf in `scratch/pkg-I6/I6.lean`) puts the fixed field of `ker χ` inside
  `ℚ_p(μ_n)`, `n = p^k m`, `p ∤ m`. Then `sqrt_criterion_level_pow` with
  `K = ℚ_p(μ_{p^k m}) ⊆ L = ℚ_p(μ_{p^{k+1}(p^{2f}−1)})` gives the criterion with `τ = τ₋₁`. Only the
  plumbing between `G_{ℚ_p}` and these finite groups remains (§3). No other arithmetic input is
  needed (SPECULATIVE in the sense that the plumbing is unwritten; no deep input is expected).

## 3. What remains (not proved)

**Item (2): plumbing from `G_{ℚ_p} = Gal(PadicAlgCl p/ℚ_p)` to finite levels.** Not written. It
needs:
1. A character with open kernel (that is, continuous into discrete `ℚ/ℤ`) factors through
   `Gal(M/ℚ_p)` for a finite Galois `M`, the fixed field of the kernel. That `M` is abelian over `ℚ_p`.
   This uses Mathlib's infinite Galois correspondence (`InfiniteGalois`).
2. I6.3 gives `M ≤ adjoin ℚ_p {x | x^n = 1}`. Then one needs:
   - an `IsCyclotomicExtension {p^k m}` instance for that intermediate field, and for the
     level-`p^{k+1}(p^{2f}−1)` one;
   - `Algebra ℤ_[p]`/`IsScalarTower` instances for intermediate fields (`Algebra.compHom`);
   - the tower `K ≤ L` as `[Algebra K L] [IsScalarTower ℚ_[p] K L]`
     (`IntermediateField.inclusion`).
3. Moving `χ` from `Gal(M/ℚ_p)` to `Gal(K/ℚ_p)` (restriction `K → M`), and inflating `ψ` from
   `Gal(L/ℚ_p)` to `G_{ℚ_p}` through `AlgEquiv.restrictNormalHom`. The kernel is the fixing subgroup of
   `L`, which is open because `L` is finite.
4. Choosing `τ₋₁ ∈ G_{ℚ_p}` (any lift of `τ` from `exists_tau` at a fixed level). Showing that
   `χ(τ₋₁)` does not depend on the lift (immediate, since `χ` factors through `Gal(K/ℚ_p)`).

SPECULATIVE estimate: 200-350 lines, all instance and intermediate-field bookkeeping.

Also not done: merging `Disj.lean` with glue-sqrt-local's `SqrtLocal.lean` (the `p`-power-only
results `gal_sqrt_criterion`, `gal_sqrt_criterion_lower` are the case `m = 1` and stay valid as they are).

## 4. Files

- `scratch/glue-sqrt-disj/Disj.lean` (1027 lines): the combined, self-contained file. It is glue-sqrt-local's
  `Unramified.lean` verbatim, then `SqrtLocal.lean` lines 84-242 verbatim (`exists_half_iff`, `redU`,
  `redU_sq_eq_one` and helpers), then `Ram.lean`, then the sections `Disj` and `Crit`.
- `scratch/glue-sqrt-disj/Ram.lean`: the degree bound alone (standalone).
- `scratch/glue-sqrt-disj/Level.lean`: the level-change arithmetic alone (standalone).
- `scratch/glue-sqrt-disj/log.md`: results log.
