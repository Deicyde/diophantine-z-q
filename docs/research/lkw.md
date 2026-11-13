# Local Kronecker–Weber for ℚ_p (leaf T16 / I6.3) from Tau Ceti's local class field theory

## Main result (VERIFIED: compiles, `#print axioms` below)

Leaf **T16** (I6.3, local Kronecker–Weber) is proved, and with it leaf **T30** (L-B2c, the local
square-root criterion):

```lean
-- ZInQKernel/Contrib/LocalKW/LocalKW.lean
theorem ZInQ.Contrib.localKroneckerWeber (p : ℕ) [Fact p.Prime] : PkgI6.LocalKroneckerWeber p
-- ZInQKernel/Contrib/LocalKW/T30.lean
theorem ZInQ.Contrib.leafSqrtCrit : GlueDescent.B2Q.LeafSqrtCrit
```

`#print axioms` (scratch/lkw/Axioms.lean, scratch/lkw/AxiomsT30.lean):

```
'ZInQ.Contrib.localKroneckerWeber' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.leafSqrtCrit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Files (all new, under ZInQKernel/Contrib/LocalKW/):

* `Basic.lean` (imports only the vendored Tau Ceti modules `Local.ExplicitCyclotomicSymbol.ArtinMap`,
  `Local.Cyclotomic` and three Mathlib files). Declarations, all in `ZInQ.Contrib.LocalKW`, all with
  axioms `[propext, Classical.choice, Quot.sound]` (`zpow_apply_eq_self`: `[propext, Quot.sound]`):
  - `le_adjoin_rootsOfUnity (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ_[p] L]
    [IsGalois ℚ_[p] L] [IsMulCommutative Gal(L/ℚ_[p])] : ∃ m : ℕ, 0 < m ∧ L ≤ IntermediateField.adjoin ℚ_[p] {x | x ^ m = 1}`
  - `le_of_normGroup_le (L M) [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L] [IsMulCommutative Gal(L/ℚ_[p])]
    [FiniteDimensional ℚ_[p] M] [IsGalois ℚ_[p] M] (h : normGroup ℚ_[p] M ≤ normGroup ℚ_[p] L) : L ≤ M` (Lemma A)
  - `fixes_of_mem_normGroup`: a representative of the Artin symbol of a norm from an abelian `L` fixes `L`
  - `normGroup_cyclotomic_le_powerSubgroup (hn : 0 < n) (hζ : IsPrimitiveRoot ζ (p ^ (2 * padicValNat p n + 1) * (p ^ n - 1))) :
    normGroup ℚ_[p] ℚ_[p]⟮ζ⟯ ≤ powerSubgroup ℚ_[p]ˣ n` (Lemma C)
  - `exists_pow_eq_of_norm_sub_one_le (hn : 0 < n) (hu : ‖u - 1‖ ≤ p ^ (-(2 v_p(n) + 1))) : ∃ z : ℤ_[p], z ^ n = u` (Lemma B)
  - helpers `sepIncl`, `coe_sepIncl`, `artinGal` (the Artin map of an abelian layer read in `Gal(M/ℚ_p)`),
    `localArtinMap_eq_artinGal`, `artinGal_eq_one_of_mem`, `exists_eq_zpow_mul_unit`, `valuation_unit`,
    `norm_natCast_padicInt`, `coprime_self_pow_sub_one`, `zpow_apply_eq_self`.
* `LocalKW.lean`: `ZInQ.Contrib.localKroneckerWeber` (imports `Basic` and `HDecomp.Conductor.I6Base`).
* `SqrtCrit.lean`: a verbatim copy of t30-adelic's `scratch/t30-adelic/SqrtCrit.lean` (commit 85ed47cb), namespace
  renamed `ZInQ.Contrib.LocalKW.SqrtCrit`; it proves `LeafSqrtCrit` from T16 at every prime.
* `T30.lean`: `ZInQ.Contrib.leafSqrtCrit`.

Dependencies: the vendored Tau Ceti oct16 modules of task tc-port (branch wip/tc-port, merged at 395103a4).
No Tau Ceti module was vendored by lkw; wip/kw-new is not needed. The local existence theorem is not used.

## Target

`PkgI6.LocalKroneckerWeber p` (ZInQKernel/HDecomp/Conductor/I6Base.lean):
every `L : IntermediateField ℚ_[p] (PadicAlgCl p)` with `FiniteDimensional ℚ_[p] L` and
`IsAbelianGalois ℚ_[p] L` satisfies `L ≤ adjoin ℚ_[p] {x | x ^ m = 1}` for some `m > 0`.
Deliverable: `ZInQ.Contrib.localKroneckerWeber (p : ℕ) [Fact p.Prime] : PkgI6.LocalKroneckerWeber p`.

## Step 1 findings (VERIFIED by reading ~/tc-oct16, ~/tc-nov01, ~/tc-main)

* Tau Ceti does **not** state local Kronecker–Weber, nor the norm group of ℚ_p(μ_m)/ℚ_p.
  (`grep -i kronecker` finds only the global `TauCeti.ClassFieldTheory.kroneckerWeber`.)
* `PadicAlgCl p` is Mathlib's `abbrev PadicAlgCl := AlgebraicClosure ℚ_[p]`
  (Mathlib/NumberTheory/Padics/Complex.lean:54), and Tau Ceti's absolute Galois group
  `Field.absoluteGaloisGroup K` is `Gal(AlgebraicClosure K/K)`, so no bridge between closures
  is needed for the absolute Artin map.
* What Tau Ceti provides at oct16 (all in kw-rest.txt, so vendored by task tc-port):
  - `Local/Reciprocity.lean`: `localArtinMap K L ι : Additive Kˣ →+ Additive (Abelianization Gal(L/K))`
    for finite Galois `L/K`, `ι : L →ₐ[K] SeparableClosure K`;
    `localArtinMap_eq_zero_iff : localArtinMap … x = 0 ↔ x ∈ normGroup K L`;
    `powerSubgroup_le_normGroup_of_exponent_dvd : exponent Gal(L/K) ∣ n → (Kˣ)ⁿ ≤ normGroup K L`.
  - `Local/ArtinMap.lean`: absolute `artinMap K : Kˣ →* G_K^ab`; `artinMap_restrict`
    (finite restrictions are `localArtinMap`); `mem_normGroup_of_mk_eq_artinMap_of_fixes`;
    `denseRange_artinMap`.
  - `Local/Cyclotomic.lean`: `localArtinMap_cyclotomic_uniformizer` (a lift of the Artin symbol of
    a uniformizer acts as `ζ ↦ ζ^q` on roots of unity of order prime to `q`),
    `localArtinMap_cyclotomic_padic` (the case `π = p` over ℚ_p).
  - `Local/ExplicitCyclotomicSymbol/ArtinMap.lean`: `localArtinMap_cyclotomic_padic_primePow`
    (over ℚ_p, a lift of the Artin symbol of `p^k u` acts on `μ_{pⁿ}` by `ζ ↦ ζ^(u⁻¹ mod pⁿ)`).
  The local existence theorem (LocalExistence/Existence.lean, not in the lists) is **not** needed.

## Derivation (STANDARD mathematics; the Lean route)

Let `K = ℚ_p`, `Ω = AlgebraicClosure K`, `G = Gal(Ω/K)`, `N_E = N_{E/K}(Eˣ)` for finite `E/K`.

**Lemma A (norm groups reverse inclusion).** Let `L, M ⊆ Ω` be finite Galois over `K`, `L` abelian.
If `N_M ≤ N_L` then `L ≤ M`.
Proof. Let `σ ∈ G` fix `M`. The coset `σ·(Fix L ∩ Fix M)` is open in `G`; its image in `G^ab` is open
(quotient maps of topological groups are open), so by density of `artinMap K` it contains
`artinMap K x` for some `x ∈ Kˣ`, represented by some `τ ∈ σ·(Fix L ∩ Fix M)`. `τ` fixes `M`, so
`x ∈ N_M` (`mem_normGroup_of_mk_eq_artinMap_of_fixes`), so `x ∈ N_L`, so
`Abelianization.of (τ|_L) = localArtinMap x = 0` (`artinMap_restrict`, `localArtinMap_eq_zero_iff`);
`Gal(L/K)` is commutative, so `τ|_L = 1`, so `τ` and hence `σ` fix `L`. Thus `Fix M ≤ Fix L` and
`L ≤ fixedField (Fix M) = M` (infinite Galois correspondence; `Ω/K` is Galois in characteristic 0).

**Lemma B (Hensel).** If `n ≥ 1`, `u ∈ ℤ_pˣ` and `u ≡ 1 mod p^(2 v_p(n) + 1)`, then `u = zⁿ` with
`z ∈ ℤ_p`: Hensel's lemma (`hensels_lemma`) for `Xⁿ − u` at `1`, since
`‖1 − u‖ ≤ p^-(2v+1) < p^-2v = ‖n‖²`.

**Lemma C (norm group of a cyclotomic field).** Let `n ≥ 1`, `k = 2 v_p(n) + 1`,
`m = p^k (pⁿ − 1)`, `M = K(ζ_m) ⊆ Ω`. Then `N_M ≤ (Kˣ)ⁿ`.
Proof. Let `x ∈ N_M`, `x = p^a u` with `a ∈ ℤ`, `u ∈ ℤ_pˣ`. Since `Gal(M/K)` is commutative,
`R(y) := (localArtinMap y)` read in `Gal(M/K)` is a homomorphism `Kˣ → Gal(M/K)` with kernel `N_M`;
`R(x) = 1`.
(i) `ζ_m^(pⁿ−1)` has order `p^k`; `localArtinMap_cyclotomic_padic_primePow` gives
`R(x) ζ = ζ^(u⁻¹ mod p^k)`, hence `u⁻¹ ≡ 1`, so `u ≡ 1 mod p^k`.
(ii) `η = ζ_m^(p^k)` has order `pⁿ − 1`, prime to `p`. `φ := R(p)` and `R(pu)` both act on `η` by
`η ↦ η^p` (`localArtinMap_cyclotomic_padic`, `localArtinMap_cyclotomic_uniformizer`, `pu` is a
uniformizer, `#𝓀[ℚ_p] = p`); so `R(u) η = η`, and `η = R(x) η = φ^a R(u) η = φ^a η`.
Since `φⁿ η = η^(pⁿ) = η`, writing `a = nq + r` with `0 ≤ r < n` gives `η = φ^r η = η^(p^r)`, so
`pⁿ − 1 ∣ p^r − 1 < pⁿ − 1`, so `r = 0`.
By Lemma B, `u = zⁿ`, so `x = (p^q z)ⁿ`.

**Theorem.** Let `L ⊆ Ω` be finite abelian over `K`, `n = [L : K] ≥ 1`. Then
`N_M ≤ (Kˣ)ⁿ ≤ N_L` (Lemma C; `powerSubgroup_le_normGroup_of_exponent_dvd`, as the exponent of
`Gal(L/K)` divides its order `n`), so `L ≤ M = K(ζ_m) ≤ K({x | x^m = 1})` by Lemma A, `m > 0`.

Remark: (i) and (ii) are the explicit cyclotomic symbol of Milne, *Class Field Theory* VII Ex. 8.2
(as cited by Tau Ceti), read on `ℚ_p(μ_m)`; the converse inclusion `(Kˣ)ⁿ`-type bounds
(`N_M = p^(nℤ)·U^(k)`) is not needed.
