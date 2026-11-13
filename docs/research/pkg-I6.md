# pkg-I6: arithmetic of ℚ and of local fields (h-trust steps B1, B2, C10, D1, D3, D4)

Status: research note (task pkg-I6, 2026-11-11). Package I6 of `docs/research/wk-h.md` §2. Lean
drafts are in `scratch/pkg-I6/I6.lean` (imports Mathlib only) and `scratch/pkg-I6/Check.lean`. The
results log is `scratch/pkg-I6/log.md`. No file under `ZInQKernel/`, `blueprint/` or other notes
was edited.

Marks: **VERIFIED** means read in a source in the repository, computed, or compiled. **STANDARD**
means a published theorem with a reference. **SPECULATIVE** means an assessment. No network was
available, so theorem numbers given from memory are marked UNVERIFIED. Tau Ceti was not available
offline. Its declaration names are copied from `docs/research/prereq-survey.md` and were not
re-checked here.

## Summary

1. **Every I6 input can be stated today as a concrete Lean Prop over genuine Mathlib objects
   (VERIFIED: `I6.lean` compiles).** There are 10 leaves, I6.1-I6.10, some with variants. This
   corrects wk-h §3.2 ("local CFT and ramification filtrations no"), and the three I6 leaves
   that hdec-faithful's draft leaves as `def … : Prop := sorry`: `L15b_BrauerCohomology`,
   `L16_LocalCFT` and `L20_RamificationGroups`. Two Mathlib facts make this possible:
   - Mathlib v4.35 has continuous Galois cohomology. That means `Field.absoluteGaloisGroup` with
     the continuous map `G_F → G_K` induced by a field map, `continuousCohomology`, and a
     Tate–Shafarevich subgroup (`ContinuousCohomology.tateShafarevich`, 2026).
   - Mathlib has `differentIdeal`, `AddSubgroup.inertia`, `IsArithFrobAt` and `PadicAlgCl`.
2. **The Brauer step of B2 is proved in Lean from three leaves (VERIFIED; axioms `propext`,
   `Classical.choice`, `Quot.sound`).** Two classes of `H²(G_ℚ, ℤ/2)` that are locally nonzero at
   the same primes are equal: `eq_of_same_finite_support` and its cochain form
   `cob_of_same_finite_support`. The leaves are stated on `H²(G_ℚ, ℤ/2)` itself. This avoids the
   identification `H²(G_ℚ, ±1) = Br(ℚ)[2]`, which prereq-survey could not find in any library and
   which hdec-faithful leaves as a hole.
3. **Two of Glazer's uses of local class field theory are replaced by weaker inputs.**
   - B2's square-root criterion needs only **local Kronecker–Weber for `ℚ_p`** (I6.3), with
     elementary glue. SPECULATIVE until the glue is written.
   - D3's appeal to the norm functoriality of reciprocity can be avoided (argument in §3.4,
     SPECULATIVE until reviewed). What remains is a finite-level reciprocity map for the one
     field `F`, with the upper numbering theorem (I6.10).
4. **Library status.**
   - Mathlib has none of the ten leaves.
   - Tau Ceti has the Brauer group forms of I6.2 (`brLocalization_injective`,
     `sumLocalInv_brLocalization_eq_zero`, `h2MuEquivZMod`), Skolem–Noether, Chebotarev, Herbrand's
     theorem, Hilbert's different formula and Artin conductors (per prereq-survey).
   - Not located anywhere: Serre's upper bound for the different, Brauer–Nesbitt, local
     Kronecker–Weber, and the Galois-cohomology form of I6.2.
5. **Biggest obstacle.** The leaves can be stated. The objects they are applied to cannot (yet):
   - B1 applies Skolem–Noether to `End⁰(A_{\bar ℚ})` of the QM surface (I1/I3).
   - B2's cocycle `ε` is built from the isogenies `μ_σ`.
   - C10 and D1-D4 apply to the ℓ-adic representation `r_ℓ` of `G_{ℚ_p}`; its Artin conductor is
     defined through its finite wild image, and D5 (Carayol, I4) consumes it.

   So I6 is ready to be crowdsourced as statements. Gluing them to H waits on I1-I4.

## 1. The inputs, leaf by leaf

Columns:
- "Used in N5" gives the line numbers of `diophantine_zq.tex`.
- "Leaf" names the Lean declaration in `scratch/pkg-I6/I6.lean`; every one compiles.
- "Library" gives the status in Mathlib v4.35 (grep of `.lake/packages/mathlib`, VERIFIED) and
  in Tau Ceti (per prereq-survey).

| # | Published statement (exact form used) | Used in N5 | Leaf (`I6.lean`) | Library |
| --- | --- | --- | --- | --- |
| I6.1 | **Skolem–Noether.** `A` a finite-dimensional central simple `K`-algebra, `B` a simple finite-dimensional `K`-algebra. Any two `K`-maps `B → A` are conjugate by `A^×`. Reiner, *Maximal orders* (1975) Thm 7.21 (UNVERIFIED). B1 uses `B = A`: automorphisms are inner | B1, L637-639 | `SkolemNoether` (L30); `skolemNoether_aut` (L37, proved) | Mathlib: no. Tau Ceti: `TauCeti.skolemNoether` |
| I6.2a | **Albert–Brauer–Hasse–Noether, 2-torsion.** `H²(G_ℚ, ℤ/2) → ∏_v H²(G_{ℚ_v}, ℤ/2)` is injective. That is ABHN (`Br ℚ ↪ ⊕ Br ℚ_v`) composed with the natural Kummer isomorphism `H²(G_K, μ₂) ≅ Br(K)[2]` (Hilbert 90). Milne, *ADT* Ch. I; Tate in Cassels–Fröhlich VII §11 (UNVERIFIED locators) | B2, L690-692 | `BrauerHasse2` (L75) on `continuousCohomology`; `BrauerHasse2C` (L163) on continuous cochains | Mathlib: definitions only. Tau Ceti: `brLocalization_injective` (Br form); the H² bridge was not located |
| I6.2b | **Reciprocity, 2-torsion.** For `x ∈ H²(G_ℚ, ℤ/2)`, the set of places with `x_v ≠ 0` is finite and has even size. That is `∑_v inv_v = 0` with `inv_v(x) ∈ {0, ½}` (same references) | B2, L690 | `BrauerReciprocity2` (L84), `BrauerReciprocity2C` (L169) | Tau Ceti: `sumLocalInv_brLocalization_eq_zero`, `range_brLocalization` (Br form) |
| I6.2c | **Local `H²`.** `H²(G_{ℚ_p}, ℤ/2) ≅ Br(ℚ_p)[2] ≅ ℤ/2` and `H²(G_ℝ, ℤ/2) ≅ ℤ/2`. Serre, *Corps locaux* XIII §3; X §5 (UNVERIFIED) | B2, L683-689 | `LocalH2Card` (L93), `LocalH2CardC` (L185) | Tau Ceti: `h2MuEquivZMod` (local `H²(F, μ_n) ≅ ℤ/n`; whether its `H²` is Mathlib's is unknown) |
| I6.3 | **Local Kronecker–Weber for `ℚ_p`.** Every finite abelian extension of `ℚ_p` in `\bar ℚ_p` lies in some `ℚ_p(μ_n)`. Neukirch, *ANT* V (1.10) (UNVERIFIED) | B2, L683-687 (replaces "local reciprocity") | `LocalKroneckerWeber` (L251) | not located (Tau Ceti has global `kroneckerWeber`) |
| I6.4 | **Chebotarev, existence form.** For `M/ℚ` finite Galois, `S` finite and `σ ∈ Gal(M/ℚ)`, there is an unramified `p ∉ S` with `σ` the arithmetic Frobenius at some `Q | p`. A consequence of the density theorem, Neukirch *ANT* VII (13.4) (UNVERIFIED) | C10, L792 | `ChebotarevExists` (L267), with Mathlib's `IsArithFrobAt ℤ σ Q` | Mathlib: no. Tau Ceti: `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet` |
| I6.5 | **Brauer–Nesbitt, characteristic 0.** Finite-dimensional semisimple representations of a group over a field of characteristic 0 with equal characters are isomorphic. Lang, *Algebra* XVII Cor. 3.8; Curtis–Reiner (1962) §30 (UNVERIFIED) | C10, L792-793 | `BrauerNesbittChar0` (L281) | not located |
| I6.6 | **Serre's bound for the different.** `v_B(𝔇_{B/A}) ≤ e − 1 + v_B(e)` for a finite separable extension of complete DVRs with perfect residue field. Serre, *Corps locaux* III §6, remark after Prop. 13 (UNVERIFIED) | D1, L800-803 | `DifferentBound` (L350): `𝔇 ∣ 𝔪_B^{e−1}·(e)` | Mathlib: only the lower bound `pow_sub_one_dvd_differentIdeal`. Tau Ceti: not located |
| I6.7 | **Hilbert's formula.** `v_B(𝔇_{B/A}) = ∑_{i≥0}(|G_i| − 1)` for `B/A` Galois. Serre IV §1 Prop. 4 (UNVERIFIED) | D1, L804-806 | `HilbertDifferentFormula` (L362) | Tau Ceti: `…multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one` |
| I6.8 | **Herbrand.** `(G/H)^v = G^v H/H`. Serre IV §3 Prop. 14 (UNVERIFIED) | D1, D3 (L839-843), D4 | `HerbrandQuotient` (L375), restriction `r` given by its defining property | Tau Ceti: `map_restrictNormalHom_upperRamificationGroup` |
| I6.9 | **Transitivity.** `φ_{L/K} = φ_{L'/K} ∘ φ_{L/L'}` for `L'/K` Galois. Serre IV §3 Prop. 15 (UNVERIFIED) | D3, L839-843 (the subgroup formula) | `HerbrandTransitivity` (L392) | Tau Ceti: `psiNat` (not checked for this statement) |
| I6.10 | **Local CFT with the upper numbering theorem, finite abelian level.** There is a surjection `θ: K^× → Gal(L/K)` with kernel `N(L^×)` and `θ(π)` = Frobenius on the residue field, mapping `U^{⌈v⌉}` onto `G^v` (`v ≥ 0`). Serre, *Corps locaux* XIII §4 Prop. 13, XV §2 Thm 1 and Cor.; Hasse–Arf V §7 Thm 1 for non-integral `v` (UNVERIFIED) | B2 (via I6.3), D3 L826-838 | `LocalReciprocityUpper` (L420) | Tau Ceti: global CFT and local `H²` per survey; a local Artin map with upper numbering was not located |

Concrete definitions (`I6.lean` Part II), in Serre's setting: `A → B` a finite extension of DVRs,
`A` complete with perfect residue field, `B ≃ₐ[A] B = Gal(L/K)`.

- `lowerRam A B i` is `G_i`, the inertia subgroup (Mathlib `AddSubgroup.inertia`) of `𝔪_B^{i+1}`.
  glue-conductor's global `ramGroup` uses the same construction for a Galois number field.
- `lowerRamR` is `G_u` for real `u ≥ −1`.
- `herbrandPhi` is `φ(u) = ∫₀ᵘ |G_t|/|G_0| dt`.
- `upperRam` is `G^v = G_{ψ(v)}`.
- `unitFiltration` is `U^{(n)}`.
- `artinConductor` is Serre VI §2's `f(V) = ∑_{i≥0} (|G_i|/|G_0|) codim V^{G_i}`.

`lowerRam_tower` (the subgroup rule `H_i = G_i ∩ H`, Serre IV §1 Prop. 2) is proved by `rfl`.
`Check.lean` (VERIFIED) shows that the hypothesis classes of I6.6-I6.10 hold for `ℤ_[p]`, so the
local leaves have models. Non-trivial extensions were not instantiated.

**Faithfulness notes (SPECULATIVE, by reading).**
- Each leaf is the published statement or a consequence of it.
- I6.2a-c combine ABHN, reciprocity and `inv_p` with the Kummer isomorphism. Both sides are
  natural in the field, and conjugation acts trivially on cohomology. So the leaves do not depend
  on the embedding `\bar ℚ → \bar ℚ_v` that `Field.absoluteGaloisGroup.map` chooses.
- I6.10 is an ∃-form: the canonical reciprocity map is one such `θ`. Without the Frobenius
  normalization it would still be a consequence. With it, it pins the unramified part.
- I6.4 is weaker than the density theorem. Glazer needs only that Frobenius elements meet every
  coset of every open subgroup, which follows by Galois theory (glue). hdec-faithful's
  `FrobeniusDense` states that density form directly.
- All leaves quantify over `Type` (universe 0), which suffices for the application.

## 2. Where each leaf enters, and the glue that remains

### B1 (N5 L632-664)
- **Leaf:** I6.1, applied to the `ℚ`-algebra automorphism `b ↦ ψ_σ ᵟb ψ_σ^{-1}` of
  `B = End⁰(A_{\bar ℚ})`.
- **Glue:** glue-descent's `ProjRep.lean`. It gives the cocycle, the sign normalization and
  `ρ = β⁻¹aμ`, compiled without `sorry` on origin/wip/glue-descent. That glue is purely algebraic.
- **Not statable here:** the identification of `End⁰(A_{\bar ℚ})` with the quaternion algebra.
  It is A9 (I1/I3).

### B2 (N5 L665-693)
- **Leaves:** I6.2a-c, I6.3.
- **Glue, proved here:** the Brauer step (`eq_of_same_finite_support`,
  `cob_of_same_finite_support`).
- **Glue to be written (elementary; sizes SPECULATIVE):**
  1. `[ε]_p = 0` for `p ∉ T`. The restriction is inflated from the cyclic group `Gal(L_v/ℚ_p)`
     of order `f`, and inflation `H²(ℤ/f, ℤ/2) → H²(ℤ/2f, ℤ/2)` is zero. Mathlib has
     `GroupCohomology/FiniteCyclic.lean`. Continuous inflation from a finite quotient is not in
     Mathlib. 100-200 lines on cochains.
  2. **The square-root criterion.** A finite-order character `χ` of `G_{ℚ_p}` has a character
     square root iff `χ(τ₋₁) = 1`. Here `τ₋₁` acts by `ζ ↦ ζ^{-1}` on `p`-power roots of unity
     and trivially on prime-to-`p` ones. From I6.3:
     - `χ` factors through `Gal(ℚ_p(μ_{p^k m})/ℚ_p) ≅ (ℤ/p^k)^× × ⟨Frob⟩`. This needs the
       irreducibility of the `p^k`-th cyclotomic polynomial over `ℚ_p` (Eisenstein) and the
       disjointness of the totally ramified and unramified parts.
     - The criterion then holds because a character of a profinite abelian group `Γ` is a square
       iff it kills `Γ[2]`, and `Γ[2] = {±1}` here.
     - It was checked numerically by rv-h-novel (`c2_sqrt_criterion.py`, 135 characters,
       0 mismatches).
     - Mathlib has `IsCyclotomicExtension.autEquivPow`.
     - 500-1000 lines.
  3. `ω_p(−1) = χ_p(−1)` (rv-h-novel R1). This is the image of `τ₋₁` in `(ℤ/N)^×` under
     `galEquivZMod`. Elementary.
  4. **From `[ε]` to a class.** On cochains, nothing is needed (`BrauerHasse2C` etc.). For the
     `continuousCohomology` form, one needs the comparison "continuous inhomogeneous 2-cocycles
     modulo coboundaries = Mathlib's `H²`". It is not in Mathlib (only `H⁰` is described
     explicitly), so **use the cochain forms.**
- Dirichlet-character bookkeeping and `m ≤ 2R^R M`: glue-descent (`Cochain.lean`, compiled).

### C10 (N5 L776-795)
- **Leaves:** I6.4 and I6.5.
- **Glue:**
  - Frobenius density in `G_ℚ` from I6.4 (Galois theory of a finite quotient).
  - Equality of traces on a dense set implies equality everywhere, by continuity of an ℓ-adic
    representation.
  - Then I6.5 over the coefficient field.
- **Not I6:** the trace identity (Mumford §19 Thm 4, I2/I3), the semisimplicity of both sides
  (Faltings, I3), and Néron reduction of `μ_σ` (I2). Continuous ℓ-adic representations need a
  topological finite extension of `ℚ_ℓ` with a `ContRepresentation`. That is definable today, but
  no library has Tate modules of abelian varieties.

### D1 (N5 L796-812)
- **Leaves:** I6.6 and I6.7, applied to `L/K₀` (`K₀` the maximal unramified subfield) and to
  `Gal(L/ℚ_p)`. They share `G_i` for `i ≥ 0`.
- **Glue, done elsewhere:** glue-conductor (`Breaks.lean`, compiled). It proves D1 from its own
  global-form copies of I6.6/I6.7 (`SerreDifferentBound`, `HilbertDifferentFormula` over
  `differentIdeal ℤ (𝓞 L)` and `Ideal.inertia`), plus the Herbrand integral as a finite sum and
  the numerics `2δ/e ≤ 4a²`.
- The global form (a Galois number field `L`, a prime `P`) and the local form here (complete DVRs)
  are equivalent by completion (Serre III §4, UNVERIFIED). Both are faithful. The global form
  avoids local fields in the application, because Glazer's `L_v` is a completion of a Galois
  number field `L`. **Recommendation:** adopt glue-conductor's global form for D1, and keep the
  local form for D3, where `F = L_v(A[3])` need not be a completion of a Galois number field.

### D3 (N5 L823-846)
- **Leaves:** I6.8, I6.9, I6.10.
- **Glue:**
  - `(U^{e+1})⁴ = U^{3e+1}`: proved by glue-conductor (`Dyadic.lean`, Mathlib's Henselian
    property of complete local rings). It replaces Silverman IV.6.4. `sq_principalUnits` here is
    the same statement, unproved.
  - The subgroup formula `G^u ∩ G_F = G_F^{ψ_{F/ℚ₂}(u)}` follows from `lowerRam_tower` and I6.9
    when `F/ℚ₂` is Galois (rv-h-novel R3). Whether `F = L_v(A[3])` is Galois over `ℚ₂` is a
    glue-conductor question.
  - The absolute upper groups `G_{ℚ_p}^u` are needed only through one finite Galois quotient
    containing the fields of `β|_{G_F}` and `F`, so finite-level leaves suffice.

### D4 (N5 L846-852)
- **Definition:** `artinConductor`.
- **Glue:**
  - `artinConductor_le_of_upper`: if `G^v` acts trivially for `v > U ≥ 0`, then
    `f(V) ≤ dim V·(1+U)`. Statement here, `sorry`. glue-conductor proves the numeric core
    (`swan_le`, `artin_le`) on sequences `g_i`. Bridging `lowerRam` to `g_i` is about 100 lines.
  - The ℓ-adic conductor of `r_ℓ` is `codim V^I + Sw(V)`, with `Sw` computed on the finite image
    of wild inertia. Its definition sits at the I4 interface, because Carayol (D5) is stated for
    it, so I6 supplies only the finite-group part.

## 3. Findings

### 3.1 Mathlib inventory (VERIFIED by grep, v4.35.0)
- **Present:** `Field.absoluteGaloisGroup`, `Field.absoluteGaloisGroup.map`,
  `continuousCohomology`, `ContinuousCohomology.map`, `ContinuousCohomology.tateShafarevich`,
  `ContRepresentation.trivial`, `PadicAlgCl` (spectral norm, `NormedField`), `IsAbelianGalois`,
  `IsArithFrobAt`, `differentIdeal` (with `pow_sub_one_dvd_differentIdeal`,
  `dvd_differentIdeal_iff`), `AddSubgroup.inertia`, `Algebra.IsCentral`, `IsSimpleRing`,
  `BrauerGroup` (definition only), `IsCyclotomicExtension.autEquivPow`.
- **Absent:** Skolem–Noether, Hilbert symbol, base change and invariants on `BrauerGroup`,
  Chebotarev, Brauer–Nesbitt, the upper bound for the different, higher ramification groups,
  Herbrand's function, Artin conductor, the local reciprocity map, and the comparison of `H²` with
  inhomogeneous cochains.

### 3.2 Statability verdict
All of I6 is statable now. Only I6.2 and I6.4 use Galois groups of infinite extensions, and both
use Mathlib's `absoluteGaloisGroup`. The local leaves are finite-level and need only commutative
algebra.

### 3.3 Recommended leaf list for the crowdsourcing (I6 part)
1. Skolem–Noether (I6.1).
2. Brauer 2-torsion, as the three cochain-level statements I6.2a′-c′.
3. Local Kronecker–Weber (I6.3).
4. Chebotarev (I6.4).
5. Brauer–Nesbitt (I6.5).
6. Serre's different bound (I6.6).
7. Hilbert's formula (I6.7).
8. Herbrand (I6.8) with transitivity (I6.9).
9. Local CFT with upper numbering (I6.10).

Items 1, 2 (Br form), 4, 7 and 8 have Tau Ceti proofs per the survey. Porting them means checking
that the statements match. For I6.2, it also needs the Kummer bridge to `H²`.

### 3.4 D3 without norm functoriality (SPECULATIVE until reviewed)
N5 L826-829 uses "local reciprocity and the norm map" to get `β⁴ = 1` on `U_F`. Instead:
1. `β⁴ = χ²` on `G_F`.
2. The 2-component of `χ` has conductor dividing 4, so its square is trivial. Hence `χ²` is a
   Dirichlet character of odd conductor and is unramified at 2. Hence `β⁴` is trivial on the
   inertia group of `F`.
3. By I6.10 for the abelian extension cut out by `β|_{G_F}`, `θ_F(U_F) = G_0`. So
   `(β∘θ_F)⁴ = 1` on `U_F`.
4. With `U^{3e+1} ⊆ (U^{e+1})⁴` (glue-conductor), `β∘θ_F` is trivial on `U^{3e+1}`.
5. By I6.10 again, `β` is trivial on `G^v(M/F)` for `v > 3e`.

Only the finite-level reciprocity map for `F` is used. There are no norm compatibilities between
`F` and `ℚ₂`.

### 3.5 The I6 leaves versus hdec-faithful's holes
hdec-faithful (`scratch/hdec-faithful/Leaves.lean` on its branch) has three I6 holes, written
`def … : Prop := sorry`:
- `L15b_BrauerCohomology`: superseded by I6.2a-c, which are stated on `H²` and need no bridge.
- `L16_LocalCFT`: superseded by I6.3 and I6.10.
- `L20_RamificationGroups`: superseded by I6.6-I6.9 with the Part II definitions.

Its `HasseBrauerQ`, a Hasse principle for CSAs, is faithful. B2 manipulates a cocycle, so
using it would need L15b.

## 4. Lean drafts (VERIFIED: `lake env lean scratch/pkg-I6/I6.lean`, no errors)

- **Leaves (`def … : Prop`):** `SkolemNoether`, `BrauerHasse2`, `BrauerReciprocity2`,
  `LocalH2Card`, `BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC`, `LocalKroneckerWeber`,
  `ChebotarevExists`, `BrauerNesbittChar0`, `DifferentBound`, `HilbertDifferentFormula`,
  `HerbrandQuotient`, `HerbrandTransitivity`, `LocalReciprocityUpper`.
- **Proved, with standard axioms (`#print axioms`):** `skolemNoether_aut`,
  `eq_of_same_finite_support`, `cob_of_same_finite_support`, `lowerRam_tower`,
  `eq_of_ne_zero_of_card_two`, `IsCocycle2.sub`, `IsCoboundary2.sub`, `IsCocycle2.resC`.
- **Glue statements with `sorry`:**
  - `artinConductor_le_of_upper` (D4).
  - `sq_principalUnits` (D3; proved by glue-conductor in `Dyadic.lean`).
- **Non-vacuity:** `Check.lean` (instances for `ℤ_[p]`).

## 5. Open checks
1. Read the printed statements of Serre, *Corps locaux* III §6 (the bound on the different), IV
   §§1-3 and XV §2, and of Lang XVII Cor. 3.8. Every locator above is from memory.
2. Read Tau Ceti's statements of `brLocalization_injective`, `h2MuEquivZMod`, `skolemNoether`,
   the Chebotarev density theorem and `upperRamificationGroup`, and compare them with the leaves.
3. Check whether `F = L_v(A[3])` is Galois over `ℚ₂` (D3, rv-h-novel R3), or replace the subgroup
   formula by I6.8 inside one Galois closure.
4. Review §3.4.
