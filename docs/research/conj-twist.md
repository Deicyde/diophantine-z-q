# conj-twist: `ConjTwistNontrivial` and `ConjTwistFromLeaves` (G10 core)

Task conj-twist, 2026-11-13. Lean: `scratch/conj-twist/ConjTwist.lean` (1140 lines). Check it with
`lake env lean scratch/conj-twist/ConjTwist.lean` after `lake build ZInQKernel.HDecomp.LeafPush2.T`.
It has no `sorry`, and all 14 `#print axioms` give `[propext, Classical.choice, Quot.sound]`
(VERIFIED, compiled 2026-11-13). Log: `scratch/conj-twist/log.md`.

## Result

**Both Props are proved in Lean from leaves and four smaller named glue Props.** The leaves are
Faltings, T26, T35 and a Hom form of T11(a). The four glue Props N1, N3, N4 and N5 are
elementary: comparison of points, conjugation, inverse limits and dimension. VERIFIED, compiled:

```
G0Galois.conjTwistNontrivial_of_lattice :
  PkgI3.TateModuleFree → ZInQ.LeafPush2.UniformizationExists →
  ArtinTorsion → HomLinearLift → ConjAntiLift → TateLattice → ConjVarDim →
  ConjTwistNontrivial

G0Galois.conjTwistFromLeaves_of_lattice :
  ArtinTorsion → HomLinearLift → ConjAntiLift → TateLattice → ConjVarDim →
  ConjTwistFromLeaves
```

`ConjTwistNontrivial` and `ConjTwistFromLeaves` are copied verbatim from
`scratch/g10-odd/G10Odd.lean` (L185-205, L383-391; VERIFIED by diff). Neither statement was
changed. `PkgI3.FaltingsTate` is a hypothesis inside `ConjTwistNontrivial`. T26 and T35 are among
the hypotheses of `ConjTwistFromLeaves`, so the second theorem needs only N1-N5. With
g10-odd's `g10Glue_of_conjTwist` and `g10GlueConcrete_of_conjTwistFromLeaves`, this reduces
`G10Glue` and the corrected `G10GlueConcrete` to the same Props.

### What is left

| Name | Kind | Statement | Source / proof |
|---|---|---|---|
| `PkgI3.FaltingsTate` | leaf (in build) | `Hom(A,B) ⊗ ℤ_ℓ ≅ Hom_{G_K}(T_ℓA, T_ℓB)` | Faltings 1983, Satz 4 / Kor. 1 |
| `PkgI3.TateModuleFree` (T26) | leaf (in build) | `T_ℓ A` free of rank `2 dim A` | Mumford §4, §18-19 |
| `UniformizationExists` (T35) | leaf (in build) | `A(ℂ)_σ ≅ ℂ^g/Λ`, analytic | Mumford §1, GAGA |
| N2 `HomLinearLift` | **textbook leaf** (new) | every `f ∈ Hom_K(A,B)` lifts to a `ℂ`-linear `M`: `Φ_B(Mz) = f(Φ_A z)` | Birkenhake–Lange, *Complex abelian varieties*, Prop. 1.2.1, plus holomorphy of algebraic maps (Mumford §1). UNVERIFIED numbers. `T11a_RiemannEnd` is the case `A = B` over `ℂ`. |
| N1 `ArtinTorsion` | glue | `toC : A(K̄) → A(ℂ)_{ι∘alg}`, `P ↦ P ∘ Spec ι`, is injective and onto `n`-torsion | `Spec ℂ → Spec K̄` is fpqc, hence an epimorphism. Both torsion groups have `n^{2g}` elements by T5 over `K̄` and over `ℂ`. STANDARD |
| N4 `TateLattice` | glue | `α : ℤ_ℓ ⊗ Λ ≅ T_ℓ A` with `toC(α(1⊗λ))ₙ = Φ(ℓ⁻ⁿλ)` | follows from N1 by algebra alone: `T_ℓ = lim A(ℂ)[ℓⁿ] = lim ℓ⁻ⁿΛ/Λ = Λ ⊗ ℤ_ℓ`. This is Artin's comparison for abelian varieties, SGA 4 XI 4.4. STANDARD |
| N3 `ConjAntiLift` | glue | if `σ∘s = conj∘σ`, then `twistC : A(ℂ)_σ → A^s(ℂ)_σ` lifts to an injective `ℂ`-antilinear `N` | `z ↦ twistC(Φ z̄)` is a holomorphic uniformization of `A^s(ℂ)_σ = A(ℂ)_{conj∘σ}`. Two uniformizations differ by a `ℂ`-linear isomorphism (BL 1.2.1). STANDARD |
| N5 `ConjVarDim` | glue | `dim A^s = dim A` for a number field `K` | `s` is an automorphism, so `A^s → A` is an isomorphism. STANDARD |

N1 and N3-N5 are true by the arguments in the table. N2 is a consequence of a published
statement, not a strengthening. Each is stated over the project's genuine objects: `PkgI3.AbVar`,
`CPts`, `IsUniformization`, `Tate.T`, and the new concrete `conjVar`, `toC` and `twistC`.

## What the Lean file proves

Everything below compiles, with no `sorry` and the standard axioms.

- **§2 `faltingsV`** (from `FaltingsTate` and T26). A `G_K`-equivariant map
  `V_ℓ(A) → V_ℓ(B)` lies in the `ℚ_ℓ`-span of `{V_ℓ(f) : f ∈ Hom_K(A,B)}`.
- **§3 `conjData`, `exists_twist`.** Fix `K/ℚ` Galois and a complex conjugation `c ∈ G_ℚ`.
  Transport `c` to `cc ∈ Aut(K̄)` along `qEmbRing`. Then `cc` is an involution, preserves `K`,
  and is complex conjugation for `ι = j ∘ qEmbRing⁻¹`. A twist `τ∘cc = cc∘σ` gives
  `resQ τ = c·resQ σ·c⁻¹`, and every `τ ∈ G_K` is a twist of some `σ`.
- **§5 the conjugate variety and `c_*`, as concrete definitions:**
  - `conjVar A s = A ×_{Spec K, Spec s} Spec K` (`Over.pullback`);
  - `conjPt : A(K̄) →* A^s(K̄)`, `P ↦ P ∘ Spec(cc)` read through `Over.map ⊣ Over.pullback`;
  - `conjT` and `conjV` on `T_ℓ` and `V_ℓ`;
  - `conjV_galRep`, the twisted equivariance `c_* ρ_A(σ) = ρ_{A^s}(τ) c_*` whenever `τ∘cc = cc∘σ`.
- **§6 `toC_conjPt`.** `toC(c_* P) = twistC(toC P)`, which is
  `Spec ι ≫ Spec cc = Spec conj ≫ Spec ι` read through the adjunction. This is the point-level
  statement that `c_*` is complex conjugation.
- **§7 naturality from N1.**
  - `homT_tateLattice`: `T_ℓ(f) α_A(1⊗λ) = α_B(1⊗M_fλ)`.
  - `conjT_tateLattice`: `c_* α_A(1⊗λ) = α_{A^s}(1⊗Nλ)`.
  - `lift_mem_lattice`: lifts map lattices to lattices.
- **§8 `lattice_contradiction`, `conjTwistNontrivial_of_lattice`.** In the bases `α(1⊗bᵢ)`, the
  matrices of `c_*` and of `V_ℓ(f)` are the integer matrices of `N` and `M_f`
  (`toMatrix_of_lattice`).
  1. Faltings puts the first matrix in the `ℚ_ℓ`-span of the others.
  2. Rationality (`matrix_mem_of_map_mem_span`, from g10-odd) moves it into their `ℚ`-span.
  3. So `N` is `ℂ`-linear (`toLin_of_lattice`; a `ℤ`-basis of `Λ` is an `ℝ`-basis of `ℂ^g`).
  4. `N` is also antilinear, so `N = 0`, which contradicts injectivity.
- **§4-§5, an intermediate route.** It is not needed for the main result, but it compiles.
  - `ConjBettiData`: a conjugate variety and a Betti `ℚ`-structure, stated over abstract `H, J`.
  - `ConjBettiComparison`: the same for the concrete `c_*`.
  - Proved: `conjTwistNontrivial_of_conjBettiData`, `conjBettiData_of_comparison`,
    `conjTwistNontrivial_of_comparison`, `conjTwistFromLeaves_of_comparison`.

## Findings

- **F1 (VERIFIED, compiled).** `ConjTwistNontrivial` is true and is not vacuous. g10-odd's
  `exists_resQ_conj` shows that the twist condition constrains every `σ`. The proof above derives
  it from published results and true glue. The rank-4, division and noncommutativity hypotheses
  of `G10Glue` play no role, and neither does `IsGalois` except through `cc` preserving `K`.
- **F2 (VERIFIED, compiled).** The conjugate variety `A^s`, the transport `c_*` and its twisted
  equivariance are now Lean definitions and theorems. g10-odd listed them as missing. They need
  no leaf, only Mathlib's `Over.pullback` adjunction, following scratch/unram-tate/BCPoints.lean.
- **F3 (argument).** N2 cannot be derived from `T11a_RiemannEnd`. T11a covers only `End` of an
  abelian variety over `ℂ`. `Hom(A, A^s)` over `K` would need products `A × A^s`, which `AbVar`
  lacks, or a separate Hom statement. So N2 is a new leaf from the same sources as T11(a).
- **F4 (argument).** N4 follows from N1 by algebra alone: inverse limits and `Λ ≅ ℤ^{2g}`. No
  geometry enters, so N4 is a good first formalization target. N1 itself needs T5 over `ℂ` and the
  epimorphism property of `Spec ℂ → Spec K̄`.
- **F5 (statement choice).** N3's conclusion includes `Function.Injective N`. This is true,
  because `N` lifts the bijection `twistC`, and the proof uses it to get `N ≠ 0`. The opaque
  placeholders T11 and T12 of `G10Glue` (g10-odd F1) are not used anywhere.

## Integration recommendation

Use `conjTwistFromLeaves_of_lattice` with g10-odd's `g10GlueConcrete_of_conjTwistFromLeaves`.
G10 then rests on Faltings, T5, T26, T35, T11(b) (unused), the new leaf N2, and the glue N1, N3,
N4 and N5.
