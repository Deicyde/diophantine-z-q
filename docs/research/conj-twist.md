# conj-twist: `ConjTwistNontrivial` and `ConjTwistFromLeaves` (G10 core)

Task conj-twist, 2026-11-13. Lean: `scratch/conj-twist/ConjTwist.lean`. Check it with
`lake env lean scratch/conj-twist/ConjTwist.lean` after `lake build ZInQKernel.HDecomp.LeafPush2.T`.
It has no `sorry`, and every `#print axioms` gives `[propext, Classical.choice, Quot.sound]`
(VERIFIED, compiled 2026-11-13). Log: `scratch/conj-twist/log.md`.

## Result

**Both Props are proved in Lean from leaves and two smaller named glue Props.** VERIFIED,
compiled:

```
G0Galois.conjTwistNontrivial_main :
  PkgI3.TateModuleFree → ZInQ.LeafPush2.UniformizationExists →
  ArtinTorsionSurj → HomLinearLift → ConjUniformization → ConjTwistNontrivial

G0Galois.conjTwistFromLeaves_main :
  ArtinTorsionSurj → HomLinearLift → ConjUniformization → ConjTwistFromLeaves
```

`ConjTwistNontrivial` and `ConjTwistFromLeaves` are copied verbatim from
`scratch/g10-odd/G10Odd.lean` (L185-205, L383-391; VERIFIED by diff). Neither statement was
changed. `PkgI3.FaltingsTate` is a hypothesis inside `ConjTwistNontrivial`. T26
(`TateModuleFree`) and T35 (`UniformizationExists`) are among the hypotheses of
`ConjTwistFromLeaves`. With g10-odd's `g10Glue_of_conjTwist` and
`g10GlueConcrete_of_conjTwistFromLeaves`, this reduces `G10Glue` and the corrected
`G10GlueConcrete` to the same Props.

### What is left

| Name | Kind | Statement | Source / proof |
|---|---|---|---|
| `PkgI3.FaltingsTate` | leaf (in build) | `Hom(A,B) ⊗ ℤ_ℓ ≅ Hom_{G_K}(T_ℓA, T_ℓB)` | Faltings 1983, Satz 4 / Kor. 1 |
| `PkgI3.TateModuleFree` (T26) | leaf (in build) | `T_ℓ A` free of rank `2 dim A` | Mumford §4, §18-19 |
| `UniformizationExists` (T35) | leaf (in build) | `A(ℂ)_σ ≅ ℂ^g/Λ`, analytic, `Λ` a full lattice | Mumford §1, GAGA |
| `HomLinearLift` (N2) | **textbook leaf** (new) | for uniformizations `Φ_A, Φ_B` of `A(ℂ)_σ, B(ℂ)_σ`, every `f ∈ Hom_K(A,B)` lifts to a `ℂ`-linear `M`: `Φ_B(Mz) = f(Φ_A z)` | Birkenhake–Lange, *Complex abelian varieties*, Prop. 1.2.1, with holomorphy of algebraic morphisms (Mumford §1). UNVERIFIED numbers. `T11a_RiemannEnd`'s second half is the case `A = B` over `ℂ`. |
| `ArtinTorsionSurj` (N1-surj) | glue | every `n`-torsion point of `A(ℂ)_{ι∘alg}` is `toC P = P ∘ Spec ι` for some `P ∈ A(K̄)` | `toC` is injective (proved, `toC_injective`). `A(K̄)[n]` and `A(ℂ)[n]` both have `n^{2g}` elements by T5 over `K̄` and over `ℂ`. Equivalently, `A[n]` is finite étale in characteristic 0. STANDARD |
| `ConjUniformization` (N3a) | glue | if `σ∘s = conj∘σ` and `Φ` uniformizes `A(ℂ)_σ` with kernel `Λ`, then `z ↦ twistC(Φ z̄)` uniformizes `A^s(ℂ)_σ` with kernel `Λ̄`. Here `twistC : A(ℂ)_σ → A^s(ℂ)_σ` is `Q ↦ Q ∘ Spec(conj)` read through `A^s(ℂ)_σ = A(ℂ)_{σ∘s}` | `twistC` is a bijective homomorphism (`twistC_injective`, `twistC_one`). On affine charts it conjugates the values of regular functions, and `z ↦ conj(f(z̄))` is holomorphic when `f` is. STANDARD |

N3a replaces the earlier `ConjAntiLift` (N3: `twistC` lifts to an injective antilinear `N`).
`conjAntiLiftLat_of` proves N3 (for number fields and full lattices) from N2 and N3a. It applies
N2 to the identity of `A^s` with the uniformizations `z ↦ twistC(Φ z̄)` and `Φ'`, sets
`N = M ∘ conj`, and gets injectivity from `eq_zero_of_real_smul_mem`.

Both glue Props are true by the arguments in the table. Both are stated over the project's
genuine objects (`PkgI3.AbVar`, `CPts`, `IsUniformization`) and the new concrete `toC`, `conjVar`
and `twistC`. N2 is a consequence of a published statement, not a strengthening.

**Reductions that were glue in g10-odd and are now proved:**
- the conjugate variety and `c_*`;
- the Artin comparison `ℤ_ℓ ⊗ Λ ↪ T_ℓ(A)` (from N1);
- its naturality;
- `dim A^s = dim A`;
- the injectivity of `A(K̄) → A(ℂ)`;
- the Faltings + rationality + holomorphy argument.

## What the Lean file proves

Everything below compiles, with no `sorry` and the standard axioms.

- **§2 `faltingsV`** (from `FaltingsTate` and T26). A `G_K`-equivariant map
  `V_ℓ(A) → V_ℓ(B)` lies in the `ℚ_ℓ`-span of `{V_ℓ(f) : f ∈ Hom_K(A,B)}`.
- **§3 `conjData`, `exists_twist`.** For `K/ℚ` Galois and a complex conjugation `c ∈ G_ℚ`, let
  `cc ∈ Aut(K̄)` be `c` transported along `qEmbRing`. Then `cc` is an involution, preserves `K`,
  and is complex conjugation for an embedding `ι : K̄ → ℂ`. A twist `τ∘cc = cc∘σ` gives
  `resQ τ = c·resQ σ·c⁻¹`, and every `τ` is a twist of some `σ`.
- **§5 the conjugate variety and `c_*`:**
  - `conjVar A s = A ×_{Spec K, Spec s} Spec K` (`Over.pullback`);
  - `conjPt : A(K̄) →* A^s(K̄)`, `P ↦ P ∘ Spec(cc)` through `Over.map ⊣ Over.pullback`;
  - `conjT` and `conjV` on `T_ℓ` and `V_ℓ`;
  - `conjV_galRep`, the twisted equivariance `c_* ρ_A(σ) = ρ_{A^s}(τ) c_*`.
- **§6 `toC_conjPt`.** `toC(c_* P) = twistC(toC P)`: at the level of points, `c_*` is complex
  conjugation.
- **§7 naturality.** `homT_tateLattice` and `conjT_tateLattice` (with `lift_mem_lattice`):
  `T_ℓ(f) α_A(1⊗λ) = α_B(1⊗M_fλ)` and `c_* α_A(1⊗λ) = α_{A^s}(1⊗Nλ)`.
- **§8 `lattice_contradiction`.** Suppose the integer matrix of an antilinear `N ≠ 0` lies in the
  `ℚ_ℓ`-span of the integer matrices of `ℂ`-linear maps. Rationality
  (`matrix_mem_of_map_mem_span`, from g10-odd) puts it in their `ℚ`-span. A `ℤ`-basis of `Λ` is
  an `ℝ`-basis of `ℂ^g` (`toLin_of_lattice`), so `N` is `ℂ`-linear. It is also antilinear, so
  `N = 0`, a contradiction.
- **§9 `conjVarDim`** (glue N5, proved). For a number field, `Spec(s)` is an isomorphism, so
  `A^s ≅ A` and the dimensions are equal.
- **§10 `conjTwistNontrivial_of_latticeInj`.** An injective comparison `α` suffices: `ℚ_ℓ` is flat
  over `ℤ_ℓ`, so postcomposition with `ℚ_ℓ ⊗ α_B` is injective, and the matrices are taken on
  `ℚ_ℓ ⊗ (ℤ_ℓ ⊗ Λ)`.
- **§11 `tateLatticeInj_of_artinTorsion`** (glue N4', proved from N1). `x(λ)ₙ` is the unique
  `K̄`-point with `toC(x(λ)ₙ) = Φ(ℓ⁻ⁿλ)`, and the `ℤ_ℓ`-linear extension is injective:
  `Σ (aᵢ mod ℓⁿ) bᵢ ∈ ℓⁿΛ` forces `ℓⁿ ∣ (aᵢ mod ℓⁿ)` for every `n`.
- **§9b `conjAntiLiftLat_of`** (N3 from N2 and N3a, proved).
- **§12 `toC_injective`** (half of N1, proved). Mathlib's `ext_of_isDominant_of_isSeparated`
  applies: `Spec ℂ → Spec K̄` is surjective, `Spec K̄` is reduced, and `A` is proper.
- **Intermediate routes, also compiled.**
  - `ConjBettiData`, `ConjBettiComparison`: an abstract Betti `ℚ`-structure.
  - `ArtinTorsion`, `TateLattice`, `TateLatticeInj`: earlier forms of N1 and N4.
  - Reductions: `conjTwistNontrivial_of_conjBettiData`, `_of_comparison`, `_of_lattice`,
    `_of_latticeInj`, `_of_N123`.

## Findings

- **F1 (VERIFIED, compiled).** `ConjTwistNontrivial` is true and is not vacuous. g10-odd's
  `exists_resQ_conj` shows that the twist condition constrains every `σ`. The proof above derives
  it from published results and true glue. The rank-4, division and noncommutativity hypotheses
  of `G10Glue` play no role. `IsGalois ℚ K` is used only to make `cc` preserve `K`.
- **F2 (VERIFIED, compiled).** The objects g10-odd listed as missing are now Lean definitions and
  theorems, needing no leaf beyond Faltings and T26: the conjugate variety `A^s`, `c_*`, its
  twisted equivariance, the comparison `ℤ_ℓ ⊗ Λ ↪ T_ℓ(A)` and its naturality.
- **F3 (argument).** `HomLinearLift` cannot be derived from `T11a_RiemannEnd`. T11a covers only
  `End` of an abelian variety over `ℂ`. `Hom(A, A^s)` over `K` would need products `A × A^s`,
  which `AbVar` lacks. So N2 is a new leaf from the same sources as T11(a).
- **F4 (statement choice).** `ConjAntiLift` asserts `Function.Injective N`. This is true, because
  `N` lifts the bijection `twistC`, and the proof uses it to get `N ≠ 0`. The opaque placeholders
  T11 and T12 of `G10Glue` (g10-odd F1) are not used anywhere.
- **F5 (next steps).**
  - N1-surj needs T5 over `ℂ`. That means base change of `A` along `σ`, an invariance-of-dimension
    statement, and `AlgebraicClosure ℂ ≅ ℂ`.
  - N3a is a statement about regular functions of `A^s = A ×_{Spec s} Spec K` and complex
    conjugation. No lifting or covering theory is needed.

## Integration recommendation

Use `conjTwistFromLeaves_main` with g10-odd's `g10GlueConcrete_of_conjTwistFromLeaves`.
G10 then rests on:
- the leaves Faltings, T26, T35 and the new N2 (T5, T11a and T11b are hypotheses of
  `ConjTwistFromLeaves` but are unused);
- the glue N1-surj and N3a.
