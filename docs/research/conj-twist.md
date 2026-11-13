# conj-twist: `ConjTwistNontrivial` and `ConjTwistFromLeaves` (G10 core)

Task conj-twist, 2026-11-13. Lean: `scratch/conj-twist/ConjTwist.lean` (1830 lines). Check it
with `lake env lean scratch/conj-twist/ConjTwist.lean` after
`lake build ZInQKernel.HDecomp.LeafPush2.T`. It has no `sorry`, and all 32 `#print axioms` give
`[propext, Classical.choice, Quot.sound]` (VERIFIED, compiled 2026-11-13). Log:
`scratch/conj-twist/log.md`.

## Result

**`ConjTwistFromLeaves` is proved in Lean from one new textbook leaf and one analytic glue
Prop. `ConjTwistNontrivial` also needs the leaves already in the build.** VERIFIED, compiled:

```
G0Galois.conjTwistFromLeaves_final' :
  HomLinearLift → ConjUniformizationAnalytic → ConjTwistFromLeaves

G0Galois.conjTwistNontrivial_final' :
  PkgI2.TorsionStructure → PkgI3.TateModuleFree → ZInQ.LeafPush2.UniformizationExists →
  HomLinearLift → ConjUniformizationAnalytic → ConjTwistNontrivial
```

`ConjTwistNontrivial` and `ConjTwistFromLeaves` are copied verbatim from
`scratch/g10-odd/G10Odd.lean` (L185-205, L383-391; VERIFIED by diff). Neither statement was
changed.
- `PkgI3.FaltingsTate` (Faltings 1983) is a hypothesis inside `ConjTwistNontrivial`.
- T5 (`TorsionStructure`), T26 (`TateModuleFree`) and T35 (`UniformizationExists`) are among the
  hypotheses of `ConjTwistFromLeaves`. That is why the first theorem needs only the two new Props.
- With g10-odd's `g10Glue_of_conjTwist` and `g10GlueConcrete_of_conjTwistFromLeaves`, this
  reduces `G10Glue` and the corrected `G10GlueConcrete` to the same Props.

### What is left

| Name | Kind | Statement | Source / proof |
|---|---|---|---|
| `PkgI3.FaltingsTate` | leaf (in build) | `Hom(A,B) ⊗ ℤ_ℓ ≅ Hom_{G_K}(T_ℓA, T_ℓB)` | Faltings 1983, Satz 4 / Kor. 1 |
| `PkgI2.TorsionStructure` (T5) | leaf (in build) | `A(K̄)[n] ≅ (ℤ/n)^{2g}` | Mumford §4 |
| `PkgI3.TateModuleFree` (T26) | leaf (in build) | `T_ℓ A` free of rank `2 dim A` | Mumford §4, §18-19 |
| `UniformizationExists` (T35) | leaf (in build) | `A(ℂ)_σ ≅ ℂ^g/Λ`, analytic, `Λ` a full lattice | Mumford §1, GAGA |
| `HomLinearLift` (N2) | **textbook leaf** (new) | for uniformizations `Φ_A, Φ_B` of `A(ℂ)_σ, B(ℂ)_σ` (`g = dim`), every `f ∈ Hom_K(A,B)` lifts to a `ℂ`-linear `M` with `Φ_B(Mz) = f(Φ_A z)` | Birkenhake–Lange, *Complex abelian varieties*, Prop. 1.2.1, with holomorphy of algebraic morphisms (Mumford §1). UNVERIFIED numbers. `T11a_RiemannEnd`'s second half is the case `A = B` over `ℂ`. |
| `ConjUniformizationAnalytic` (N3a-an) | glue | let `σ∘s = conj∘σ`, `Φ` a uniformization of `A(ℂ)_σ`, and `ψ(z) = twistC(Φ(z̄))`, where `twistC : A(ℂ)_σ → A^s(ℂ)_σ` is `Q ↦ Q ∘ Spec(conj)` read through `A^s(ℂ)_σ = A(ℂ)_{σ∘s}`. Then `ψ⁻¹(U(ℂ))` is open and every regular function of `A^s` on `U` is holomorphic along `ψ`, for every open `U` of `A^s` | On an affine chart `Spec(R ⊗_{K,s} K)`, the value of `r ⊗ k` at `ψ(z)` is `conj(r(Φ(z̄)))·σ(k)`, and `z ↦ conj(f(z̄))` is holomorphic when `f` is. STANDARD |

Both new Props are true by the arguments in the table, and both are stated over the project's
genuine objects: `PkgI3.AbVar`, `CPts`, `IsUniformization`, `cDom`, `cEvalAt`, and the new
concrete `conjVar`, `twistC` and `conjL`. N2 is a consequence of a published statement, not a
strengthening. N3a-an is exactly the two analytic clauses of `IsUniformization` for `ψ`. The three
group-theoretic clauses are proved (`conjUniformization_of_analytic`).

## How the proof goes (all compiled)

1. **Complex conjugation on `K̄`** (§3 `conjData`, `exists_twist`). Transport `c` along
   `qEmbRing : ℚ̄ ≅ K̄` to `cc`. Then `cc` is an involution, preserves `K` (`K/ℚ` normal), and is
   complex conjugation for `ι = j ∘ qEmbRing⁻¹`. A twist `τ∘cc = cc∘σ` gives
   `resQ τ = c·resQ σ·c⁻¹`, and every `τ ∈ G_K` is a twist.
2. **The conjugate variety and `c_*`** (§5). Let `s = cc|_K` (`restrictK`).
   - `conjVar A s = A ×_{Spec K, Spec s} Spec K` (`Over.pullback`).
   - `conjPt : A(K̄) →* A^s(K̄)`, `P ↦ P ∘ Spec(cc)` through `Over.map ⊣ Over.pullback`.
   - `conjT`, `conjV` on `T_ℓ` and `V_ℓ`, with `conjV_galRep`:
     `c_* ρ_A(σ) = ρ_{A^s}(τ) c_*` whenever `τ∘cc = cc∘σ`.
   - Under the negated conclusion of `ConjTwistNontrivial`, `c_*` is `G_K`-equivariant.
3. **Faltings** (§2 `faltingsV`, from `FaltingsTate` and T26). An equivariant
   `V_ℓ(A) → V_ℓ(A^s)` lies in the `ℚ_ℓ`-span of `{V_ℓ(f) : f ∈ Hom_K(A, A^s)}`.
4. **Uniformizations and lifts.**
   - T35 gives `Φ_A`, `Φ_B` for `A` and `A^s` at `σ = ι∘alg`. This uses `dim A^s = dim A`,
     proved as `conjVarDim`: `Spec(s)` is an isomorphism.
   - N2 gives `ℂ`-linear lifts `M_f`. N2 and N3a give an injective antilinear lift `N` of
     `twistC` (`conjAntiLiftLat_of`): N2 is applied to `id` of `A^s` with `ψ` and `Φ_B`, and
     `eq_zero_of_real_smul_mem` gives injectivity.
   - Lifts map lattices to lattices (`lift_mem_lattice`).
5. **Artin comparison** (§11-§13).
   - `toC : A(K̄) → A(ℂ)`, `P ↦ P ∘ Spec ι`, is injective (`toC_injective`, via Mathlib's
     `ext_of_isDominant_of_isSeparated`).
   - It is onto torsion (`torsion_surj_of_T5`): `A(ℂ)[n] ↪ (ℤ/n)^{2g}` by lattice coordinates, and
     `|A(K̄)[n]| = n^{2g}` by T5.
   - `x(λ)ₙ = toC⁻¹Φ(ℓ⁻ⁿλ)` defines an injective `ℤ_ℓ ⊗ Λ → T_ℓ(A)`
     (`xLin_liftBaseChange_injective`).
   - It is natural for `f` and for `c_*` (`homT_tateLattice`, `conjT_tateLattice`, with
     `toC_conjPt`: `toC(c_* P) = twistC(toC P)`).
6. **The contradiction** (§10 `conjTwistNontrivial_of_latticeInj`, §8 `lattice_contradiction`).
   - `ℚ_ℓ` is flat over `ℤ_ℓ`, so `ℚ_ℓ ⊗ α_B` is injective. On `ℚ_ℓ ⊗ (ℤ_ℓ ⊗ Λ)`, `c_*` and
     `V_ℓ(f)` become the base changes of `N|_Λ` and `M_f|_Λ`.
   - Their integer matrices satisfy: `N ∈ span_{ℚ_ℓ}{M_f}`. Rationality
     (`matrix_mem_of_map_mem_span`, from g10-odd) gives `N ∈ span_ℚ{M_f}`.
   - A `ℤ`-basis of `Λ` is an `ℝ`-basis of `ℂ^g`, so `N` is `ℂ`-linear. It is also antilinear,
     so `N = 0`, which contradicts injectivity.

The file also keeps the intermediate routes, all compiled:
- `ConjBettiData` and `ConjBettiComparison` (an abstract Betti `ℚ`-structure);
- `ArtinTorsion`, `ArtinTorsionSurj`, `TateLattice`, `TateLatticeInj`, `ConjAntiLift`,
  `ConjAntiLiftLat`, `ConjUniformization`, `ConjVarDim`, with their reductions.

Each of these is now proved, or implied by the two remaining Props.

## Findings

- **F1 (VERIFIED, compiled).** `ConjTwistNontrivial` is true and is not vacuous. g10-odd's
  `exists_resQ_conj` shows that the twist condition constrains every `σ`. The proof derives it
  from published results and the true glue N3a-an. The rank-4, division and noncommutativity
  hypotheses of `G10Glue` play no role. `IsGalois ℚ K` is used only to make `cc` preserve `K`.
- **F2 (VERIFIED, compiled).** Everything g10-odd listed as missing is now a Lean definition or
  theorem: the conjugate variety, `c_*`, the Artin comparison at `ι` with its compatibility with
  `c_*`, and the instantiation of the Betti argument. The only analytic input is the leaf N2 plus
  N3a-an. The opaque placeholders T11 and T12 of `G10Glue` (g10-odd F1) are not used.
- **F3 (argument).** `HomLinearLift` cannot be derived from `T11a_RiemannEnd`. T11a covers only
  `End` of an abelian variety over `ℂ`. `Hom(A, A^s)` over a number field would need products, or
  base change plus a transport of `IsUniformization`, neither of which is available. So N2 is a
  new leaf from the same sources as T11(a). The proof uses it twice: for `Hom(A, A^s)`, and for
  `id_{A^s}` to compare two uniformizations.
- **F4 (VERIFIED, compiled).** T11(a) and T11(b), hypotheses of `ConjTwistFromLeaves`, are unused.
- **F5 (next step).** N3a-an is about regular functions of a base change `A ×_{Spec s} Spec K`
  evaluated at conjugated points. Formalizing it needs the affine-chart description of sections of
  a pullback and the holomorphy of `z ↦ conj(f(z̄))`. No covering or lifting theory is needed.

## Integration recommendation

Replace `odd : G10Glue` in g0-mod-galois's `GaloisPieces` by the pair
`HomLinearLift` (leaf) and `ConjUniformizationAnalytic` (glue). Then use
`conjTwistFromLeaves_final'` with g10-odd's `g10GlueConcrete_of_conjTwistFromLeaves`.
