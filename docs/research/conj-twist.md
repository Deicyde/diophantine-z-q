# conj-twist: `ConjTwistNontrivial` and `ConjTwistFromLeaves` (G10 core)

Task conj-twist, 2026-11-13. Lean: `scratch/conj-twist/ConjTwist.lean` (2226 lines). Check it
with `lake env lean scratch/conj-twist/ConjTwist.lean` after
`lake build ZInQKernel.HDecomp.LeafPush2.T ZInQKernel.HDecomp.I3Linalg.C2`. It has no `sorry`,
and all 41 `#print axioms` give `[propext, Classical.choice, Quot.sound]` (VERIFIED, compiled
2026-11-13 06:56). Log:
`scratch/conj-twist/log.md`.

## Result

**`ConjTwistFromLeaves` is proved in Lean from one new textbook leaf, `HomLinearLift`. No glue
remains. `ConjTwistNontrivial` is proved from that leaf and three leaves already in the build.**
VERIFIED, compiled:

```
G0Galois.conjTwistFromLeaves_of_homLinearLift :
  HomLinearLift → ConjTwistFromLeaves

G0Galois.conjTwistNontrivial_of_leaves :
  PkgI2.TorsionStructure → PkgI3.TateModuleFree → ZInQ.LeafPush2.UniformizationExists →
  HomLinearLift → ConjTwistNontrivial

-- corollaries (§17; G10Glue, G10GlueConcrete copied verbatim from scratch/g10-odd)
G0Galois.g10GlueConcrete_of_homLinearLift : HomLinearLift → G10GlueConcrete
G0Galois.g10Glue_of_leaves :
  PkgI2.TorsionStructure → PkgI3.TateModuleFree → ZInQ.LeafPush2.UniformizationExists →
  HomLinearLift → G10Glue
```

`ConjTwistNontrivial` and `ConjTwistFromLeaves` are copied verbatim from
`scratch/g10-odd/G10Odd.lean` (L185-205, L383-391; VERIFIED by diff). Neither statement was
changed.
- `PkgI3.FaltingsTate` (Faltings 1983, Satz 4 / Kor. 1) is a hypothesis inside
  `ConjTwistNontrivial`.
- T5 (`TorsionStructure`), T26 (`TateModuleFree`) and T35 (`UniformizationExists`) are hypotheses
  of `ConjTwistFromLeaves`, alongside T11(a) and T11(b), which are unused.
- Composing with g10-odd's reductions (copied verbatim in §17) gives:
  - the corrected `G10GlueConcrete` from `HomLinearLift` alone;
  - `G10Glue` from `HomLinearLift` plus T5, T26 and T35.

  Both corollaries compile.

### The one new leaf

```
def HomLinearLift : Prop :=
  ∀ (K : Type) [Field K] (A B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛA : Submodule ℤ (Fin g → ℂ)) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization σ ΛA ΦA → IsUniformization σ ΛB ΦB →
    ∀ f : PkgI3.AbVar.Hom A B, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ),
      ∀ z, ΦB (M z) = ΦA z ≫ f.hom
```

It says that a homomorphism of abelian varieties lifts along analytic uniformizations to a
`ℂ`-linear map. Sources: Birkenhake–Lange, *Complex abelian varieties*, Prop. 1.2.1 (holomorphic
maps of complex tori lift to affine maps, and to linear maps for homomorphisms), plus the
holomorphy of algebraic morphisms (Mumford, *Abelian varieties*, §1). Theorem numbers are
UNVERIFIED. It is a consequence of the published statements, not a strengthening. Its objects are
the project's own: `CPts`, `IsUniformization`, `PkgI3.AbVar.Hom`, also used by T35 and T11(a).
`T11a_RiemannEnd`'s second half is the case `A = B` over `ℂ`. Why N2 does not follow from T11a is
explained in F3.

The proof uses N2 twice: for `f ∈ Hom_K(A, A^s)`, and for `id_{A^s}` to compare two
uniformizations of `A^s`.

## How the proof goes (all compiled)

1. **Complex conjugation on `K̄`** (§3 `conjData`, `exists_twist`). Transport `c ∈ G_ℚ` along
   `qEmbRing : ℚ̄ ≅ K̄` to `cc`. Then `cc` is an involution, preserves `K` (`K/ℚ` normal), and is
   complex conjugation for `ι = j ∘ qEmbRing⁻¹`. A twist `τ∘cc = cc∘σ` gives
   `resQ τ = c·resQ σ·c⁻¹`, and every `τ ∈ G_K` is a twist.
2. **The conjugate variety and `c_*`** (§5). Let `s = cc|_K`.
   - `conjVar A s = A ×_{Spec K, Spec s} Spec K` (`Over.pullback`).
   - `conjPt : A(K̄) →* A^s(K̄)`, `P ↦ P ∘ Spec(cc)` through `Over.map ⊣ Over.pullback`.
   - `conjT`, `conjV` on `T_ℓ` and `V_ℓ`, with twisted equivariance (`conjV_galRep`).
   - If the conclusion of `ConjTwistNontrivial` fails, `c_*` is `G_K`-equivariant.
3. **Faltings** (§2 `faltingsV`, from `FaltingsTate` and T26). An equivariant
   `V_ℓ(A) → V_ℓ(A^s)` lies in the `ℚ_ℓ`-span of `{V_ℓ(f) : f ∈ Hom_K(A, A^s)}`.
4. **Uniformizations** (T35 for `A` and `A^s` at `σ = ι∘alg`).
   - `dim A^s = dim A` (`conjVarDim`: `Spec(s)` is an isomorphism for a number field).
   - `ψ = twistC ∘ Φ_A ∘ conj` is a uniformization of `A^s(ℂ)_σ`, where
     `twistC : A(ℂ)_σ → A^s(ℂ)_σ` is `Q ↦ Q ∘ Spec(conj)` through the adjunction.
   - The group clauses come from `twistC_mul`, `twistC_injective` and `twistC_surjective`.
   - The analytic clauses come from `twistCEval` and `differentiableOn_conj_conj`.
     - `twistCEval`: for `fst : A^s ≅ A`, `(twistC Q).left = Spec(conj) ≫ Q.left ≫ fst⁻¹`.
       Sections at `twistC Q` are complex conjugates, by `ΓSpecIso` naturality.
     - `differentiableOn_conj_conj`: `z ↦ conj(F(z̄))` is holomorphic on `ℂ^g` where `F` is.
5. **Lifts.**
   - N2 gives `ℂ`-linear `M_f`.
   - N2 for `id_{A^s}` (from `ψ` to `Φ_B`), composed with `conj`, gives an injective antilinear
     lift `N` of `twistC` (`conjAntiLiftLat_of`, `eq_zero_of_real_smul_mem`).
   - All lifts map lattices to lattices.
6. **Artin comparison** (§11-§13).
   - `toC : A(K̄) → A(ℂ)`, `P ↦ P ∘ Spec ι`, is injective (`toC_injective`, by
     `ext_of_isDominant_of_isSeparated`).
   - It is onto torsion (`torsion_surj_of_T5`): `A(ℂ)[n] ↪ (ℤ/n)^{2g}` by lattice coordinates, and
     `|A(K̄)[n]| = n^{2g}` by T5.
   - `x(λ)ₙ = toC⁻¹Φ(ℓ⁻ⁿλ)` defines an injective `ℤ_ℓ ⊗ Λ → T_ℓ(A)`.
   - It is natural for `f` and for `c_*` (`homT_tateLattice`, `conjT_tateLattice`,
     `toC_conjPt`).
7. **Contradiction** (§10, §8).
   - `ℚ_ℓ` is flat over `ℤ_ℓ`, so on `ℚ_ℓ ⊗ (ℤ_ℓ ⊗ Λ)` the integer matrix of `N` lies in the
     `ℚ_ℓ`-span of the integer matrices of the `M_f`.
   - By rationality (`matrix_mem_of_map_mem_span`, g10-odd) it lies in their `ℚ`-span.
   - A `ℤ`-basis of `Λ` is an `ℝ`-basis of `ℂ^g`, so `N` is `ℂ`-linear. It is also antilinear,
     so `N = 0`, which contradicts injectivity.

**Intermediate Props in the file.**
- Proved, and used by the final proof: `TateLatticeInj`, `ConjAntiLiftLat`, `ConjUniformization`,
  `ConjUniformizationAnalytic`, `TwistCEval`, `ConjVarDim`, and torsion surjectivity under a
  uniformization.
- Kept for reference, with reductions to the target, but neither proved nor needed:
  `ArtinTorsion`, `ArtinTorsionSurj` (both without a uniformization), `TateLattice`,
  `ConjAntiLift`, `ConjBettiData`, `ConjBettiComparison`.

## Findings

- **F1 (VERIFIED, compiled).** `ConjTwistNontrivial` is true and is not vacuous. g10-odd's
  `exists_resQ_conj` shows that the twist condition constrains every `σ`. The proof derives it
  from Faltings, T5, T26, T35 and N2. The rank-4, division and noncommutativity hypotheses of
  `G10Glue` play no role. `IsGalois ℚ K` is used only to make `cc` preserve `K`.
- **F2 (VERIFIED, compiled).** Everything g10-odd listed as missing is now a Lean theorem:
  - the conjugate variety `A^s` and `c_*`;
  - the Artin comparison at `ι` and its compatibility with `c_*`;
  - the antiholomorphy of complex conjugation;
  - the instantiation of the Betti argument.

  The opaque placeholders T11 and T12 of `G10Glue` (g10-odd F1) are not used. Neither is
  `T12_ComplexConjEigen`.
- **F3 (argument).** N2 cannot be derived from `T11a_RiemannEnd`. T11a covers only `End` of an
  abelian variety over `ℂ`. `Hom(A, A^s)` over a number field would need products of abelian
  varieties, or base change to `ℂ` with a transport of `IsUniformization`, neither of which is
  available. N2 is the Hom form from the same sources as T11(a).
- **F4 (VERIFIED, compiled).** T11(a) and T11(b), hypotheses of `ConjTwistFromLeaves`, are
  unused.

## Integration recommendation

Replace `odd : G10Glue` in g0-mod-galois's `GaloisPieces` by the leaf `HomLinearLift`, and
derive G10 with `g10Glue_of_leaves` (or `g10GlueConcrete_of_homLinearLift`).

G10 then rests on Faltings, T5, T26, T35 and the new textbook leaf `HomLinearLift`, all over
genuine definitions, with no glue.
