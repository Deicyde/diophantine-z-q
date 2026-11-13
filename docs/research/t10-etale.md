# t10-etale: T10 stated Galois-equivariantly over Mathlib's ℓ-adic cohomology

## Verdict

**T10 is now a concrete leaf in the Galois-equivariant form the decomposition asks for.** The
statement is `T10Etale.T10_TateDuality` in `scratch/t10-etale/T10Etale.lean` (VERIFIED, compiled).
It reads:

> For every field `K`, abelian variety `A/K` and prime `ℓ` with `(ℓ : K) ≠ 0`, there is a
> `ℤ_ℓ`-linear isomorphism `φ : H¹(A_K̄, ℤ_ℓ) ≃ Hom_{ℤ_ℓ}(T_ℓ A, ℤ_ℓ)` with
> `φ (σ · x) = (σ · φ(x))` for every `σ ∈ Gal(K̄/K)`.

Here `H¹` is Mathlib's pro-étale `Scheme.EllAdicCohomology`, and `σ · f = f ∘ σ⁻¹` is the
contragredient action.

This goes beyond leaf-push2's `T10_groupIso`, which was an isomorphism of abelian groups only. It
was possible because Mathlib v4.35 already contains everything needed to *construct* the missing
structure, so none of it is invented:
- functoriality of sheaf cohomology in the sheaf (`Sheaf.H.map`);
- `Ext` along exact functors (`Ext.mapExactFunctor`, `Functor.mapExt_bijective_of_preservesInjectiveObjects`);
- equivalences of sites (`Equivalence.sheafCongr`);
- `MorphismProperty.Over.map/mapId/mapComp`;
- the description of the small pro-étale topology by its precoverage.

This task builds the following on top of Mathlib, all proved, no `sorry`, axioms `propext`,
`Classical.choice`, `Quot.sound` only (VERIFIED, `#print axioms`):
1. **The `ℤ_ℓ`-module structure** on `EllAdicCohomology X ℓ n`. `a ∈ ℤ_ℓ` acts through the sheaf
   endomorphism "multiply by `a`" of `U ↦ C(U, ℤ_ℓ)`.
2. **Transport `e_*` along a scheme isomorphism** `e : X ≅ Y`. It is `ℤ_ℓ`-linear and bijective,
   and in degree 0 it is `f ↦ f ∘ e⁻¹`.
3. **The Galois action** on `H¹(A_K̄, ℤ_ℓ)`: `σ` acts by transport of structure along
   `1 × Spec(σ⁻¹)` on `A ×_K Spec K̄`.

The implications `T10_TateDuality → T10_linIso → T10_groupIso` are proved. The leaf rests on
Milne 1986, Thm 15.1 (UNVERIFIED sub-item and number), on the Bhatt–Scholze comparison of
pro-étale and étale `ℓ`-adic cohomology (UNVERIFIED number), and on the naturality of both under
scheme automorphisms (STANDARD argument, §4). It is a consequence of these, not stronger.

What is still open:
- **Proof of the leaf.** This is crowdsourcing material, very large: étale cohomology of abelian
  varieties and the pro-étale/étale comparison.
- **Group-action laws for the Galois action (optional).** They are not needed to state the leaf.
  The list with sizes is in §5.

## 1. The statements (Lean, compiled)

```lean
-- scratch/t10-etale/T10Etale.lean, namespace T10Etale
def T10_TateDuality : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    ∃ φ : (A.baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1 ≃ₗ[ℤ_[ℓ]]
        Module.Dual ℤ_[ℓ] (A.T ℓ),
      ∀ (σ : Field.absoluteGaloisGroup K) x,
        φ (galH A ℓ σ x) = (A.galT (ℓ := ℓ) σ⁻¹).dualMap (φ x)

def T10_linIso : Prop :=   -- ℤ_ℓ-linear, not equivariant
  ∀ (K : Type) [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    Nonempty ((A.baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1 ≃ₗ[ℤ_[ℓ]]
      Module.Dual ℤ_[ℓ] (A.T ℓ))

theorem T10_linIso_of_tateDuality : T10_TateDuality → T10_linIso
theorem T10_groupIso_of_linIso : T10_linIso → T10_groupIso   -- leaf-push2's form, copied verbatim
```

The ingredients are genuine definitions:
- `AbVar`, `AbVar.baseChange`, `AbVar.T` (`T_ℓ A = lim A(K̄)[ℓⁿ]`), `AbVar.galT` (`σ` acts on
  points `P : Spec K̄ → A` by `P ↦ Spec(σ) ≫ P`) and `AbVar.galHom` come from the build
  (`ZInQKernel/HDecomp/Objects.lean`).
- `Scheme.EllAdicCohomology` is Mathlib's.
- `galH` and the module structure are new here (§2).

`T10_TateDuality` keeps the name of the `opaque` placeholder in `scratch/h-decomposition/Leaves.lean`
(field `t10`), so folding it in replaces the placeholder.

## 2. New definitions and lemmas (all in `T10Etale.lean`, 543 lines)

| Lean name | Content | Lines | Status |
| --- | --- | --- | --- |
| `smulHom`, `smulEnd`, `smulEnd_one/mul/add/zero` | multiplication by `a ∈ ℤ_ℓ` on `U ↦ ULift C(U.left, ℤ_ℓ)` as a sheaf endomorphism (naturality by `rfl`) | ~50 | VERIFIED (compiled) |
| `instance : Module ℤ_[ℓ] (X.EllAdicCohomology ℓ n)` | `a • x = Sheaf.H.map (smulEnd a) n x` | ~25 | VERIFIED |
| `H0Equiv : X.EllAdicCohomology ℓ 0 ≃ₗ[ℤ_[ℓ]] C(X, ℤ_[ℓ])`, `nontrivial_H0`, `H0Equiv_smul` | sanity check of the module structure (`Sheaf.H.equiv₀` at the terminal object `X → X` of `X.ProEt`) | ~35 | VERIFIED |
| `mem_topology_iff` | a sieve on `U` covers in `X.ProEt` iff its image in `Scheme` is a pro-étale covering sieve of `U.left` | ~12 | VERIFIED |
| `proEtMap`, `proEtEquiv e : X.ProEt ≌ Y.ProEt`, `IsDenseSubsite` instance, `sheafEquiv e` | equivalence of small pro-étale sites and of abelian sheaf categories for a scheme isomorphism `e` | ~35 | VERIFIED |
| `ellIso`, `adjL`, `adjR`, `constIso` | the sheaf equivalence carries `C(-, ℤ_ℓ)` to `C(-, ℤ_ℓ)` (componentwise identity) and constant sheaves to constant sheaves (`Adjunction.leftAdjointUniq`) | ~35 | VERIFIED |
| `transport ℓ e n`, `transportₗ` | `e_* : Hⁿ(X, ℤ_ℓ) → Hⁿ(Y, ℤ_ℓ)` via `Ext.mapExactFunctor` and `Ext.mk₀` of the two isomorphisms | ~10 | VERIFIED |
| `transport_smul` | transport is `ℤ_ℓ`-linear | ~20 | VERIFIED |
| `transport_bijective` | transport is bijective | ~35 | VERIFIED |
| `transport_mk₀`, `unit_ellIso_sections`, `transport_homEquiv`, `transport_H0` | degree-0 check: `transport` is `f ↦ f ∘ e⁻¹` on global sections, so `constIso` is the canonical isomorphism | ~75 | VERIFIED |
| `specAut`, `AKbar`, `galAut`, `galAut_mul`, `galAut_one`, `galIso`, `galIso_mul`, `galIso_inv_mul` | `1 × Spec(σ)` on `A_K̄ = A ×_K Spec K̄` as a scheme automorphism; `galAut (στ) = galAut σ ≫ galAut τ`; `galIso (στ)⁻¹ = galIso τ⁻¹ ≪≫ galIso σ⁻¹` | ~70 | VERIFIED |
| `galH A ℓ σ := transportₗ ℓ (galIso A σ⁻¹) 1` | Galois action on `H¹(A_K̄, ℤ_ℓ)` | ~10 | VERIFIED |
| `T10_linIso`, `T10_groupIso`, `T10_TateDuality` + implications, `subsingleton_T_zero`, `T10_linIso_zero` | the leaf and its checks | ~70 | VERIFIED |

Technical notes (VERIFIED):
- The file needs `set_option backward.isDefEq.respectTransparency.types false`, scoped to the
  cohomology and transport sections, as Mathlib's own pro-étale files do. Without it the instance
  `ContainsIdentities @WeaklyEtale` is not found.
- It needs an explicit `import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`, which Mathlib's
  `Proetale.lean` imports only privately.
- It needs `open MonObj` for the group structure on `A(K̄)`.
- A full check run takes about 2 minutes.

## 3. Checks (non-vacuity and correctness)

All checks below are compiled (VERIFIED) unless marked otherwise.

- **The module structure is the standard one.** `H0Equiv` identifies `H⁰(X, ℤ_ℓ)` with
  `C(X, ℤ_ℓ)` as `ℤ_ℓ`-modules, with `a` acting by multiplication. `nontrivial_H0` shows that
  `EllAdicCohomology` is nonzero for nonempty `X`, so the cohomology groups are not trivially zero.
- **T10 has content.** `T10_linIso_zero` instantiates the leaf at `AbVar.zero K`, whose `T_ℓ` is 0.
  There it says that `H¹_proet(Spec K̄ ×_K Spec K, ℤ_ℓ) = 0`.
  - This is true, because `Spec K̄` is w-contractible (Bhatt–Scholze §2.4; UNVERIFIED number).
  - It is not provable by unfolding definitions, and it is the only instance that can be built in
    Mathlib v4.35, which has no nonzero `AbVar` (Objects.lean's docstring).
  - So the hypotheses of the leaf are satisfiable, and the leaf is not vacuous over an empty class.
- **The transport is non-degenerate.** `transport_bijective` shows every `galH σ` is a bijection.
  This matters because a degenerate action (for example 0) would make `T10_TateDuality` false, not
  vacuous.
- **The transport is `e_*` and nothing else.**
  - `transport_H0`: in degree 0, with global sections of `Y` computed at the terminal object
    `(X →e Y)`, transport is the identity of `C(X, ℤ_ℓ)`. On `C(Y, ℤ_ℓ)` this is `f ↦ f ∘ e⁻¹`.
  - So the choice in `constIso` (an isomorphism of constant sheaves) is the canonical one; no sign
    or other automorphism of `ℤ` enters.
  - `transport_smul` gives `ℤ_ℓ`-linearity. The leaf forces `galH σ` to be linear, so an additive
    but non-linear action would also make it false.
- **Conventions (σ against σ⁻¹).** This argument is a hand computation, not Lean.
  - `galAut (στ) = galAut σ ≫ galAut τ` (VERIFIED). So `s_σ := galAut σ⁻¹ = 1 × Spec(σ⁻¹)`
    satisfies `s_σ ∘ s_τ = s_{στ}`, and `σ ↦ (s_σ)_*` is a left action, provided transport is
    functorial (the action laws are not proved; §5).
  - `σ ↦ galT σ` is a left action on `T_ℓ A` (`galHom_mul` in Objects.lean).
  - The contragredient `σ ↦ (galT σ⁻¹).dualMap` is a left action, and it is the only one built
    from `galT` that is.
  - Transport of structure along the automorphism `σ` of `K̄` acts:
    - on `K̄`-points of `A` by `P ↦ Spec(σ) ≫ P`, which is `galT σ`;
    - on the scheme `A_K̄` by `s_σ`;
    - on cohomology by `(s_σ)_*`, which is `galH σ`.
  - A canonical isomorphism commutes with transport of structure, so the stated pairing is the
    natural one.
- **Not stronger than the source.**
  - `(ℓ : K) ≠ 0` is Milne's hypothesis.
  - `K̄ = AlgebraicClosure K` is separably closed, as Milne requires.
  - `H¹` lives in `Type 1` and `Module.Dual ℤ_ℓ (A.T ℓ)` in `Type 0`. A linear isomorphism
    across universes asserts nothing beyond the mathematical isomorphism.

## 4. Literature

- **Milne, "Abelian varieties", in Cornell–Silverman (eds.), *Arithmetic Geometry* (1986), §15,
  Thm 15.1.** It gives `H¹_et(A_{k_s}, ℤ_ℓ) ≅ Hom(T_ℓ A, ℤ_ℓ)` canonically, for `ℓ ≠ char k`.
  The sub-item ((a) per h-decomposition) and the exact wording are UNVERIFIED: there was no network
  access and the source was not read.
- **Equivariance.** Milne's isomorphism comes from the Galois covers `[ℓⁿ] : A_{k_s} → A_{k_s}`
  with group `A[ℓⁿ]`. The automorphism `s_σ` commutes with `[ℓⁿ]` and carries translation by `P`
  to translation by `σ(P)`, so the isomorphism intertwines the actions. This is a STANDARD
  argument. Whether Milne states equivariance in words is SPECULATIVE; the leaf is a consequence
  either way.
- **Bhatt–Scholze, "The pro-étale topology for schemes", Astérisque 369 (2015).**
  - Def. 6.8.1 is the definition Mathlib cites for `ellAdicSheaf` (VERIFIED: the citation in
    Mathlib's docstring; the paper itself was not read).
  - The comparison `H^i(X_proet, ℤ_ℓ) = lim H^i(X_et, ℤ/ℓⁿ)` for schemes with finite étale
    cohomology mod `ℓ` (such as `A_K̄`) is in §5.6 (UNVERIFIED number).
  - Mathlib's pro-étale site is the big site of all weakly étale `U → X` in the same universe, not
    a cardinal-bounded one. That the cohomology agrees is part of the comparison Mathlib's
    docstring announces as future work (UNVERIFIED).

## 5. What remains: exact list, with sizes

**(a) To state T10.** Nothing; done. The leaf can replace the `opaque T10_TateDuality` in
`Leaves.lean` once `T10Etale.lean` is folded in. Folding needs the Mathlib imports
`Sites.ElladicCohomology`, `Morphisms.WeaklyEtale`, `Ext.Map` and `Ext.MapBijective`.

**(b) Optional strengthening of the statement's glue** (not needed for the leaf's meaning):

| Item | Lean statement | Estimated size | Main difficulty |
| --- | --- | --- | --- |
| `transport_refl` | `transport ℓ (Iso.refl X) n = id` | 60–120 lines | `proEtEquiv (Iso.refl X)` is not definitionally the identity (objects `(U, f ≫ 𝟙)`); needs `sheafCongr` naturality and `leftAdjointUniq_refl` |
| `transport_trans` | `transport ℓ (e ≪≫ e') n = transport ℓ e' n ∘ transport ℓ e n` | 150–250 lines | the natural iso `S_e ⋙ S_{e'} ≅ S_{e≪≫e'}` (componentwise identity) with `Ext.comp_mapExactFunctor` and `Ext.mapExactFunctor_comp_mk₀_natTransApp`; the hard part is the compatibility of the three `constIso`s, which are defined at three different terminal objects, so it needs the restriction maps between them |
| `galH_mul`, `galH_one` | `galH` is a representation `G_K → GL(H¹)` | ~10 lines given `transport_trans` | `galIso_inv_mul` (proved) + `transport_trans`; `galH_one` also follows from `transport_trans` + `transport_bijective` (an idempotent bijection is the identity) |
| `ℚ_ℓ` form | `V_ℓ(A) ≅ (H¹ ⊗ ℚ_ℓ)^∨` as `G_K`-representations (`AbVar.galRep`) | ~100 lines | needs `T_ℓ A` finite free (the `TateModuleFree` leaf) to commute `Dual` with `⊗ ℚ_ℓ` |
| continuity of `galH` | not needed by any step | — | — |

**(c) To prove T10 (crowdsourcing).** Very large; none of it is in Mathlib v4.35:
- the pro-étale/étale comparison for `ℤ_ℓ`-coefficients (Mathlib's announced future work);
- `H¹_et` of an abelian variety via torsors or `π₁`;
- the Kummer-type sequences for `[ℓⁿ]`;
- `lim¹` vanishing;
- naturality under scheme automorphisms.

**(d) How the decomposition uses T10.** h-decomposition §R10 says that the Tate-module form of R10
stated in Lean (`PkgI4.DeRhamComparison`) is a consequence of R10 together with T10. R10 is
already stated over Tate modules, so T10 is used only in that derivation. That derivation also
needs the `ℚ_ℓ` form of (b), with `K` a finite extension of `ℚ_p`; `K` is arbitrary here, so this
is covered.

## 6. Independent check

One read-only model review (subagent, 2026-11-13) was given `T10Etale.lean`, Objects.lean and
Mathlib's sources, but not this report's conclusions; it did not run Lean. **Verdict: no DEFECT.**
This is a model review, not a human review.

**What it confirmed:**
1. **Module structure: OK.** It is the standard action coming from the coefficient sheaf.
   - `smulEnd_mul` reverses the order of composition, which is harmless because `ℤ_ℓ` is
     commutative.
   - Ext computed in abelian sheaves has the same groups and functoriality as Ext in sheaves of
     `ℤ_ℓ`-modules.
2. **Transport is `e_*`: OK.** `sheafCongr.functor` precomposes with `proEtMap e.symm`, so it sends
   `G` to `(e⁻¹)^*G = e_*G`, and `ellIso` is the componentwise identity.
   - The only possible ambiguity in `constIso` is a locally constant unit `ε`.
   - `transport_H0` at `x = 1` forces `ε = 1`.
3. **Galois conventions: OK, no swap.** In Mathlib, `AlgEquiv` multiplication is `(στ)(x) = σ(τ(x))`
   and `≫` is diagrammatic.
   - `galAct`/`galT` is a left action, and `σ ↦ (galT σ⁻¹).dualMap` is the contragredient left
     action.
   - `galH σ = (1 × Spec σ⁻¹)_* = (1 × Spec σ)^*` is a left action.
   - The reviewer computed how the `[ℓⁿ]`-torsor transforms under `1 × Spec σ`. The result,
     `(s_σ)^*Φ(χ) = Φ(χ ∘ galT σ⁻¹)` for the canonical map `Φ : Hom(T_ℓ A, ℤ_ℓ) → H¹`, is
     exactly the identity required by `T10_TateDuality`.
   - Cross-check: `H¹(G_m) = ℤ_ℓ(−1) = T_ℓ(G_m)^∨`.
4. **Strength and vacuity: OK.**
   - `(ℓ : K) ≠ 0` is `ℓ ≠ char K`. Using `K̄` instead of `K^sep` is harmless.
   - The universes are fine.
   - The existential `∃ φ` is weaker than "the canonical `φ`", but not vacuous or trivial.
   - `T10_linIso_zero` is true content: every faithfully flat weakly étale `K̄`-algebra has a
     `K̄`-point, so `Spec K̄` is w-contractible.

**RISKs (minor):**
1. **Pro-étale against étale.** Faithfulness to Milne depends on the Bhatt–Scholze comparison
   `RΓ_proet(X, ℤ̂_ℓ) = R lim RΓ_et(X, ℤ/ℓⁿ)`.
   - `lim¹` vanishes here because the groups are finite.
   - `ℤ̂_ℓ = C(−, ℤ_ℓ)` (Bhatt–Scholze, reviewer's recollection: about Lemma 4.2.12; UNVERIFIED).
   - The comparison must also cover Mathlib's site having no cardinal cutoff.
   - *Done:* already disclosed in §4 and in the docstrings as UNVERIFIED.
2. **Citation.** The Milne sub-item "(a)" is unverified. *Open:* read Milne §15.

**Gap it noted:** functoriality of `transport` is not proved (§5(b)). The statement does not need
it.
