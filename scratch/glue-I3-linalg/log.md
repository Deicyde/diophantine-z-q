# glue-I3-linalg results log

## Files
- `I3.lean`: verbatim copy of `scratch/pkg-I3/I3.lean` (object layer and leaves; not modified, not recompiled here).
- `Commutant.lean`: new glue, imports only Mathlib (RepresentationTheory.Semisimple, .Irreducible,
  LinearAlgebra.Projection, LinearAlgebra.FiniteDimensional.Basic).

## Statements and compile outcomes (`lake env lean scratch/glue-I3-linalg/Commutant.lean`, 2026-11-11 22:29 PST)
- `GlueI3.projection_comm`: the projection onto a subrepresentation along an invariant complement
  commutes with every `ρ g`. VERIFIED (compiled).
- `GlueI3.isIrreducible_of_commutant_scalar`: `ρ : Representation k G V`, `V` nontrivial,
  `ρ.IsSemisimpleRepresentation`, every `φ` with `φ ∘ ρ g = ρ g ∘ φ` for all `g` is a scalar
  ⇒ `ρ.IsIrreducible`. VERIFIED (compiled); axioms [propext, Classical.choice, Quot.sound].
- `GlueI3.commOf r`: commutant of a family `r : G → End_k W`, as a `k`-submodule.
- `GlueI3.blockMap ρ`, `blockMap_injective`: `(a,b,c,d) ↦ [[a,b],[c,d]]`, injective `k`-linear map
  `End_G(V)⁴ → End_G(V ⊕ V)`. VERIFIED (compiled).
- `GlueI3.isIrreducible_of_finrank_commOf_prod_le_four`: `V` finite-dimensional and nontrivial,
  `ρ` semisimple, `finrank_k End_G(V ⊕ V) ≤ 4` ⇒ `ρ` irreducible and `End_G(V) = k`.
  VERIFIED (compiled); axioms [propext, Classical.choice, Quot.sound].

- `GlueI3.id_mem_commOf`, `GlueI3.scalar_of_finrank_commOf_eq_one` (a 1-dimensional commutant on a
  nonzero space is the scalars), `GlueI3.finrank_commOf_eq_one_of_prod_le_four`. VERIFIED (compiled).
- `GlueI3.repBaseChange E ρ`: `ρ_E g = (ρ g).baseChange E` on `E ⊗_k V`, a Mathlib `Representation`
  (laws proved). VERIFIED (compiled).
- `GlueI3.InvariantsBaseChange`, `GlueI3.SemisimpleBaseChange`: statements (`def … : Prop`) of the two
  linear-algebra glue facts; NOT proved (STANDARD linear algebra; see the report).
- `GlueI3.absolutelyIrreducible_of_finrank_commOf_prod_le_four`: from `InvariantsBaseChange` and
  `SemisimpleBaseChange`: char 0, `V ≠ 0` finite-dimensional, `ρ` semisimple,
  `finrank End_G(V ⊕ V) ≤ 4` ⇒ `repBaseChange F ρ` irreducible for every field `F ⊇ k`.
  VERIFIED (compiled 22:31 PST); axioms [propext, Classical.choice, Quot.sound]. File has no `sorry`.

- `GlueI3.exists_equivariant_ne_zero_of_common` (E1, first arrow): `ρ` semisimple, `U ≠ ⊥` a
  subrepresentation of `ρ`, `U'` a subrepresentation of `σ`, `e : U ≃ₗ U'` equivariant ⇒ a nonzero
  `G`-equivariant `φ : V →ₗ W`. VERIFIED (compiled 22:36 PST); axioms [propext, Classical.choice, Quot.sound].
- `TateBC.lean` (§1 copied verbatim from pkg-I3's `I3.lean`, Tate module of an abelian group):
  `PkgI3.Tate.map_injective`, `ell_smul_succ` (`(ℓ•x)ₙ₊₁ = xₙ`), `mem_range_of_ell_smul`
  (saturation), `mem_range_of_smul` (cokernel torsion-free, via `PadicInt.unitCoeff_spec`),
  `map_bijective`: `φ : M →+ N` injective, `T_ℓ M` free finite, `T_ℓ N` finite, equal finrank ⇒
  `Tate.map φ` bijective. VERIFIED (compiled 22:34 PST); axioms [propext, Classical.choice, Quot.sound].

- `C2.lean` = `I3.lean` (verbatim) + the body of `Commutant.lean` + `GlueI3.finrank_commOf_le_of_equiv`
  (an equivariant linear iso `V ≃ W` gives `dim End_G V ≤ dim End_G W`) + §5:
  `PkgI3.equivEnd_eq_commOf` (`rfl`) and `PkgI3.C2_absolutelyIrreducible`: from `FaltingsSemisimple`, `FaltingsTate`,
  `TateModuleFree`, `HomFreeFinite`, `InvariantsBaseChange`, `SemisimpleBaseChange`,
  `finrank ℤ (End A) = 4`, `E ⊇ ℚ_ℓ` with `CharZero E`, a representation `r` on a nonzero
  finite-dimensional `U`, and an equivariant `E ⊗ V_ℓ A ≃ₗ[E] U × U` ⇒ `repBaseChange F r` irreducible for
  every `F ⊇ E`. VERIFIED (compiled 22:39 PST, ~15 s); axioms [propext, Classical.choice, Quot.sound].
  Semisimplicity of `r` is derived (22:39) via `GlueI3.isSemisimple_of_surjective` (semisimplicity passes
  to equivariant quotients; Mathlib `IsSemisimpleModule.of_surjective` + `equivLinearMapAsModule`), applied
  to `fst ∘ e`.

- `C2.lean` also: `GlueI3.EquivariantDescent` (statement only, NOT proved: a nonzero `G`-equivariant
  `E`-map `V⊗E → W⊗E` gives a nonzero `G`-equivariant `k`-map `V → W`) and
  `PkgI3.E1_exists_hom_ne_zero`: from `FaltingsSemisimple`, `FaltingsTate`, `TateModuleFree`,
  `SemisimpleBaseChange`, `EquivariantDescent`, a nonzero subrepresentation `U` of `V_ℓ(A) ⊗ E`
  equivariantly isomorphic to a subrepresentation `U'` of `V_ℓ(J) ⊗ E` ⇒ `∃ f : Hom A J, f ≠ 0`.
  VERIFIED (compiled 22:40 PST); axioms [propext, Classical.choice, Quot.sound].

- `GlueI3.exists_equivariant_ne_zero_of_baseChange` (Commutant.lean and C2.lean) and
  `GlueI3.equivariantDescent : EquivariantDescent` (C2.lean): PROVED (22:42 PST; expand in a `k`-basis of
  `E` via `TensorProduct.finsuppScalarLeft`, take a nonzero coordinate; no finite-dimensionality used).
  `PkgI3.E1_exists_hom_ne_zero` no longer takes `EquivariantDescent` as a hypothesis. Axioms
  [propext, Classical.choice, Quot.sound].

## Findings
- Mathlib v4.35.0 has `Representation.IsIrreducible` (`IsSimpleOrder (Subrepresentation ρ)`) and
  `IsSemisimpleRepresentation` (`ComplementedLattice`), so the commutant argument is statable over
  genuine definitions. VERIFIED (read Mathlib/RepresentationTheory/{Semisimple,Irreducible}.lean).
- Lean 4.35 pitfall: `FiniteDimensional.of_injective` / `IsNoetherian` instances on a `Submodule`
  of `W →ₗ W` (W = V × V) fail to unify (`Submodule.addCommMonoid` vs
  `AddCommGroup.toAddCommMonoid`) even with `backward.isDefEq.respectTransparency false`; worked
  around by assuming `[FiniteDimensional k V]` so that instances come from the ambient space.

## Not done (see docs/research/glue-I3-linalg.md §3)
- invariants under extension of coefficients; semisimplicity under extension (char 0);
  `V_ℓ ⊗ E ≅ r ⊕ r` from `B ⊗ E ≅ M₂(E)`; the geometric half of `T_ℓ` under base change
  (`A(K̄) ↪ A(L̄) = A_L(L̄)`, Galois compatibility, `dim A_L = dim A`);
  the application of `PoincareReducibility` in E1.
