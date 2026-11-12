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
