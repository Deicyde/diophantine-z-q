# t10-etale results log

- 22:54 start. Base 01267822. Mathlib v4.35 `Scheme.EllAdicCohomology X ℓ n` = `Sheaf.H` (Ext from
  constant `ULift ℤ`) of `ulift ∘ ellAdicSheaf`, `AddCommGroup` only (VERIFIED, read
  Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean).
- Mathlib has `Sheaf.H.map` (functoriality in the sheaf, with `map_id/map_comp/map_add`),
  `Ext.mapExactFunctor` + `Functor.mapExt_bijective_of_preservesInjectiveObjects`
  (Ext/Map.lean, Ext/MapBijective.lean), `Ext` along adjunctions (Ext/MapAdjunction.lean)
  (VERIFIED, read).
- Test1.lean: `smulEnd X ℓ a` (multiplication by `a ∈ ℤ_ℓ` on `U ↦ ULift C(U.left, ℤ_ℓ)`, naturality
  by `rfl`), lemmas `smulEnd_one/mul/add/zero`, and
  `instance : Module ℤ_[ℓ] (X.EllAdicCohomology ℓ n)` via `Sheaf.H.map`. COMPILED (no sorry), ~65 s.
- T10Etale.lean (renamed from Test1): + `H0Equiv : X.EllAdicCohomology ℓ 0 ≃ₗ[ℤ_[ℓ]] C(X, ℤ_[ℓ])`
  (via `Sheaf.H.equiv₀` at the terminal object `X → X` of `X.ProEt` and its naturality),
  `nontrivial_H0 [Nonempty X]`, `H0Equiv_smul`. COMPILED. Needs
  `set_option backward.isDefEq.respectTransparency.types false` (else `ContainsIdentities
  @WeaklyEtale` is not found) and an explicit `import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`
  (Proetale.lean imports it privately).
