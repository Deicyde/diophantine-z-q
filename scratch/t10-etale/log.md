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
- T10Etale.lean: + `T10_linIso` (∀ K A ℓ, ℓ ≠ char K → Nonempty (H¹_proet(A_K̄.left, ℤ_ℓ) ≃ₗ[ℤ_ℓ]
  Module.Dual ℤ_ℓ (A.T ℓ))), `T10_groupIso` (copied from leaf-push2), `T10_groupIso_of_linIso`,
  `subsingleton_T_zero`, `T10_linIso_zero` (at `AbVar.zero K` the leaf says
  `H¹(Spec K̄ ×_K Spec K, ℤ_ℓ) = 0`). COMPILED; axioms propext, Classical.choice, Quot.sound.
  (Needs `open MonObj` for the group structure on points.)
- Transport.lean (Mathlib only): `mem_topology_iff` (S covers U in `X.ProEt` iff its image under
  `X.ProEt ⥤ Scheme` is a pro-étale covering sieve of `U.left`), `proEtMap e`, `proEtEquiv e :
  X.ProEt ≌ Y.ProEt` for a scheme iso `e` (from `MorphismProperty.Over.map/mapId/mapComp`),
  `IsDenseSubsite` of its inverse, `sheafEquiv e` (`Equivalence.sheafCongr`), additivity. COMPILED.
- Transport.lean: + `ellIso e` (sheaf equivalence carries `Fs X` to `Fs Y`, componentwise `Iso.refl`),
  `constIso e A` (carries constant sheaves to constant sheaves: `Adjunction.leftAdjointUniq` of
  `constantSheafAdj ∘ sheafEquiv.toAdjunction` and `constantSheafAdj` at the image of the terminal
  object), `transport ℓ e n : X.EllAdicCohomology ℓ n →+ Y.EllAdicCohomology ℓ n`
  (`Ext.mapExactFunctor` + `Ext.mk₀` of the two isos). COMPILED (exactness instances of the
  equivalence found automatically).
- Merged Transport.lean into T10Etale.lean (Transport.lean removed). + `ellIso_smulEnd`,
  `transport_smul` (transport is ℤ_ℓ-linear), `transportₗ`. COMPILED.
- T10Etale.lean: + `specAut σ = Spec(σ)`, `specAut_comp/mul/one`, `AKbar A := pullback A.X.hom
  (Spec K̄ → Spec K)` (= `(A.baseChange K̄).X.left` by `rfl`), `galAut A σ = 1 × Spec(σ)`,
  `galAut_mul` (anti-hom: `galAut (στ) = galAut σ ≫ galAut τ`), `galAut_one`, `galIso A σ`,
  `galH A ℓ σ := transportₗ ℓ (galIso A σ⁻¹) 1` (transport of structure along `1 × Spec(σ⁻¹)`),
  **`T10_TateDuality`** (∃ ℤ_ℓ-linear `φ : H¹ ≃ Dual(T_ℓ A)` with
  `φ (galH σ x) = (galT σ⁻¹).dualMap (φ x)`), `T10_linIso_of_tateDuality`. COMPILED, standard axioms.
