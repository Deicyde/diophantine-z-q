# t10-etale fold notes

Fragment: `scratch/leaf-adopt3/fold/t10-etale.lean` (section `T10EtaleSec`, namespace `T10Etale`).
Source: `scratch/t10-etale/T10Etale.lean` (543 lines), copied verbatim. Only changes: the imports
and the 8 `#print axioms` lines are dropped, the local copy `T10Etale.T10_groupIso` is deleted
(see below), and a short bridge section is added at the end.

The `sorry` occurrence is in the module docstring ("No `sorry`; ..."). It is not a real `sorry`.

## Bundle change (field `t10` of `HSyn.TextbookLeaves`)

- Change the field to `t10 : T10Etale.T10_TateDuality`. Write the name fully qualified: inside
  `namespace HSyn`, a bare `T10_TateDuality` would still resolve to the opaque if it is kept.
- **Delete** `opaque HSyn.T10_TateDuality : Prop` (Leaves.lean ~21346-21348) and its docstring.
  Its only use is the field `t10` (line ~21493); nothing else refers to it.
- Docstring for the field:

  ```
  /-- T10, Galois-equivariant Tate duality (t10-etale): for an abelian variety `A/K` and a prime
  `ℓ ≠ char K`, a `ℤ_ℓ`-linear isomorphism `H¹_proet(A_K̄, ℤ_ℓ) ≅ Hom_{ℤ_ℓ}(T_ℓ A, ℤ_ℓ)` (Mathlib's
  `Scheme.EllAdicCohomology` with the `ℤ_ℓ`-module structure of `T10Etale`) intertwining the
  Galois action `T10Etale.galH` (transport along `1 × Spec σ⁻¹`) with the contragredient action
  `f ↦ f ∘ galT σ⁻¹`. Milne 1986 (Cornell–Silverman) Thm 15.1(a) with the pro-étale/étale
  comparison of Bhatt–Scholze 2015 §5.6 (UNVERIFIED numbers). -/
  ```

## Bridging theorems

There is no theorem into the old opaque, because the field's type itself changes. The fragment
does prove the implication down to leaf-push2's form:
- `T10Etale.T10_linIso_of_tateDuality : T10Etale.T10_TateDuality → T10Etale.T10_linIso` (from the
  file);
- `T10Etale.T10_groupIso_of_linIso : T10Etale.T10_linIso → ZInQ.LeafPush2.T10_groupIso`. The
  conclusion was retargeted from the deleted local copy to the Leaves.lean original;
- `T10Etale.T10_groupIso_of_tateDuality : T10Etale.T10_TateDuality → ZInQ.LeafPush2.T10_groupIso`
  (new, two lines).

## New leaf Prop

`T10Etale.T10_TateDuality` (a `def … : Prop`, statement unchanged from the scratch file):

```lean
∀ (K : Type) [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
  ∃ φ : (A.baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1 ≃ₗ[ℤ_[ℓ]]
      Module.Dual ℤ_[ℓ] (A.T ℓ),
    ∀ (σ : Field.absoluteGaloisGroup K) x,
      φ (galH A ℓ σ x) = (A.galT (ℓ := ℓ) σ⁻¹).dualMap (φ x)
```

Here `AbVar` is `PkgI3.AbVar` (via `open PkgI3`). `T10Etale.T10_linIso` is the non-equivariant
form; it is not a leaf.

## Deleted as duplicate

- `T10Etale.T10_groupIso`. It has a new name, but its body is character-for-character the body of
  `ZInQ.LeafPush2.T10_groupIso` (Leaves.lean 21078). Uses now point to the Leaves.lean original.
- Nothing else duplicates a Leaves.lean name. All `T10Etale.*` names are new, and grep finds no
  Leaves.lean declaration named `F`, `smulEnd`, `transport`, `galH`, `galIso`, `specAut`, `AKbar`,
  etc. in an opened namespace.

## Kernel declarations

The file imports `ZInQKernel.HDecomp.Objects`. It uses `PkgI3.AbVar`, `.X`, `.baseChange`, `.T`,
`.galT`, `.Pt`, `.zero`, and `PkgI3.Tate.T`.
- Objects.lean lines 56-403 against Leaves.lean lines 2425-2771 (`PkgI3.Tate`, `PkgI3`,
  `PkgI3.AbVar`): `diff` shows one difference only, a docstring line wrap in `tateHomZl`. The
  definitions are identical.
- No kernel declaration needed copying.

## Expected compile trouble spots

- **Full Mathlib import.** The scratch file imported only 4 Mathlib modules plus Objects; Leaves.lean
  imports all of `Mathlib`. All four modules (`Sites.ElladicCohomology`, `Morphisms.WeaklyEtale`,
  `Ext.Map`, `Ext.MapBijective`) are in `Mathlib.lean`. A larger simp set could change these bare
  `simp`/`simpa` calls:
  - `unit_ellIso_sections` (`simp`, then `simpa [terminalProEt, proEtEquiv, proEtMap]`);
  - `specAut_comp`, `galAut_mul`, `galAut_one`;
  - `smulHom_*`;
  - `transport_homEquiv` (`erw` chain).
- **`set_option backward.isDefEq.respectTransparency.types false`** sits at the start of sections
  `Coh` and `Transport`; it is required (Mathlib's pro-étale files do the same).
- **`universe u`** is declared inside the section. Leaves.lean has no top-level `universe`; all four
  of its `universe u` lines are inside sections or namespaces.
- **No `noncomputable section` wrapper.** The original had none; every def that needs it is marked
  `noncomputable`.
- **Run time.** The scratch check took about 2 minutes.

## `#print axioms` dropped

`H0Equiv`, `T10_groupIso_of_linIso`, `T10_linIso_zero`, `transport_smul`, `galIso`,
`transport_bijective`, `transport_H0`, `T10_linIso_of_tateDuality` (all in `T10Etale`). All were
`[propext, Classical.choice, Quot.sound]` per the report.
