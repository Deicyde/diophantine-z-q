# The homotopy equivalence `L ≃ P'` after inverting `t`: verification


## Scope after independent review (2026-11-18)

The general lemma `exists_homotopyEquiv_of_quasiIso` (a quasi-isomorphism between bounded-above complexes over a field is a homotopy equivalence) passed review. The consumer wrappers do not discharge the after-t input: the review compiled that the freely chosen change-of-condition package is equivalent to the homotopy-equivalence input it replaces, that the full witness wrappers accept identity changes, and an example in which the variable t and zero have identical reductions but generic ranks 0 and 2. The wrappers are reformulations of the input; tying the change of condition to the actual arithmetic complexes remains the open input.

## Result

`HomotopyInput.lean` constructs the input `e : HomotopyEquiv L P'` of
`residualRankCounts_afterT'`, `residualRankCounts_afterT''` (`GenuineInst/ResidualAfterT2.lean`) and
`residualRankCounts_afterT'''` (`GenuineInst/ResidualAfterT3.lean`) from the hypotheses of the
manuscript (`diophantine_zq.tex`, tex 4612–4647): over a field, a quasi-isomorphism of bounded-above
complexes is a homotopy equivalence; the change of condition with acyclic quotient after inverting
`t` is a quasi-isomorphism; hence every minimal model of the original-support complex is homotopy
equivalent to the base change of the smaller-support model. The acyclicity after inverting `t` is
itself derived from an integral comparison homotopy `d h + h d = c` with `c` invertible in
`𝔽₂((t))`, through flat base change. The consumers are wrapped so that `e` (and, in the cohomology
and integral forms, also `L`, `hLmin` and `P'`) is built; at the active witness the wrapped
constructors give `2 ≤ genericRank ≤ rankTot` and `genericRank ≤ 294`, with an integral change of
condition that is not acyclic before inverting `t`.

## Source and compilation

Source: `ZInQKernel/Contrib/RC53Assist/AfterTHomotopy/HomotopyInput.lean`.

- Size: 118928 bytes, 1873 lines.
- SHA256: `8ed0cf76903fb69fcd6edfa22e6581bdccec42df6eea0066e42a3d0f2ec004b6`.
- Single-file compilation: exit code 0, no diagnostics.
- Declarations: 80; each has a docstring with its kind and tex locators.
- Axiom audit (a temporary copy with one `#print axioms` per declaration, removed afterwards):
  every declaration depends exactly on `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, new axioms, `native_decide`, `implemented_by`, notation, macros, syntax,
  `#eval`, `run_cmd`, `#check`, `#print` or `set_option`; no wholesale `import Mathlib`.
- No pre-existing source or compiled file was modified.

The single-file command within the repository was:

```text
lake env lean ZInQKernel/Contrib/RC53Assist/AfterTHomotopy/HomotopyInput.lean
```

## What remains (arithmetic input)

The tree has no Galois cochains with coefficients in `𝔽₂[[t]]` or `𝔽₂((t))` and no inner limit.
The identification of the models with the actual complexes therefore stays an input, in one of
three forms (none of them equivalent to `e`):

1. generic: the original-support complex `Q'` over `𝔽₂((t))` containing the smaller-support model
   `P'` with acyclic quotient `W'` (the active comparison blocks after inverting `t`);
2. integral: the model `Q` over `𝔽₂[[t]]` of the original-support complex from the inner limit of
   the retained diagram (tex 4401–4406, 4626–4628), containing `P` as an actual subcomplex (tex
   3494–3498) with quotient `W`, and the retained comparison homotopy `d h + h d = c` on `W`, `c` a
   product of the scalars `(1+t)^{±e} − 1` from the reduction of (4.4) at the active places (tex
   4619–4626);
3. Selmer: Selmer data over `𝔽₂((t))` with the full condition at the active places, the unramified
   sub-condition with acyclic singular quotient after inverting `t`, and a quasi-isomorphism from
   `P'` to the unramified-condition complex (the support comparison of Nekovář 7.8.8(ii) after the
   inner limit and the inversion of `t`).

## Exact statements

All declarations are in the namespace `ZInQ.Contrib.RC53Assist.AfterTHomotopy`, with
`open CategoryTheory CategoryTheory.Limits DerivedCategory` and `universe u`; each section adds the
`open` lines of the source. Every declaration below depends on the axioms
`[propext, Classical.choice, Quot.sound]`.

### Section `Field`

```lean
variable {F : Type u} [Field F]
```

`isKProjective_of_isStrictlyLE` (theorem):

```lean
theorem isKProjective_of_isStrictlyLE (K : CochainComplex (ModuleCat.{u} F) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] : K.IsKProjective
```

`exists_homotopyEquiv_of_quasiIso` (theorem):

```lean
theorem exists_homotopyEquiv_of_quasiIso {K L : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyLE b] (φ : K ⟶ L) [QuasiIso φ] :
    ∃ e : HomotopyEquiv K L, e.hom = φ
```

`quasiIso_iff_exists_homotopyEquiv` (theorem):

```lean
theorem quasiIso_iff_exists_homotopyEquiv {K L : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyLE b] (φ : K ⟶ L) :
    QuasiIso φ ↔ ∃ e : HomotopyEquiv K L, e.hom = φ
```

`exists_homotopyEquiv_of_quasiIso_finiteDimensional` (theorem):

```lean
theorem exists_homotopyEquiv_of_quasiIso_finiteDimensional
    {K L : CochainComplex (ModuleCat.{u} F) ℤ} (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ n, FiniteDimensional F (K.X n)] [∀ n, FiniteDimensional F (L.X n)]
    (φ : K ⟶ L) [QuasiIso φ] : ∃ e : HomotopyEquiv K L, e.hom = φ
```

`exists_quasiIso_lift` (theorem):

```lean
theorem exists_quasiIso_lift {L P X : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ)
    [L.IsStrictlyLE b] (l : L ⟶ X) [QuasiIso l] (p : P ⟶ X) [QuasiIso p] :
    ∃ g : L ⟶ P, QuasiIso g
```

`nonempty_homotopyEquiv_of_zigzag` (theorem):

```lean
theorem nonempty_homotopyEquiv_of_zigzag {L P X : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ)
    [L.IsStrictlyLE b] [P.IsStrictlyLE b] (l : L ⟶ X) [QuasiIso l] (p : P ⟶ X) [QuasiIso p] :
    Nonempty (HomotopyEquiv L P)
```

`cohomologyCx` (abbrev):

```lean
abbrev cohomologyCx (C : CochainComplex (ModuleCat.{u} F) ℤ) :
    CochainComplex (ModuleCat.{u} F) ℤ
```

`cohomologyCx_d` (theorem):

```lean
theorem cohomologyCx_d (C : CochainComplex (ModuleCat.{u} F) ℤ) (i j : ℤ) :
    (cohomologyCx C).d i j = 0
```

`cohomologyRep` (def):

```lean
def cohomologyRep (C : CochainComplex (ModuleCat.{u} F) ℤ) : cohomologyCx C ⟶ C
```

`cohomologyRep_f` (theorem):

```lean
theorem cohomologyRep_f (C : CochainComplex (ModuleCat.{u} F) ℤ) (n : ℤ) :
    (cohomologyRep C).f n =
      Projective.factorThru (𝟙 (C.homology n)) (C.homologyπ n) ≫ C.iCycles n
```

`cohomologyRep_quasiIso` (instance):

```lean
instance cohomologyRep_quasiIso (C : CochainComplex (ModuleCat.{u} F) ℤ) :
    QuasiIso (cohomologyRep C)
```

`cohomologyCx_isStrictlyLE` (instance):

```lean
instance cohomologyCx_isStrictlyLE (C : CochainComplex (ModuleCat.{u} F) ℤ) (b : ℤ)
    [C.IsLE b] : (cohomologyCx C).IsStrictlyLE b
```

`cohomologyCx_isStrictlyGE` (instance):

```lean
instance cohomologyCx_isStrictlyGE (C : CochainComplex (ModuleCat.{u} F) ℤ) (a : ℤ)
    [C.IsGE a] : (cohomologyCx C).IsStrictlyGE a
```

`homology_finite` (theorem):

```lean
theorem homology_finite (C : CochainComplex (ModuleCat.{u} F) ℤ) (n : ℤ)
    [Module.Finite F (C.X n)] : Module.Finite F (C.homology n)
```

`exists_homotopyEquiv_cohomologyCx` (theorem):

```lean
theorem exists_homotopyEquiv_cohomologyCx (C : CochainComplex (ModuleCat.{u} F) ℤ) (b : ℤ)
    [C.IsStrictlyLE b] : ∃ e : HomotopyEquiv (cohomologyCx C) C, e.hom = cohomologyRep C
```

`isLE_of_quasiIso` (theorem):

```lean
theorem isLE_of_quasiIso {K L : CochainComplex (ModuleCat.{u} F) ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (b : ℤ) [K.IsLE b] : L.IsLE b
```

`isGE_of_quasiIso` (theorem):

```lean
theorem isGE_of_quasiIso {K L : CochainComplex (ModuleCat.{u} F) ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (a : ℤ) [K.IsGE a] : L.IsGE a
```

`homology_finite_of_quasiIso` (theorem):

```lean
theorem homology_finite_of_quasiIso {K L : CochainComplex (ModuleCat.{u} F) ℤ} (φ : K ⟶ L)
    [QuasiIso φ] (n : ℤ) [Module.Finite F (K.X n)] : Module.Finite F (L.homology n)
```

`cohomologyCx_minimal` (theorem):

```lean
theorem cohomologyCx_minimal (C : CochainComplex (ModuleCat.{u} F) ℤ) (i j : ℤ)
    (x : (cohomologyCx C).X i) :
    ((cohomologyCx C).d i j).hom x ∈
      IsLocalRing.maximalIdeal F • (⊤ : Submodule F ((cohomologyCx C).X j))
```

`d_eq_zero_of_minimal` (theorem):

```lean
theorem d_eq_zero_of_minimal {L : CochainComplex (ModuleCat.{u} F) ℤ}
    (hLmin : ∀ i j x, (L.d i j).hom x ∈ IsLocalRing.maximalIdeal F • (⊤ : Submodule F (L.X j)))
    (i j : ℤ) : L.d i j = 0
```

`finrank_eq_finrank_homology_of_minimal` (theorem):

```lean
theorem finrank_eq_finrank_homology_of_minimal {L Q : CochainComplex (ModuleCat.{u} F) ℤ}
    (hd : ∀ i j, L.d i j = 0) (l : L ⟶ Q) [QuasiIso l] (n : ℤ) :
    Module.finrank F (L.X n) = Module.finrank F (Q.homology n)
```

### Section `Change`

```lean
variable {F : Type u} [Field F]
-- (the first two theorems of the section bind their own ring `R`)
```

`quasiIso_of_change` (theorem):

```lean
theorem quasiIso_of_change {R : Type u} [CommRing R] {P Q W : CochainComplex (ModuleCat.{u} R) ℤ}
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W.Acyclic) : QuasiIso ι
```

`quasiIso_changeMap` (theorem):

```lean
theorem quasiIso_changeMap {R : Type u} [CommRing R] (Dfull : SelData R) (U' W : GCx R)
    (f : GHom U' Dfull.U) (g : GHom Dfull.U W)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hW : W.toCC.Acyclic) : QuasiIso (GHom.toCC (changeMap Dfull f))
```

`exists_homotopyEquiv_inclusion` (theorem):

```lean
theorem exists_homotopyEquiv_inclusion {P' Q' W' : CochainComplex (ModuleCat.{u} F) ℤ}
    (b : ℤ) [P'.IsStrictlyLE b] [Q'.IsStrictlyLE b]
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) : ∃ e : HomotopyEquiv P' Q', e.hom = ι
```

`comparisonCone_contractible` (theorem):

```lean
theorem comparisonCone_contractible {k : Type} [Field k]
    {P' Q' W' : CochainComplex (ModuleCat.{0} k) ℤ} (b : ℤ) [P'.IsStrictlyLE b] [Q'.IsStrictlyLE b]
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) : Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone ι)) 0)
```

`nonempty_homotopyEquiv_of_change` (theorem):

```lean
theorem nonempty_homotopyEquiv_of_change {P' Q' W' L : CochainComplex (ModuleCat.{u} F) ℤ}
    (b : ℤ) [P'.IsStrictlyLE b] [L.IsStrictlyLE b]
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) (l : L ⟶ Q') [QuasiIso l] : Nonempty (HomotopyEquiv L P')
```

`homotopyEquivOfChange` (def):

```lean
def homotopyEquivOfChange {P' Q' W' L : CochainComplex (ModuleCat.{u} F) ℤ}
    (b : ℤ) [P'.IsStrictlyLE b] [L.IsStrictlyLE b]
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) (l : L ⟶ Q') [QuasiIso l] : HomotopyEquiv L P'
```

`nonempty_homotopyEquiv_of_change_of_homotopyEquiv` (theorem):

```lean
theorem nonempty_homotopyEquiv_of_change_of_homotopyEquiv
    {P' Q' W' L : CochainComplex (ModuleCat.{u} F) ℤ}
    (b : ℤ) [P'.IsStrictlyLE b] [L.IsStrictlyLE b]
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) (eL : HomotopyEquiv L Q') : Nonempty (HomotopyEquiv L P')
```

`nonempty_homotopyEquiv_of_change_of_quasiIso_to` (theorem):

```lean
theorem nonempty_homotopyEquiv_of_change_of_quasiIso_to
    {P' Q' W' L : CochainComplex (ModuleCat.{u} F) ℤ}
    (b : ℤ) [P'.IsStrictlyLE b] [L.IsStrictlyLE b]
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) (r : Q' ⟶ L) [QuasiIso r] : Nonempty (HomotopyEquiv L P')
```

`nonempty_homotopyEquiv_of_cone_contractible` (theorem):

```lean
theorem nonempty_homotopyEquiv_of_cone_contractible
    {P' Q' L : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ) [P'.IsStrictlyLE b] [L.IsStrictlyLE b]
    (j : P' ⟶ Q') (hj : Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone j)) 0))
    (l : L ⟶ Q') [QuasiIso l] : Nonempty (HomotopyEquiv L P')
```

`nonempty_homotopyEquiv_of_selmerChange` (theorem):

```lean
theorem nonempty_homotopyEquiv_of_selmerChange (Dfull : SelData F) (U' W : GCx F)
    (f : GHom U' Dfull.U) (g : GHom Dfull.U W)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hW : W.toCC.Acyclic) {P' L : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ)
    [P'.IsStrictlyLE b] [L.IsStrictlyLE b]
    (pP : P' ⟶ (selCx (restrictData Dfull f)).toCC) [QuasiIso pP]
    (pL : L ⟶ (selCx Dfull).toCC) [QuasiIso pL] : Nonempty (HomotopyEquiv L P')
```

`nonempty_homotopyEquiv_of_supportChange` (theorem):

```lean
theorem nonempty_homotopyEquiv_of_supportChange (T : SupportChangeData F)
    (hT : QuasiIso (GHom.toCC (supportMap T)))
    (Dfull : SelData F) (W : GCx F) (f : GHom T.Dp.U Dfull.U) (g : GHom Dfull.U W)
    (hDp : T.Dp = restrictData Dfull f)
    (hfg : ∀ i (u : T.Dp.U.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hW : W.toCC.Acyclic) {P' L : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ)
    [P'.IsStrictlyLE b] [L.IsStrictlyLE b]
    (pP : P' ⟶ (selCx T.D).toCC) [QuasiIso pP]
    (pL : L ⟶ (selCx Dfull).toCC) [QuasiIso pL] : Nonempty (HomotopyEquiv L P')
```

`nonempty_homotopyEquiv_cohomologyCx_of_change` (theorem):

```lean
theorem nonempty_homotopyEquiv_cohomologyCx_of_change
    {P' Q' W' : CochainComplex (ModuleCat.{u} F) ℤ} (b : ℤ) [P'.IsStrictlyLE b]
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) : Nonempty (HomotopyEquiv (cohomologyCx Q') P')
```

### Section `BaseChange`

```lean
variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
```

`baseChangeCxMap` (def):

```lean
def baseChangeCxMap {P Q : CochainComplex (ModuleCat.{0} R) ℤ} (g : P ⟶ Q) :
    baseChangeCx φ P ⟶ baseChangeCx φ Q
```

`baseChangeCxMap_comp` (theorem):

```lean
theorem baseChangeCxMap_comp {P Q W : CochainComplex (ModuleCat.{0} R) ℤ} (f : P ⟶ Q)
    (g : Q ⟶ W) : baseChangeCxMap φ (f ≫ g) = baseChangeCxMap φ f ≫ baseChangeCxMap φ g
```

`baseChangeCxMap_zero` (theorem):

```lean
theorem baseChangeCxMap_zero (P Q : CochainComplex (ModuleCat.{0} R) ℤ) :
    baseChangeCxMap φ (0 : P ⟶ Q) = 0
```

`baseChangeCx_isStrictlyLE` (instance):

```lean
instance baseChangeCx_isStrictlyLE (P : CochainComplex (ModuleCat.{0} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] : (baseChangeCx φ P).IsStrictlyLE b
```

`baseChangeCx_isStrictlyGE` (instance):

```lean
instance baseChangeCx_isStrictlyGE (P : CochainComplex (ModuleCat.{0} R) ℤ) (a : ℤ)
    [P.IsStrictlyGE a] : (baseChangeCx φ P).IsStrictlyGE a
```

`baseChangeCx_finite` (instance):

```lean
instance baseChangeCx_finite (P : CochainComplex (ModuleCat.{0} R) ℤ) (n : ℤ)
    [Module.Finite R (P.X n)] : Module.Finite S ((baseChangeCx φ P).X n)
```

`baseChangeCx_shortExact` (theorem):

```lean
theorem baseChangeCx_shortExact (hφ : letI := φ.toAlgebra; Module.Flat R S)
    {P Q W : CochainComplex (ModuleCat.{0} R) ℤ} (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) :
    (ShortComplex.mk (baseChangeCxMap φ ι) (baseChangeCxMap φ π)
      (by rw [← baseChangeCxMap_comp, hιπ, baseChangeCxMap_zero])).ShortExact
```

`baseChangeCx_acyclic_of_homotopy` (theorem):

```lean
theorem baseChangeCx_acyclic_of_homotopy {W : CochainComplex (ModuleCat.{0} R) ℤ} (c : R)
    (H : Homotopy (c • 𝟙 W) 0) (hc : IsUnit (φ c)) : (baseChangeCx φ W).Acyclic
```

### Section `Integral`

```lean
-- (no section variables)
```

`nonempty_homotopyEquiv_of_integralChange` (theorem):

```lean
theorem nonempty_homotopyEquiv_of_integralChange {R S : Type} [CommRing R] [Field S]
    (φ : R →+* S) (hφ : letI := φ.toAlgebra; Module.Flat R S)
    {P Q W : CochainComplex (ModuleCat.{0} R) ℤ} (b : ℤ) [P.IsStrictlyLE b]
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : R) (H : Homotopy (c • 𝟙 W) 0) (hc : IsUnit (φ c)) :
    Nonempty (HomotopyEquiv (cohomologyCx (baseChangeCx φ Q)) (baseChangeCx φ P))
```

`baseChangeCx_contractible_of_homotopy` (theorem):

```lean
theorem baseChangeCx_contractible_of_homotopy {R S : Type} [CommRing R] [Field S] (φ : R →+* S)
    {W : CochainComplex (ModuleCat.{0} R) ℤ} (b : ℤ) [W.IsStrictlyLE b] (c : R)
    (H : Homotopy (c • 𝟙 W) 0) (hc : IsUnit (φ c)) :
    Nonempty (Homotopy (𝟙 (baseChangeCx φ W)) 0)
```

`laurentSeries_flat` (theorem):

```lean
theorem laurentSeries_flat :
    letI := (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))).toAlgebra
    Module.Flat (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))
```

`genericCx` (abbrev):

```lean
abbrev genericCx (Q : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ) :
    CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ
```

`genericMap` (abbrev):

```lean
abbrev genericMap {P Q : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ} (g : P ⟶ Q) :
    genericCx P ⟶ genericCx Q
```

`genericMap_quasiIso` (theorem):

```lean
theorem genericMap_quasiIso {P Q W : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ}
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : PowerSeries (ZMod 2)) (H : Homotopy (c • 𝟙 W) 0)
    (hc : IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) c)) :
    QuasiIso (genericMap ι)
```

`genericHomotopyEquiv` (def):

```lean
def genericHomotopyEquiv {P Q W : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ}
    [P.IsStrictlyLE 3]
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : PowerSeries (ZMod 2)) (H : Homotopy (c • 𝟙 W) 0)
    (hc : IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) c)) :
    HomotopyEquiv (cohomologyCx (genericCx Q)) (genericCx P)
```

`sum_finrank_homology_le_of_change` (theorem):

```lean
theorem sum_finrank_homology_le_of_change
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)]
    (P' Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ) (a b : ℤ)
    [P'.IsStrictlyGE a] [P'.IsStrictlyLE b] [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (hW : W'.Acyclic) (s : Finset ℤ) :
    ∑ n ∈ s, Module.finrank (LaurentSeries (ZMod 2)) (Q'.homology n) ≤
      ∑ n ∈ s, Module.finrank (PowerSeries (ZMod 2)) (P.X n)
```

`sum_finrank_genericHomology_le_of_integralChange` (theorem):

```lean
theorem sum_finrank_genericHomology_le_of_integralChange
    (P Q W : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0) (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : PowerSeries (ZMod 2)) (H : Homotopy (c • 𝟙 W) 0)
    (hc : IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) c))
    (s : Finset ℤ) :
    ∑ n ∈ s, Module.finrank (LaurentSeries (ZMod 2)) ((genericCx Q).homology n) ≤
      ∑ n ∈ s, Module.finrank (PowerSeries (ZMod 2)) (P.X n)
```

### Section `Consumers`

```lean
variable (K : Type) [Field K] [NumberField K]
  (Ew : ∀ w : HeightOneSpectrum (𝓞 K), WeierstrassCurve (w.adicCompletionIntegers K))
  [hEw : ∀ w, ((Ew w).baseChange (w.adicCompletion K)).IsElliptic]
-- each declaration of the section is preceded by `open Classical in`
```

`residualRankCounts_afterT'_ofChange` (def):

```lean
def residualRankCounts_afterT'_ofChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (hG3 : GlobalDegreeThreeVanishes Dsel)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    -- the change of condition after inverting `t`, and the minimal model `L` of its middle term
    (Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) (hW : W'.Acyclic)
    (l : L ⟶ Q') [QuasiIso l] :
    ResidualRankCounts
```

`residualRankCounts_afterT''_ofChange` (def):

```lean
def residualRankCounts_afterT''_ofChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2]
      continuousCohomology 3 (Wrep K (primesAboveSet K (chargedPrimes N r D))))
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    -- the change of condition after inverting `t`, and the minimal model `L` of its middle term
    (Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) (hW : W'.Acyclic)
    (l : L ⟶ Q') [QuasiIso l] :
    ResidualRankCounts
```

`residualRankCounts_afterT'''_ofChange` (def):

```lean
def residualRankCounts_afterT'''_ofChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    -- the change of condition after inverting `t`, and the minimal model `L` of its middle term
    (Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) (hW : W'.Acyclic)
    (l : L ⟶ Q') [QuasiIso l] :
    ResidualRankCounts
```

`residualRankCounts_afterT'_ofChange_genericRank` (theorem):

```lean
theorem residualRankCounts_afterT'_ofChange_genericRank
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (hG3 : GlobalDegreeThreeVanishes Dsel)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    -- the change of condition after inverting `t`, and the minimal model `L` of its middle term
    (Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) (hW : W'.Acyclic)
    (l : L ⟶ Q') [QuasiIso l] :
    (residualRankCounts_afterT'_ofChange K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr
      D hD hDodd cond hcondD hfull w hw Sloc Dsel eG hG3 hUm hLm P ered P' L ebc hLmin
      Q' W' ι π hιπ hE hW l).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (LaurentSeries (ZMod 2)) (Q'.homology n)
```

`residualRankCounts_afterT'''_ofChange_genericRank` (theorem):

```lean
theorem residualRankCounts_afterT'''_ofChange_genericRank
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    -- the change of condition after inverting `t`, and the minimal model `L` of its middle term
    (Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) (hW : W'.Acyclic)
    (l : L ⟶ Q') [QuasiIso l] :
    (residualRankCounts_afterT'''_ofChange K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr
      D hD hDodd cond hcondD hfull w hw Sloc Dsel eG eG3 hUm hLm P ered P' L ebc hLmin
      Q' W' ι π hιπ hE hW l).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (LaurentSeries (ZMod 2)) (Q'.homology n)
```

`residualRankCounts_afterT'''_ofSelmerChange` (def):

```lean
def residualRankCounts_afterT'''_ofSelmerChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    -- the change of local conditions of Selmer data over `𝔽₂((t))`, and the models `P'`, `L`
    (Dfull : SelData (LaurentSeries (ZMod 2))) (U' Wc : GCx (LaurentSeries (ZMod 2)))
    (f : GHom U' Dfull.U) (g : GHom Dfull.U Wc)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hWc : Wc.toCC.Acyclic)
    (pP : P' ⟶ (selCx (restrictData Dfull f)).toCC) [QuasiIso pP]
    (pL : L ⟶ (selCx Dfull).toCC) [QuasiIso pL] :
    ResidualRankCounts
```

`residualRankCounts_afterT'''_ofSelmerChange_genericRank` (theorem):

```lean
theorem residualRankCounts_afterT'''_ofSelmerChange_genericRank
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    -- the change of local conditions of Selmer data over `𝔽₂((t))`, and the models `P'`, `L`
    (Dfull : SelData (LaurentSeries (ZMod 2))) (U' Wc : GCx (LaurentSeries (ZMod 2)))
    (f : GHom U' Dfull.U) (g : GHom Dfull.U Wc)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hWc : Wc.toCC.Acyclic)
    (pP : P' ⟶ (selCx (restrictData Dfull f)).toCC) [QuasiIso pP]
    (pL : L ⟶ (selCx Dfull).toCC) [QuasiIso pL] :
    (residualRankCounts_afterT'''_ofSelmerChange K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr
      D hD hDodd cond hcondD hfull w hw Sloc Dsel eG eG3 hUm hLm P ered P' L ebc hLmin
      Dfull U' Wc f g hfg hinj hsurj hex hWc pP pL).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3,
        Module.finrank (LaurentSeries (ZMod 2)) ((selCx Dfull).toCC.homology n)
```

`residualRankCounts_afterT'_ofIntegralChange` (def):

```lean
def residualRankCounts_afterT'_ofIntegralChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (hG3 : GlobalDegreeThreeVanishes Dsel)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    -- the integral change of condition over `𝔽₂[[t]]` and its comparison homotopy
    (Q W : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : PowerSeries (ZMod 2)) (H : Homotopy (c • 𝟙 W) 0)
    (hc : IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) c)) :
    ResidualRankCounts
```

`residualRankCounts_afterT'_ofIntegralChange_genericRank` (theorem):

```lean
theorem residualRankCounts_afterT'_ofIntegralChange_genericRank
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (hG3 : GlobalDegreeThreeVanishes Dsel)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    -- the integral change of condition over `𝔽₂[[t]]` and its comparison homotopy
    (Q W : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : PowerSeries (ZMod 2)) (H : Homotopy (c • 𝟙 W) 0)
    (hc : IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) c)) :
    (residualRankCounts_afterT'_ofIntegralChange K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr
      D hD hDodd cond hcondD hfull w hw Sloc Dsel eG hG3 hUm hLm P ered
      Q W ι π hιπ hE c H hc).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3,
        Module.finrank (LaurentSeries (ZMod 2)) ((genericCx Q).homology n)
```

`residualRankCounts_afterT'''_ofIntegralChange` (def):

```lean
def residualRankCounts_afterT'''_ofIntegralChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    -- the integral change of condition over `𝔽₂[[t]]` and its comparison homotopy
    (Q W : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : PowerSeries (ZMod 2)) (H : Homotopy (c • 𝟙 W) 0)
    (hc : IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) c)) :
    ResidualRankCounts
```

`residualRankCounts_afterT'''_ofIntegralChange_genericRank` (theorem):

```lean
theorem residualRankCounts_afterT'''_ofIntegralChange_genericRank
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    -- the integral change of condition over `𝔽₂[[t]]` and its comparison homotopy
    (Q W : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    (ι : P ⟶ Q) (π : Q ⟶ W) (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact)
    (c : PowerSeries (ZMod 2)) (H : Homotopy (c • 𝟙 W) 0)
    (hc : IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2)) c)) :
    (residualRankCounts_afterT'''_ofIntegralChange K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr
      D hD hDodd cond hcondD hfull w hw Sloc Dsel eG eG3 hUm hLm P ered
      Q W ι π hιπ hE c H hc).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3,
        Module.finrank (LaurentSeries (ZMod 2)) ((genericCx Q).homology n)
```

`residualRankCounts_afterT'''_ofChangeCohomology` (def):

```lean
def residualRankCounts_afterT'''_ofChangeCohomology (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    -- the change of condition after inverting `t`; the minimal model is the cohomology of `Q'`
    (Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) (hW : W'.Acyclic) :
    ResidualRankCounts
```

`residualRankCounts_afterT'''_ofChangeCohomology_genericRank` (theorem):

```lean
theorem residualRankCounts_afterT'''_ofChangeCohomology_genericRank
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    -- the change of condition after inverting `t`; the minimal model is the cohomology of `Q'`
    (Q' W' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    (ι : P' ⟶ Q') (π : Q' ⟶ W') (hιπ : ι ≫ π = 0)
    (hE : (ShortComplex.mk ι π hιπ).ShortExact) (hW : W'.Acyclic) :
    (residualRankCounts_afterT'''_ofChangeCohomology K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr
      D hD hDodd cond hcondD hfull w hw Sloc Dsel eG eG3 hUm hLm P ered P' ebc
      Q' W' ι π hιπ hE hW).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (LaurentSeries (ZMod 2)) (Q'.homology n)
```

`residualRankCounts_afterT'''_ofSelmerChangeCohomology` (def):

```lean
def residualRankCounts_afterT'''_ofSelmerChangeCohomology (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    -- the change of local conditions of Selmer data over `𝔽₂((t))`; the minimal model is the
    -- cohomology of the original-support Selmer complex
    (Dfull : SelData (LaurentSeries (ZMod 2))) (U' Wc : GCx (LaurentSeries (ZMod 2)))
    (f : GHom U' Dfull.U) (g : GHom Dfull.U Wc)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hWc : Wc.toCC.Acyclic)
    (pP : P' ⟶ (selCx (restrictData Dfull f)).toCC) [QuasiIso pP] :
    ResidualRankCounts
```

`residualRankCounts_afterT'''_ofSelmerChangeCohomology_genericRank` (theorem):

```lean
theorem residualRankCounts_afterT'''_ofSelmerChangeCohomology_genericRank
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    -- the change of local conditions of Selmer data over `𝔽₂((t))`; the minimal model is the
    -- cohomology of the original-support Selmer complex
    (Dfull : SelData (LaurentSeries (ZMod 2))) (U' Wc : GCx (LaurentSeries (ZMod 2)))
    (f : GHom U' Dfull.U) (g : GHom Dfull.U Wc)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hWc : Wc.toCC.Acyclic)
    (pP : P' ⟶ (selCx (restrictData Dfull f)).toCC) [QuasiIso pP] :
    (residualRankCounts_afterT'''_ofSelmerChangeCohomology K Ew h410 h51 h28 h23 k α hα hK N hN A
      hA r hr D hD hDodd cond hcondD hfull w hw Sloc Dsel eG eG3 hUm hLm P ered P'
      ebc Dfull U' Wc f g hfg hinj hsurj hex hWc pP).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3,
        Module.finrank (LaurentSeries (ZMod 2)) ((selCx Dfull).toCC.homology n)
```

### Section `NonVacuity`

```lean
variable {R : Type u} [CommRing R]
```

`activeBlock` (abbrev):

```lean
abbrev activeBlock (K : CochainComplex (ModuleCat.{u} R) ℤ) (c : R) :
    CochainComplex (ModuleCat.{u} R) ℤ
```

`activeBlockHomotopy` (def):

```lean
def activeBlockHomotopy (K : CochainComplex (ModuleCat.{u} R) ℤ) (c : R) :
    Homotopy (c • 𝟙 (activeBlock K c)) 0
```

`integralChange_nonvacuous` (theorem):

```lean
theorem integralChange_nonvacuous (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    (b : ℤ) [P.IsStrictlyLE b] (K : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    {e : ℕ} (he : Odd e) :
    Nonempty (HomotopyEquiv
      (cohomologyCx (genericCx
        (P ⊞ activeBlock K (((1 : PowerSeries (ZMod 2)) + PowerSeries.X) ^ e - 1))))
      (genericCx P))
```

`integralChange_transfer_nonvacuous` (theorem):

```lean
theorem integralChange_transfer_nonvacuous
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (K : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ) {e : ℕ} (he : Odd e)
    (s : Finset ℤ) :
    ∑ n ∈ s, Module.finrank (LaurentSeries (ZMod 2))
        ((genericCx (P ⊞ activeBlock K (((1 : PowerSeries (ZMod 2)) + PowerSeries.X) ^ e
          - 1))).homology n) ≤
      ∑ n ∈ s, Module.finrank (PowerSeries (ZMod 2)) (P.X n)
```

### Section `Witness`

```lean
open scoped Classical
```

`homotopyOfCHomotopy` (def):

```lean
def homotopyOfCHomotopy {R : Type} [CommRing R] {C : GCx R} {c : R} (H : CHomotopy C c) :
    Homotopy (c • 𝟙 C.toCC) 0
```

`witnessIncl` (abbrev):

```lean
abbrev witnessIncl : afterP ⟶ afterQ_G.toCC
```

`witnessProj` (abbrev):

```lean
abbrev witnessProj : afterQ_G.toCC ⟶ activeW.toCC
```

`witnessIncl_proj` (theorem):

```lean
theorem witnessIncl_proj : witnessIncl ≫ witnessProj = 0
```

`witness_integralSES` (theorem):

```lean
theorem witness_integralSES :
    (ShortComplex.mk witnessIncl witnessProj witnessIncl_proj).ShortExact
```

`witnessCountsOfChange` (def):

```lean
def witnessCountsOfChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) : ResidualRankCounts
```

`witnessCountsOfChange_bounds` (theorem):

```lean
theorem witnessCountsOfChange_bounds (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    2 ≤ (witnessCountsOfChange h410 h51 h28 h23).genericRank ∧
      (witnessCountsOfChange h410 h51 h28 h23).genericRank ≤
        (witnessCountsOfChange h410 h51 h28 h23).rankTot ∧
      (witnessCountsOfChange h410 h51 h28 h23).genericRank ≤ 294
```

`witnessCountsOfChangeCohomology` (def):

```lean
def witnessCountsOfChangeCohomology (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) : ResidualRankCounts
```

`witnessCountsOfChangeCohomology_bounds` (theorem):

```lean
theorem witnessCountsOfChangeCohomology_bounds (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    2 ≤ (witnessCountsOfChangeCohomology h410 h51 h28 h23).genericRank ∧
      (witnessCountsOfChangeCohomology h410 h51 h28 h23).genericRank ≤
        (witnessCountsOfChangeCohomology h410 h51 h28 h23).rankTot ∧
      (witnessCountsOfChangeCohomology h410 h51 h28 h23).genericRank ≤ 294
```

`witnessCountsOfIntegralChange` (def):

```lean
def witnessCountsOfIntegralChange (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) : ResidualRankCounts
```

`witnessCountsOfIntegralChange_bounds` (theorem):

```lean
theorem witnessCountsOfIntegralChange_bounds (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    ¬ activeW.toCC.Acyclic ∧
      2 ≤ (witnessCountsOfIntegralChange h410 h51 h28 h23).genericRank ∧
      (witnessCountsOfIntegralChange h410 h51 h28 h23).genericRank ≤
        (witnessCountsOfIntegralChange h410 h51 h28 h23).rankTot ∧
      (witnessCountsOfIntegralChange h410 h51 h28 h23).genericRank ≤ 294
```
