import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Dominant
import ZInQKernel.Contrib.RC53Assist.NewformPeriodsDictionary.Dictionary

/-!
# Modular Weil: from a dominant morphism of scheme models to a pointed function-field map

The F2 step of the newform-periods dictionary (`RC53Assist/NewformPeriodsDictionary`): Faltings'
conclusion is an isogeny of elliptic curves over `ℚ` at the level of schemes (abelian varieties);
the dictionary's `isogenyOfPointedFunctionFieldMap` turns a pointed `ℚ`-embedding of the actual
Weierstrass function fields `σ : K(E₂) → K(E₁)` into a `TauCeti.Isogeny`. This file reduces the
remaining step — from a morphism of schemes to `σ` — to three explicit inputs (Silverman, *The
Arithmetic of Elliptic Curves*, II.2 and III.4; Hartshorne I.4.4):

* **R1** (input): a scheme model `X` of `E` over `ℚ` — the projective Weierstrass model; it is not
  in this tree (only its homogeneous coordinate ring is vendored), so a `SchemeModel` takes any
  irreducible scheme `X`;
* **R2** (input): an identification of the function field (generic stalk) of `X` with the actual
  function field `E.toAffine.FunctionField` (`SchemeModel.e`, a ring isomorphism);
* **R3** (PROVED here): a dominant morphism `f : X₁ → X₂` gives the pullback of rational functions
  (Tau Ceti's `Scheme.Hom.functionFieldMap`), hence `fieldMap M₁ M₂ f : K(E₂) →ₐ[ℚ] K(E₁)` (every
  ring map between fields of characteristic zero is `ℚ`-linear), functorially
  (`fieldMap_id`, `fieldMap_comp`);
* **R4** (input): pointedness in the valuation form of the dictionary, `IsPointedMap M₁ M₂ f`
  (the place at infinity of `E₁` restricts to the place at infinity of `E₂`; for the projective
  models this is `f(O₁) = O₂` read through the stalks at the origins, not formalized here).

`isogenyOfDominant`: the `TauCeti.Isogeny E₁ → E₂` of the dictionary
(`isogenyOfPointedFunctionFieldMap`) with `fieldPullback = fieldMap M₁ M₂ f`
(`isogenyOfDominant_fieldPullback`); pointed maps compose (`isPointedMap_comp`).

Non-vacuity (`affineChart`, `isPointedMap_id_affineChart`, `isogenyOfDominant_nonvacuous`): **the
instance is the affine chart** `Spec (E.toAffine.CoordinateRing)` with its function field identified
by Mathlib's `functionField_isFractionRing_of_affine`, and `f = 𝟙` — **not the projective model**
(which is not available here). It shows the inputs are consistent, not that R1, R2, R4 hold for the
projective models.

**Classification.** Definitions and PROVED statements; R1, R2, R4 are explicit inputs.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ModularWeil

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Affine
  ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary

/-- **A scheme model of `E` with its function field identified** (inputs R1, R2): a scheme `X`
(irreducible) and a ring isomorphism between its generic stalk `K(X)` and the actual function field
`K(E) = E.toAffine.FunctionField`. -/
structure SchemeModel (E : WeierstrassCurve ℚ) where
  X : Scheme.{0}
  [irreducible : IrreducibleSpace X]
  e : X.functionField ≃+* E.toAffine.FunctionField


instance SchemeModel.instIrreducible {E : WeierstrassCurve ℚ} (M : SchemeModel E) :
    IrreducibleSpace M.X :=
  M.irreducible

variable {E₁ E₂ E₃ : WeierstrassCurve ℚ} (M₁ : SchemeModel E₁) (M₂ : SchemeModel E₂)
  (M₃ : SchemeModel E₃)

/-- **R3: the pullback of rational functions along a dominant morphism of models**, as a
`ℚ`-algebra map `K(E₂) → K(E₁)`: `e₁ ∘ f^* ∘ e₂⁻¹`. -/
def fieldMap (f : M₁.X ⟶ M₂.X) [IsDominant f] :
    E₂.toAffine.FunctionField →ₐ[ℚ] E₁.toAffine.FunctionField :=
  ((M₁.e.toRingHom.comp f.functionFieldMap.hom).comp M₂.e.symm.toRingHom).toRatAlgHom

theorem fieldMap_apply (f : M₁.X ⟶ M₂.X)
    [IsDominant f] (x : E₂.toAffine.FunctionField) :
    fieldMap M₁ M₂ f x = M₁.e (f.functionFieldMap.hom (M₂.e.symm x)) :=
  rfl

/-- Functoriality: the identity. PROVED. -/
theorem fieldMap_id : fieldMap M₁ M₁ (𝟙 M₁.X) = AlgHom.id ℚ _ := by
  refine AlgHom.ext fun x => ?_
  rw [fieldMap_apply, Scheme.Hom.functionFieldMap_id]
  change M₁.e (M₁.e.symm x) = x
  exact M₁.e.apply_symm_apply x

/-- Functoriality: composition. PROVED. -/
theorem fieldMap_comp (f : M₁.X ⟶ M₂.X) (g : M₂.X ⟶ M₃.X) [IsDominant f] [IsDominant g] :
    fieldMap M₁ M₃ (f ≫ g) = (fieldMap M₁ M₂ f).comp (fieldMap M₂ M₃ g) := by
  refine AlgHom.ext fun x => ?_
  rw [AlgHom.comp_apply, fieldMap_apply, fieldMap_apply, fieldMap_apply,
    Scheme.Hom.functionFieldMap_comp, M₂.e.symm_apply_apply]
  rfl

/-- **R4: pointedness** of a dominant morphism of models, in the valuation form of the
dictionary: the place at infinity of `E₁` restricted along `fieldMap` is equivalent to the place at
infinity of `E₂`. -/
def IsPointedMap (f : M₁.X ⟶ M₂.X) [IsDominant f] :
    Prop :=
  ((infinityPlace E₁.toAffine).comap (fieldMap M₁ M₂ f).toRingHom).IsEquiv
    (infinityPlace E₂.toAffine)

/-- **The isogeny of a pointed dominant morphism of models** (through the dictionary's
`isogenyOfPointedFunctionFieldMap`). -/
def isogenyOfDominant (f : M₁.X ⟶ M₂.X)
    [IsDominant f] (hf : IsPointedMap M₁ M₂ f) : TauCeti.Isogeny E₁.toAffine E₂.toAffine :=
  isogenyOfPointedFunctionFieldMap E₁ E₂ (fieldMap M₁ M₂ f) hf

/-- The isogeny induces exactly the pullback of rational functions. PROVED. -/
theorem isogenyOfDominant_fieldPullback (f : M₁.X ⟶ M₂.X) [IsDominant f] (hf : IsPointedMap M₁ M₂ f) :
    (isogenyOfDominant M₁ M₂ f hf).fieldPullback = fieldMap M₁ M₂ f :=
  isogenyOfPointedFunctionFieldMap_fieldPullback E₁ E₂ _ hf

/-- Pointed dominant morphisms compose. PROVED. -/
theorem isPointedMap_comp (f : M₁.X ⟶ M₂.X) (g : M₂.X ⟶ M₃.X) [IsDominant f] [IsDominant g]
    (hf : IsPointedMap M₁ M₂ f) (hg : IsPointedMap M₂ M₃ g) : IsPointedMap M₁ M₃ (f ≫ g) := by
  have hc : ∀ x, fieldMap M₁ M₃ (f ≫ g) x = fieldMap M₁ M₂ f (fieldMap M₂ M₃ g x) := fun x => by
    rw [fieldMap_comp]; rfl
  intro r s
  have h1 := hf (fieldMap M₂ M₃ g r) (fieldMap M₂ M₃ g s)
  have h2 := hg r s
  simp only [Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1 h2 ⊢
  rw [hc, hc]
  exact h1.trans h2

/-! ### Non-vacuity on the affine chart (not the projective model) -/

/-- The function field of `Spec R` (`R` a domain) is any fraction field of `R`. -/
def affineFunctionFieldEquiv (R : CommRingCat.{0}) [IsDomain R] (L : Type) [CommRing L]
    [Algebra R L] [IsFractionRing R L] : (Spec R).functionField ≃+* L :=
  IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl R)

/-- **The affine chart as a model** — NOT the projective model: `X = Spec (E.toAffine.CoordinateRing)`
with its function field identified with `E.toAffine.FunctionField` (both are fraction fields of the
affine coordinate ring; Mathlib's `functionField_isFractionRing_of_affine`). -/
def affineChart (E : WeierstrassCurve ℚ) : SchemeModel E :=
  letI : IsDomain (CommRingCat.of E.toAffine.CoordinateRing) :=
    inferInstanceAs (IsDomain E.toAffine.CoordinateRing)
  letI : Algebra (CommRingCat.of E.toAffine.CoordinateRing) E.toAffine.FunctionField :=
    inferInstanceAs (Algebra E.toAffine.CoordinateRing E.toAffine.FunctionField)
  haveI : IsFractionRing (CommRingCat.of E.toAffine.CoordinateRing) E.toAffine.FunctionField :=
    inferInstanceAs (IsFractionRing E.toAffine.CoordinateRing E.toAffine.FunctionField)
  { X := Spec (CommRingCat.of E.toAffine.CoordinateRing)
    e := affineFunctionFieldEquiv (CommRingCat.of E.toAffine.CoordinateRing)
      E.toAffine.FunctionField }

/-- The identity of the affine chart is pointed. PROVED. -/
theorem isPointedMap_id_affineChart (E : WeierstrassCurve ℚ) :
    IsPointedMap (affineChart E) (affineChart E) (𝟙 (affineChart E).X) := by
  unfold IsPointedMap
  rw [fieldMap_id]
  intro r s
  exact Iff.rfl

/-- **Non-vacuity of the inputs R1, R2, R4 (on the affine chart)**: for every Weierstrass curve `E`
over `ℚ`, the affine chart with `f = 𝟙` gives the identity isogeny through `isogenyOfDominant`,
with `fieldPullback` the identity. This instance is the affine chart, not the projective model.
PROVED. -/
theorem isogenyOfDominant_nonvacuous (E : WeierstrassCurve ℚ) :
    (isogenyOfDominant (affineChart E) (affineChart E) (𝟙 (affineChart E).X)
      (isPointedMap_id_affineChart E)).fieldPullback = AlgHom.id ℚ _ := by
  rw [isogenyOfDominant_fieldPullback, fieldMap_id]

end ZInQ.Contrib.CloudB3RC53.ModularWeil
