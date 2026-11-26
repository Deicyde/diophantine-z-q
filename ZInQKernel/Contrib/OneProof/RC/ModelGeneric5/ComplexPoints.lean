import ZInQKernel.Contrib.OneProof.RC.ModelGeneric5.Extension
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric3.AtkinCoordinates
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric4.Surjectivity

/-! The Atkin–Lehner operators as involutions, and their action on complex points.

* `atkinRat_involutive`, `atkinLevel_involutive`, `Wint_comp_self`: the rational and integral
  ring maps, and `Wint`, are involutions (from `RationalAtkin.square` and the open immersion).
* `rationalPointAtParameter_atkinRat`: at the analytic point of `τ`, the pinned rational map
  `atkinRat hQ` gives the analytic point of the matrix translate `W_Q τ`.
* `rationalPoints_atkinRat_complex`: for every complex point `y` of the pinned rational open
  there is `τ` with `rationalPoints y = analyticCyclicPair τ` and
  `rationalPoints (y ∘ atkinRat) = analyticCyclicPair (W_Q τ)`, with actual readings on both
  sides (generic4, items 1–2).

What this leaves for the moduli form (item 3): `analyticCyclicPair (W_Q τ)` is the class of
`(E_τ / C_Q, (E_τ[Q] + C)/C_Q)` built from the vendored Vélu quotient; see the report. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ModularCurve
open scoped TauCeti.ExactDivisor
open WeierstrassCurve.ModelTorsion WeierstrassCurve.ModelLevels
  WeierstrassCurve.ModelLevels.ModelGeneric WeierstrassCurve.ModelLevels.ModelGeneric2
open ZInQ.Manuscript.RC.AtkinRational

namespace ZInQ.Manuscript.RC.ModelGeneric5

attribute [local instance 2000] levelCommRing

variable {ell N Q : ℕ} [Fact ell.Prime] [NeZero N]
  (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)

omit [Fact ell.Prime] in
/-- `Spec` of two ring maps into the pinned rational ring agree after the open immersion only
if the ring maps agree. -/
theorem ringHom_eq_of_openImmersion {A : Type} [CommRing A]
    {f g : Y0RationalAlgebra h₂ →+* A}
    (h : Spec.map (CommRingCat.ofHom f) ≫ rationalOpenImmersion h₂ =
      Spec.map (CommRingCat.ofHom g) ≫ rationalOpenImmersion h₂) : f = g := by
  haveI := rationalOpenImmersion_isOpen h₂
  have h' := (cancel_mono (rationalOpenImmersion h₂)).mp h
  have h'' := Spec.map_injective h'
  exact congrArg CommRingCat.Hom.hom h''

omit [Fact ell.Prime] in
/-- **The rational Atkin–Lehner ring map is an involution.** -/
theorem atkinRat_involutive (hQ : Q ∥ N) :
    (atkinRat h₂ hQ).comp (atkinRat h₂ hQ) = RingHom.id _ := by
  apply ringHom_eq_of_openImmersion h₂
  have hsq := (rationalAtkin hQ).square
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, atkinRat_openImmersion,
    ← Category.assoc, atkinRat_openImmersion, Category.assoc]
  change _ ≫ (rationalAtkin hQ).hom ≫ (rationalAtkin hQ).hom = _
  rw [hsq, Category.comp_id]
  change _ = Spec.map (𝟙 _) ≫ _
  rw [Spec.map_id, Category.id_comp]

/-- **The integral Atkin–Lehner ring map is an involution.** -/
theorem atkinLevel_involutive (hQ : Q ∥ N) (a : Pinned.Y0LevelAlgebra h₅ htame h₂) :
    atkinLevel h₅ htame h₂ hQ (atkinLevel h₅ htame h₂ hQ a) = a := by
  apply levelToRat_injective h₅ htame h₂
  rw [levelToRat_atkinLevel, levelToRat_atkinLevel]
  exact RingHom.congr_fun (atkinRat_involutive h₂ hQ) _

/-- **`Wint` is an involution of the pinned model.** -/
theorem Wint_comp_self (hQ : Q ∥ N) :
    Wint h₅ htame h₂ hQ ≫ Wint h₅ htame h₂ hQ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (atkinLevel h₅ htame h₂ hQ)) ≫
    Spec.map (CommRingCat.ofHom (atkinLevel h₅ htame h₂ hQ)) = 𝟙 _
  have hr : CommRingCat.ofHom (atkinLevel h₅ htame h₂ hQ) ≫
      CommRingCat.ofHom (atkinLevel h₅ htame h₂ hQ) = 𝟙 _ :=
    CommRingCat.hom_ext (RingHom.ext fun a => atkinLevel_involutive h₅ htame h₂ hQ a)
  exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map hr).trans (Spec.map_id _))

omit [Fact ell.Prime] in
/-- **At the analytic point of `τ`, `atkinRat` gives the analytic point of `W_Q τ`.** -/
theorem rationalPointAtParameter_atkinRat (hQ : Q ∥ N) (τ : UpperHalfPlane) :
    (ModelGeneric3.rationalPointAtParameter h₂ τ).toRingHom.comp (atkinRat h₂ hQ) =
      (ModelGeneric3.rationalPointAtParameter h₂ (AtkinPin.atkinGL hQ • τ)).toRingHom := by
  apply ringHom_eq_of_openImmersion h₂
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, atkinRat_openImmersion,
    ← Category.assoc]
  exact ModelGeneric3.rationalAtkin_rationalPointAtParameter h₂ hQ τ

/-- The rational Atkin–Lehner map as a `ℚ`-algebra map. -/
def atkinRatAlg (hQ : Q ∥ N) : Y0RationalAlgebra h₂ →ₐ[ℚ] Y0RationalAlgebra h₂ :=
  (atkinRat h₂ hQ).toRatAlgHom

omit [Fact ell.Prime] in
/-- **The pinned class after `atkinRat`, at every complex point.** For every complex point
`y` of the pinned rational open there is `τ ∈ ℍ` with `rationalPoints y` the class of
`(ℂ/(ℤτ+ℤ), ⟨1/N⟩)`, and `rationalPoints (y ∘ atkinRat)` the class at `W_Q τ`. -/
theorem rationalPoints_atkinRat_complex (hQ : Q ∥ N)
    (y : Y0RationalAlgebra h₂ →ₐ[ℚ] ℂ) :
    ∃ τ : UpperHalfPlane,
      rationalPoints h₂ y = ModelGeneric3.analyticCyclicPair (N := N) τ ∧
      rationalPoints h₂ (y.comp (atkinRatAlg h₂ hQ)) =
        ModelGeneric3.analyticCyclicPair (N := N) (AtkinPin.atkinGL hQ • τ) := by
  obtain ⟨τ, rfl⟩ := ModelGeneric4.exists_rationalPointAtParameter_eq h₂ y
  refine ⟨τ, ModelGeneric4.rationalPoints_rationalPointAtParameter h₂ τ, ?_⟩
  have h : (ModelGeneric3.rationalPointAtParameter h₂ τ).comp (atkinRatAlg h₂ hQ) =
      ModelGeneric3.rationalPointAtParameter h₂ (AtkinPin.atkinGL hQ • τ) :=
    AlgHom.ext fun a => RingHom.congr_fun (rationalPointAtParameter_atkinRat h₂ hQ τ) a
  rw [h]
  exact ModelGeneric4.rationalPoints_rationalPointAtParameter h₂ _

#print axioms ringHom_eq_of_openImmersion
#print axioms atkinRat_involutive
#print axioms atkinLevel_involutive
#print axioms Wint_comp_self
#print axioms rationalPointAtParameter_atkinRat
#print axioms atkinRatAlg
#print axioms rationalPoints_atkinRat_complex

end ZInQ.Manuscript.RC.ModelGeneric5
