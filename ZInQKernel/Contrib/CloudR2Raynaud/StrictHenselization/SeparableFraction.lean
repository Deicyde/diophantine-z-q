/-
Copyright (c) 2026 Contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.

Uses filtered-colimit, étale base-change and separability results from Mathlib,
distributed under Apache 2.0 at revision
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

import Mathlib

/-!
# Separable fraction fields of ind-étale algebras

An element of a filtered colimit of étale algebras is represented at an actual
étale stage. After base change to the coefficient field, a field-valued point
of that stage factors through a separable kernel quotient. This proves
separability of the image of every ring element; closure under inverse and
product then proves separability of the fraction field.

The coefficient-field algebra structure is supplied, not replaced. Its
compatibility with the two base-ring maps is expressed by the scalar towers.
No discrete-valuation, henselian or finite-type hypothesis on the entire
ind-étale algebra is used.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ZInQ.Contrib.CloudR2Raynaud.StrictHenselization

/-- Each element of an ind-étale algebra is the image of an element at an
étale stage of its given filtered colimit presentation. -/
private theorem etale_stage_element
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R A)) (a : A) :
    ∃ B : CommAlgCat.{u} R, Algebra.Etale R B ∧
      ∃ (f : B →ₐ[R] A) (b : B), f b = a := by
  obtain ⟨J, hJ, hfil, pres, het⟩ := hind
  letI := hJ
  letI := hfil
  haveI : IsConnected J := IsFiltered.isConnected J
  have hforget : forget (CommAlgCat.{u} R) =
      (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
        Under.forget (CommRingCat.of R) ⋙ forget CommRingCat.{u} := rfl
  haveI : PreservesColimitsOfShape J (forget (CommAlgCat.{u} R)) := by
    rw [hforget]
    infer_instance
  obtain ⟨j, b, hb⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (CommAlgCat.{u} R)) pres.isColimit) a
  exact ⟨pres.diag.obj j, het j, (pres.ι.app j).hom, b, hb⟩

/-- A field-valued point of an étale stage has separable values over a
compatible coefficient field. Essential finite type is used at the stage,
not assumed for the final field. -/
private theorem separable_image_at_etale_stage
    {R K B L : Type u} [CommRing R] [Field K] [CommRing B] [Field L]
    [Algebra R K] [Algebra R B] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] [Algebra.Etale R B]
    (f : B →ₐ[R] L) (b : B) : IsSeparable K (f b) := by
  let C := K ⊗[R] B
  haveI : Algebra.Etale K C := inferInstance
  let g : C →ₐ[K] L := (AlgHom.liftEquiv R K B L) f
  let p : Ideal C := RingHom.ker g.toRingHom
  haveI : p.IsPrime := RingHom.ker_isPrime g.toRingHom
  haveI : Algebra.IsSeparable K (C ⧸ p) := inferInstance
  let gbar : C ⧸ p →ₐ[K] L := Ideal.kerLiftAlg g
  have hgbar : Function.Injective gbar := Ideal.kerLiftAlg_injective g
  have hsep : IsSeparable K (gbar (Ideal.Quotient.mk p ((1 : K) ⊗ₜ[R] b))) :=
    IsSeparable.map gbar hgbar
      (Algebra.IsSeparable.isSeparable K (Ideal.Quotient.mk p ((1 : K) ⊗ₜ[R] b)))
  have hvalue : gbar (Ideal.Quotient.mk p ((1 : K) ⊗ₜ[R] b)) = f b := by
    change g ((1 : K) ⊗ₜ[R] b) = f b
    simpa only [g, one_smul] using (AlgHom.liftEquiv_tmul f (1 : K) b)
  rw [hvalue] at hsep
  exact hsep

/-- The actual fraction field of a domain that is ind-étale over the base is
separable over any supplied compatible coefficient field. -/
theorem separable_fraction_of_indEtale
    {R K Rh : Type u} [CommRing R] [Field K] [CommRing Rh] [IsDomain Rh]
    [Algebra R K] [Algebra R Rh]
    [Algebra K (FractionRing Rh)]
    [IsScalarTower R Rh (FractionRing Rh)] [IsScalarTower R K (FractionRing Rh)]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R Rh)) :
    Algebra.IsSeparable K (FractionRing Rh) := by
  have hRhTower : @IsScalarTower R Rh (FractionRing Rh)
      (Algebra.toSMul : SMul R Rh)
      (Algebra.toSMul : SMul Rh (FractionRing Rh))
      (Algebra.toSMul : SMul R (FractionRing Rh)) :=
    inferInstanceAs (IsScalarTower R Rh (FractionRing Rh))
  have hKTower : @IsScalarTower R K (FractionRing Rh)
      (Algebra.toSMul : SMul R K)
      (Algebra.toSMul : SMul K (FractionRing Rh))
      (Algebra.toSMul : SMul R (FractionRing Rh)) :=
    inferInstanceAs (IsScalarTower R K (FractionRing Rh))
  have himage (r : Rh) : IsSeparable K (algebraMap Rh (FractionRing Rh) r) := by
    obtain ⟨B, hB, f, b, hfb⟩ := etale_stage_element hind r
    haveI : Algebra.Etale R B := hB
    let point : B →ₐ[R] FractionRing Rh :=
      (@IsScalarTower.toAlgHom R Rh (FractionRing Rh) _ _ _ _ _ _ hRhTower).comp f
    have hpoint : point b = algebraMap Rh (FractionRing Rh) (f b) := by
      rfl
    have hsep := @separable_image_at_etale_stage
      R K B (FractionRing Rh) _ _ _ _ _ _ _ _ hKTower hB point b
    rw [hpoint, hfb] at hsep
    exact hsep
  constructor
  intro z
  obtain ⟨r, s, -, rfl⟩ := IsFractionRing.div_surjective Rh z
  rw [div_eq_mul_inv]
  exact Field.isSeparable_mul (himage r) (Field.isSeparable_inv (himage s))

end ZInQ.Contrib.CloudR2Raynaud.StrictHenselization
