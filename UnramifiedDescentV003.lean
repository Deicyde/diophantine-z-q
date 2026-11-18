import PointUnramifiedV002

/-!
# Unramified descent of inertia-fixed points, in unfolded form

Restates `exists_unramified_point_field` with the center of `w` on the integral closure written as
the comap of the maximal ideal of `w` along `b ↦ ((b : M) : Ω)` (co-restricted to `w`), with all
coordinate-field data as existential witnesses: a finite, separable intermediate field `M`, an
`O`-algebra structure on `M` compatible with `K`, unramifiedness of the integral closure of `O` in
`M` at that center, and a point over `M` whose base change to `Ω` is the given point.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace InertiaPointDescent

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

theorem integralCenter_eq_comap (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (M : IntermediateField K Ω) [FiniteDimensional K M]
    [Algebra O M] [IsScalarTower O K M]
    (h : ∀ b : integralClosure O M,
      ((M.val.toRingHom).comp (algebraMap (integralClosure O M) M)) b ∈ w) :
    integralCenter O w hw M.val =
      (maximalIdeal w).comap
        (((M.val.toRingHom).comp (algebraMap (integralClosure O M) M)).codRestrict w h) := by
  ext b
  rw [mem_integralCenter_iff, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

/-- **Inertia-fixed points have an unramified descent** (unfolded form). -/
theorem inertia_fixed_unramified_descent (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K)
    (x : A.Pt Ω) (hx : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → A.galAct σ x = x) :
    ∃ (M : IntermediateField K Ω) (_ : FiniteDimensional K M) (_ : Algebra.IsSeparable K M)
      (_ : Algebra O M) (_ : IsScalarTower O K M)
      (h : ∀ b : integralClosure O M,
        ((M.val.toRingHom).comp (algebraMap (integralClosure O M) M)) b ∈ w)
      (_ : Algebra.IsUnramifiedAt O ((maximalIdeal w).comap
        (((M.val.toRingHom).comp (algebraMap (integralClosure O M) M)).codRestrict w h)))
      (y : A.Pt M), Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫ y.left = x.left := by
  obtain ⟨M, hfd, -, ⟨y, hy⟩, hU⟩ := exists_unramified_point_field O w hw A x hx
  let _ : Algebra O M := ((algebraMap K M).comp (algebraMap O K)).toAlgebra
  have hst : IsScalarTower O K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hsep : Algebra.IsSeparable K M := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have h : ∀ b : integralClosure O M,
      ((M.val.toRingHom).comp (algebraMap (integralClosure O M) M)) b ∈ w := fun b =>
    mem_of_integralOver O w hw (integralOver_embed O M.val b)
  refine ⟨M, hfd, hsep, inferInstance, hst, h, ?_, y, hy⟩
  have heq := integralCenter_eq_comap O w hw M h
  convert hU using 2 <;> exact heq.symm

end InertiaPointDescent
