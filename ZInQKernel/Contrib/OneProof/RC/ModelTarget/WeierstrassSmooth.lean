import ZInQKernel.Contrib.OneProof.RC.ModelTarget.ChartSmoothY
import ZInQKernel.Contrib.OneProof.RC.ModelNeron.Target
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! The projective Weierstrass cubic of a unit-discriminant equation is smooth over the
base, tex 8477–8479. The charts `D₊(Y)` and `D₊(Z)` cover `Proj` (a point with
`Y = Z = 0` would have `X³ = 0`, so it would contain the irrelevant ideal), and both
charts are smooth by `ChartSmooth` and `ChartSmoothY`. At the detector, with `ℓ ≥ 5`, a
shear constant among `0, 1, 2, 3` exists because the third finite difference of a monic
cubic is `6`. The Jacobian-criterion background is Silverman, *The Arithmetic of Elliptic
Curves*, 2009, VII.5, and Katz–Mazur 1985 §2.2 (both UNVERIFIED); the formal
argument is on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve HomogeneousLocalization
open WeierstrassCurve.ModelTorsion

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.ModelTarget

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- The structure morphism of the projective cubic to the base. -/
abbrev projStructure : Proj W.toProjective.grading ⟶ Spec (.of R) :=
  Proj.toSpecZero W.toProjective.grading ≫
    Spec.map W.toProjective.gradingZeroEquiv.toRingEquiv.toCommRingCatIso.hom

theorem coord_zero_cube :
    W.toProjective.coord 0 ^ 3 =
      W.toProjective.coord 1 * (W.toProjective.coord 1 * W.toProjective.coord 2 +
          algebraMap R _ W.a₁ * W.toProjective.coord 0 * W.toProjective.coord 2 +
          algebraMap R _ W.a₃ * W.toProjective.coord 2 ^ 2) +
        W.toProjective.coord 2 * (-(algebraMap R _ W.a₂ * W.toProjective.coord 0 ^ 2) -
          algebraMap R _ W.a₄ * W.toProjective.coord 0 * W.toProjective.coord 2 -
          algebraMap R _ W.a₆ * W.toProjective.coord 2 ^ 2) := by
  have key : ∀ p : MvPolynomial (Fin 3) R, p = W.toProjective.polynomial →
      Ideal.Quotient.mk (Ideal.span {W.toProjective.polynomial}) p = 0 :=
    fun p hp => hp ▸ Ideal.Quotient.mk_singleton_self _
  have h := key (MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 +
      MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 +
      MvPolynomial.C W.a₃ * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2 -
      (MvPolynomial.X 0 ^ 3 + MvPolynomial.C W.a₂ * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 +
        MvPolynomial.C W.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2 +
        MvPolynomial.C W.a₆ * MvPolynomial.X 2 ^ 3)) rfl
  simp only [map_sub, map_add, map_mul, map_pow] at h
  simp only [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
  linear_combination -h

/-- The charts `D₊(Y)` and `D₊(Z)` cover the projective cubic. -/
theorem iSup_basicOpen_YZ :
    ⨆ i : Fin 2, Proj.basicOpen W.toProjective.grading
      (![W.toProjective.coord 1, W.toProjective.coord 2] i) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rw [TopologicalSpace.Opens.mem_iSup]
  by_contra h
  push Not at h
  have h1 : W.toProjective.coord 1 ∈ x.asHomogeneousIdeal := by
    simpa [Proj.mem_basicOpen] using h 0
  have h2 : W.toProjective.coord 2 ∈ x.asHomogeneousIdeal := by
    simpa [Proj.mem_basicOpen] using h 1
  have h0 : W.toProjective.coord 0 ∈ x.asHomogeneousIdeal := by
    have hp : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
    refine hp.mem_of_pow_mem 3 ?_
    rw [coord_zero_cube]
    exact x.asHomogeneousIdeal.toIdeal.add_mem (x.asHomogeneousIdeal.toIdeal.mul_mem_right _ h1)
      (x.asHomogeneousIdeal.toIdeal.mul_mem_right _ h2)
  apply x.not_irrelevant_le
  intro a ha
  have hspan : Ideal.span (Set.range W.toProjective.coord) ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    exacts [h0, h1, h2]
  exact hspan (W.toProjective.irrelevant_le_span_range_coord ha)

set_option backward.isDefEq.respectTransparency false in
/-- On a chart the structure morphism is the spectrum of the constants of the chart. -/
theorem smooth_chart_iff (i : Fin 3) :
    Smooth ((Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)).ι ≫
      projStructure W) ↔ RingHom.Smooth (chartConst W i) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Smooth.{0})
    (Proj.basicOpenIsoSpec W.toProjective.grading (W.toProjective.coord i)
      (W.toProjective.coord_mem_grading i) zero_lt_one).inv, ← Category.assoc, ← Category.assoc,
    ← Proj.awayι, Proj.awayι_toSpecZero, ← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @Smooth.{0})]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The projective cubic of a unit-discriminant equation is smooth over the base, given
a shear constant. -/
theorem smooth_projStructure [W.IsElliptic] {c w : R}
    (hw : w * (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) = -1) : Smooth (projStructure W) := by
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Smooth.{0}) _ (iSup_basicOpen_YZ W)]
  intro i
  fin_cases i
  · exact (smooth_chart_iff W 1).mpr (smooth_chartY W hw)
  · exact (smooth_chart_iff W 2).mpr (smooth_chartZ W)

/-- A monic cubic over `ℤ` takes a value prime to a prime `ℓ ≥ 5` at one of `0, 1, 2, 3`:
its third finite difference is `6`. -/
theorem exists_shear (ell : ℕ) (hp : ell.Prime) (h₅ : 5 ≤ ell) (a b d : ℤ) :
    ∃ c : ℤ, ¬ (ell : ℤ) ∣ c ^ 3 + a * c ^ 2 + b * c + d := by
  by_contra! h
  have h6 : (ell : ℤ) ∣ 6 := by
    have := (((h 3).sub (dvd_mul_of_dvd_right (h 2) 3)).add
      (dvd_mul_of_dvd_right (h 1) 3)).sub (h 0)
    convert this using 1
    ring
  have : ell ∣ 6 := by exact_mod_cast h6
  have hle := Nat.le_of_dvd (by norm_num) this
  interval_cases ell
  · norm_num at this
  · norm_num at hp

variable (ell : ℕ) [Fact ell.Prime]

/-- **Smoothness of the detector's good cubic.** For an integral Weierstrass equation
whose discriminant is prime to the detector `ℓ ≥ 5`, the projective cubic of its
localization at `ℓ` is smooth over the detector ring. -/
theorem weierstrassModel_smooth (h₅ : 5 ≤ ell) (W₀ : WeierstrassCurve ℤ)
    (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) :
    Smooth (ModelNeron.weierstrassModel ell (W₀.map (algebraMap ℤ (LocalIntegers ell)))).hom := by
  have := ModelNeron.isElliptic_at_detector ell W₀ hΔ
  obtain ⟨c, hc⟩ := exists_shear ell Fact.out h₅ W₀.a₂ W₀.a₄ W₀.a₆
  let u : (integerPrimeIdeal ell).primeCompl :=
    ⟨c ^ 3 + W₀.a₂ * c ^ 2 + W₀.a₄ * c + W₀.a₆, by
      simpa [integerPrimeIdeal, Ideal.mem_span_singleton] using hc⟩
  have hu := IsLocalization.map_units (LocalIntegers ell) u
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine smooth_projStructure (W₀.map (algebraMap ℤ (LocalIntegers ell)))
    (c := algebraMap ℤ _ c) (w := -v) ?_
  simp only [map_a₂, map_a₄, map_a₆]
  rw [neg_mul, mul_comm, ← neg_neg (1 : LocalIntegers ell)]
  congr 1
  rw [← hv]
  simp [u, map_add, map_mul, map_pow]

#print axioms coord_zero_cube
#print axioms iSup_basicOpen_YZ
#print axioms smooth_chart_iff
#print axioms smooth_projStructure
#print axioms exists_shear
#print axioms weierstrassModel_smooth

end ZInQ.Manuscript.RC.ModelTarget
