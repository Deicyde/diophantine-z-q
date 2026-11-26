import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! The standard affine charts of the projective Weierstrass cubic over any
commutative ring. For a coordinate `Xᵢ`, the degree-zero localization
`R[X,Y,Z]/(F)_(Xᵢ)` is generated over `R` by the ratios `Xⱼ/Xᵢ`. A dehomogenization
`φ` with `φ(Xᵢ) = 1` and a map `ψ` back sending `φ(Xⱼ)` to `Xⱼ/Xᵢ` identify the chart
with any presentation of the affine piece. The chart algebra is standard
(Silverman, *The Arithmetic of Elliptic Curves*, 2009, III.1, UNVERIFIED); the
formal identifications here are on the spot (c). -/

noncomputable section

open WeierstrassCurve HomogeneousLocalization MvPolynomial

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.ModelTarget

private theorem eval₂_smul_of_isHomogeneous {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (g : R →+* S) {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) (c : S) (v : σ → S) :
    eval₂ g (fun i => c * v i) p = c ^ n * eval₂ g v p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [eval₂_sum, eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [eval₂_monomial, eval₂_monomial]
  have hdeg : d.sum (fun _ e => e) = n := by
    have := hp (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply] using this
  have hc : (d.prod fun _ e => c ^ e) = c ^ n := by
    rw [← hdeg, Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum]
  simp only [mul_pow, Finsupp.prod_mul, hc]
  ring

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- The standard affine chart `D₊(Xᵢ)` of the projective cubic, as a ring. -/
abbrev Chart (i : Fin 3) : Type :=
  Away W.toProjective.grading (W.toProjective.coord i)

theorem coord_mem_one (j : Fin 3) : W.toProjective.coord j ∈ W.toProjective.grading (1 • 1) := by
  simpa using W.toProjective.coord_mem_grading j

/-- The base ring acting on a chart through the degree-zero part. -/
def chartConst (i : Fin 3) : R →+* Chart W i :=
  (fromZeroRingHom W.toProjective.grading _).comp
    W.toProjective.gradingZeroEquiv.toRingEquiv.toRingHom

/-- The ratio `Xⱼ/Xᵢ` in the chart `D₊(Xᵢ)`. -/
def ratio (i j : Fin 3) : Chart W i :=
  Away.mk _ (W.toProjective.coord_mem_grading i) 1 (W.toProjective.coord j) (coord_mem_one W j)

private abbrev ChartLoc (i : Fin 3) := Localization.Away (W.toProjective.coord i)

private def denUnit (i : Fin 3) : (ChartLoc W i)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := ChartLoc W i) (W.toProjective.coord i)).unit

private theorem denUnit_val (i : Fin 3) :
    (denUnit W i : ChartLoc W i) = algebraMap _ _ (W.toProjective.coord i) :=
  IsUnit.unit_spec _

private theorem mk_val (i : Fin 3) (n : ℕ) (a : W.toProjective.CoordinateRing)
    (ha : a ∈ W.toProjective.grading (n • (1 : ℕ))) :
    (Away.mk _ (W.toProjective.coord_mem_grading i) n a ha).val =
      ((denUnit W i)⁻¹ : (ChartLoc W i)ˣ).val ^ n * algebraMap _ _ a := by
  rw [Away.val_mk, Localization.mk_eq_mk']
  apply (IsLocalization.mk'_eq_iff_eq_mul (S := ChartLoc W i)).2
  change algebraMap _ _ a = _ * algebraMap _ _ (W.toProjective.coord i ^ n)
  rw [map_pow, ← denUnit_val W i, mul_comm (_ ^ n * _), ← mul_assoc,
    ← mul_pow, Units.mul_inv, one_pow, one_mul]

private theorem ratio_val (i j : Fin 3) :
    (ratio W i j).val = ((denUnit W i)⁻¹ : (ChartLoc W i)ˣ).val *
      algebraMap _ _ (W.toProjective.coord j) := by
  simpa only [ratio, pow_one] using mk_val W i 1 (W.toProjective.coord j) (coord_mem_one W j)

private theorem chartConst_val (i : Fin 3) (r : R) :
    (chartConst W i r).val = algebraMap R (ChartLoc W i) r := by
  change algebraMap W.toProjective.CoordinateRing (ChartLoc W i)
    ((W.toProjective.gradingZeroEquiv r : W.toProjective.grading 0) :
      W.toProjective.CoordinateRing) = _
  rw [W.toProjective.gradingZeroEquiv_apply]
  rfl

theorem ratio_self (i : Fin 3) : ratio W i i = 1 := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (W.toProjective.coord i))
  rw [ratio_val, ← denUnit_val W i, Units.inv_mul, HomogeneousLocalization.val_one]

/-- Dehomogenizing a form of degree `n` gives its fraction over `Xᵢⁿ`. -/
theorem dehomogenize (i : Fin 3) {n : ℕ} (p : MvPolynomial (Fin 3) R) (hp : p.IsHomogeneous n) :
    eval₂ (chartConst W i) (ratio W i) p =
      Away.mk _ (W.toProjective.coord_mem_grading i) n (Ideal.Quotient.mk _ p)
        (by simpa using W.toProjective.mk_mem_grading hp) := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (W.toProjective.coord i))
  change algebraMap (Chart W i) (ChartLoc W i) _ = _
  rw [eval₂_comp_left, mk_val]
  have hc : (algebraMap (Chart W i) (ChartLoc W i)).comp (chartConst W i) =
      algebraMap R (ChartLoc W i) := RingHom.ext (chartConst_val W i)
  have hv : (algebraMap (Chart W i) (ChartLoc W i) ∘ ratio W i) = fun j =>
      ((denUnit W i)⁻¹ : (ChartLoc W i)ˣ).val *
        algebraMap W.toProjective.CoordinateRing (ChartLoc W i) (W.toProjective.coord j) :=
    funext (ratio_val W i)
  rw [hc, hv, eval₂_smul_of_isHomogeneous _ hp]
  congr 1
  rw [show (Ideal.Quotient.mk _ p : W.toProjective.CoordinateRing) =
      eval₂ (algebraMap R _) W.toProjective.coord p from ?_]
  · rw [eval₂_comp_left, IsScalarTower.algebraMap_eq R W.toProjective.CoordinateRing (ChartLoc W i)]
    rfl
  · rw [← MvPolynomial.coe_eval₂Hom]
    change (Ideal.Quotient.mk _).comp (RingHom.id _) p = _
    congr 1
    exact MvPolynomial.ringHom_ext (fun r => by simp only [RingHom.comp_apply, RingHom.id_apply, coe_eval₂Hom, eval₂_C]; rw [← MvPolynomial.algebraMap_eq]; exact Ideal.Quotient.mk_algebraMap _ _ _) (fun j => by simp)

/-- The chart equation: the ratios satisfy the projective equation. -/
theorem chart_equation (i : Fin 3) :
    eval₂ (chartConst W i) (ratio W i) W.toProjective.polynomial = 0 := by
  rw [dehomogenize W i _ W.toProjective.isHomogeneous_polynomial]
  apply HomogeneousLocalization.val_injective (Submonoid.powers (W.toProjective.coord i))
  rw [mk_val, Ideal.Quotient.mk_singleton_self, map_zero, mul_zero,
    HomogeneousLocalization.val_zero]

/-- Ring maps out of a chart agree when they agree on the base ring and on the ratios. -/
theorem chart_ringHom_ext (i : Fin 3) {S : Type*} [CommRing S] {f g : Chart W i →+* S}
    (h₁ : f.comp (chartConst W i) = g.comp (chartConst W i))
    (h₂ : ∀ j, f (ratio W i j) = g (ratio W i j)) : f = g := by
  ext a : 1
  obtain ⟨n, a, ha, rfl⟩ :=
    Away.mk_surjective W.toProjective.grading (W.toProjective.coord_mem_grading i) a
  obtain ⟨p, hp, rfl⟩ := W.toProjective.mem_grading_iff.mp
    (show a ∈ W.toProjective.grading n by simpa using ha)
  rw [← dehomogenize W i p hp, eval₂_comp_left, eval₂_comp_left, h₁,
    show f ∘ ratio W i = g ∘ ratio W i from funext h₂]

variable {W}

/-- A dehomogenization `φ` with `φ(Xᵢ) = 1` factors through the chart. -/
def chartLift (i : Fin 3) {B : Type*} [CommRing B] (φ : W.toProjective.CoordinateRing →+* B)
    (hφ : φ (W.toProjective.coord i) = 1) : Chart W i →+* B :=
  (IsLocalization.Away.lift (S := ChartLoc W i) (W.toProjective.coord i)
    (g := φ) (by rw [hφ]; exact isUnit_one)).comp (algebraMap _ _)

theorem chartLift_mk (i : Fin 3) {B : Type*} [CommRing B]
    (φ : W.toProjective.CoordinateRing →+* B) (hφ : φ (W.toProjective.coord i) = 1)
    (n : ℕ) (a : W.toProjective.CoordinateRing) (ha : a ∈ W.toProjective.grading (n • (1 : ℕ))) :
    chartLift i φ hφ (Away.mk _ (W.toProjective.coord_mem_grading i) n a ha) = φ a := by
  have h1 : IsLocalization.Away.lift (S := ChartLoc W i) (W.toProjective.coord i)
      (g := φ) (by rw [hφ]; exact isUnit_one) (denUnit W i : ChartLoc W i) = 1 := by
    rw [denUnit_val, IsLocalization.Away.lift_eq, hφ]
  have h2 : IsLocalization.Away.lift (S := ChartLoc W i) (W.toProjective.coord i)
      (g := φ) (by rw [hφ]; exact isUnit_one) (((denUnit W i)⁻¹ : (ChartLoc W i)ˣ) : _) = 1 := by
    have := congrArg (IsLocalization.Away.lift (S := ChartLoc W i) (W.toProjective.coord i)
      (g := φ) (by rw [hφ]; exact isUnit_one)) (Units.inv_mul (denUnit W i))
    rwa [map_mul, h1, mul_one, map_one] at this
  simp only [chartLift, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, mk_val,
    map_mul, IsLocalization.Away.lift_eq]
  rw [map_pow, h2, one_pow, one_mul]

theorem chartLift_ratio (i j : Fin 3) {B : Type*} [CommRing B]
    (φ : W.toProjective.CoordinateRing →+* B) (hφ : φ (W.toProjective.coord i) = 1) :
    chartLift i φ hφ (ratio W i j) = φ (W.toProjective.coord j) :=
  chartLift_mk i φ hφ 1 _ _

theorem chartLift_const (i : Fin 3) {B : Type*} [CommRing B]
    (φ : W.toProjective.CoordinateRing →+* B) (hφ : φ (W.toProjective.coord i) = 1) (r : R) :
    chartLift i φ hφ (chartConst W i r) = φ (algebraMap R _ r) := by
  simp only [chartLift, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    chartConst_val, IsScalarTower.algebraMap_apply R W.toProjective.CoordinateRing (ChartLoc W i),
    IsLocalization.Away.lift_eq]

/-- A presentation of the affine piece: a dehomogenization `φ` and a map `ψ` back to
the chart sending the image of each coordinate to its ratio and inverting `φ` on
the presentation identify the presentation with the chart. -/
def chartEquiv (i : Fin 3) {B : Type*} [CommRing B]
    (φ : W.toProjective.CoordinateRing →+* B) (hφ : φ (W.toProjective.coord i) = 1)
    (ψ : B →+* Chart W i)
    (hconst : ∀ r, ψ (φ (algebraMap R _ r)) = chartConst W i r)
    (hcoord : ∀ j, ψ (φ (W.toProjective.coord j)) = ratio W i j)
    (hinv : (chartLift i φ hφ).comp ψ = RingHom.id B) : B ≃+* Chart W i :=
  RingEquiv.ofRingHom ψ (chartLift i φ hφ) (by
    apply chart_ringHom_ext W i
    · ext r
      simp [chartLift_const, hconst]
    · intro j
      simp [chartLift_ratio, hcoord]) hinv

theorem chartEquiv_apply (i : Fin 3) {B : Type*} [CommRing B]
    (φ : W.toProjective.CoordinateRing →+* B) (hφ : φ (W.toProjective.coord i) = 1)
    (ψ : B →+* Chart W i) (hconst hcoord hinv) (b : B) :
    chartEquiv i φ hφ ψ hconst hcoord hinv b = ψ b := rfl

#print axioms dehomogenize
#print axioms chart_equation
#print axioms chart_ringHom_ext
#print axioms chartLift_mk
#print axioms chartEquiv

end ZInQ.Manuscript.RC.ModelTarget
