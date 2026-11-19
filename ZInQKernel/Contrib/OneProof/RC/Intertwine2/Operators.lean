import ZInQKernel.Contrib.OneProof.RC.Intertwine2.Local

/-! The tensor product formulas on the rectangular class-function basis
(tex 8729–8744, 9000–9007). Reducing the restricted product to these
cylinders and extending linearly is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Intertwine2

open Intertwine OldStageLaw MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators

private theorem atPlace_quad (p : Place) (a : Fin 3 → ℕ) (x : FiniteVectors) (n : ℤ) :
    (-(n : RationalFiniteAdeles) * quad a x) p = -(n : ℚ_[p.val]) * quad a (atPlace p x) := by
  let ev : RationalFiniteAdeles →+* ℚ_[p.val] :=
    RestrictedProduct.evalRingHom (fun t : Place => ℚ_[t.val]) p
  change ev (-(n : RationalFiniteAdeles) * quad a x) = _
  simp only [quad, map_mul, map_neg, map_intCast, _root_.map_sum, map_natCast, map_pow]
  rfl

private theorem atPlace_polar (p : Place) (a : Fin 3 → ℕ) (x y : FiniteVectors) :
    polar a x y p = polar a (atPlace p x) (atPlace p y) := by
  let ev : RationalFiniteAdeles →+* ℚ_[p.val] :=
    RestrictedProduct.evalRingHom (fun t : Place => ℚ_[t.val]) p
  change ev (polar a x y) = _
  simp only [polar, _root_.map_sum, map_mul, map_natCast]
  rfl

private theorem eventually_localLattice (x : FiniteVectors) :
    ∀ᶠ p in cofinite, atPlace p x ∈ localLattice p := by
  exact (Filter.eventually_all.mpr fun i : Fin 3 => (x i).2).mono
    fun _ hp i _ => hp i

private theorem phase_finite (z : RationalFiniteAdeles) :
    (fun p => localPhase p (z p)).HasFiniteMulSupport :=
  Filter.eventually_cofinite.mp ((show ∀ᶠ p in cofinite, z p ∈ PadicInt.subring p.val from z.2).mono
    fun p hp => (localPhase_eq_one p _).2 hp)

open Classical in
private theorem finprod_indicator {P : Place → Prop}
    (hP : ∀ᶠ p in cofinite, P p) :
    (∏ᶠ p, if P p then (1 : ℂ) else 0) = if ∀ p, P p then 1 else 0 := by
  have hfin : (fun p => if P p then (1 : ℂ) else 0).HasFiniteMulSupport :=
    Filter.eventually_cofinite.mp (hP.mono fun p hp => ite_eq_left hp)
  split_ifs with h
  · exact finprod_eq_one_of_forall_eq_one (fun p => ite_eq_left (h p))
  · push Not at h
    obtain ⟨p, hp⟩ := h
    exact finprod_eq_zero _ p (ite_eq_right hp) hfin

variable {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]

/-- The zero extension of an elementary class function. -/
def cosetIndicator (r : Grid a) : FiniteVectors → ℂ :=
  (coset (I₀ := integralAdeles) r).indicator (fun _ => 1)

omit [∀ i, NeZero (2 * a i)] in
private theorem coset_finSupport (r : Grid a) (x : FiniteVectors) :
    (fun p => localCoset p (atPlace p (center r)) (atPlace p x)).HasFiniteMulSupport :=
  Filter.eventually_cofinite.mp ((eventually_localLattice (x - center r)).mono fun p hp => by
    simp [localCoset, show atPlace p x - atPlace p (center r) ∈ localLattice p from hp])

omit [∀ i, NeZero (2 * a i)] in
theorem cosetIndicator_tensor (r : Grid a) (x : FiniteVectors) :
    cosetIndicator r x = ∏ᶠ p, localCoset p (atPlace p (center r)) (atPlace p x) := by
  classical
  let P : Place → Prop := fun p => atPlace p (x - center r) ∈ localLattice p
  have hf : (∏ᶠ p, localCoset p (atPlace p (center r)) (atPlace p x)) =
      if ∀ p, P p then 1 else 0 :=
    finprod_indicator (P := P) (eventually_localLattice (x - center r))
  rw [hf]
  by_cases hx : x - center r ∈ lattice integralAdeles
  · have hl : ∀ p, P p := (rectangular_iff_local _).1 hx
    rw [ite_eq_left hl]
    simp [cosetIndicator, coset, hx]
  · have hl : ¬ ∀ p, P p := mt (rectangular_iff_local _).2 hx
    rw [ite_eq_right hl]
    simp [cosetIndicator, coset, hx]

/-- The inverse upper operator, multiplied place by place. -/
def upper (a : Fin 3 → ℕ) (n : ℤ) (f : FiniteVectors → ℂ) (x : FiniteVectors) : ℂ :=
  (∏ᶠ p, localPhase p ((-(n : RationalFiniteAdeles) * quad a x) p)) * f x

/-- The inverse Weyl operator: self-dual Haar Fourier and the finite index. -/
def weyl (a : Fin 3 → ℕ) (g : ℂˣ) (f : FiniteVectors → ℂ) : FiniteVectors → ℂ :=
  (g : ℂ) • haarFourier (a := a) rationalFiniteModel (nuF a) f

omit [∀ i, NeZero (2 * a i)] in
theorem upper_description (n : ℤ) (f : FiniteVectors → ℂ) (x : FiniteVectors) :
    upper a n f x = finitePhase rationalFiniteModel (-(n : RationalFiniteAdeles) * quad a x) * f x := by
  rw [upper, ← finitePhase_finprod]

omit [∀ i, NeZero (2 * a i)] in
theorem weyl_description (g : ℂˣ) (f : FiniteVectors → ℂ) :
    weyl a g f = (g : ℂ) • haarFourier (a := a) rationalFiniteModel (normalizedHaar a) f := by
  rw [weyl, nuF_eq_normalizedHaar]

omit [∀ i, NeZero (2 * a i)] in
theorem upper_tensor (n : ℤ) (r : Grid a) (x : FiniteVectors) :
    upper a n (cosetIndicator r) x =
      ∏ᶠ p, localUpper a p n (localCoset p (atPlace p (center r))) (atPlace p x) := by
  rw [upper, cosetIndicator_tensor, ← finprod_mul_distrib
    (phase_finite _) (coset_finSupport r x)]
  exact finprod_congr fun p => by rw [atPlace_quad, localUpper]

private def volumeFactor (a : Fin 3 → ℕ) (p : Place) : ℂ :=
  Real.sqrt (localNorm (determinant a) p)

private theorem volume_good {p : Place} (hp : p ∉ badPlaces (determinant a)) :
    volumeFactor a p = 1 := by
  have hd : determinant a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (2 * a i)
  simp [volumeFactor, localNorm_good hd hp]

private theorem volume_support :
    Function.mulSupport (volumeFactor a) ⊆ ↑(badPlaces (determinant a)) :=
  fun _ hp => by by_contra h; exact hp (volume_good h)

private theorem volume_finprod :
    (finiteVolume a : ℂ) = ∏ᶠ p, volumeFactor a p := by
  rw [finprod_eq_prod_of_mulSupport_subset _ volume_support, finiteVolume, Complex.ofReal_prod]
  rfl

private theorem fourier_finite (r : Grid a) (y : FiniteVectors) :
    (fun p => localFourier a p (localCoset p (atPlace p (center r))) (atPlace p y)).HasFiniteMulSupport := by
  have hv : ∀ᶠ p in cofinite, p ∉ badPlaces (determinant a) :=
    Filter.eventually_cofinite.mpr ((badPlaces (determinant a)).finite_toSet.subset fun p hp => by
      change ¬ (p ∉ badPlaces (determinant a)) at hp
      exact Finset.mem_coe.mpr (not_not.mp hp))
  have hφ : ∀ᶠ p in cofinite, polar a (center r) y p ∈ PadicInt.subring p.val :=
    (polar a (center r) y).2
  exact Filter.eventually_cofinite.mp (((eventually_localLattice y).and (hv.and hφ)).mono fun p ⟨hy, hp, hφ⟩ => by
    have hd : localDual a p (atPlace p y) :=
      fun i => (PadicInt.subring p.val).mul_mem (natCast_mem _ _) (hy i (mem_univ i))
    change localFourier a p (localCoset p (atPlace p (center r))) (atPlace p y) = 1
    rw [localFourier_coset, ite_eq_left hd, ← atPlace_polar, (localPhase_eq_one p _).2 hφ, one_mul]
    exact volume_good hp)

private theorem dual_iff_local (y : FiniteVectors) :
    dual integralAdeles a y ↔ ∀ p, localDual a p (atPlace p y) :=
  ((annihilator_iff rationalFiniteModel y).symm.trans (adelic_annihilator_placewise a y))

/-- The adèlic Fourier integral on a basis cylinder is the product of the
actual local Fourier integrals, including zero if any local integral vanishes
off the dual. -/
theorem fourier_tensor (r : Grid a) (y : FiniteVectors) :
    haarFourier (a := a) rationalFiniteModel (nuF a) (cosetIndicator r) y =
      ∏ᶠ p, localFourier a p (localCoset p (atPlace p (center r))) (atPlace p y) := by
  classical
  let : (nuF a).IsAddLeftInvariant := (nuF_eq_normalizedHaar a).symm ▸
    (inferInstance : (normalizedHaar a).IsAddLeftInvariant)
  have he : ∀ x : FiniteVectors, cosetIndicator r x * finitePhase rationalFiniteModel (polar a x y) =
      (coset (I₀ := integralAdeles) r).indicator (fun z => finitePhase rationalFiniteModel (polar a z y)) x := by
    intro x
    by_cases hx : x ∈ coset (I₀ := integralAdeles) r <;> simp [cosetIndicator, hx]
  unfold haarFourier
  simp_rw [he]
  rw [integrate_coset rationalFiniteModel (nuF a), lattice_integral _ _ rectangular_open.measurableSet]
  by_cases hy : dual integralAdeles a y
  · have hv : 0 ≤ finiteVolume a := Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
    rw [ite_eq_left hy, measureReal_def, nuF_volume, ENNReal.toReal_ofReal hv, finitePhase_finprod,
      volume_finprod, ← finprod_mul_distrib (phase_finite _)
        ((badPlaces (determinant a)).finite_toSet.subset volume_support)]
    exact finprod_congr fun p => by
      rw [localFourier_coset, ite_eq_left ((dual_iff_local y).1 hy p), ← atPlace_polar]
      rfl
  · rw [ite_eq_right hy, mul_zero]
    have hn := mt (dual_iff_local y).2 hy
    push Not at hn
    obtain ⟨p, hp⟩ := hn
    have hz : localFourier a p (localCoset p (atPlace p (center r))) (atPlace p y) = 0 := by
      rw [localFourier_coset, ite_eq_right hp]
    exact (finprod_eq_zero _ p hz (fourier_finite r y)).symm

theorem weyl_tensor (γ : Place → ℂˣ) (hγ : γ.HasFiniteMulSupport) (r : Grid a) (y : FiniteVectors) :
    weyl a (∏ᶠ p, γ p) (cosetIndicator r) y =
      ∏ᶠ p, (γ p : ℂ) * localFourier a p (localCoset p (atPlace p (center r))) (atPlace p y) := by
  change ((∏ᶠ p, γ p : ℂˣ) : ℂ) *
    haarFourier (a := a) rationalFiniteModel (nuF a) (cosetIndicator r) y = _
  have hc : (fun p => (γ p : ℂ)).HasFiniteMulSupport :=
    hγ.subset fun p hp h => hp (by simp [h])
  have hmap : ((∏ᶠ p, γ p : ℂˣ) : ℂ) = ∏ᶠ p, (γ p : ℂ) :=
    (Units.coeHom ℂ).map_finprod hγ
  rw [fourier_tensor, hmap, ← finprod_mul_distrib hc (fourier_finite r y)]

#print axioms atPlace_quad
#print axioms atPlace_polar
#print axioms eventually_localLattice
#print axioms phase_finite
#print axioms finprod_indicator
#print axioms coset_finSupport
#print axioms cosetIndicator_tensor
#print axioms upper_description
#print axioms weyl_description
#print axioms upper_tensor
#print axioms volume_good
#print axioms volume_support
#print axioms volume_finprod
#print axioms fourier_finite
#print axioms dual_iff_local
#print axioms fourier_tensor
#print axioms weyl_tensor

end ZInQ.Manuscript.RC.Intertwine2
