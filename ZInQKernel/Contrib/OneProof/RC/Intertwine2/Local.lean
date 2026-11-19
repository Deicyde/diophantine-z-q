import ZInQKernel.Contrib.OneProof.RC.Intertwine2.Measure

/-! The local inverse generators on rectangular cylinder factors.
Local character orthogonality is the translation calculation in
tex 8646–8657; the finite-support bookkeeping is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Intertwine2

open Intertwine MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators

def localPhase (p : Place) (x : ℚ_[p.val]) : ℂ :=
  rationalPhase (localFraction p x)

private def onePlace (p : Place) (z : ℚ_[p.val]) : RationalFiniteAdeles := by
  classical
  refine RestrictedProduct.mk (Function.update (fun q : Place => (0 : ℚ_[q.val])) p z) ?_
  rw [Filter.eventually_cofinite]
  apply (Set.finite_singleton p).subset
  intro q hq
  by_contra h
  exact hq (by simp [Function.update_of_ne h])

private theorem singlePhase (p : Place) (z : ℚ_[p.val]) :
    finitePhase rationalFiniteModel (onePlace p z) = localPhase p z := by
  classical
  rw [finitePhase_local_product _ {p} (by
    intro q h
    have hqp : q ≠ p := by simpa using h
    change Function.update (fun q : Place => (0 : ℚ_[q.val])) p z q ∈ PadicInt.subring q.val
    simp [Function.update_of_ne hqp])]
  simp [localPhase, onePlace]

theorem localPhase_add (p : Place) (x y : ℚ_[p.val]) :
    localPhase p (x + y) = localPhase p x * localPhase p y := by
  classical
  have h : onePlace p (x + y) = onePlace p x + onePlace p y := by
    ext q
    change Function.update (fun q : Place => (0 : ℚ_[q.val])) p (x + y) q =
      Function.update (fun q : Place => (0 : ℚ_[q.val])) p x q + Function.update (fun q : Place => (0 : ℚ_[q.val])) p y q
    by_cases hqp : q = p
    · subst q
      simp
    · simp [Function.update_of_ne hqp]
  rw [← singlePhase, h, finitePhase_add, singlePhase, singlePhase]

theorem localPhase_eq_one (p : Place) (z : ℚ_[p.val]) :
    localPhase p z = 1 ↔ z ∈ PadicInt.subring p.val := by
  classical
  rw [← singlePhase, finitePhase_eq_one]
  change (∀ q, Function.update (fun q : Place => (0 : ℚ_[q.val])) p z q ∈ PadicInt.subring q.val) ↔ _
  refine ⟨fun h => by simpa using h p, fun h q => ?_⟩
  by_cases hqp : q = p
  · subst q
    simpa using h
  · simp [Function.update_of_ne hqp]

theorem finitePhase_finprod (z : RationalFiniteAdeles) :
    finitePhase rationalFiniteModel z = ∏ᶠ p, localPhase p (z p) := by
  classical
  have hz : ∀ᶠ p in cofinite, z p ∈ PadicInt.subring p.val := z.2
  rw [Filter.eventually_cofinite] at hz
  have hS : ∀ p, p ∉ hz.toFinset → z p ∈ PadicInt.subring p.val := by
    intro p hp
    by_contra h
    exact hp (hz.mem_toFinset.mpr h)
  rw [finitePhase_local_product _ hz.toFinset hS,
    finprod_eq_prod_of_mulSupport_subset _ (s := hz.toFinset)]
  · rfl
  · intro p hp
    by_contra hn
    exact hp ((localPhase_eq_one p _).2 (hS p hn))

def localDual (a : Fin 3 → ℕ) (p : Place) (y : LocalVectors p) : Prop :=
  ∀ i, ((2 * a i : ℕ) : ℚ_[p.val]) * y i ∈ PadicInt.subring p.val

theorem local_annihilator (a : Fin 3 → ℕ) (p : Place) (y : LocalVectors p) :
    (∀ t ∈ localLattice p, localPhase p (polar a t y) = 1) ↔ localDual a p y := by
  classical
  constructor
  · intro h i
    let t : LocalVectors p := Pi.single i 1
    have ht : t ∈ localLattice p := by
      intro j _
      by_cases hj : j = i <;> simp [t, hj]
    apply (localPhase_eq_one p _).mp
    have he : polar a t y = ((2 * a i : ℕ) : ℚ_[p.val]) * y i := by
      unfold polar
      rw [Finset.sum_eq_single i]
      · simp [t]
      · intro j _ hj
        simp [t, hj]
      · simp
    rw [← he]
    exact h t ht
  · intro h t ht
    apply (localPhase_eq_one p _).mpr
    exact (PadicInt.subring p.val).sum_mem fun i _ => by
      rw [mul_comm _ (t i), mul_assoc]
      exact (PadicInt.subring p.val).mul_mem (ht i (mem_univ i)) (h i)

def localCoset (p : Place) (c : LocalVectors p) : LocalVectors p → ℂ :=
  fun x => ({x | x - c ∈ localLattice p} : Set (LocalVectors p)).indicator (fun _ => 1) x

def localUpper (a : Fin 3 → ℕ) (p : Place) (n : ℤ)
    (f : LocalVectors p → ℂ) (x : LocalVectors p) : ℂ :=
  localPhase p (-(n : ℚ_[p.val]) * quad a x) * f x

def localFourier (a : Fin 3 → ℕ) (p : Place)
    (f : LocalVectors p → ℂ) (y : LocalVectors p) : ℂ :=
  ∫ x, f x * localPhase p (polar a x y) ∂localHaar a p

open Classical in
/-- The local integral on a translated lattice, including its value off the dual. -/
theorem localFourier_coset (a : Fin 3 → ℕ) (p : Place) (c y : LocalVectors p) :
    localFourier a p (localCoset p c) y =
      if localDual a p y then
        localPhase p (polar a c y) * (Real.sqrt (localNorm (determinant a) p) : ℂ)
      else 0 := by
  classical
  let f : LocalVectors p → ℂ := (localLattice p).indicator (fun x => localPhase p (polar a x y))
  have hshift : localFourier a p (localCoset p c) y =
      localPhase p (polar a c y) * ∫ x, f x ∂localHaar a p := by
    unfold localFourier
    rw [← integral_add_left_eq_self (μ := localHaar a p)
        (fun x => localCoset p c x * localPhase p (polar a x y)) c, ← integral_const_mul]
    congr 1
    funext x
    by_cases hx : x ∈ localLattice p <;>
      simp [localCoset, f, hx, polar_add, localPhase_add]
  rw [hshift]
  by_cases hy : localDual a p y
  · rw [ite_eq_left hy]
    have hf : f = (localLattice p).indicator (fun _ => 1) := by
      funext x
      by_cases hx : x ∈ localLattice p <;> simp [f, hx, (local_annihilator a p y).2 hy]
    rw [hf, integral_indicator_const _ (localLattice_open p).measurableSet,
      RCLike.real_smul_eq_coe_mul, mul_one, measureReal_def, localHaar_volume,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    rfl
  · have hn := mt (local_annihilator a p y).1 hy
    push Not at hn
    obtain ⟨t, ht, ht'⟩ := hn
    have hl : localLattice p = (lattice (PadicInt.subring p.val) : Set (LocalVectors p)) := by
      ext x
      simp only [localLattice, Set.mem_pi, Set.mem_univ, forall_const]
      rfl
    have hmem (x : LocalVectors p) : x + t ∈ localLattice p ↔ x ∈ localLattice p := by
      rw [hl]
      rw [hl] at ht
      exact (lattice _).add_mem_cancel_right ht
    have htrans (x : LocalVectors p) : f (t + x) = localPhase p (polar a t y) * f x := by
      have he : t + x ∈ localLattice p ↔ x ∈ localLattice p := by rw [add_comm, hmem]
      by_cases hx : x ∈ localLattice p <;> simp [f, hx, he, polar_add, localPhase_add]
    have h := integral_add_left_eq_self (μ := localHaar a p) f t
    simp_rw [htrans, integral_const_mul] at h
    have hz : (∫ x, f x ∂localHaar a p) = 0 := by
      by_contra hc
      exact ht' (mul_right_cancel₀ hc (h.trans (one_mul _).symm))
    rw [ite_eq_right hy, hz, mul_zero]

#print axioms singlePhase
#print axioms localPhase_add
#print axioms localPhase_eq_one
#print axioms finitePhase_finprod
#print axioms local_annihilator
#print axioms localFourier_coset

end ZInQ.Manuscript.RC.Intertwine2
