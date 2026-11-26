import ZInQKernel.Contrib.OneProof.RC.ModelTarget.WeierstrassSmooth

/-! Morphisms from affine schemes to the projective Weierstrass cubic over a base ring,
given by solution vectors with a unit coordinate. Changing the unit coordinate or
scaling the vector by a unit does not change the morphism, and every morphism of
base schemes from an affine scheme into a standard chart is of this form. These
generalize the rational chart calculus of `J0Cusps` to any base. On the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve HomogeneousLocalization

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.ModelTarget

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- The inclusion of the chart `D₊(Xᵢ)`. -/
abbrev chartι (i : Fin 3) : Spec (.of (Chart W i)) ⟶ Proj W.toProjective.grading :=
  Proj.awayι _ _ (W.toProjective.coord_mem_grading i) zero_lt_one

/-- Evaluate a degree-zero fraction with denominator a power of `f` at a ring map that
inverts `f`. -/
def evalAway (f : W.toProjective.CoordinateRing) {A : Type} [CommRing A]
    (k : W.toProjective.CoordinateRing →+* A) (hk : IsUnit (k f)) :
    Away W.toProjective.grading f →+* A :=
  (IsLocalization.Away.lift (S := Localization.Away f) f hk).comp (algebraMap _ _)

theorem evalAway_fraction (f : W.toProjective.CoordinateRing) {A : Type} [CommRing A]
    (k : W.toProjective.CoordinateRing →+* A) (hk : IsUnit (k f))
    {d : ℕ} (hf : f ∈ W.toProjective.grading d)
    (n : ℕ) (a : W.toProjective.CoordinateRing) (ha : a ∈ W.toProjective.grading (n • d)) :
    k f ^ n * evalAway W f k hk (Away.mk _ hf n a ha) = k a := by
  simp only [evalAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  rw [Localization.mk_eq_mk']
  let t : Submonoid.powers f := ⟨f ^ n, ⟨n, rfl⟩⟩
  let hu (y : Submonoid.powers f) : IsUnit (k y) := by
    obtain ⟨m, hm⟩ := y.2
    rw [← hm, map_pow]
    exact hk.pow m
  let z := (IsLocalization.lift (S := Localization.Away f) hu)
    (IsLocalization.mk' (Localization.Away f) a t)
  change k f ^ n * z = _
  have he := (IsLocalization.lift_mk'_spec (S := Localization.Away f) hu a z t).mp rfl
  simpa [t] using he.symm

theorem evalAway_algebraMap (f : W.toProjective.CoordinateRing) {A : Type} [CommRing A]
    (k : W.toProjective.CoordinateRing →+* A) (hk : IsUnit (k f)) (a : W.toProjective.grading 0) :
    evalAway W f k hk (fromZeroRingHom _ _ a) = k a := by
  change IsLocalization.Away.lift (S := Localization.Away f) f hk
    (Localization.mk (a : W.toProjective.CoordinateRing) 1) = k a
  rw [Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift_eq]

variable {A : Type} [CommRing A] (g : R →+* A)

/-- A solution vector with a unit coordinate gives a ring map out of its chart. -/
def chartEval (v : Fin 3 → A) (hv : (W.toProjective.map g).Equation v) (i : Fin 3)
    (hi : IsUnit (v i)) : Chart W i →+* A :=
  evalAway W (W.toProjective.coord i) (W.toProjective.evalHom g hv) (by
    rwa [show W.toProjective.evalHom g hv (W.toProjective.coord i) = v i from
      congrFun (W.toProjective.evalHom_comp_coord g hv) i])

theorem chartEval_ratio (v : Fin 3 → A) (hv : (W.toProjective.map g).Equation v) (i : Fin 3)
    (hi : IsUnit (v i)) (j : Fin 3) : v i * chartEval W g v hv i hi (ratio W i j) = v j := by
  have h (k : Fin 3) : W.toProjective.evalHom g hv (W.toProjective.coord k) = v k :=
    congrFun (W.toProjective.evalHom_comp_coord g hv) k
  have he := evalAway_fraction W (W.toProjective.coord i) (W.toProjective.evalHom g hv)
    (by rwa [h]) (W.toProjective.coord_mem_grading i) 1 (W.toProjective.coord j) (coord_mem_one W j)
  simp only [h, pow_one] at he
  exact he

theorem chartEval_const (v : Fin 3 → A) (hv : (W.toProjective.map g).Equation v) (i : Fin 3)
    (hi : IsUnit (v i)) (r : R) : chartEval W g v hv i hi (chartConst W i r) = g r := by
  simp only [chartEval, chartConst, RingHom.comp_apply]
  rw [evalAway_algebraMap]
  rw [show ((W.toProjective.gradingZeroEquiv.toRingEquiv.toRingHom r : W.toProjective.grading 0) :
      W.toProjective.CoordinateRing) = algebraMap R _ r from by
    simp [W.toProjective.gradingZeroEquiv_apply]]
  exact RingHom.congr_fun (W.toProjective.evalHom_comp_algebraMap g hv) r

/-- The morphism to the projective cubic given by a solution vector with a unit coordinate. -/
def chartMorphism (v : Fin 3 → A) (hv : (W.toProjective.map g).Equation v) (i : Fin 3)
    (hi : IsUnit (v i)) : Spec (.of A) ⟶ Proj W.toProjective.grading :=
  Spec.map (CommRingCat.ofHom (chartEval W g v hv i hi)) ≫ chartι W i

theorem chartι_structure (i : Fin 3) :
    chartι W i ≫ projStructure W = Spec.map (CommRingCat.ofHom (chartConst W i)) := by
  rw [projStructure, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

theorem chartMorphism_structure (v : Fin 3 → A) (hv : (W.toProjective.map g).Equation v)
    (i : Fin 3) (hi : IsUnit (v i)) :
    chartMorphism W g v hv i hi ≫ projStructure W = Spec.map (CommRingCat.ofHom g) := by
  rw [chartMorphism, Category.assoc, chartι_structure, ← Spec.map_comp]
  congr 2
  ext r
  exact chartEval_const W g v hv i hi r

/-- Ring maps out of a chart into a ring are determined by the constants and ratios. -/
theorem chartEval_eq_of (v : Fin 3 → A) (hv : (W.toProjective.map g).Equation v) (i : Fin 3)
    (hi : IsUnit (v i)) (f : Chart W i →+* A) (hc : f.comp (chartConst W i) = g)
    (hr : ∀ j, v i * f (ratio W i j) = v j) : f = chartEval W g v hv i hi := by
  apply chart_ringHom_ext W i
  · rw [hc]
    exact (RingHom.ext (chartEval_const W g v hv i hi)).symm
  · intro j
    apply hi.mul_left_cancel
    rw [hr, chartEval_ratio]

theorem chartMorphism_smul (v : Fin 3 → A) (hv : (W.toProjective.map g).Equation v)
    (i : Fin 3) (hi : IsUnit (v i)) (u : A) (hu : IsUnit u)
    (hv' : (W.toProjective.map g).Equation (u • v)) (hi' : IsUnit ((u • v) i)) :
    chartMorphism W g (u • v) hv' i hi' = chartMorphism W g v hv i hi := by
  unfold chartMorphism
  congr 3
  symm
  apply chartEval_eq_of
  · exact RingHom.ext (chartEval_const W g v hv i hi)
  · intro j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_assoc, chartEval_ratio]

theorem chartMorphism_map {B : Type} [CommRing B] (φ : A →+* B) (v : Fin 3 → A)
    (hv : (W.toProjective.map g).Equation v) (i : Fin 3) (hi : IsUnit (v i))
    (hw : (W.toProjective.map (φ.comp g)).Equation (φ ∘ v)) :
    Spec.map (CommRingCat.ofHom φ) ≫ chartMorphism W g v hv i hi =
      chartMorphism W (φ.comp g) (φ ∘ v) hw i (hi.map φ) := by
  unfold chartMorphism
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine congrArg CommRingCat.ofHom ?_
  apply chartEval_eq_of
  · ext r
    simp [chartEval_const]
  · intro j
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
    rw [← map_mul, chartEval_ratio]

private theorem evalAway_overlap {f h : W.toProjective.CoordinateRing}
    (hf : f ∈ W.toProjective.grading (1 : ℕ)) (hh : h ∈ W.toProjective.grading (1 : ℕ))
    (k : W.toProjective.CoordinateRing →+* A) (hf' : IsUnit (k f)) (hh' : IsUnit (k h))
    {w : W.toProjective.CoordinateRing} (hw : w = f * h) :
    (evalAway W w k (by rw [hw, map_mul]; exact hf'.mul hh')).comp
        (awayMap W.toProjective.grading hh hw) = evalAway W f k hf' := by
  ext s : 1
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective W.toProjective.grading hf s
  simp only [RingHom.comp_apply, awayMap_mk]
  apply ((hf'.pow n).mul (hh'.pow n)).mul_left_cancel
  calc
    _ = k (a * h ^ n) := by
      simpa only [hw, map_mul, mul_pow] using
        evalAway_fraction W w k _ (hw ▸ SetLike.mul_mem_graded hf hh) n (a * h ^ n) _
    _ = _ := by
      rw [map_mul, map_pow, mul_comm (k f ^ n), mul_assoc, evalAway_fraction]
      ac_rfl

/-- Changing the unit coordinate gives the same morphism. -/
theorem chartMorphism_independent (v : Fin 3 → A) (hv : (W.toProjective.map g).Equation v)
    (i j : Fin 3) (hi : IsUnit (v i)) (hj : IsUnit (v j)) :
    chartMorphism W g v hv i hi = chartMorphism W g v hv j hj := by
  let k := W.toProjective.evalHom g hv
  have hk (l : Fin 3) : k (W.toProjective.coord l) = v l :=
    congrFun (W.toProjective.evalHom_comp_coord g hv) l
  have hi' : IsUnit (k (W.toProjective.coord i)) := by rwa [hk]
  have hj' : IsUnit (k (W.toProjective.coord j)) := by rwa [hk]
  have ei := evalAway_overlap W (W.toProjective.coord_mem_grading i)
    (W.toProjective.coord_mem_grading j) k hi' hj' rfl
  have ej := evalAway_overlap W (W.toProjective.coord_mem_grading j)
    (W.toProjective.coord_mem_grading i) k hj' hi' (mul_comm _ _)
  change Spec.map (CommRingCat.ofHom (evalAway W _ k hi')) ≫ chartι W i =
    Spec.map (CommRingCat.ofHom (evalAway W _ k hj')) ≫ chartι W j
  rw [← ei, ← ej]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

/-- A morphism of base schemes from an affine scheme into a chart is a chart morphism. -/
theorem eq_chartMorphism (i : Fin 3) (p : Spec (.of A) ⟶ Proj W.toProjective.grading)
    (f : Chart W i →+* A) (hp : p = Spec.map (CommRingCat.ofHom f) ≫ chartι W i)
    (hs : p ≫ projStructure W = Spec.map (CommRingCat.ofHom g)) :
    ∃ (hv : (W.toProjective.map g).Equation (f ∘ ratio W i)) (hi : IsUnit ((f ∘ ratio W i) i)),
      p = chartMorphism W g (f ∘ ratio W i) hv i hi := by
  have hc : f.comp (chartConst W i) = g := by
    rw [hp, Category.assoc, chartι_structure, ← Spec.map_comp] at hs
    have := Spec.map_injective hs
    exact congrArg CommRingCat.Hom.hom this
  have hv : (W.toProjective.map g).Equation (f ∘ ratio W i) := by
    have h := congrArg f (chart_equation W i)
    rw [map_zero, ← MvPolynomial.coe_eval₂Hom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom,
      MvPolynomial.coe_eval₂Hom, hc] at h
    rw [Projective.Equation, Projective.map_polynomial, MvPolynomial.eval_map]
    exact h
  have hi : IsUnit ((f ∘ ratio W i) i) := by simp [ratio_self]
  refine ⟨hv, hi, ?_⟩
  rw [hp, chartMorphism]
  congr 3
  apply chartEval_eq_of W g _ hv i hi f hc
  intro j
  simp [ratio_self]

#print axioms chartEval_ratio
#print axioms chartMorphism_structure
#print axioms chartMorphism_smul
#print axioms chartMorphism_map
#print axioms chartMorphism_independent
#print axioms eq_chartMorphism

end ZInQ.Manuscript.RC.ModelTarget
