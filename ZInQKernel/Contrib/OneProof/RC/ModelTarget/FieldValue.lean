import ZInQKernel.Contrib.OneProof.RC.ModelTarget.ChartMorphism
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Nonsingular

/-! Points of the relative projective cubic with values in a field. A morphism
`Spec F ⟶ Proj` over a ring map `R → F` is a chart morphism of a nonzero solution
vector, unique up to a unit; its value is the affine point of that vector on the base
change. The value determines the morphism. On the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve HomogeneousLocalization
open scoped WeierstrassCurve.Projective

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.ModelTarget

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

theorem coord_mem_iff_chart {F : Type} [Field F] (i j : Fin 3) (f : Chart W i →+* F) :
    W.toProjective.coord j ∈
        ((Spec.map (CommRingCat.ofHom f) ≫ chartι W i) default).asHomogeneousIdeal ↔
      f (ratio W i j) = 0 := by
  let A := W.toProjective.grading
  let c := W.toProjective.coord i
  let d := W.toProjective.coord_mem_grading i
  let b := Proj.basicOpenIsoSpec A c d zero_lt_one
  let x := b.inv (Spec.map (CommRingCat.ofHom f) default)
  have he : (Proj.basicOpenToSpec A c).toLRSHom = ProjectiveSpectrum.Proj.toSpec A c := by
    refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
    dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
    simp only [Category.assoc, ← Spec.map_comp]
    rfl
  have h := ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply A x
    ⟨1 • (1 : ℕ), ⟨W.toProjective.coord j, coord_mem_one W j⟩,
      ⟨c ^ 1, SetLike.pow_mem_graded 1 d⟩, ⟨1, rfl⟩⟩
  rw [← he] at h
  change _ ∈ ((Proj.basicOpenToSpec A c) x).asIdeal ↔ _ at h
  have hx : Proj.basicOpenToSpec A c x = Spec.map (CommRingCat.ofHom f) default := by
    change b.hom (b.inv _) = _
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  rw [hx] at h
  refine h.symm.trans ?_
  change ratio W i j ∈ ((Spec.map (CommRingCat.ofHom f)) default).asIdeal ↔ _
  rw [Spec.map_apply]
  change ratio W i j ∈ (default : Spec (.of F)).asIdeal.comap f ↔ _
  rw [Ideal.mem_comap, Scheme.default_asIdeal, Ideal.mem_bot]

variable {F : Type} [Field F] (g : R →+* F)

/-- Two solution vectors giving the same morphism from the spectrum of a field are
proportional. -/
theorem equiv_of_chartMorphism_eq (v v' : Fin 3 → F) (hv : (W.toProjective.map g).Equation v)
    (hv' : (W.toProjective.map g).Equation v') (i j : Fin 3) (hi : IsUnit (v i))
    (hj : IsUnit (v' j)) (h : chartMorphism W g v hv i hi = chartMorphism W g v' hv' j hj) :
    v ≈ v' := by
  have hvj : v j ≠ 0 := by
    intro h0
    have hmem : W.toProjective.coord j ∈
        ((Spec.map (CommRingCat.ofHom (chartEval W g v hv i hi)) ≫ chartι W i) default).asHomogeneousIdeal := by
      rw [coord_mem_iff_chart]
      have := chartEval_ratio W g v hv i hi j
      rw [h0] at this
      exact (mul_eq_zero.mp this).resolve_left hi.ne_zero
    change W.toProjective.coord j ∈ (chartMorphism W g v hv i hi default).asHomogeneousIdeal at hmem
    rw [h] at hmem
    have hrange : chartMorphism W g v' hv' j hj default ∈
        Proj.basicOpen W.toProjective.grading (W.toProjective.coord j) := by
      rw [← Proj.opensRange_awayι _ _ (W.toProjective.coord_mem_grading j) zero_lt_one]
      exact ⟨_, rfl⟩
    exact (Proj.mem_basicOpen _ _ _).mp hrange hmem
  have hvj' : IsUnit (v j) := isUnit_iff_ne_zero.mpr hvj
  rw [chartMorphism_independent W g v hv i j hi hvj'] at h
  have he : chartEval W g v hv j hvj' = chartEval W g v' hv' j hj := by
    have h2 := (cancel_mono (chartι W j)).mp h
    have h3 := Spec.map_injective h2
    exact congrArg CommRingCat.Hom.hom h3
  refine ⟨(isUnit_iff_ne_zero.mpr (div_ne_zero hvj hj.ne_zero)).unit, ?_⟩
  funext l
  have e1 := chartEval_ratio W g v hv j hvj' l
  have e2 := chartEval_ratio W g v' hv' j hj l
  rw [he] at e1
  simp only [Units.smul_def, IsUnit.unit_spec, Pi.smul_apply, smul_eq_mul]
  rw [← e1, ← e2]
  field_simp [hj.ne_zero]

theorem chartMorphism_eq_of_equiv (v v' : Fin 3 → F) (hv : (W.toProjective.map g).Equation v)
    (hv' : (W.toProjective.map g).Equation v') (i j : Fin 3) (hi : IsUnit (v i))
    (hj : IsUnit (v' j)) (h : v ≈ v') :
    chartMorphism W g v hv i hi = chartMorphism W g v' hv' j hj := by
  obtain ⟨u, hu⟩ := h
  have e : v = (u : F) • v' := hu.symm
  subst e
  rw [chartMorphism_independent W g ((u : F) • v') hv i j hi (by
      change IsUnit ((u : F) * v' j); exact u.isUnit.mul hj)]
  exact chartMorphism_smul W g v' hv' j hj (u : F) u.isUnit _ _

/-- Every morphism from the spectrum of a field over the base is a chart morphism. -/
theorem exists_chartMorphism (p : Spec (.of F) ⟶ Proj W.toProjective.grading)
    (hp : p ≫ projStructure W = Spec.map (CommRingCat.ofHom g)) :
    ∃ (v : Fin 3 → F) (hv : (W.toProjective.map g).Equation v) (i : Fin 3) (hi : IsUnit (v i)),
      p = chartMorphism W g v hv i hi := by
  have htop : p default ∈ (⊤ : (Proj W.toProjective.grading).Opens) := trivial
  rw [← iSup_basicOpen_YZ W, TopologicalSpace.Opens.mem_iSup] at htop
  obtain ⟨k, hk⟩ := htop
  let i : Fin 3 := ![1, 2] k
  have hi : p default ∈ (chartι W i).opensRange := by
    rw [Proj.opensRange_awayι]
    fin_cases k <;> exact hk
  have hsub : Set.range p ⊆ Set.range (chartι W i) := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z default]
    exact hi
  obtain ⟨f, ef⟩ := Spec.map_surjective (IsOpenImmersion.lift (chartι W i) p hsub)
  have hpf : p = Spec.map (CommRingCat.ofHom f.hom) ≫ chartι W i := by
    rw [CommRingCat.ofHom_hom, ef, IsOpenImmersion.lift_fac]
  obtain ⟨hv, hi', e⟩ := eq_chartMorphism W g i p f.hom hpf hp
  exact ⟨_, hv, i, hi', e⟩

/-- The affine point of a field point of the projective cubic. -/
def fieldValue (p : Spec (.of F) ⟶ Proj W.toProjective.grading)
    (hp : p ≫ projStructure W = Spec.map (CommRingCat.ofHom g)) : (W.map g).toAffine.Point :=
  Projective.Point.toAffine (W.toProjective.map g) (exists_chartMorphism W g p hp).choose

theorem fieldValue_eq (p : Spec (.of F) ⟶ Proj W.toProjective.grading)
    (hp : p ≫ projStructure W = Spec.map (CommRingCat.ofHom g)) (v : Fin 3 → F)
    (hv : (W.toProjective.map g).Equation v) (i : Fin 3) (hi : IsUnit (v i))
    (h : p = chartMorphism W g v hv i hi) :
    fieldValue W g p hp = Projective.Point.toAffine (W.toProjective.map g) v := by
  obtain ⟨hv₀, i₀, hi₀, e₀⟩ := (exists_chartMorphism W g p hp).choose_spec
  exact Projective.Point.toAffine_of_equiv
    (equiv_of_chartMorphism_eq W g _ v hv₀ hv i₀ i hi₀ hi (e₀.symm.trans h))

theorem fieldValue_chartMorphism (v : Fin 3 → F) (hv : (W.toProjective.map g).Equation v)
    (i : Fin 3) (hi : IsUnit (v i)) :
    fieldValue W g (chartMorphism W g v hv i hi) (chartMorphism_structure W g v hv i hi) =
      Projective.Point.toAffine (W.toProjective.map g) v :=
  fieldValue_eq W g _ _ v hv i hi rfl

theorem equiv_of_toAffine_eq (W' : WeierstrassCurve.Projective F) {P Q : Fin 3 → F} (hP : W'.Nonsingular P)
    (hQ : W'.Nonsingular Q) (h : Projective.Point.toAffine W' P = Projective.Point.toAffine W' Q) :
    P ≈ Q := by
  classical
  have hinj := (Projective.Point.toAffineAddEquiv (W := W')).injective
    (a₁ := ⟨(Projective.nonsingularLift_iff (W' := W') P).mpr hP⟩)
    (a₂ := ⟨(Projective.nonsingularLift_iff (W' := W') Q).mpr hQ⟩) (by
      exact h)
  exact Quotient.exact (congrArg Projective.Point.point hinj)

/-- The value determines a field point of the projective cubic of an elliptic equation. -/
theorem fieldValue_injective [W.IsElliptic] (p q : Spec (.of F) ⟶ Proj W.toProjective.grading)
    (hp : p ≫ projStructure W = Spec.map (CommRingCat.ofHom g))
    (hq : q ≫ projStructure W = Spec.map (CommRingCat.ofHom g))
    (h : fieldValue W g p hp = fieldValue W g q hq) : p = q := by
  obtain ⟨v, hv, i, hi, rfl⟩ := exists_chartMorphism W g p hp
  obtain ⟨v', hv', j, hj, rfl⟩ := exists_chartMorphism W g q hq
  rw [fieldValue_chartMorphism, fieldValue_chartMorphism] at h
  have hns (w : Fin 3 → F) (hw : (W.toProjective.map g).Equation w) (k : Fin 3) (hk : IsUnit (w k)) :
      (W.toProjective.map g).Nonsingular w := by
    have : (W.toProjective.map g).IsElliptic := inferInstanceAs (W.map g).IsElliptic
    refine (Projective.equation_iff_nonsingular_of_ne_zero (W := W.toProjective.map g) ?_).mp hw
    intro h0
    exact hk.ne_zero (congrFun h0 k)
  exact chartMorphism_eq_of_equiv W g v v' hv hv' i j hi hj
    (equiv_of_toAffine_eq _ (hns v hv i hi) (hns v' hv' j hj) h)

#print axioms coord_mem_iff_chart
#print axioms equiv_of_chartMorphism_eq
#print axioms chartMorphism_eq_of_equiv
#print axioms exists_chartMorphism
#print axioms fieldValue_eq
#print axioms equiv_of_toAffine_eq
#print axioms fieldValue_injective

end ZInQ.Manuscript.RC.ModelTarget
