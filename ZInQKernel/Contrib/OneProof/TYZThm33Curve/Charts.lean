import ZInQKernel.Contrib.OneProof.GrossZagierScheme
import ZInQKernel.Contrib.OneProof.CurveModelUnique
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Prime

/-!
# h33-d1: the projective curve `ESch E = Proj ℚ[X, Y, Z]/(F_E)` as a model of its function field

* `ESch E` is an integral scheme (`isIntegral_ESch`).
* Every point lies in `D₊(Z)` or `D₊(Y)` (`mem_basicOpen_Y_of_not_mem_Z`).
* `A_(Z) ≅ ℚ[x, y]/(W_E)` (`azEquiv`) and `ℚ(ESch E) ≅ ℚ(E)` (`ffEquiv`), compatibly with the chart
  `D₊(Z)` (`kappaZ`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace ZInQ.H33D1

open ZInQ.GZSch

/-! ## §0. Homogeneous polynomials -/

theorem eval₂_mul_homog {R S σ : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (g : σ → S) (c : S) {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    MvPolynomial.eval₂ f (fun i => c * g i) p = c ^ n * MvPolynomial.eval₂ f g p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [MvPolynomial.eval₂_sum, Finset.mul_sum, MvPolynomial.eval₂_monomial]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg := hp (MvPolynomial.mem_support_iff.mp hd)
  have h1 : (d.prod fun i k => (c * g i) ^ k) = c ^ (d.sum fun _ k => k) * d.prod fun i k => g i ^ k := by
    simp only [mul_pow, Finsupp.prod_mul]
    congr 1
    simp only [Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum]
  rw [h1]
  have h2 : (d.sum fun _ k => k) = n := by
    rw [← hdeg]
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [h2]
  ring

/-! ## §1. `ESch E` is integral -/

variable (E : WeierstrassCurve ℚ)

/-- The affine coordinate ring `ℚ[X, Y]/(W_E)`. -/
abbrev CR : Type := E.toAffine.CoordinateRing

abbrev xA : CR E := WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine (Polynomial.C Polynomial.X)
abbrev yA : CR E := WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine Polynomial.X

theorem wEqA_xA_yA : WEqA E (xA E) (yA E) := by
  refine WEqA.of_map (algebraMap (CR E) E.toAffine.FunctionField)
    (IsFractionRing.injective _ _) ?_
  exact wEqA_of_wEqR (ZInQ.GZDict2.wEqR_gen E)

theorem zC_ne_zero : zC E ≠ 0 := by
  intro h
  have := evAB_zC E (xA E) (yA E) (affEq_of_wEqA (wEqA_xA_yA E))
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem zC_mem_irrelevant : zC E ∈ (HomogeneousIdeal.irrelevant (gr E)).toIdeal := by
  rw [HomogeneousIdeal.irrelevant_eq_span]
  exact Ideal.subset_span (Set.mem_iUnion₂.mpr ⟨1, one_pos, zC_mem E⟩)

/-- **The generic point of `ESch E`**: the zero ideal (the coordinate ring is a domain). -/
def eta0 : ProjectiveSpectrum (gr E) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    change (⊥ : Ideal E.toProjective.CoordinateRing).IsPrime
    exact Ideal.isPrime_bot
  not_irrelevant_le := by
    intro h
    have : zC E ∈ (⊥ : Ideal E.toProjective.CoordinateRing) := h (zC_mem_irrelevant E)
    exact zC_ne_zero E (by simpa using this)

instance irreducibleSpace_ESch : IrreducibleSpace (ESch E) := by
  have h : closure ({eta0 E} : Set (ProjectiveSpectrum (gr E))) = Set.univ := by
    ext p
    simp only [Set.mem_univ, iff_true]
    rw [← ProjectiveSpectrum.le_iff_mem_closure]
    change (⊥ : HomogeneousIdeal (gr E)) ≤ p.asHomogeneousIdeal
    exact bot_le
  rw [irreducibleSpace_def]
  have := (isIrreducible_singleton (x := eta0 E)).closure
  rw [h] at this
  exact this

instance isReduced_stalk_ESch (x : ESch E) : _root_.IsReduced ((ESch E).presheaf.stalk x) := by
  haveI : _root_.IsReduced (AtPrime (gr E) x.asHomogeneousIdeal.toIdeal) :=
    isReduced_of_injective (algebraMap (AtPrime (gr E) x.asHomogeneousIdeal.toIdeal)
      (Localization.AtPrime x.asHomogeneousIdeal.toIdeal)) (val_injective _)
  exact isReduced_of_injective (Proj.stalkIso (gr E) x).hom.hom
    ((Proj.stalkIso (gr E) x).commRingCatIsoToRingEquiv.injective)

instance isReduced_ESch : IsReduced (ESch E) := isReduced_of_isReduced_stalk _

/-- **`ESch E` is integral.** -/
instance isIntegral_ESch : IsIntegral (ESch E) := isIntegral_of_irreducibleSpace_of_isReduced _

/-! ## §2. Every point lies in `D₊(Z)` or `D₊(Y)` -/

abbrev yC : E.toProjective.CoordinateRing := E.toProjective.coord 1
abbrev xC : E.toProjective.CoordinateRing := E.toProjective.coord 0

theorem yC_mem : yC E ∈ gr E 1 := E.toProjective.coord_mem_grading 1

/-- `X³ = Z · (Y² + a₁XY + a₃YZ − a₂X² − a₄XZ − a₆Z²)` in the homogeneous coordinate ring. -/
theorem xC_cube : xC E ^ 3 = zC E * (yC E ^ 2 + algebraMap ℚ _ E.a₁ * xC E * yC E +
    algebraMap ℚ _ E.a₃ * yC E * zC E - algebraMap ℚ _ E.a₂ * xC E ^ 2 -
    algebraMap ℚ _ E.a₄ * xC E * zC E - algebraMap ℚ _ E.a₆ * zC E ^ 2) := by
  have h := (WeierstrassCurve.Projective.equation_iff _).mp E.toProjective.equation_coord
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
  linear_combination -h

/-- **The complement of `D₊(Z)` lies in `D₊(Y)`** (if `Z ∈ p` then `X ∈ p`, so `Y ∉ p`). -/
theorem mem_basicOpen_Y_of_not_mem_Z (p : ESch E) (hp : p ∉ Proj.basicOpen (gr E) (zC E)) :
    p ∈ Proj.basicOpen (gr E) (yC E) := by
  rw [Proj.mem_basicOpen] at hp ⊢
  push_neg at hp
  have hx : xC E ∈ p.asHomogeneousIdeal := by
    have : xC E ^ 3 ∈ p.asHomogeneousIdeal.toIdeal := by
      rw [xC_cube]; exact Ideal.mul_mem_right _ _ hp
    exact p.isPrime.mem_of_pow_mem 3 this
  intro hy
  apply p.not_irrelevant_le
  refine (E.toProjective.irrelevant_le_span_range_coord).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact hx
  · exact hy
  · exact hp

/-! ## §3. `A_(Z)` is generated by `x = X/Z` and `y = Y/Z` -/

/-- `ℚ → (A)₀ → A_(Z)`. -/
instance algQAZ : Algebra ℚ (AZ E) :=
  ((algebraMap (gr E 0) (AZ E)).comp (algebraMap ℚ (gr E 0))).toAlgebra

theorem val_xz : (xz E).val = Localization.mk (xC E) (⟨zC E ^ 1, 1, rfl⟩ : Submonoid.powers (zC E)) := rfl
theorem val_yz : (yz E).val = Localization.mk (yC E) (⟨zC E ^ 1, 1, rfl⟩ : Submonoid.powers (zC E)) := rfl

/-- **`F/Zⁿ = F(x, y, 1)` for `F` homogeneous of degree `n`.** -/
theorem away_mk_eq_aeval (n : ℕ) (p : MvPolynomial (Fin 3) ℚ) (hp : p.IsHomogeneous n)
    (h : Ideal.Quotient.mk (Ideal.span {E.toProjective.polynomial}) p ∈ gr E (n • 1)) :
    Away.mk (gr E) (zC_mem E) n (Ideal.Quotient.mk _ p) h =
      MvPolynomial.aeval ![xz E, yz E, 1] p := by
  apply val_injective
  set L := Localization.Away (zC E)
  set ψ := algebraMap E.toProjective.CoordinateRing L
  have hval : ∀ a : AZ E, a.val = algebraMap (AZ E) L a := fun a => rfl
  rw [hval (MvPolynomial.aeval _ p), MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
  rw [Away.val_mk]
  have hz : IsUnit (ψ (zC E)) := IsLocalization.Away.algebraMap_isUnit (zC E)
  have hzx : ∀ i, ψ (E.toProjective.coord i) = ψ (zC E) * (algebraMap (AZ E) L ∘ ![xz E, yz E, 1]) i := by
    intro i
    fin_cases i
    · simp only [Function.comp_apply, Fin.zero_eta, Matrix.cons_val_zero]
      have key := IsLocalization.mk'_spec' L (E.toProjective.coord 0)
        (⟨zC E ^ 1, 1, rfl⟩ : Submonoid.powers (zC E))
      rw [← hval, val_xz, Localization.mk_eq_mk']
      convert key.symm using 2
      simp [ψ]
    · simp only [Function.comp_apply, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      have key := IsLocalization.mk'_spec' L (E.toProjective.coord 1)
        (⟨zC E ^ 1, 1, rfl⟩ : Submonoid.powers (zC E))
      rw [← hval, val_yz, Localization.mk_eq_mk']
      convert key.symm using 2
      simp [ψ]
    · simp [Function.comp_apply, map_one]
  have hmk : ψ (Ideal.Quotient.mk _ p) = MvPolynomial.eval₂ (ψ.comp (algebraMap ℚ _))
      (fun i => ψ (E.toProjective.coord i)) p := by
    conv_lhs => rw [← MvPolynomial.eval₂_eta p]
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
    rfl
  have hmain : ψ (Ideal.Quotient.mk _ p) = ψ (zC E) ^ n *
      MvPolynomial.eval₂ ((algebraMap (AZ E) L).comp (algebraMap ℚ (AZ E)))
        (algebraMap (AZ E) L ∘ ![xz E, yz E, 1]) p := by
    rw [hmk]
    have hfun : (fun i => ψ (E.toProjective.coord i)) =
        fun i => ψ (zC E) * (algebraMap (AZ E) L ∘ ![xz E, yz E, 1]) i := funext hzx
    rw [hfun, eval₂_mul_homog _ _ _ hp,
      RingHom.ext_rat (ψ.comp (algebraMap ℚ _)) ((algebraMap (AZ E) L).comp (algebraMap ℚ (AZ E)))]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul, hmain]
  simp only [map_pow]
  ring

theorem mem_gr_iff {n : ℕ} {F : E.toProjective.CoordinateRing} (hF : F ∈ gr E (n • 1)) :
    ∃ p : MvPolynomial (Fin 3) ℚ, p.IsHomogeneous n ∧ Ideal.Quotient.mk _ p = F := by
  have : F ∈ gr E n := by simpa using hF
  exact E.toProjective.mem_grading_iff.mp this

/-- **Ring maps out of `A_(Z)` agreeing on `x`, `y` are equal.** -/
theorem ringHom_ext_AZ {K : Type*} [CommRing K] {f g : AZ E →+* K} (hx : f (xz E) = g (xz E))
    (hy : f (yz E) = g (yz E)) : f = g := by
  ext u
  obtain ⟨n, F, hF, rfl⟩ := Away.mk_surjective (gr E) (zC_mem E) u
  obtain ⟨p, hp, rfl⟩ := mem_gr_iff E hF
  rw [away_mk_eq_aeval E n p hp, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left,
    MvPolynomial.eval₂_comp_left, RingHom.ext_rat (f.comp _) (g.comp _)]
  congr 1
  funext i
  fin_cases i
  · exact hx
  · exact hy
  · simp

/-- `(x, y)` is on `E` in `A_(Z)`. -/
theorem wEqA_xz_yz : WEqA E (xz E) (yz E) := by
  have hp := E.toProjective.isHomogeneous_polynomial
  have h0 : (Ideal.Quotient.mk (Ideal.span {E.toProjective.polynomial}) E.toProjective.polynomial) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hmem : Ideal.Quotient.mk (Ideal.span {E.toProjective.polynomial}) E.toProjective.polynomial ∈
      gr E (3 • 1) := by simpa using E.toProjective.mk_mem_grading hp
  have h := away_mk_eq_aeval E 3 _ hp hmem
  have hz : Away.mk (gr E) (zC_mem E) 3 _ hmem = 0 := by
    apply val_injective
    rw [Away.val_mk, h0, Localization.mk_zero, val_zero]
  rw [hz] at h
  unfold WEqA
  simp only [WeierstrassCurve.Projective.polynomial, map_sub, map_add, map_mul, map_pow,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_pow, mul_one] at h
  linear_combination -h

/-! ## §4. `A_(Z) ≅ ℚ[x, y]/(W_E)` -/


/-- `A_(Z) → ℚ[x, y]/(W_E)`, `X/Z ↦ x`, `Y/Z ↦ y`. -/
def azToCR : AZ E →+* CR E := chartHom E (xA E) (yA E) (affEq_of_wEqA (wEqA_xA_yA E))

theorem onCurve_xz_yz : E.toAffine.polynomial.eval₂
    (Polynomial.eval₂RingHom (algebraMap ℚ (AZ E)) (xz E)) (yz E) = 0 := by
  have h := wEqA_xz_yz E
  unfold WEqA at h
  simp only [WeierstrassCurve.Affine.polynomial, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_pow]
  linear_combination h

/-- `ℚ[x, y]/(W_E) → A_(Z)`, `x ↦ X/Z`, `y ↦ Y/Z`. -/
def crToAZ : CR E →+* AZ E :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap ℚ (AZ E)) (xz E)) (yz E) (onCurve_xz_yz E)

theorem crToAZ_xA : crToAZ E (xA E) = xz E := by
  simp [crToAZ, xA, WeierstrassCurve.Affine.CoordinateRing.mk, AdjoinRoot.lift_mk]

theorem crToAZ_yA : crToAZ E (yA E) = yz E := by
  simp [crToAZ, yA, WeierstrassCurve.Affine.CoordinateRing.mk, AdjoinRoot.lift_mk]

theorem crToAZ_azToCR (a : AZ E) : crToAZ E (azToCR E a) = a := by
  have : (crToAZ E).comp (azToCR E) = RingHom.id _ := by
    apply ringHom_ext_AZ E
    · change crToAZ E (azToCR E (xz E)) = xz E
      rw [azToCR, chartHom_xz, crToAZ_xA]
    · change crToAZ E (azToCR E (yz E)) = yz E
      rw [azToCR, chartHom_yz, crToAZ_yA]
  exact RingHom.congr_fun this a

theorem azToCR_crToAZ (a : CR E) : azToCR E (crToAZ E a) = a := by
  have : (azToCR E).comp (crToAZ E) = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    refine Polynomial.ringHom_ext' ?_ ?_
    · refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
      change azToCR E (crToAZ E (xA E)) = xA E
      rw [crToAZ_xA]
      simp [azToCR, chartHom_xz]
    · change azToCR E (crToAZ E (yA E)) = yA E
      rw [crToAZ_yA]
      simp [azToCR, chartHom_yz]
  exact RingHom.congr_fun this a

/-- **`A_(Z) ≅ ℚ[x, y]/(W_E)`.** -/
def azEquiv : AZ E ≃+* CR E :=
  RingEquiv.ofRingHom (azToCR E) (crToAZ E) (RingHom.ext (azToCR_crToAZ E))
    (RingHom.ext (crToAZ_azToCR E))

/-- **A ring map out of `A_(Z)` is the point given by its values on `x`, `y`.** -/
theorem eq_chartHom {K : Type} [CommRing K] [Algebra ℚ K] (χ : AZ E →+* K)
    (h : (E.map (algebraMap ℚ K)).toAffine.Equation (χ (xz E)) (χ (yz E))) :
    χ = chartHom E (χ (xz E)) (χ (yz E)) h :=
  ringHom_ext_AZ E (by rw [chartHom_xz]) (by rw [chartHom_yz])

theorem equation_of_hom {K : Type} [CommRing K] [Algebra ℚ K] (χ : AZ E →+* K) :
    (E.map (algebraMap ℚ K)).toAffine.Equation (χ (xz E)) (χ (yz E)) := by
  refine affEq_of_wEqA ?_
  exact (wEqA_xz_yz E).map χ

/-! ## §5. Charts through the generic point: `R → K(X)` -/

section Kappa

variable {X : Scheme.{0}} [IsIntegral X] {R : CommRingCat.{0}} (j : Spec R ⟶ X) [IsOpenImmersion j]

/-- **A chart through the generic point gives `R → K(X)`**: `Spec K(X) → X` factors through it. -/
theorem exists_kappa (h : genericPoint X ∈ j.opensRange) :
    ∃ u : R →+* X.functionField,
      Spec.map (CommRingCat.ofHom u) ≫ j = X.fromSpecFunctionField := by
  have hr : Set.range X.fromSpecFunctionField ⊆ Set.range j := by
    rw [ZInQ.CurveModel.range_fromSpecFunctionField]
    rintro _ rfl
    exact h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j X.fromSpecFunctionField hr)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

theorem kappa_unique {u u' : R →+* X.functionField}
    (hu : Spec.map (CommRingCat.ofHom u) ≫ j = X.fromSpecFunctionField)
    (hu' : Spec.map (CommRingCat.ofHom u') ≫ j = X.fromSpecFunctionField) : u = u' := by
  have h1 := Spec.map_injective ((cancel_mono j).mp (hu.trans hu'.symm))
  exact congrArg CommRingCat.Hom.hom h1

theorem genericPoint_mem_of_kappa {u : R →+* X.functionField}
    (hu : Spec.map (CommRingCat.ofHom u) ≫ j = X.fromSpecFunctionField) :
    genericPoint X ∈ j.opensRange := by
  have h := congrArg (fun f => f (IsLocalRing.closedPoint (CommRingCat.of X.functionField))) hu
  simp only [Scheme.Hom.comp_apply] at h
  have h0 : X.fromSpecFunctionField (IsLocalRing.closedPoint (CommRingCat.of X.functionField)) =
      genericPoint X := Scheme.fromSpecStalk_closedPoint
  exact ⟨_, h.trans h0⟩

/-- **`K(X)` is the fraction field of `R`** through `R → K(X)`. -/
theorem isFractionRing_of_chart {u : R →+* X.functionField}
    (hu : Spec.map (CommRingCat.ofHom u) ≫ j = X.fromSpecFunctionField) :
    @IsFractionRing R _ X.functionField _ u.toAlgebra := by
  set U := j.opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange j
  have hgen : genericPoint X ∈ U := genericPoint_mem_of_kappa j hu
  haveI : Nonempty U := ⟨⟨_, hgen⟩⟩
  have hF := functionField_isFractionRing_of_isAffineOpen X U hU
  let e := IsOpenImmersion.isoOfRangeEq hU.fromSpec j (by rw [hU.range_fromSpec]; rfl)
  let r : R ⟶ Γ(X, U) := Spec.preimage e.hom
  let r' : Γ(X, U) ⟶ R := Spec.preimage e.inv
  have hr : Spec.map r = e.hom := Spec.map_preimage _
  have hr' : Spec.map r' = e.inv := Spec.map_preimage _
  have h1 : r ≫ r' = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hr, hr', e.inv_hom_id, Spec.map_id])
  have h2 : r' ≫ r = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hr, hr', e.hom_inv_id, Spec.map_id])
  let rr : R ≃+* Γ(X, U) := RingEquiv.ofRingHom r.hom r'.hom
    (by ext a; exact congrArg (fun f => f.hom a) h2) (by ext a; exact congrArg (fun f => f.hom a) h1)
  have hFF : X.fromSpecFunctionField = Spec.map (X.germToFunctionField U) ≫ hU.fromSpec := by
    exact (hU.fromSpecStalk_eq_fromSpecStalk hgen).symm
  have hu2 : u = (r ≫ X.germToFunctionField U).hom := by
    refine kappa_unique j hu ?_
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, hr,
      IsOpenImmersion.isoOfRangeEq_hom_fac, hFF]
  have h3 := (IsFractionRing.isFractionRing_iff_of_base_ringEquiv X.functionField rr.symm).mp hF
  have key : (algebraMap Γ(X, U) X.functionField).comp rr.symm.symm.toRingHom = u := by
    rw [hu2]; rfl
  rw [key] at h3
  exact h3

/-- **The local ring at a point of the chart contains `R`** (`R → 𝒪_{X,p} → K(X)` is `u`), and
`Spec 𝒪_{X,p} → X` factors through the chart. -/
theorem exists_stalk_lift {u : R →+* X.functionField}
    (hu : Spec.map (CommRingCat.ofHom u) ≫ j = X.fromSpecFunctionField) (p : X)
    (hp : p ∈ j.opensRange) :
    ∃ θ : R →+* X.presheaf.stalk p, (algebraMap (X.presheaf.stalk p) X.functionField).comp θ = u ∧
      X.fromSpecStalk p = Spec.map (CommRingCat.ofHom θ) ≫ j := by
  have hr : Set.range (X.fromSpecStalk p) ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    have hz : X.fromSpecStalk p z ⤳ p := by
      have h0 : X.fromSpecStalk p z ∈ Set.range (X.fromSpecStalk p) := Set.mem_range_self z
      rw [Scheme.range_fromSpecStalk] at h0
      exact h0
    have := hz.mem_open j.opensRange.isOpen hp
    simpa using this
  set ℓ := IsOpenImmersion.lift j (X.fromSpecStalk p) hr
  have hℓ : ℓ ≫ j = X.fromSpecStalk p := IsOpenImmersion.lift_fac _ _ _
  set θ := Spec.preimage ℓ
  have h1 : Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes p)) ≫
      X.fromSpecStalk p = X.fromSpecFunctionField := Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  have h2 : Spec.map (θ ≫ X.presheaf.stalkSpecializes (genericPoint_specializes p)) =
      Spec.map (CommRingCat.ofHom u) := by
    rw [← cancel_mono j, Spec.map_comp, Category.assoc, Spec.map_preimage, hℓ, h1, hu]
  have h3 := Spec.map_injective h2
  refine ⟨θ.hom, ?_, ?_⟩
  · have := congrArg CommRingCat.Hom.hom h3
    rw [CommRingCat.hom_ofHom] at this
    rw [← this]
    rfl
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage, hℓ]

end Kappa

/-! ## §6. The function field of `ESch E` is `ℚ(E)` -/

theorem opensRange_chartZ : (chartZ E).opensRange = Proj.basicOpen (gr E) (zC E) :=
  Proj.opensRange_awayι _ _ _ _

theorem genericPoint_mem_chartZ : genericPoint (ESch E) ∈ (chartZ E).opensRange := by
  rw [opensRange_chartZ]
  refine ((genericPoint_spec (ESch E)).mem_open_set_iff (Proj.basicOpen (gr E) (zC E)).isOpen).mpr
    ⟨eta0 E, trivial, ?_⟩
  change zC E ∉ (⊥ : HomogeneousIdeal (gr E))
  intro h
  have h' : zC E ∈ (⊥ : HomogeneousIdeal (gr E)).toIdeal := h
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h'
  exact zC_ne_zero E h'

/-- **`A_(Z) → K(ESch E)`**, the chart `D₊(Z)` at the generic point. -/
def kappaZ : AZ E →+* (ESch E).functionField :=
  (exists_kappa (chartZ E) (genericPoint_mem_chartZ E)).choose

theorem kappaZ_spec : Spec.map (CommRingCat.ofHom (kappaZ E)) ≫ chartZ E =
    (ESch E).fromSpecFunctionField :=
  (exists_kappa (chartZ E) (genericPoint_mem_chartZ E)).choose_spec

/-- **`K(ESch E) ≅ ℚ(E)`**, `X/Z ↦ x`, `Y/Z ↦ y`. -/
def ffEquiv : (ESch E).functionField ≃+* E.toAffine.FunctionField :=
  letI := (kappaZ E).toAlgebra
  haveI := isFractionRing_of_chart (chartZ E) (kappaZ_spec E)
  IsFractionRing.ringEquivOfRingEquiv (K := (ESch E).functionField) (L := E.toAffine.FunctionField)
    (azEquiv E)

theorem ffEquiv_kappaZ (a : AZ E) :
    ffEquiv E (kappaZ E a) = algebraMap (CR E) E.toAffine.FunctionField (azToCR E a) := by
  letI := (kappaZ E).toAlgebra
  haveI := isFractionRing_of_chart (chartZ E) (kappaZ_spec E)
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (azEquiv E) a

theorem ffEquiv_xz : ffEquiv E (kappaZ E (xz E)) = ZInQ.GZAlg.genX E := by
  rw [ffEquiv_kappaZ]; simp [azToCR, chartHom_xz, ZInQ.GZAlg.genX]

theorem ffEquiv_yz : ffEquiv E (kappaZ E (yz E)) = ZInQ.GZAlg.genY E := by
  rw [ffEquiv_kappaZ]; simp [azToCR, chartHom_yz, ZInQ.GZAlg.genY]

/-! ## §7. The chart `D₊(Y)` at `O`, and `Z/Y = 1/y` -/


theorem yC_ne_zero : yC E ≠ 0 := by
  intro h
  have hO : (E.toProjective.map (RingHom.id ℚ)).Equation ![0, 1, 0] := by
    rw [WeierstrassCurve.Projective.equation_iff]
    simp
  have := congrFun (E.toProjective.evalHom_comp_coord (RingHom.id ℚ) hO) 1
  simp only [Function.comp_apply] at this
  rw [show E.toProjective.coord 1 = 0 from h, map_zero] at this
  simp at this

/-- The chart `D₊(Y) = Spec A_(Y) ⟶ ESch E` (it contains `O = [0 : 1 : 0]`). -/
def chartY : Spec (CommRingCat.of (Away (gr E) (yC E))) ⟶ ESch E :=
  Proj.awayι (gr E) (yC E) (yC_mem E) one_pos

instance : IsOpenImmersion (chartY E) := by unfold chartY; infer_instance

abbrev AY : Type := Away (gr E) (yC E)
/-- `v = Z/Y ∈ A_(Y)`. -/
abbrev vY : AY E := Away.isLocalizationElem (yC_mem E) (zC_mem E)

end ZInQ.H33D1
