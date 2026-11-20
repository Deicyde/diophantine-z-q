import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveSchemeCharts
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveAdditionCoordinates

/-! A construction of morphisms to the fixed Weierstrass Proj by polynomial
formulas on charts of a reduced source. On the spot (c), tex 1785–1787. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme

namespace ZInQ.Manuscript.RC.J0Cusps

open PreparedParam

theorem schemeMapsToRat_unique {T : Scheme.{0}} (f g : T ⟶ Spec (.of ℚ)) :
    f = g := by
  apply ext_to_Spec
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

private theorem overlapEq (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {T : Scheme.{0}} [IsReduced T] (f g : T ⟶ (projectiveTarget E).left)
    (h : ∀ (F : Type) [Field F] [Algebra ℚ F] (p : Spec (.of F) ⟶ T),
      projectiveValue (p ≫ f) = projectiveValue (p ≫ g)) : f = g := by
  haveI : IsProper (projectiveOverQ E) := by
    unfold projectiveOverQ
    have := isProper_proj E
    infer_instance
  apply ext_of_fromSpecResidueField_eq f g (projectiveOverQ E) Set.univ dense_univ
  · intro x _
    let p := T.fromSpecResidueField x
    let alg : Algebra ℚ (T.residueField x) :=
      (Spec.homEquiv (p ≫ f ≫ projectiveOverQ E)).hom.toAlgebra
    exact (@projectiveValue_bijective E _ (T.residueField x) _ alg).1 (@h _ _ alg p)
  · apply schemeMapsToRat_unique

private theorem fieldPoint_lifts {X Y : Scheme.{0}} {F : Type} [Field F]
    (f : Y ⟶ X) [IsOpenImmersion f] (p : Spec (.of F) ⟶ X)
    (h : p default ∈ Set.range f) :
    ∃ q : Spec (.of F) ⟶ Y, q ≫ f = p := by
  have hh : Set.range p ⊆ Set.range f := by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z (default : Spec (.of F))] using h
  exact ⟨IsOpenImmersion.lift f p hh, IsOpenImmersion.lift_fac _ _ _⟩

/-- A collection of local formulas agreeing with one field-point rule
glues on a reduced scheme. The local input asks for a map near each point
only; no compatibility of open charts is assumed. -/
theorem projectiveMorphism_of_local (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (T : Scheme.{0}) [IsReduced T]
    (rule : ∀ (F : Type) [Field F] [Algebra ℚ F],
      (Spec (.of F) ⟶ T) → (E.baseChange F).toAffine.Point)
    (h : ∀ x : T, ∃ (R : CommRingCat.{0}) (inc : Spec R ⟶ T)
        (m : Spec R ⟶ (projectiveTarget E).left),
      IsOpenImmersion inc ∧ x ∈ Set.range inc ∧
      ∀ (F : Type) [Field F] [Algebra ℚ F] (p : Spec (.of F) ⟶ Spec R),
        projectiveValue (p ≫ m) = rule F (p ≫ inc)) :
    ∃ m : T ⟶ (projectiveTarget E).left,
      ∀ (F : Type) [Field F] [Algebra ℚ F] (p : Spec (.of F) ⟶ T),
        projectiveValue (p ≫ m) = rule F p := by
  classical
  choose R inc m hc hmem hm using h
  let cover : T.OpenCover :=
    { I₀ := T
      X x := Spec (R x)
      f := inc
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun p => ⟨p, hmem p⟩, hc⟩ }
  have agree (i j : cover.I₀) :
      pullback.fst (cover.f i) (cover.f j) ≫ m i =
        pullback.snd (cover.f i) (cover.f j) ≫ m j := by
    haveI : IsReduced (pullback (cover.f i) (cover.f j)) :=
      isReduced_of_isOpenImmersion (pullback.fst (cover.f i) (cover.f j) ≫ cover.f i)
    apply overlapEq E
    intro F _ _ p
    rw [← Category.assoc, ← Category.assoc, hm i, hm j,
      Category.assoc, Category.assoc, pullback.condition]
  refine ⟨cover.glueMorphisms m agree, ?_⟩
  intro F _ _ p
  let i := p default
  obtain ⟨q, hq⟩ := fieldPoint_lifts (cover.f i) p (hmem i)
  rw [← hq, Category.assoc, cover.ι_glueMorphisms]
  exact hm i F q

private theorem equation_of_field_evaluations (E : WeierstrassCurve ℚ)
    {R : Type} [CommRing R] [Algebra ℚ R] [IsReduced R]
    (v : Fin 3 → R)
    (h : ∀ (F : Type) [Field F] [Algebra ℚ F] (g : R →+* F),
      (E.baseChange F).toProjective.Equation (g ∘ v)) :
    (E.baseChange R).toProjective.Equation v := by
  change (E.toProjective.map (algebraMap ℚ R)).Equation v
  rw [Projective.equation_map_iff_aeval]
  let p : R := MvPolynomial.aeval v E.toProjective.polynomial
  change p = 0
  have hp : p ∈ nilradical R := by
    rw [PrimeSpectrum.nilradical_eq_iInf, Ideal.mem_iInf]
    intro x
    let F := FractionRing (R ⧸ x.asIdeal)
    let g : R →+* F := (algebraMap (R ⧸ x.asIdeal) F).comp (Ideal.Quotient.mk x.asIdeal)
    have he := (Projective.equation_map_iff_aeval E.toProjective _).mp (h F g)
    have e : g p = 0 := by
      change g (MvPolynomial.aeval v E.toProjective.polynomial) = 0
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left,
        show g.comp (algebraMap ℚ R) = algebraMap ℚ F from Subsingleton.elim _ _]
      exact he
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact IsFractionRing.injective _ F (e.trans (map_zero _).symm)
  rwa [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] at hp

private theorem openLift_ring_map (E : WeierstrassCurve ℚ) (i : Fin 3)
    {R : Type} [CommRing R] (p : Spec (.of R) ⟶ (projectiveTarget E).left)
    (h : Set.range p ⊆ Set.range (projectiveChartInclusion E i)) :
    ∃ g : ProjectiveChart E i →+* R,
      p = Spec.map (CommRingCat.ofHom g) ≫ projectiveChartInclusion E i := by
  obtain ⟨g, e⟩ := Spec.map_surjective (IsOpenImmersion.lift (projectiveChartInclusion E i) p h)
  exact ⟨g.hom, (IsOpenImmersion.lift_fac _ _ _).symm.trans
    (congrArg (fun q => q ≫ projectiveChartInclusion E i) e.symm)⟩

private theorem projectiveChart_covers (E : WeierstrassCurve ℚ)
    (x : (projectiveTarget E).left) :
    ∃ i : Fin 3, x ∈ Set.range (projectiveChartInclusion E i) := by
  let c := Proj.affineOpenCoverOfIrrelevantLESpan E.toProjective.grading E.toProjective.coord
    E.toProjective.coord_mem_grading (fun _ => zero_lt_one) E.toProjective.irrelevant_le_span_range_coord
  exact ⟨c.idx x, c.covers x⟩


set_option maxHeartbeats 1000000 in
/-- Evaluate a polynomial family on normalized homogeneous coordinates. If
the formulas agree with the point operation wherever nonzero and at least
one is nonzero everywhere, the operation is represented by a morphism.
The hypotheses involve equations over rings and fields, with no scheme
morphism realizing the operation presumed. -/
theorem projectiveMorphism_of_formulas (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {n : ℕ} {I : Type} (T : Scheme.{0}) [IsReduced T] (s : T ⟶ Spec (.of ℚ))
    (f : Fin n → (T ⟶ (projectiveTarget E).left))
    (formula : ∀ (R : Type) [CommRing R] [Algebra ℚ R],
      I → (Fin n → Fin 3 → R) → Fin 3 → R)
    (op : ∀ (F : Type) [Field F] [Algebra ℚ F],
      (Fin n → (E.baseChange F).toAffine.Point) → (E.baseChange F).toAffine.Point)
    (map_formula : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
      (g : R →+* S) (j : I) (v : Fin n → Fin 3 → R),
      g ∘ formula R j v = formula S j (fun a => g ∘ v a))
    (fields : ∀ (F : Type) [Field F] [Algebra ℚ F] (v : Fin n → Fin 3 → F),
      (∀ a, (E.baseChange F).toProjective.Nonsingular (v a)) →
      (∃ j, formula F j v ≠ 0) ∧
        ∀ j, formula F j v ≠ 0 →
          (E.baseChange F).toProjective.Equation (formula F j v) ∧
            Projective.Point.toAffine (E.baseChange F).toProjective (formula F j v) =
              op F (fun a => Projective.Point.toAffine (E.baseChange F).toProjective (v a))) :
    ∃ m : T ⟶ (projectiveTarget E).left,
      ∀ (F : Type) [Field F] [Algebra ℚ F] (p : Spec (.of F) ⟶ T),
        projectiveValue (p ≫ m) = op F (fun a => projectiveValue (p ≫ f a)) := by
  classical
  let rule (F : Type) [Field F] [Algebra ℚ F] (p : Spec (.of F) ⟶ T) :
      (E.baseChange F).toAffine.Point := op F (fun a => projectiveValue (p ≫ f a))
  refine projectiveMorphism_of_local E T rule ?_
  intro x
  choose i hi using fun a => projectiveChart_covers E (f a x)
  let V : T.Opens := ⨅ a, (f a) ⁻¹ᵁ (projectiveChartInclusion E (i a)).opensRange
  have hx : x ∈ V := by
    change x ∈ (V : Set T)
    simp only [V, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    exact hi
  obtain ⟨U, hUa, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hx
  let R : Type := Γ(T, U)
  let inc := hUa.fromSpec
  haveI : Algebra ℚ R := (Spec.homEquiv (inc ≫ s)).hom.toAlgebra
  haveI : IsReduced R := inferInstanceAs (IsReduced Γ(T, U))
  have hinc : x ∈ Set.range inc := by
    rw [hUa.range_fromSpec]
    exact hxU
  obtain ⟨x', hx'⟩ := hinc
  have hrange (a : Fin n) : Set.range (inc ≫ f a) ⊆
      Set.range (projectiveChartInclusion E (i a)) := by
    rintro _ ⟨b, rfl⟩
    have hb : inc b ∈ U := by
      have hb' : inc b ∈ Set.range inc := Set.mem_range_self b
      rwa [hUa.range_fromSpec] at hb'
    exact (iInf_le (fun a => (f a) ⁻¹ᵁ
      (projectiveChartInclusion E (i a)).opensRange) a) (hUV hb)
  choose g hg using fun a => openLift_ring_map E (i a) (inc ≫ f a) (hrange a)
  let v (a : Fin n) : Fin 3 → R := g a ∘ projectiveChartRatio E (i a)
  have hv (F : Type) [Field F] [Algebra ℚ F] (k : R →+* F) (a : Fin n) :
      (E.baseChange F).toProjective.Nonsingular (k ∘ v a) := by
    have h : (k ∘ v a) (i a) = 1 := by simp [v, projectiveChartRatio_self]
    apply nonsingular_of_equation_ne_zero (E.baseChange F) _ (fun e => by
      have ee := congrFun e (i a)
      exact one_ne_zero (h.symm.trans ee))
    change (E.toProjective.map (algebraMap ℚ F)).Equation (k ∘ v a)
    have e := projectiveChart_equation E (i a)
    rw [Projective.equation_map_iff_aeval, MvPolynomial.aeval_def] at e ⊢
    rw [← map_zero k, ← map_zero (g a), ← e, MvPolynomial.eval₂_comp_left,
      MvPolynomial.eval₂_comp_left]
    rw [show k.comp ((g a).comp (algebraMap ℚ (ProjectiveChart E (i a)))) =
      algebraMap ℚ F from Subsingleton.elim _ _]
  let xR : PrimeSpectrum R := x'
  letI : xR.asIdeal.IsPrime := xR.isPrime
  let F := FractionRing (R ⧸ xR.asIdeal)
  letI : Field F := inferInstanceAs (Field (FractionRing (R ⧸ xR.asIdeal)))
  let k : R →+* F := (algebraMap (R ⧸ xR.asIdeal) F).comp (Ideal.Quotient.mk xR.asIdeal)
  letI : Algebra ℚ F := (k.comp (algebraMap ℚ R)).toAlgebra
  obtain ⟨j, hj⟩ := (fields F _ (hv F k)).1
  let w := formula R j v
  have hk : k ∘ w ≠ 0 := fun e => hj ((map_formula R F k j v).symm.trans e)
  have hsome : ∃ t, k (w t) ≠ 0 := by
    by_contra! h
    exact hk (funext h)
  obtain ⟨t, ht⟩ := hsome
  have ht' : w t ∉ xR.asIdeal := by
    intro h
    exact ht (by simp [k, Ideal.Quotient.eq_zero_iff_mem.mpr h])
  have hw : (E.baseChange R).toProjective.Equation w := by
    apply equation_of_field_evaluations
    intro K _ _ l
    change (E.baseChange K).toProjective.Equation (l ∘ formula R j v)
    rw [map_formula R K l j v]
    by_cases h0 : formula K j (fun a => l ∘ v a) = 0
    · rw [h0, Projective.equation_of_Z_eq_zero (by rfl)]
      simp
    · exact ((fields K _ (hv K l)).2 j h0).1
  let A := Localization.Away (w t)
  let l : R →+* A := algebraMap R A
  letI : Algebra ℚ A := (l.comp (algebraMap ℚ R)).toAlgebra
  let aff := Spec.map (CommRingCat.ofHom l)
  have hlt : IsUnit (l (w t)) := IsLocalization.Away.algebraMap_isUnit (w t)
  have e : (E.toProjective.map (algebraMap ℚ A)).Equation (l ∘ w) := by
    change (E.toProjective.map (algebraMap ℚ R)).Equation w at hw
    rw [Projective.equation_map_iff_aeval, MvPolynomial.aeval_def] at hw ⊢
    rw [← map_zero l, ← hw, MvPolynomial.eval₂_comp_left]
    rw [show l.comp (algebraMap ℚ R) = algebraMap ℚ A from Subsingleton.elim _ _]
  let patch := projectiveChartMorphism E (l ∘ w) e t hlt
  have hp' : x' ∈ Set.range aff := by
    change x' ∈ aff.opensRange
    rw [Scheme.Hom.opensRange_localizationAway (w t)]
    exact ht'
  refine ⟨.of A, aff ≫ inc, patch, inferInstance, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hp'
    exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, hx']⟩
  · intro K _ _ p
    obtain ⟨φ, rfl⟩ := Spec.map_surjective p
    let u : R →+* K := φ.hom.comp l
    have hw' : u ∘ w ≠ 0 := fun h =>
      (hlt.map φ.hom).ne_zero (congrFun h t)
    have hu : u ∘ w = formula K j (fun a => u ∘ v a) := map_formula R K u j v
    have hφ := (fields K _ (hv K u)).2 j (hu ▸ hw')
    rw [← hu] at hφ
    have eK : (E.toProjective.map (algebraMap ℚ K)).Equation (φ.hom ∘ (l ∘ w)) := hφ.1
    have hK : (E.baseChange K).toProjective.Nonsingular (φ.hom ∘ (l ∘ w)) :=
      nonsingular_of_equation_ne_zero (E.baseChange K) hφ.1 hw'
    change projectiveValue (Spec.map (CommRingCat.ofHom φ.hom) ≫
      projectiveChartMorphism E (l ∘ w) e t hlt) =
      op K (fun a => projectiveValue ((Spec.map φ ≫ aff ≫ inc) ≫ f a))
    calc
      _ = projectiveValue (projectiveChartMorphism E (φ.hom ∘ (l ∘ w)) eK t (hlt.map φ.hom)) :=
        congrArg (fun p : Spec (.of K) ⟶ (projectiveTarget E).left => projectiveValue p)
          (projectiveChartMorphism_map E (l ∘ w) e t hlt φ.hom eK)
      _ = Projective.Point.toAffine (E.baseChange K).toProjective (u ∘ w) :=
        projectiveValue_chartMorphism E _ hK t (hlt.map φ.hom)
      _ = op K (fun a => Projective.Point.toAffine (E.baseChange K).toProjective (u ∘ v a)) := hφ.2
      _ = _ := by
        congr 1
        funext a
        have ea : (Spec.map φ ≫ aff ≫ inc) ≫ f a =
            Spec.map (CommRingCat.ofHom (u.comp (g a))) ≫ projectiveChartInclusion E (i a) := by
          simp only [Category.assoc, hg a]
          unfold aff u
          rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
          rfl
        rw [ea]
        exact (projectiveValue_fromChart E (i a) (u.comp (g a)) (hv K u a)).symm



end ZInQ.Manuscript.RC.J0Cusps
