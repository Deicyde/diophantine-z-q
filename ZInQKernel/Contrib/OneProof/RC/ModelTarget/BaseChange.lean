import ZInQKernel.Contrib.OneProof.RC.ModelTarget.RuleGluing
import ZInQKernel.Contrib.OneProof.RC.ModelTarget.FormulaMorphism

/-! Base change of the projective cubic along a ring map `ψ : R → S`: maps between the
pullback of `Proj W` along `Spec S → Spec R` and `Proj (W.map ψ)`, both the identity in
homogeneous coordinates. On the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve
open scoped WeierstrassCurve.Projective

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ZInQ.Manuscript.RC.ModelTarget

variable {R S : Type} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (ψ : R →+* S)

theorem chartMorphism_ring_congr {A : Type} [CommRing A] {g g' : R →+* A} (h : g = g')
    (v : Fin 3 → A) (hv : (W.toProjective.map g).Equation v)
    (hv' : (W.toProjective.map g').Equation v) (i : Fin 3) (hi : IsUnit (v i)) :
    chartMorphism W g v hv i hi = chartMorphism W g' v hv' i hi := by
  subst h
  rfl

/-- The base-changed scheme `Proj W ×_R S`. -/
abbrev baseChangeScheme : Scheme.{0} :=
  pullback (projStructure W) (Spec.map (CommRingCat.ofHom ψ))

theorem exists_chart_cover (y : Proj W.toProjective.grading) :
    ∃ k : Fin 2, y ∈ (chartι W (![1, 2] k)).opensRange := by
  have htop : y ∈ (⊤ : (Proj W.toProjective.grading).Opens) := trivial
  rw [← iSup_basicOpen_YZ W, TopologicalSpace.Opens.mem_iSup] at htop
  obtain ⟨k, hk⟩ := htop
  refine ⟨k, ?_⟩
  rw [Proj.opensRange_awayι]
  fin_cases k <;> exact hk

theorem fst_structure {F : Type} [Field F] (g : S →+* F) (p : Spec (.of F) ⟶ baseChangeScheme W ψ)
    (hp : p ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom g)) :
    (p ≫ pullback.fst _ _) ≫ projStructure W = Spec.map (CommRingCat.ofHom (g.comp ψ)) := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, hp, ← Spec.map_comp,
    CommRingCat.ofHom_comp]

/-- A solution vector of a field point of the base change, read in `Proj W`. -/
def bcVec {F : Type} [Field F] (g : S →+* F) (p : Spec (.of F) ⟶ baseChangeScheme W ψ)
    (hp : p ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom g)) : Fin 3 → F :=
  (exists_chartMorphism W (g.comp ψ) (p ≫ pullback.fst _ _) (fst_structure W ψ g p hp)).choose

theorem bcVec_spec {F : Type} [Field F] (g : S →+* F) (p : Spec (.of F) ⟶ baseChangeScheme W ψ)
    (hp : p ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom g)) :
    ∃ (hv : (W.toProjective.map (g.comp ψ)).Equation (bcVec W ψ g p hp)) (i : Fin 3)
      (hi : IsUnit (bcVec W ψ g p hp i)),
      p ≫ pullback.fst _ _ = chartMorphism W (g.comp ψ) (bcVec W ψ g p hp) hv i hi :=
  (exists_chartMorphism W (g.comp ψ) (p ≫ pullback.fst _ _) (fst_structure W ψ g p hp)).choose_spec

/-- The base change map `Proj W ×_R S → Proj (W.map ψ)`, identity in coordinates. -/
theorem exists_baseChangeHom [(W.map ψ).IsElliptic] [IsReduced (baseChangeScheme W ψ)] :
    ∃ (m : baseChangeScheme W ψ ⟶ Proj (W.map ψ).toProjective.grading)
      (hm : m ≫ projStructure (W.map ψ) = pullback.snd _ _),
      ∀ (F : Type) [Field F] (g : S →+* F) (p : Spec (.of F) ⟶ baseChangeScheme W ψ)
        (hp : p ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom g)),
        fieldValue (W.map ψ) g (p ≫ m) (comp_structure (W.map ψ) hm hp) =
          Projective.Point.toAffine ((W.map ψ).toProjective.map g) (bcVec W ψ g p hp) := by
  classical
  apply morphism_of_rule (W.map ψ) (baseChangeScheme W ψ) (pullback.snd _ _)
    (fun F _ g p hp => Projective.Point.toAffine ((W.map ψ).toProjective.map g) (bcVec W ψ g p hp))
  intro x
  obtain ⟨k, hk⟩ := exists_chart_cover W (pullback.fst (projStructure W)
    (Spec.map (CommRingCat.ofHom ψ)) x)
  let i : Fin 3 := ![1, 2] k
  let V := (pullback.fst (projStructure W) (Spec.map (CommRingCat.ofHom ψ))) ⁻¹ᵁ (chartι W i).opensRange
  have hx : x ∈ V := hk
  obtain ⟨U, hUa, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hx
  let Γ : Type := Γ(baseChangeScheme W ψ, U)
  let inc := hUa.fromSpec
  obtain ⟨gU, hgU⟩ : ∃ gU : S →+* Γ, inc ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom gU) :=
    ⟨(Spec.preimage (inc ≫ pullback.snd _ _)).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  have hinc : x ∈ Set.range inc := by
    rw [hUa.range_fromSpec]
    exact hxU
  have hrange : Set.range (inc ≫ pullback.fst _ _) ⊆ Set.range (chartι W i) := by
    rintro _ ⟨b, rfl⟩
    have hb : inc b ∈ U := by
      have hb' : inc b ∈ Set.range inc := Set.mem_range_self b
      rwa [hUa.range_fromSpec] at hb'
    exact hUV hb
  obtain ⟨φ₀, e₀⟩ := Spec.map_surjective (IsOpenImmersion.lift (chartι W i) _ hrange)
  have hga : inc ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom φ₀.hom) ≫ chartι W i := by
    rw [CommRingCat.ofHom_hom, e₀, IsOpenImmersion.lift_fac]
  have hs : (inc ≫ pullback.fst (projStructure W) (Spec.map (CommRingCat.ofHom ψ))) ≫
      projStructure W = Spec.map (CommRingCat.ofHom (gU.comp ψ)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hgU, ← Spec.map_comp,
      CommRingCat.ofHom_comp]
  obtain ⟨hv, hi, he⟩ := eq_chartMorphism W (gU.comp ψ) i _ φ₀.hom hga hs
  let v := φ₀.hom ∘ ratio W i
  have hv' : ((W.map ψ).toProjective.map gU).Equation v := hv
  let m := chartMorphism (W.map ψ) gU v hv' i hi
  have hm : m ≫ projStructure (W.map ψ) = inc ≫ pullback.snd _ _ := by
    simp only [m]
    rw [chartMorphism_structure, hgU]
  refine ⟨.of Γ, inc, m, hm, inferInstance, hinc, ?_⟩
  intro F _ g q hq
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  have hg : g = φ.hom.comp gU := by
    rw [hgU, ← CommRingCat.ofHom_hom φ, ← Spec.map_comp] at hq
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective hq)).symm
  subst hg
  have hφ : Spec.map φ = Spec.map (CommRingCat.ofHom φ.hom) := by rw [CommRingCat.ofHom_hom]
  calc fieldValue (W.map ψ) _ (Spec.map φ ≫ m) _
      = fieldValue (W.map ψ) (φ.hom.comp gU) (chartMorphism (W.map ψ) (φ.hom.comp gU) (φ.hom ∘ v)
          (equation_map (W.map ψ) gU φ.hom v hv') i (hi.map φ.hom)) (chartMorphism_structure ..) :=
        fieldValue_congr (W.map ψ) _ (by rw [hφ]; exact chartMorphism_map _ gU φ.hom v hv' i hi _) _ _
    _ = Projective.Point.toAffine ((W.map ψ).toProjective.map (φ.hom.comp gU)) (φ.hom ∘ v) :=
        fieldValue_chartMorphism _ _ _ _ _ _
    _ = _ := by
        apply Projective.Point.toAffine_of_equiv
        obtain ⟨hb, j, hj, eb⟩ := bcVec_spec W ψ (φ.hom.comp gU) (Spec.map φ ≫ inc) hq
        apply Setoid.symm
        refine equiv_of_chartMorphism_eq W ((φ.hom.comp gU).comp ψ) _ _ hb
          (equation_map W (gU.comp ψ) φ.hom v hv) j i hj (hi.map φ.hom) ?_
        rw [← eb, Category.assoc, he, hφ,
          chartMorphism_map W (gU.comp ψ) φ.hom v hv i hi (equation_map W (gU.comp ψ) φ.hom v hv)]
        exact chartMorphism_ring_congr W (RingHom.comp_assoc _ _ _).symm _ _ _ _ _

#print axioms exists_baseChangeHom

end ZInQ.Manuscript.RC.ModelTarget
