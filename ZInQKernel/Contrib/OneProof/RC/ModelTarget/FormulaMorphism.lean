import ZInQKernel.Contrib.OneProof.RC.ModelTarget.FormulaGluing

/-! A morphism into the relative projective cubic given by polynomial formulas that
cover all field points and compute an operation on affine points. On the spot (c);
the relative form of `J0Cusps.projectiveMorphism_of_formulas`. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve HomogeneousLocalization

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ZInQ.Manuscript.RC.ModelTarget

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

theorem nonsingular_of_unit_coord [W.IsElliptic] {F : Type} [Field F] (g : R →+* F)
    (v : Fin 3 → F) (hv : (W.toProjective.map g).Equation v) (k : Fin 3) (hk : v k ≠ 0) :
    (W.toProjective.map g).Nonsingular v := by
  have : (W.toProjective.map g).IsElliptic := inferInstanceAs (W.map g).IsElliptic
  refine (Projective.equation_iff_nonsingular_of_ne_zero (W := W.toProjective.map g) ?_).mp hv
  intro h0
  exact hk (congrFun h0 k)

theorem equation_map {A B : Type} [CommRing A] [CommRing B] (g : R →+* A) (φ : A →+* B)
    (v : Fin 3 → A) (hv : (W.toProjective.map g).Equation v) :
    (W.toProjective.map (φ.comp g)).Equation (φ ∘ v) := by
  rw [Projective.Equation, Projective.map_polynomial, MvPolynomial.eval_map] at hv ⊢
  rw [← MvPolynomial.eval₂_comp_left, hv, map_zero]

variable {n : ℕ} (T : Scheme.{0}) (s : T ⟶ Spec (.of R)) (f : Fin n → (T ⟶ Proj W.toProjective.grading))
  (hf : ∀ a, f a ≫ projStructure W = s)
  (op : ∀ (F : Type) [Field F] (g : R →+* F),
    (Fin n → (W.map g).toAffine.Point) → (W.map g).toAffine.Point)

/-- Polynomial formulas covering all field points and computing `op` give a morphism. -/
theorem morphism_of_formulas [W.IsElliptic] [IsReduced T] {I : Type}
    (formula : ∀ (A : Type) [CommRing A] (_ : R →+* A), I → (Fin n → Fin 3 → A) → Fin 3 → A)
    (map_formula : ∀ (A B : Type) [CommRing A] [CommRing B] (g : R →+* A) (φ : A →+* B) (j : I)
      (v : Fin n → Fin 3 → A), φ ∘ formula A g j v = formula B (φ.comp g) j (fun a => φ ∘ v a))
    (equation : ∀ (A : Type) [CommRing A] (g : R →+* A) (j : I) (v : Fin n → Fin 3 → A),
      (∀ a, (W.toProjective.map g).Equation (v a)) →
        (W.toProjective.map g).Equation (formula A g j v))
    (fields : ∀ (F : Type) [Field F] (g : R →+* F) (v : Fin n → Fin 3 → F),
      (∀ a, (W.toProjective.map g).Nonsingular (v a)) →
        (∃ j, formula F g j v ≠ 0) ∧ ∀ j, formula F g j v ≠ 0 →
          Projective.Point.toAffine (W.toProjective.map g) (formula F g j v) =
            op F g (fun a => Projective.Point.toAffine (W.toProjective.map g) (v a))) :
    ∃ (m : T ⟶ Proj W.toProjective.grading) (hm : m ≫ projStructure W = s),
      Computes W T s f hf op (𝟙 T) m (by rw [hm, Category.id_comp]) := by
  classical
  apply morphism_of_local W T s f hf op
  intro x
  have hcov (y : Proj W.toProjective.grading) : ∃ k : Fin 2, y ∈ (chartι W (![1, 2] k)).opensRange := by
    have htop : y ∈ (⊤ : (Proj W.toProjective.grading).Opens) := trivial
    rw [← iSup_basicOpen_YZ W, TopologicalSpace.Opens.mem_iSup] at htop
    obtain ⟨k, hk⟩ := htop
    refine ⟨k, ?_⟩
    rw [Proj.opensRange_awayι]
    fin_cases k <;> exact hk
  choose kk hkk using fun a => hcov (f a x)
  let i (a : Fin n) : Fin 3 := ![1, 2] (kk a)
  let V : T.Opens := ⨅ a, (f a) ⁻¹ᵁ (chartι W (i a)).opensRange
  have hx : x ∈ V := by
    change x ∈ (V : Set T)
    simp only [V, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    exact hkk
  obtain ⟨U, hUa, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hx
  let Γ : Type := Γ(T, U)
  let inc := hUa.fromSpec
  let gU : R →+* Γ := (Spec.preimage (inc ≫ s)).hom
  have hgU : inc ≫ s = Spec.map (CommRingCat.ofHom gU) := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hinc : x ∈ Set.range inc := by
    rw [hUa.range_fromSpec]
    exact hxU
  obtain ⟨x', hx'⟩ := hinc
  have hrange (a : Fin n) : Set.range (inc ≫ f a) ⊆ Set.range (chartι W (i a)) := by
    rintro _ ⟨b, rfl⟩
    have hb : inc b ∈ U := by
      have hb' : inc b ∈ Set.range inc := Set.mem_range_self b
      rwa [hUa.range_fromSpec] at hb'
    exact (iInf_le (fun a => (f a) ⁻¹ᵁ (chartι W (i a)).opensRange) a) (hUV hb)
  have hlift (a : Fin n) : ∃ ga : Chart W (i a) →+* Γ,
      inc ≫ f a = Spec.map (CommRingCat.ofHom ga) ≫ chartι W (i a) := by
    obtain ⟨φ, e⟩ := Spec.map_surjective (IsOpenImmersion.lift (chartι W (i a)) (inc ≫ f a) (hrange a))
    refine ⟨φ.hom, ?_⟩
    rw [CommRingCat.ofHom_hom, e, IsOpenImmersion.lift_fac]
  choose ga hga using hlift
  have hrep (a : Fin n) := eq_chartMorphism W gU (i a) (inc ≫ f a) (ga a) (hga a)
    (by rw [Category.assoc, hf, hgU])
  choose hv hvi hve using hrep
  let v (a : Fin n) : Fin 3 → Γ := ga a ∘ ratio W (i a)
  have hvone (a : Fin n) : v a (i a) = 1 := by simp [v, ratio_self]
  have hns (F : Type) [Field F] (k : Γ →+* F) (a : Fin n) :
      (W.toProjective.map (k.comp gU)).Nonsingular (k ∘ v a) :=
    nonsingular_of_unit_coord W _ _ (equation_map W gU k _ (hv a)) (i a) (by simp [hvone])
  let xR : PrimeSpectrum Γ := x'
  let Fx := FractionRing (Γ ⧸ xR.asIdeal)
  let kx : Γ →+* Fx := (algebraMap (Γ ⧸ xR.asIdeal) Fx).comp (Ideal.Quotient.mk xR.asIdeal)
  obtain ⟨j, hj⟩ := (fields Fx (kx.comp gU) _ (hns Fx kx)).1
  let w := formula Γ gU j v
  have hk : kx ∘ w ≠ 0 := fun e => hj ((map_formula Γ Fx gU kx j v).symm.trans e)
  have hsome : ∃ t, kx (w t) ≠ 0 := by
    by_contra! h
    exact hk (funext h)
  obtain ⟨t, ht⟩ := hsome
  have ht' : w t ∉ xR.asIdeal := by
    intro h
    exact ht (by simp [kx, Ideal.Quotient.eq_zero_iff_mem.mpr h])
  have hw : (W.toProjective.map gU).Equation w := equation Γ gU j v hv
  let Aloc := Localization.Away (w t)
  let l : Γ →+* Aloc := algebraMap Γ Aloc
  let aff := Spec.map (CommRingCat.ofHom l)
  have hlt : IsUnit (l (w t)) := IsLocalization.Away.algebraMap_isUnit (w t)
  let patch := chartMorphism W (l.comp gU) (l ∘ w) (equation_map W gU l w hw) t hlt
  have hpatch : patch ≫ projStructure W = (aff ≫ inc) ≫ s := by
    rw [chartMorphism_structure, Category.assoc, hgU, ← Spec.map_comp]
    rfl
  have hp' : x' ∈ Set.range aff := by
    change x' ∈ aff.opensRange
    rw [Scheme.Hom.opensRange_localizationAway (w t)]
    exact ht'
  refine ⟨.of Aloc, aff ≫ inc, patch, hpatch, inferInstance, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hp'
    exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, hx']⟩
  · intro F _ g q hq
    obtain ⟨φ, rfl⟩ := Spec.map_surjective q
    have hg : g = φ.hom.comp (l.comp gU) := by
      simp only [Category.assoc, aff] at hq
      rw [hgU, ← Spec.map_comp, ← Spec.map_comp] at hq
      have := Spec.map_injective hq
      exact (congrArg CommRingCat.Hom.hom this).symm
    subst hg
    let u : Γ →+* F := φ.hom.comp l
    have hφ : Spec.map φ = Spec.map (CommRingCat.ofHom φ.hom) := by rw [CommRingCat.ofHom_hom]
    have hw' : u ∘ w = formula F (u.comp gU) j (fun a => u ∘ v a) := map_formula Γ F gU u j v
    have hwne : u ∘ w ≠ 0 := fun h0 => (hlt.map φ.hom).ne_zero (congrFun h0 t)
    have hval := (fields F (u.comp gU) _ (hns F u)).2 j (hw' ▸ hwne)
    calc fieldValue W _ (Spec.map φ ≫ patch) _
        = fieldValue W (u.comp gU) (chartMorphism W (u.comp gU) (u ∘ w)
            (equation_map W gU u w hw) t (hlt.map φ.hom)) (chartMorphism_structure ..) :=
          fieldValue_congr W _ (by
            rw [hφ]
            exact chartMorphism_map W (l.comp gU) φ.hom (l ∘ w) _ t hlt _) _ _
      _ = Projective.Point.toAffine (W.toProjective.map (u.comp gU)) (u ∘ w) :=
          fieldValue_chartMorphism W _ _ _ t _
      _ = op F (u.comp gU) (fun a => Projective.Point.toAffine (W.toProjective.map (u.comp gU))
            (u ∘ v a)) := by rw [hw']; exact hval
      _ = _ := by
          congr 1
          funext a
          symm
          calc fieldValue W (u.comp gU) ((Spec.map φ ≫ aff ≫ inc) ≫ f a) _
              = fieldValue W (u.comp gU) (chartMorphism W (u.comp gU) (u ∘ v a)
                  (equation_map W gU u _ (hv a)) (i a) (by simp [hvone])) (chartMorphism_structure ..) :=
                fieldValue_congr W _ (by
                  rw [Category.assoc, Category.assoc, hve a, ← Category.assoc, hφ,
                    show aff = Spec.map (CommRingCat.ofHom l) from rfl, ← Spec.map_comp,
                    ← CommRingCat.ofHom_comp]
                  exact chartMorphism_map W gU u _ (hv a) (i a) (hvi a) _) _ _
            _ = _ := fieldValue_chartMorphism W _ _ _ _ _

#print axioms morphism_of_formulas

end ZInQ.Manuscript.RC.ModelTarget
