import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower.Reduction

/-! faltings5-lower, part 5: points of a group model over `𝓞_K` with values in a `K`-scheme `T` are
the `T`-points of `A` (through the adjunction `Over.map ⊣ Over.pullback` and `gen`), compatibly with
the group law and with the Néron extension of an isogeny. -/

set_option linter.style.haveILetI false

namespace GapHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
open scoped CategoryTheory.Obj

section Transport

variable {K : Type} [Field K] [NumberField K]

/-- `Spec K → Spec 𝓞_K`. -/
noncomputable abbrev jK (K : Type) [Field K] [NumberField K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (𝓞 K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K))

/-- `Spec K → Spec K` (the base change of `A` to `K` is along it). -/
noncomputable abbrev sK (K : Type) [Field K] : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K K))

omit [NumberField K] in
theorem sK_eq : sK K = 𝟙 _ := by
  show Spec.map (CommRingCat.ofHom (RingHom.id K)) = _
  rw [CommRingCat.ofHom_id, Spec.map_id]

omit [NumberField K] in
/-- `Over.map (Spec K → Spec K) T ≅ T`. -/
noncomputable def mapSIso (T : Over (Spec (CommRingCat.of K))) : (Over.map (sK K)).obj T ≅ T :=
  Over.isoMk (Iso.refl _) (by
    simp only [Over.map_obj_hom, Iso.refl_hom, Category.id_comp]
    rw [sK_eq, Category.comp_id])

variable {A B : PkgI3.AbVar K}

/-- `gen` with the types of the two pullbacks. -/
noncomputable def gH (𝒩 : GroupModel A K) :
    (Over.pullback (jK K)).obj 𝒩.G ⟶ (Over.pullback (sK K)).obj A.X := 𝒩.gen.hom

noncomputable def gHinv (𝒩 : GroupModel A K) :
    (Over.pullback (sK K)).obj A.X ⟶ (Over.pullback (jK K)).obj 𝒩.G := 𝒩.gen.inv

theorem gH_gHinv (𝒩 : GroupModel A K) : gH 𝒩 ≫ gHinv 𝒩 = 𝟙 _ := 𝒩.gen.hom_inv_id

theorem gHinv_gH (𝒩 : GroupModel A K) : gHinv 𝒩 ≫ gH 𝒩 = 𝟙 _ := 𝒩.gen.inv_hom_id

/-- **Points of a group model with values in a `K`-scheme are points of `A`.** -/
noncomputable def theta (𝒩 : GroupModel A K) (T : Over (Spec (CommRingCat.of K))) :
    ((Over.map (jK K)).obj T ⟶ 𝒩.G) ≃ (T ⟶ A.X) where
  toFun p := (mapSIso T).inv ≫ ((Over.mapPullbackAdj (sK K)).homEquiv T A.X).symm
      ((Over.mapPullbackAdj (jK K)).homEquiv T 𝒩.G p ≫ gH 𝒩)
  invFun P := ((Over.mapPullbackAdj (jK K)).homEquiv T 𝒩.G).symm
      ((Over.mapPullbackAdj (sK K)).homEquiv T A.X ((mapSIso T).hom ≫ P) ≫ gHinv 𝒩)
  left_inv p := by
    simp only
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Equiv.apply_symm_apply,
      Category.assoc, gH_gHinv, Category.comp_id, Equiv.symm_apply_apply]
  right_inv P := by
    simp only
    rw [Equiv.apply_symm_apply, Category.assoc, gHinv_gH, Category.comp_id,
      Equiv.symm_apply_apply, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem theta_apply (𝒩 : GroupModel A K) (T : Over (Spec (CommRingCat.of K)))
    (p : (Over.map (jK K)).obj T ⟶ 𝒩.G) :
    theta 𝒩 T p = (mapSIso T).inv ≫ ((Over.mapPullbackAdj (sK K)).homEquiv T A.X).symm
      ((Over.mapPullbackAdj (jK K)).homEquiv T 𝒩.G p ≫ gH 𝒩) := rfl

/-- `theta` is natural in the group model along the extension of an isogeny. -/
theorem theta_comp (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (φ : A.X ⟶ B.X)
    (f : 𝒩A.G ⟶ 𝒩B.G) (he : CToPrinted.ExtendsIsogeny φ 𝒩A 𝒩B f)
    (T : Over (Spec (CommRingCat.of K))) (p : (Over.map (jK K)).obj T ⟶ 𝒩A.G) :
    theta 𝒩B T (p ≫ f) = theta 𝒩A T p ≫ φ := by
  rw [theta_apply, theta_apply, Adjunction.homEquiv_naturality_right, Category.assoc]
  have he' : (Over.pullback (jK K)).map f ≫ gH 𝒩B = gH 𝒩A ≫ (Over.pullback (sK K)).map φ := he
  rw [he', ← Category.assoc, Adjunction.homEquiv_naturality_right_symm, Category.assoc]

/-- `theta` is natural in `T`. -/
theorem theta_nat (𝒩 : GroupModel A K) {T T' : Over (Spec (CommRingCat.of K))} (h : T' ⟶ T)
    (p : (Over.map (jK K)).obj T ⟶ 𝒩.G) :
    theta 𝒩 T' ((Over.map (jK K)).map h ≫ p) = h ≫ theta 𝒩 T p := by
  rw [theta_apply, theta_apply, Adjunction.homEquiv_naturality_left, Category.assoc,
    Adjunction.homEquiv_naturality_left_symm, ← Category.assoc, ← Category.assoc]
  congr 1

theorem gH_mul (𝒩 : GroupModel A K) {T : Over (Spec (CommRingCat.of K))}
    (x y : T ⟶ (Over.pullback (jK K)).obj 𝒩.G) : (x * y) ≫ gH 𝒩 = x ≫ gH 𝒩 * y ≫ gH 𝒩 := by
  letI : GrpObj (genericFibre K 𝒩.G) := Functor.grpObjObj
  haveI hg : IsMonHom 𝒩.gen.hom := 𝒩.gen_hom
  haveI : IsMonHom (gH 𝒩) := hg
  exact MonObj.mul_comp x y (gH 𝒩)

/-- `theta` is multiplicative. -/
theorem theta_mul (𝒩 : GroupModel A K) (T : Over (Spec (CommRingCat.of K)))
    (p q : (Over.map (jK K)).obj T ⟶ 𝒩.G) :
    theta 𝒩 T (p * q) = theta 𝒩 T p * theta 𝒩 T q := by
  rw [theta_apply, theta_apply, theta_apply]
  have h1 : (Over.mapPullbackAdj (jK K)).homEquiv T 𝒩.G (p * q) =
      (Over.mapPullbackAdj (jK K)).homEquiv T 𝒩.G p *
        (Over.mapPullbackAdj (jK K)).homEquiv T 𝒩.G q := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Functor.map_mul, MonObj.comp_mul]
  rw [h1, gH_mul]
  set x := (Over.mapPullbackAdj (jK K)).homEquiv T 𝒩.G p ≫ gH 𝒩
  set y := (Over.mapPullbackAdj (jK K)).homEquiv T 𝒩.G q ≫ gH 𝒩
  clear_value x y
  obtain ⟨x', rfl⟩ := ((Over.mapPullbackAdj (sK K)).homEquiv T A.X).surjective x
  obtain ⟨y', rfl⟩ := ((Over.mapPullbackAdj (sK K)).homEquiv T A.X).surjective y
  have h2 : (Over.mapPullbackAdj (sK K)).homEquiv T A.X (x' * y') =
      (Over.mapPullbackAdj (sK K)).homEquiv T A.X x' *
        (Over.mapPullbackAdj (sK K)).homEquiv T A.X y' := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Functor.map_mul, MonObj.comp_mul]
  rw [← h2, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    MonObj.comp_mul]

theorem theta_one (𝒩 : GroupModel A K) (T : Over (Spec (CommRingCat.of K))) :
    theta 𝒩 T 1 = 1 := by
  have h := theta_mul 𝒩 T 1 1
  rw [_root_.mul_one] at h
  exact (mul_eq_left.mp h.symm)

/-- `Spec Ω → Spec K` for a field `Ω` with `σ : K → Ω`. -/
noncomputable def ptK {Ω : Type} [Field Ω] (σ : K →+* Ω) : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom σ))

/-- **Complex points of a group model are complex points of `A`.** -/
noncomputable def ptsTheta (𝒩 : GroupModel A K) (τ : K →+* ℂ) : 𝒩.Pts τ ≃ (ptK τ ⟶ A.X) :=
  ((ZInQ.H5Glue.ptCIso τ).homCongr (Iso.refl 𝒩.G)).trans (theta 𝒩 (ptK τ))

theorem ptsTheta_apply (𝒩 : GroupModel A K) (τ : K →+* ℂ) (p : 𝒩.Pts τ) :
    ptsTheta 𝒩 τ p = theta 𝒩 (ptK τ) ((ZInQ.H5Glue.ptCIso τ).inv ≫ p) := by
  show theta 𝒩 _ ((ZInQ.H5Glue.ptCIso τ).inv ≫ p ≫ 𝟙 _) = _
  rw [Category.comp_id]
  rfl

theorem ptsTheta_comp (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (φ : A.X ⟶ B.X)
    (f : 𝒩A.G ⟶ 𝒩B.G) (he : CToPrinted.ExtendsIsogeny φ 𝒩A 𝒩B f) (τ : K →+* ℂ)
    (p : 𝒩A.Pts τ) : ptsTheta 𝒩B τ (p ≫ f) = ptsTheta 𝒩A τ p ≫ φ := by
  rw [ptsTheta_apply, ptsTheta_apply]
  exact (congrArg (theta 𝒩B (ptK τ)) (Category.assoc _ _ _)).symm.trans
    (theta_comp 𝒩A 𝒩B φ f he _ _)

theorem ptsTheta_one (𝒩 : GroupModel A K) (τ : K →+* ℂ) : ptsTheta 𝒩 τ 1 = 1 := by
  rw [ptsTheta_apply]
  exact (congrArg (theta 𝒩 (ptK τ)) (MonObj.comp_one _)).trans (theta_one _ _)

/-- The kernel on complex points of `f` is the kernel on complex points of `φ`. -/
noncomputable def kerEquiv (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (φ : A.X ⟶ B.X)
    (f : 𝒩A.G ⟶ 𝒩B.G) (he : CToPrinted.ExtendsIsogeny φ 𝒩A 𝒩B f) (τ : K →+* ℂ) :
    {p : 𝒩A.Pts τ // p ≫ f = 1} ≃ {P : ptK τ ⟶ A.X // P ≫ φ = 1} :=
  (ptsTheta 𝒩A τ).subtypeEquiv fun p => by
    rw [← ptsTheta_comp 𝒩A 𝒩B φ f he, ← ptsTheta_one 𝒩B τ]
    exact (ptsTheta 𝒩B τ).injective.eq_iff.symm

theorem surjective_of_surjective (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (φ : A.X ⟶ B.X)
    (f : 𝒩A.G ⟶ 𝒩B.G) (he : CToPrinted.ExtendsIsogeny φ 𝒩A 𝒩B f) (τ : K →+* ℂ)
    (h : Function.Surjective fun P : ptK τ ⟶ A.X => P ≫ φ) :
    Function.Surjective fun p : 𝒩A.Pts τ => p ≫ f := by
  intro q
  obtain ⟨P, hP⟩ := h (ptsTheta 𝒩B τ q)
  refine ⟨(ptsTheta 𝒩A τ).symm P, (ptsTheta 𝒩B τ).injective ?_⟩
  simp only
  rw [ptsTheta_comp 𝒩A 𝒩B φ f he, Equiv.apply_symm_apply]
  exact hP

end Transport

end GapHeight
