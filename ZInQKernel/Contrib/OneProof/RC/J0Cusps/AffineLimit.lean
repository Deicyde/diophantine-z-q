import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ChartComparison
import ZInQKernel.Contrib.CloudB3W17Hodge.Port.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

/-! Comparing affine evaluations over the rationals with the topology on
complex points of the base change. On the spot (c), tex 1785–1787. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter PkgI3
open scoped TensorProduct Topology

namespace ZInQ.Manuscript.RC.J0Cusps

theorem maps_to_rat_unique {R : Type} [CommRing R]
    (f g : Spec (.of R) ⟶ Spec (.of ℚ)) : f = g := by
  apply Spec.homEquiv.injective
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- Restrict a section to a point and evaluate on its affine source. -/
def sectionEval {X : Scheme.{0}} {R : Type} [CommRing R] (p : Spec (.of R) ⟶ X)
    (U : X.Opens) (hp : ⊤ ≤ p ⁻¹ᵁ U) : Γ(X, U) ⟶ CommRingCat.of R :=
  p.appLE U ⊤ hp ≫ (Scheme.ΓSpecIso (.of R)).hom

/-- The evaluation ring map determines an affine scheme point. -/
theorem sectionMap_factor {X : Scheme.{0}} {R : Type} [CommRing R]
    (p : Spec (.of R) ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (hp : ⊤ ≤ p ⁻¹ᵁ U) :
    Spec.map (sectionEval p U hp) ≫ hU.fromSpec = p := by
  change Spec.map (p.appLE U ⊤ hp ≫ (Scheme.ΓSpecIso (.of R)).hom) ≫ hU.fromSpec = p
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec p _
    (isAffineOpen_top _) hp, IsAffineOpen.fromSpec_top, ← Scheme.isoSpec_Spec_hom,
    Iso.hom_inv_id_assoc]

section Affine

variable {A : Type} [CommRing A] [Algebra ℚ A]

private def specPoint (f : A →+* ℂ) :
    AbVar.ptObj (K := ℚ) ℂ ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ A))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f)) (maps_to_rat_unique _ _)

private def tensorMap (f : A →+* ℂ) : ℂ ⊗[ℚ] A →ₐ[ℂ] ℂ :=
  AlgHom.liftEquiv ℚ ℂ A ℂ
    { toRingHom := f
      commutes' := fun r => DFunLike.congr_fun
        (Subsingleton.elim (f.comp (algebraMap ℚ A)) (algebraMap ℚ ℂ)) r }

private def tensorProjection :
    Over.mk (ComplexPoint.affineSpecStructureMap (ℂ ⊗[ℚ] A)) ⟶
      complexBaseChange.obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ A)))) :=
  Over.homMk
    (Limits.pullback.lift
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] ℂ ⊗[ℚ] A).toRingHom))
      (ComplexPoint.affineSpecStructureMap (ℂ ⊗[ℚ] A))
      (maps_to_rat_unique _ _))
    (Limits.pullback.lift_snd _ _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem tensorPoint_eq (f : A →+* ℂ) :
    Point.map (tensorProjection (A := A))
      ((ComplexPoint.affineSpecEquiv (ℂ ⊗[ℚ] A)).symm (tensorMap f)) = complexLift (specPoint f) := by
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · simp only [Point.map, Over.comp_left, tensorProjection, Over.homMk_left,
      complexLift, Category.assoc, Limits.pullback.lift_fst, specPoint]
    change Spec.map (CommRingCat.ofHom (tensorMap f).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] ℂ ⊗[ℚ] A).toRingHom) =
      Spec.map (CommRingCat.ofHom f)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    change tensorMap f ((1 : ℂ) ⊗ₜ[ℚ] a) = f a
    simp [tensorMap]
  · exact Over.w _ |>.trans (Over.w _).symm

/-- Pointwise convergence of ring maps gives convergence of the associated
points in the topology of the complex base change of an affine scheme. -/
theorem tendsto_specPoint {I : Type} {F : Filter I} (f : I → A →+* ℂ) (g : A →+* ℂ)
    (h : ∀ a, Tendsto (fun i => f i a) F (𝓝 (g a))) :
    Tendsto (fun i => complexLift (specPoint (f i))) F (𝓝 (complexLift (specPoint g))) := by
  have ht (a : ℂ ⊗[ℚ] A) :
      Tendsto (fun i => tensorMap (f i) a) F (𝓝 (tensorMap g a)) := by
    induction a using TensorProduct.inductionOn with
    | tmul x y =>
      have hxy (v : A →+* ℂ) : tensorMap v (x ⊗ₜ[ℚ] y) = x * v y := by simp [tensorMap]
      simpa only [hxy] using (tendsto_const_nhds : Tendsto (fun _ : I => x) F (𝓝 x)).mul (h y)
    | add x y hx hy => simpa only [map_add] using hx.add hy
  have ht' : Tendsto (fun i => tensorMap (f i)) F (𝓝 (tensorMap g)) := by
    change Tendsto (fun i => tensorMap (f i)) F
      (@nhds _ (TopologicalSpace.induced
        (fun v : ℂ ⊗[ℚ] A →ₐ[ℂ] ℂ => (v : ℂ ⊗[ℚ] A → ℂ)) inferInstance)
        (tensorMap g))
    rw [nhds_induced, tendsto_comap_iff]
    exact tendsto_pi_nhds.mpr ht
  have hs := (ComplexPoint.continuous_affineSpecEquiv_symm (ℂ ⊗[ℚ] A)).continuousAt.tendsto.comp ht'
  have hm := (Point.continuous_map (tensorProjection (A := A))).continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, tensorPoint_eq] using hm

end Affine

/-- To establish a limit on the source curve, it suffices that its points
factor eventually through one affine neighborhood of the candidate limit and
that all the affine evaluations converge. -/
theorem tendsto_complexLift_of_sections {I : Type} {F : Filter I} {X : Over (Spec (.of ℚ))}
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (p : I → (AbVar.ptObj (K := ℚ) ℂ ⟶ X))
    (c : AbVar.ptObj (K := ℚ) ℂ ⟶ X)
    (h : ∀ᶠ i in F, ⊤ ≤ (p i).left ⁻¹ᵁ U) (hc : ⊤ ≤ c.left ⁻¹ᵁ U)
    (he : letI := Classical.propDecidable; ∀ r : Γ(X.left, U),
      Tendsto (fun i => if hi : ⊤ ≤ (p i).left ⁻¹ᵁ U then
        sectionEval (p i).left U hi r else sectionEval c.left U hc r)
        F (𝓝 (sectionEval c.left U hc r))) :
    Tendsto (fun i => complexLift (p i)) F (𝓝 (complexLift c)) := by
  classical
  let A := Γ(X.left, U)
  let := (show ℚ →+* A from
    (Spec.homEquiv (hU.fromSpec ≫ X.hom)).hom).toAlgebra
  let k : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ A))) ⟶ X :=
    Over.homMk hU.fromSpec (Spec.map_preimage _).symm
  let g : A →+* ℂ := (sectionEval c.left U hc).hom
  let f (i : I) : A →+* ℂ := if hi : ⊤ ≤ (p i).left ⁻¹ᵁ U then
    (sectionEval (p i).left U hi).hom else g
  have hf : ∀ a : A, Tendsto (fun i => f i a) F (𝓝 (g a)) := by
    intro a
    convert he a using 2
    split
    · rename_i hi
      rw [show f _ = (sectionEval (p _).left U hi).hom from dite_eq_left hi]
    · rename_i hi
      rw [show f _ = g from dite_eq_right hi]
  have hc' : specPoint g ≫ k = c :=
    Over.OverMorphism.ext (sectionMap_factor c.left hU hc)
  have hp' : ∀ᶠ i in F, specPoint (f i) ≫ k = p i := by
    filter_upwards [h] with i hi
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (f i)) ≫ hU.fromSpec = (p i).left
    have hfi : f i = (sectionEval (p i).left U hi).hom := dite_eq_left hi
    rw [hfi]
    exact sectionMap_factor (p i).left hU hi
  have ht := (Point.continuous_map (complexBaseChange.map k)).continuousAt.tendsto.comp
    (tendsto_specPoint f g hf)
  rw [← hc', complexLift_comp]
  apply ht.congr'
  filter_upwards [hp'] with i hi
  rw [Function.comp_apply, ← complexLift_comp, hi]


end ZInQ.Manuscript.RC.J0Cusps
