import ZInQKernel.Contrib.OneProof.T10Proetale.CohomologyProducts

/-!
# Degree one and the pro-étale residue limit

The comparison with compatible finite pro-étale classes is always injective.
Its surjectivity follows from one epimorphism of products of sheaves.
-/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped PadicInt

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

universe u

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

private theorem mapH_sub_apply {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J Ab.{u}] [HasExt.{u} (Sheaf J Ab.{u})]
    {F G : Sheaf J Ab.{u}} (a b : F ⟶ G) (n : ℕ) (x : F.H n) :
    Sheaf.H.map (a - b) n x = Sheaf.H.map a n x - Sheaf.H.map b n x := by
  simp only [Sheaf.H.map_apply, sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.comp_add, Ext.comp_neg]

private theorem extH1_injective {D : Type*} [Category* D] [Abelian D]
    [HasExt.{u} D] (R : D) {S : ShortComplex D} (hS : S.ShortExact)
    (hg : Function.Surjective ((Ext.mk₀ S.g).postcomp R (add_zero 0))) :
    Function.Injective ((Ext.mk₀ S.f).postcomp R (add_zero 1)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ R hS x hx (zero_add 1)
  obtain ⟨z, hz⟩ := hg y
  change z.comp (Ext.mk₀ S.g) (add_zero 0) = y at hz
  rw [← hy, ← hz, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

section Cohomology

omit [Fact ℓ.Prime] in
private lemma differenceHom_project (n : ℕ) :
    differenceHom X ℓ ≫ productProjection X ℓ n =
      productProjection X ℓ n -
        productProjection X ℓ (n + 1) ≫
          mapContinuousCoefficients X (residueStep ℓ n).toAddMonoidHom
            continuous_of_discreteTopology := by
  apply Sheaf.hom_ext
  ext U : 2
  rfl

omit [Fact ℓ.Prime] in
private lemma productH1Coordinates_difference (y : Sheaf.H.{u+1} (productSheaf X ℓ) 1) (n : ℕ) :
    productH1Coordinates X ℓ (Sheaf.H.map.{u+1} (differenceHom X ℓ) 1 y) n =
      productH1Coordinates X ℓ y n - proTransition X ℓ n 1 (productH1Coordinates X ℓ y (n + 1)) := by
  let r := mapContinuousCoefficients X (residueStep ℓ n).toAddMonoidHom continuous_of_discreteTopology
  let a := productProjection X ℓ n
  let b := productProjection X ℓ (n + 1)
  have eq : differenceHom X ℓ ≫ a = a - b ≫ r := differenceHom_project X ℓ n
  exact (Sheaf.H.map_comp_apply (differenceHom X ℓ) a y).symm.trans
    ((congrArg (fun f => Sheaf.H.map.{u+1} f 1 y) eq).trans
      ((mapH_sub_apply a (b ≫ r) 1 y).trans
        (congrArg (fun z => Sheaf.H.map.{u+1} a 1 y - z) (Sheaf.H.map_comp_apply b r y))))

private lemma productH1Coordinates_integral (x : X.EllAdicCohomology ℓ 1) (n : ℕ) :
    productH1Coordinates X ℓ (Sheaf.H.map.{u+1} (integralToProduct X ℓ) 1 x) n =
      proReduction X ℓ n 1 x := by
  let z : Sheaf.H.{u+1} (T10Etale.F X ℓ) 1 := x
  let r := mapContinuousCoefficients X (PadicInt.toZModPow (p := ℓ) n).toAddMonoidHom
    (continuous_toResidue ℓ n)
  have hr : integralToProduct X ℓ ≫ productProjection X ℓ n = r := by
    apply Sheaf.hom_ext
    ext U : 2
    rfl
  exact (Sheaf.H.map_comp_apply (integralToProduct X ℓ) (productProjection X ℓ n) z).symm.trans
    (congrArg (fun f => Sheaf.H.map.{u+1} f 1 z) hr)

omit [Fact ℓ.Prime] in
private theorem differenceH0_surjective :
    Function.Surjective (Sheaf.H.map.{u+1} (differenceHom X ℓ) 0) := by
  let T := T10Etale.terminalProEt X
  let E := Sheaf.H.equiv₀.{u+1} (productSheaf X ℓ) (T10Etale.isTerminalProEt X)
  intro y
  obtain ⟨z, hz⟩ := differenceHom_surjective_sections X ℓ T (E y)
  exact ⟨E.symm z, (Sheaf.H.equiv₀_symm_naturality (T10Etale.isTerminalProEt X)
    (differenceHom X ℓ) z).trans ((congrArg E.symm hz).trans (E.symm_apply_apply y))⟩

set_option maxHeartbeats 500000 in
/-- The actual reductions detect degree-one classes without any exact-product
assumption on the pro-étale site. -/
theorem proReduction_injective (x y : X.EllAdicCohomology ℓ 1)
    (h : ∀ n, proReduction X ℓ n 1 x = proReduction X ℓ n 1 y) : x = y := by
  let R := cohomologySource X
  let a : Sheaf.H.{u+1} (T10Etale.F X ℓ) 1 := x
  let b : Sheaf.H.{u+1} (T10Etale.F X ℓ) 1 := y
  let f := Sheaf.H.map.{u+1} (integralToProduct X ℓ) 1
  have hf : Function.Injective f :=
    extH1_injective R (S := coefficientSequence X ℓ) (coefficientSequence_shortExact X ℓ)
      (differenceH0_surjective X ℓ)
  have hcoords : productH1Coordinates X ℓ (f a) = productH1Coordinates X ℓ (f b) := by
    funext n
    exact (productH1Coordinates_integral X ℓ x n).trans
      ((h n).trans (productH1Coordinates_integral X ℓ y n).symm)
  exact hf (productH1Coordinates_injective X ℓ hcoords)

/-- Degree-one comparison with the finite pro-étale tower, conditional only
on the epimorphism of a product of coefficient-sheaf maps. -/
theorem proReduction_existsUnique_of_compatible
    (h : Epi (Limits.Pi.map fun n => (injectivePresentation (residueSheaf X ℓ n)).g))
    (x : ∀ n, ProFiniteH X ℓ n 1) (hx : ∀ n, proTransition X ℓ n 1 (x (n + 1)) = x n) :
    ∃! a : X.EllAdicCohomology ℓ 1, ∀ n, proReduction X ℓ n 1 a = x n := by
  let R := cohomologySource X
  let hS := coefficientSequence_shortExact X ℓ
  let hProd := productH1Coordinates_bijective X ℓ h
  obtain ⟨y, hy⟩ := hProd.surjective x
  have hdy : Sheaf.H.map.{u+1} (differenceHom X ℓ) 1 y = 0 := by
    apply hProd.injective
    refine (funext fun n => ?_).trans (map_zero (productH1Coordinates X ℓ)).symm
    exact (productH1Coordinates_difference X ℓ y n).trans
      ((congrArg₂ (fun a b => a - proTransition X ℓ n 1 b) (congrFun hy n)
        (congrFun hy (n + 1))).trans (sub_eq_zero.mpr (hx n).symm))
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₂ R hS y hdy
  let a : X.EllAdicCohomology ℓ 1 := z
  have ha (n : ℕ) : proReduction X ℓ n 1 a = x n :=
    (productH1Coordinates_integral X ℓ a n).symm.trans
      ((congrArg (fun b => productH1Coordinates X ℓ b n)
        (show Sheaf.H.map.{u+1} (integralToProduct X ℓ) 1 z = y from hz)).trans (congrFun hy n))
  exact ⟨a, ha, fun b hb => proReduction_injective X ℓ b a (fun n => (hb n).trans (ha n).symm)⟩

end Cohomology

end
end ZInQ.Manuscript.T10Proetale
