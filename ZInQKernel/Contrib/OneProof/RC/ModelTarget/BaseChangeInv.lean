import ZInQKernel.Contrib.OneProof.RC.ModelTarget.BaseChange

/-! The inverse comparison: `Proj (W.map ψ) → Proj W` over `Spec S → Spec R`, the
identity in homogeneous coordinates on the standard charts. On the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve
open scoped WeierstrassCurve.Projective

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ZInQ.Manuscript.RC.ModelTarget

variable {R S : Type} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (ψ : R →+* S)

/-- The structure of `Proj (W.map ψ)` over `Spec R`. -/
abbrev structR : Proj (W.map ψ).toProjective.grading ⟶ Spec (.of R) :=
  projStructure (W.map ψ) ≫ Spec.map (CommRingCat.ofHom ψ)

/-- A solution vector of a field point of `Proj (W.map ψ)`. -/
def invVec {F : Type} [Field F] (p : Spec (.of F) ⟶ Proj (W.map ψ).toProjective.grading) : Fin 3 → F :=
  (exists_chartMorphism (W.map ψ) (pointRing (projStructure (W.map ψ)) p) p
    (pointRing_spec _ p)).choose

theorem invVec_spec {F : Type} [Field F] (p : Spec (.of F) ⟶ Proj (W.map ψ).toProjective.grading) :
    ∃ (hv : ((W.map ψ).toProjective.map (pointRing (projStructure (W.map ψ)) p)).Equation
        (invVec W ψ p)) (i : Fin 3) (hi : IsUnit (invVec W ψ p i)),
      p = chartMorphism (W.map ψ) (pointRing (projStructure (W.map ψ)) p) (invVec W ψ p) hv i hi :=
  (exists_chartMorphism (W.map ψ) _ p (pointRing_spec _ p)).choose_spec

theorem chart_equation_self (i : Fin 3) :
    ((W.map ψ).toProjective.map (chartConst (W.map ψ) i)).Equation (ratio (W.map ψ) i) := by
  have h := chart_equation (W.map ψ) i
  rw [Projective.Equation, Projective.map_polynomial (W' := (W.map ψ).toProjective)
    (f := chartConst (W.map ψ) i), MvPolynomial.eval_map]
  exact h

theorem chart_equation_comp (i : Fin 3) :
    (W.toProjective.map ((chartConst (W.map ψ) i).comp ψ)).Equation (ratio (W.map ψ) i) :=
  chart_equation_self W ψ i

theorem exists_baseChangeInvHom [W.IsElliptic] [IsReduced (Proj (W.map ψ).toProjective.grading)] :
    ∃ (m : Proj (W.map ψ).toProjective.grading ⟶ Proj W.toProjective.grading)
      (hm : m ≫ projStructure W = structR W ψ),
      ∀ (F : Type) [Field F] (g : R →+* F) (p : Spec (.of F) ⟶ Proj (W.map ψ).toProjective.grading)
        (hp : p ≫ structR W ψ = Spec.map (CommRingCat.ofHom g)),
        fieldValue W g (p ≫ m) (comp_structure W hm hp) =
          Projective.Point.toAffine (W.toProjective.map g) (invVec W ψ p) := by
  classical
  apply morphism_of_rule W (Proj (W.map ψ).toProjective.grading) (structR W ψ)
    (fun F _ g p _ => Projective.Point.toAffine (W.toProjective.map g) (invVec W ψ p))
  intro x
  obtain ⟨k, hk⟩ := exists_chart_cover (W.map ψ) x
  let i : Fin 3 := ![1, 2] k
  let m := chartMorphism W ((chartConst (W.map ψ) i).comp ψ) (ratio (W.map ψ) i)
    (chart_equation_comp W ψ i) i (by simp [ratio_self])
  have hm : m ≫ projStructure W = chartι (W.map ψ) i ≫ structR W ψ := by
    simp only [m]
    rw [chartMorphism_structure, structR, ← Category.assoc, chartι_structure, ← Spec.map_comp,
      CommRingCat.ofHom_comp]
  refine ⟨.of (Chart (W.map ψ) i), chartι (W.map ψ) i, m, hm, inferInstance, hk, ?_⟩
  intro F _ g q hq
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  have hφ : Spec.map φ = Spec.map (CommRingCat.ofHom φ.hom) := by rw [CommRingCat.ofHom_hom]
  have hg : g = φ.hom.comp ((chartConst (W.map ψ) i).comp ψ) := by
    rw [← Category.assoc, hφ, structR, ← Category.assoc, Category.assoc (Spec.map _),
      chartι_structure, ← Spec.map_comp, ← Spec.map_comp] at hq
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective hq)).symm
  subst hg
  have hv1 := equation_map W ((chartConst (W.map ψ) i).comp ψ) φ.hom _ (chart_equation_comp W ψ i)
  calc fieldValue W _ (Spec.map φ ≫ m) _
      = fieldValue W (φ.hom.comp ((chartConst (W.map ψ) i).comp ψ))
          (chartMorphism W (φ.hom.comp ((chartConst (W.map ψ) i).comp ψ)) (φ.hom ∘ ratio (W.map ψ) i)
            hv1 i (by simp [ratio_self])) (chartMorphism_structure ..) :=
        fieldValue_congr W _ (by rw [hφ]; exact chartMorphism_map W _ φ.hom _ _ i _ _) _ _
    _ = Projective.Point.toAffine (W.toProjective.map (φ.hom.comp ((chartConst (W.map ψ) i).comp ψ)))
          (φ.hom ∘ ratio (W.map ψ) i) := fieldValue_chartMorphism W _ _ _ _ _
    _ = _ := by
        apply Projective.Point.toAffine_of_equiv
        obtain ⟨hb, j, hj, eb⟩ := invVec_spec W ψ (Spec.map φ ≫ chartι (W.map ψ) i)
        have hs : (Spec.map (CommRingCat.ofHom φ.hom) ≫ chartι (W.map ψ) i) ≫
            projStructure (W.map ψ) = Spec.map (CommRingCat.ofHom
              (pointRing (projStructure (W.map ψ)) (Spec.map φ ≫ chartι (W.map ψ) i))) := by
          rw [← hφ]; exact pointRing_spec _ _
        obtain ⟨hv2, hi2, e2⟩ := eq_chartMorphism (W.map ψ)
          (pointRing (projStructure (W.map ψ)) (Spec.map φ ≫ chartι (W.map ψ) i)) i
          (Spec.map (CommRingCat.ofHom φ.hom) ≫ chartι (W.map ψ) i) φ.hom rfl hs
        apply Setoid.symm
        refine equiv_of_chartMorphism_eq (W.map ψ) _ _ _ hb hv2 j i hj hi2 ?_
        rw [← eb, ← e2, hφ]

#print axioms exists_baseChangeInvHom

end ZInQ.Manuscript.RC.ModelTarget
