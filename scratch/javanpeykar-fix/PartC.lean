import ZInQKernel.Contrib.OneProof.JavanpeykarDict
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ChowLemma
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Birational.ValuativeExtension

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace JavanpeykarFix

open CategoryTheory AlgebraicGeometry Limits

/-- The generic point is dense: `Spec K(X) → X` is dominant (isj1-dict). -/
theorem isDominant_fromSpecFunctionField (X : Scheme) [IsIntegral X] :
    IsDominant X.fromSpecFunctionField := by
  constructor
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  have h : genericPoint X ∈ Set.range X.fromSpecFunctionField :=
    ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  have := closure_mono (Set.singleton_subset_iff.mpr h)
  rw [(genericPoint_spec X).def] at this
  exact this

/-- **A smooth proper integral curve over a field is projective (glue, proved).** It has a closed
immersion into a projective space `ℙ(n; Spec k)` (vendored `ProjectiveSpace`, the base change of
`Proj ℤ[x_i]`) over `k`. Proof: Chow's lemma (vendored
`exists_projectiveModification_of_finite_irreducibleComponents`) gives a projective `M → X`, an
isomorphism over a dense open `U`; the inverse on `U` is a rational map `X ⤏ M`, which extends to a
morphism `g : X → M` because the local rings of `X` are valuation rings and `M` is proper (vendored
`exists_hom_of_valuationRing_stalk`, Hartshorne I.6.8); `g` is a section of the separated `M → X`
(both agree at the generic point), hence a closed immersion. -/
theorem exists_closedImmersion_projectiveSpace {k : Type} [Field k]
    (X : Over (Spec (CommRingCat.of k))) [IsIntegral X.left] [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom] :
    ∃ (n : Type) (_ : Finite n) (i : X.left ⟶ ℙ(n; Spec (CommRingCat.of k))),
      IsClosedImmersion i ∧ i ≫ ℙ(n; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k) = X.hom := by
  have hfin : (irreducibleComponents X.left).Finite := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨M, π, n, hn, ι, hπP, -, hι, hcomm, U, hU, hiso⟩ :=
    exists_projectiveModification_of_finite_irreducibleComponents X.hom hfin
  have hη : genericPoint X.left ∈ U := by
    show genericPoint X.left ∈ (U : Set X.left)
    rw [(genericPoint_spec X.left).mem_open_set_iff U.isOpen]
    rw [Set.univ_inter]; exact hU.nonempty
  let genericMap : Spec X.left.functionField ⟶ M :=
    U.fromSpecStalkOfMem (genericPoint X.left) hη ≫ inv (π ∣_ U) ≫ (π ⁻¹ᵁ U).ι
  have hgen : genericMap ≫ π = X.left.fromSpecFunctionField := by
    simp only [genericMap, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
  letI : X.left.Over (Spec (CommRingCat.of k)) := ⟨X.hom⟩
  letI : M.Over (Spec (CommRingCat.of k)) := ⟨π ≫ X.hom⟩
  have : IsProper (M ↘ Spec (CommRingCat.of k)) := inferInstanceAs (IsProper (π ≫ X.hom))
  have : M.IsSeparated := by
    constructor
    rw [show terminal.from M = (π ≫ X.hom) ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance
  have hval : ∀ x : X.left, ValuationRing (X.left.presheaf.stalk x) := fun x =>
    Scheme.valuationRing_stalk X.hom x
  obtain ⟨g, hgo, hg⟩ := Scheme.exists_hom_of_valuationRing_stalk
    (base := Spec (CommRingCat.of k)) hval genericMap (by
      change genericMap ≫ π ≫ X.hom = _
      rw [← Category.assoc, hgen]; rfl)
  have : IsSeparated (X.left ↘ Spec (CommRingCat.of k)) := inferInstanceAs (IsSeparated X.hom)
  have : IsDominant X.left.fromSpecFunctionField := isDominant_fromSpecFunctionField X.left
  have hgπ : g ≫ π = 𝟙 X.left := by
    have : (g ≫ π).IsOver (Spec (CommRingCat.of k)) := ⟨by
      change (g ≫ π) ≫ X.hom = X.hom
      rw [Category.assoc]; exact hgo.comp_over⟩
    refine ext_of_isDominant_of_isSeparated' (Spec (CommRingCat.of k))
      X.left.fromSpecFunctionField ?_
    rw [← Category.assoc, hg, hgen, Category.comp_id]
  have : IsClosedImmersion g := by
    have : IsClosedImmersion (g ≫ π) := by rw [hgπ]; infer_instance
    exact IsClosedImmersion.of_comp g π
  refine ⟨n, hn, g ≫ ι, inferInstance, ?_⟩
  rw [Category.assoc, hcomm, ← Category.assoc, hgπ, Category.id_comp]

end JavanpeykarFix

#print axioms JavanpeykarFix.exists_closedImmersion_projectiveSpace
