import ZInQKernel.Contrib.OneProof.JavanpeykarDict
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.RepresentedBaseChange
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.AbelianVariety.BaseChange

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped TensorProduct

namespace JavanpeykarFix

open JavanpeykarDict

/-! ## Full constant field from `F ⊗_K L ≅ FL`, `L` algebraically closed -/

section Full

variable {K F L FL : Type} [Field K] [Field F] [Field L] [Field FL] [Algebra K F] [Algebra K L]
  [Algebra L FL] [Algebra K FL] [IsScalarTower K L FL]

theorem fullConstantField_of_bijective [IsAlgClosed L] (ι : F →ₐ[K] FL)
    (hbij : Function.Bijective (Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL)))
    (a : F) (ha : IsAlgebraic K a) : a ∈ Set.range (algebraMap K F) := by
  classical
  -- `ι a` is algebraic over `L`, hence in `L`
  have hL : IsAlgebraic L (ι a) := by
    have h1 : IsAlgebraic K (ι a) := (isAlgebraic_algHom_iff ι ι.injective).mpr ha
    exact h1.extendScalars (algebraMap K L).injective
  have hint : IsIntegral L (ι a) := hL.isIntegral
  have hdeg : (minpoly L (ι a)).natDegree = 1 := by
    have hirr := minpoly.irreducible hint
    have := IsAlgClosed.degree_eq_one_of_irreducible L hirr
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp hdeg
  -- `a ⊗ 1 = 1 ⊗ c`
  have heq : a ⊗ₜ[K] (1 : L) = (1 : F) ⊗ₜ[K] c := by
    apply hbij.1
    simp only [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, one_mul,
      IsScalarTower.coe_toAlgHom']
    exact hc.symm
  by_contra hna
  have hnm : a ∉ (Submodule.span K {(1 : F)}) := by
    intro hm
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hm
    exact hna ⟨k, by rw [← hk, Algebra.smul_def, mul_one]⟩
  obtain ⟨f, hfa, hf1⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnm inferInstance
  have hf1' : f 1 = 0 := by
    have : f 1 ∈ (Submodule.span K {(1 : F)}).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span rfl)
    rw [hf1] at this
    exact this
  have := congrArg (fun z => TensorProduct.lid K L (TensorProduct.map f LinearMap.id z)) heq
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul, hf1',
    zero_smul] at this
  exact hfa (by simpa using this)

end Full

/-- **Leaf: a constant field extension of an algebraic function field is unramified**, with
Stichtenoth's standing hypothesis that `K` is the full constant field of `F`. -/
def ConstantFieldExtensionUnramifiedFull : Prop :=
  ∀ (K F L FL : Type) [Field K] [Field F] [Field L] [Field FL] [Algebra K F] [Algebra K L]
    [Algebra L FL] [Algebra K FL] [IsScalarTower K L FL] [CharZero K] [Algebra.IsAlgebraic K L]
    (ι : F →ₐ[K] FL),
    (∃ t : F, Transcendental K t ∧ FiniteDimensional (IntermediateField.adjoin K {t}) F) →
    (∀ a : F, IsAlgebraic K a → a ∈ Set.range (algebraMap K F)) →
    Function.Bijective (Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL)) →
    ∀ w : ValuationSubring FL, (∀ c : L, algebraMap L FL c ∈ w) → ∀ π : F,
      π ∈ (w.comap (ι : F →+* FL)).nonunits →
      (∀ x ∈ (w.comap (ι : F →+* FL)).nonunits, ∃ y ∈ w.comap (ι : F →+* FL), x = π * y) →
      ∀ x ∈ w.nonunits, ∃ y ∈ w, x = ι π * y

theorem isBelyiFunction_baseChange_full (hS : ConstantFieldExtensionUnramifiedFull)
    {K F L FL : Type} [Field K] [Field F] [Field L] [Field FL] [Algebra K F] [Algebra K L]
    [Algebra L FL] [Algebra K FL] [IsScalarTower K L FL] [CharZero K] [IsAlgClosed L]
    [Algebra.IsAlgebraic K L] (ι : F →ₐ[K] FL)
    (hbij : Function.Bijective (Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL)))
    (t : F) (hB : LeafModCurves.IsBelyiFunction K F t) (d : ℕ)
    (hd : Module.finrank (IntermediateField.adjoin K {t}) F = d) (hd0 : 0 < d) :
    LeafModCurves.IsBelyiFunction L FL (ι t) ∧
      Module.finrank (IntermediateField.adjoin L {ι t}) FL = d := by
  haveI : FiniteDimensional (IntermediateField.adjoin K {t}) F :=
    Module.finite_of_finrank_pos (hd ▸ hd0)
  refine ⟨⟨transcendental_ι ι t hB.1, belyi_unram ι t hB.2 ?_⟩, ?_⟩
  · exact hS K F L FL ι ⟨t, hB.1, inferInstance⟩ (fullConstantField_of_bijective ι hbij) hbij
  · rw [finrank_adjoin_eq ι hbij t, hd]

open CategoryTheory AlgebraicGeometry Limits in
/-- **`BelyiBaseChange` from Stichtenoth's theorem with the full-constant-field hypothesis.** -/
theorem belyiBaseChange_of_full (hS : ConstantFieldExtensionUnramifiedFull) : BelyiBaseChange := by
  intro K _ _ X hX _ t ht d hd hd0
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  haveI hint : IsIntegral (baseChangeCurve X (AlgebraicClosure K)).left :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (isPullback_pr X (AlgebraicClosure K))
  obtain ⟨ι, hbij⟩ := functionField_baseChange X (AlgebraicClosure K)
  letI := ZInQ.LeafPush2.ffAlgebra X
  letI := ZInQ.LeafPush2.ffAlgebra (baseChangeCurve X (AlgebraicClosure K))
  letI iKM : Algebra K (baseChangeCurve X (AlgebraicClosure K)).left.functionField :=
    ((algebraMap (AlgebraicClosure K) _).comp (algebraMap K (AlgebraicClosure K))).toAlgebra
  haveI : IsScalarTower K (AlgebraicClosure K)
      (baseChangeCurve X (AlgebraicClosure K)).left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨h1, h2⟩ := isBelyiFunction_baseChange_full hS ι hbij t ht d hd hd0
  exact ⟨hint, ι t, h1, h2⟩

/-! ## `V_K̄ = Jac(X_K̄)` -/

section JacBar

open CategoryTheory AlgebraicGeometry Limits
open LeafModCurves (IsCurve)

/-- **`V_L` is the Jacobian of `X_L` (glue, proved).** For a tensor-compatible representative `V`
of `Pic⁰_{X/K}` and any field extension `L/K`, there is a tensor-compatible representative `W` of
`Pic⁰_{X_L/L}` with `V_L ≅ W` as abelian varieties (vendored `exists_abelianVariety_picardDegreeZero`
over `L` and `PicardTensorCompatible.baseChangeIso`). -/
theorem exists_jacBar {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K))) (hX : IsCurve X)
    (V : AbelianVariety K) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X)
    (htc : PicardTensorCompatible X.hom V.group rep) (L : Type) [Field L] [Algebra K L] :
    ∃ (W : AbelianVariety L)
      (repW : (picardFunctorDegree (baseChangeCurve X L).hom 0).obj.RepresentableBy W.group.X),
      PicardTensorCompatible (baseChangeCurve X L).hom W.group repW ∧
      Nonempty ((AbelianVariety.baseChange K L).obj V ≅ W) := by
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  let C : Curve K := ⟨X⟩
  let CL : Curve L := (Curve.baseChange K L).obj C
  letI : CL.carrier.left.Over (Spec (CommRingCat.of L)) := ⟨CL.carrier.hom⟩
  have : SmoothOfRelativeDimension 1 (CL.carrier.left ↘ Spec (CommRingCat.of L)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 CL.carrier.hom)
  have : IsProper (CL.carrier.left ↘ Spec (CommRingCat.of L)) :=
    inferInstanceAs (IsProper CL.carrier.hom)
  have : Smooth CL.carrier.hom := SmoothOfRelativeDimension.smooth 1 CL.carrier.hom
  have : GeometricallyIntegral (CL.carrier.left ↘ Spec (CommRingCat.of L)) :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral CL.carrier.hom
  obtain ⟨W, repW, htcW, -⟩ := exists_abelianVariety_picardDegreeZero (baseField := L) CL.carrier.left
  exact ⟨W, repW, htcW,
    ⟨InducedCategory.isoMk (F := AbelianVariety.group)
      (PicardTensorCompatible.baseChangeIso (curve := C) htc htcW)⟩⟩

end JacBar

end JavanpeykarFix

#print axioms JavanpeykarFix.exists_jacBar
#print axioms JavanpeykarFix.belyiBaseChange_of_full
