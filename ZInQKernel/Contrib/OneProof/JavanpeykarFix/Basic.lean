import ZInQKernel.Contrib.OneProof.JavanpeykarDict
import ZInQKernel.Contrib.OneProof.HeightDictionary
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.RepresentedBaseChange
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.AbelianVariety.BaseChange
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ChowLemma
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Birational.ValuativeExtension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Affine

/-! # javanpeykar-fix (part 1): the restated leaves and the reduction

Task javanpeykar-fix (2026-11-16), report `docs/research/javanpeykar-fix.md`, scratch
`scratch/javanpeykar-fix/`.

* §1 `fullConstantField_of_bijective`, the leaf `ConstantFieldExtensionUnramifiedFull` (Stichtenoth with
  his standing hypothesis that `K` is the full constant field of `F`), `belyiBaseChange_of_full`;
* §2 `exists_jacBar`: `V_K̄ ≅ Jac(X_K̄)` (`V` a tensor-compatible `Pic⁰_{X/K}`, `Jac(X_K̄)` a
  tensor-compatible `Pic⁰_{X_K̄/K̄}`), from the vendored `PicardTensorCompatible.baseChangeIso`;
* §3 `exists_closedImmersion_projectiveSpace`: a smooth proper integral curve over a field is projective
  (Chow's lemma and the valuative extension of rational maps, both vendored);
* §4 `ℙ¹ = Proj k[X₀, X₁]`, `IsBelyiMap` (a finite morphism to `ℙ¹`, unramified over
  `ℙ¹ ∖ {0, 1, ∞}`, of degree `d`), the leaf `JavanpeykarPrintedMap`, the glue `BelyiMapOfFunction`
  and the reduction `javanpeykarBound_of_map`.

No `sorry`, no `axiom`. -/

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


/-! ## §3 Projectivity -/


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



/-! ## §4 Belyi maps, the restated leaf and the reduction -/

section BelyiMaps

open CategoryTheory AlgebraicGeometry Limits

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `ℙ¹_k = Proj k[X₀, X₁]` (Mathlib's `Proj` of the polynomial ring graded by total degree; vendored
`Proj.projectiveSpaceOverAffine`). The affine coordinate is `X₀/X₁`. -/
abbrev P1 (k : Type) [Field k] : Scheme := Proj.projectiveSpaceOverAffine (Fin 2) k

/-- The structure morphism `ℙ¹_k → Spec k`. -/
def P1.toSpec (k : Type) [Field k] : P1 k ⟶ Spec (CommRingCat.of k) :=
  Proj.projectiveSpaceOverAffineToSpec (Fin 2) k

/-- `ℙ¹ ∖ {0, 1, ∞} = D₊(X₀ X₁ (X₀ − X₁))` (`0 = [0 : 1]`, `1 = [1 : 1]`, `∞ = [1 : 0]`). -/
def P1.threePointsCompl (k : Type) [Field k] : (P1 k).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (MvPolynomial.X 0 * MvPolynomial.X 1 * (MvPolynomial.X 0 - MvPolynomial.X 1))

/-- **A Belyi map of degree `d`** of an integral `k`-scheme `C` (Javanpeykar 2014 §1; Hartshorne
II.6.8 and IV.2 for the degree and the ramification index): a morphism `β : C → ℙ¹_k` over `k`
which is finite, unramified at every closed point over `ℙ¹ ∖ {0, 1, ∞}` (ramification index `1`:
the maximal ideal of `𝒪_{ℙ¹, β(x)}` generates that of `𝒪_{C, x}`, Hartshorne IV.2:
`e_x = v_x(β^♯ u)` for a local parameter `u` at `β(x)`), and of degree
`d = [k(C) : k(ℙ¹)]` (the stalk map at the generic point; Hartshorne II.6.8). -/
def IsBelyiMap {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    (β : C.left ⟶ P1 k) (d : ℕ) : Prop :=
  β ≫ P1.toSpec k = C.hom ∧ IsFinite β ∧
  (∀ x : C.left, IsClosed ({x} : Set C.left) → β x ∈ P1.threePointsCompl k →
    Ideal.map (β.stalkMap x).hom (IsLocalRing.maximalIdeal ((P1 k).presheaf.stalk (β x))) =
      IsLocalRing.maximalIdeal (C.left.presheaf.stalk x)) ∧
  @Module.finrank ((P1 k).presheaf.stalk (β (genericPoint C.left))) C.left.functionField _ _
    (β.stalkMap (genericPoint C.left)).hom.toModule = d

open LeafModCurves (IsCurve IsBelyiFunction)
open ZInQ.LeafPush2 (ffAlgebra javanpeykarBound)

/-- **Leaf R18-Javanpeykar, printed form** (A. Javanpeykar, *Polynomial bounds for Arakelov invariants
of Belyi curves*, Algebra Number Theory 8 (2014), Thm 1.1.1, p. 90; arXiv:1403.6404v1 p. 1; height
p. 98 / arXiv §2.3; read by the locator audit, docs/research/locators.md). Printed: for a smooth
projective connected curve `X/ℚ̄` of genus `g ≥ 1`, `h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`, where
`h_Fal(X)` is the stable Faltings height of `Jac(X)` and `deg_B(X)` the least degree of a finite
morphism `X → ℙ¹_ℚ̄` unramified over `ℙ¹ ∖ {0, 1, ∞}`.

Stated for `X = X₀ ×_K ℚ̄` (`X₀` a smooth proper geometrically connected curve over a number field
`K`, `ℚ̄ = AlgebraicClosure K`), each object in the print's terms:
* `X` smooth (base change), connected (`X₀` geometrically connected), projective (a closed immersion
  into a projective space over `ℚ̄`, hypothesis);
* `Jac(X)`: `W`, an abelian variety over `ℚ̄` representing the degree-zero Picard functor of `X` with
  the tensor-product group law (vendored Jacobian-Challenge `picardFunctorDegree`,
  `PicardTensorCompatible`);
* `h_Fal(Jac X)`: the printed stable height (`ZInQ.HeightDict.IsPrintedStableHeight`, height-dict) of
  a model `V` of `W` over `K` (`V_ℚ̄ ≅ W`); the stable height of an abelian variety over `ℚ̄` is that of
  any model over a number field;
* `g = genusBar X₀ = dim H¹(X, 𝒪_X)`;
* a Belyi map `β : X → ℙ¹_ℚ̄` of degree `d` (`IsBelyiMap`), so `deg_B(X) ≤ d`; the bound is increasing
  in `deg_B`. -/
def JavanpeykarPrintedMap : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : Over (Spec (CommRingCat.of K))) [IsCurve X]
    [IsIntegral (baseChangeCurve X (AlgebraicClosure K)).left],
    (∃ (n : Type) (_ : Finite n)
      (i : (baseChangeCurve X (AlgebraicClosure K)).left ⟶
        ℙ(n; Spec (CommRingCat.of (AlgebraicClosure K)))),
      IsClosedImmersion i ∧ i ≫ ℙ(n; Spec (CommRingCat.of (AlgebraicClosure K))) ↘
        Spec (CommRingCat.of (AlgebraicClosure K)) = (baseChangeCurve X (AlgebraicClosure K)).hom) →
    ∀ (W : AbelianVariety (AlgebraicClosure K))
      (repW : (picardFunctorDegree (baseChangeCurve X (AlgebraicClosure K)).hom 0).obj.RepresentableBy
        W.group.X),
      PicardTensorCompatible (baseChangeCurve X (AlgebraicClosure K)).hom W.group repW →
    ∀ V : AbelianVariety K, Nonempty ((AbelianVariety.baseChange K (AlgebraicClosure K)).obj V ≅ W) →
    1 ≤ genusBar X →
    ∀ (β : (baseChangeCurve X (AlgebraicClosure K)).left ⟶ P1 (AlgebraicClosure K)) (d : ℕ),
      IsBelyiMap (baseChangeCurve X (AlgebraicClosure K)) β d → 0 < d →
    ∀ x : ℝ, ZInQ.HeightDict.IsPrintedStableHeight (ofVendored V) x → x ≤ javanpeykarBound (genusBar X) d

/-- **Glue (step (b)): a Belyi function gives a Belyi map** (Hartshorne I.6.8 / II.6.8: a nonconstant
rational function on a smooth proper curve extends to a finite morphism to `ℙ¹` of degree
`[k(C) : k(t)]`; Hartshorne IV.2 for the ramification index). For a smooth proper integral curve `C`
over an algebraically closed field `k` of characteristic `0` and a Belyi function `t ∈ k(C)` over `k`
with `[k(C) : k(t)] = d > 0`, there is a Belyi map `C → ℙ¹_k` of degree `d`. -/
def BelyiMapOfFunction : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (C : Over (Spec (CommRingCat.of k)))
    [IsIntegral C.left] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (t : C.left.functionField),
    letI := ffAlgebra C
    IsBelyiFunction k C.left.functionField t →
    ∀ d : ℕ, Module.finrank (IntermediateField.adjoin k {t}) C.left.functionField = d → 0 < d →
    ∃ β : C.left ⟶ P1 k, IsBelyiMap C β d

/-- **The old field from the restated leaves** (steps (a)-(d) and the Stichtenoth restatement):
`JavanpeykarBound` from `JavanpeykarPrintedMap`, `ConstantFieldExtensionUnramifiedFull`, the glue
`BelyiMapOfFunction` and the textbook fields `uniformizationLeafAll`, `mumfordTorsionAlgClosed`
(which give T35, used by height-dict's `isPrintedStableHeight_of`). -/
theorem javanpeykarBound_of_map (hJ : JavanpeykarPrintedMap) (hS : ConstantFieldExtensionUnramifiedFull)
    (hM : BelyiMapOfFunction) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : ZInQ.HeightSplit.JavanpeykarBound := by
  intro K _ _ X _ _ P₀ J aj hJac g hg hg1 t ht d hd hd0 x hx
  have hX : IsCurve X := inferInstance
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  letI : X.left.Over (Spec (CommRingCat.of K)) := ⟨X.hom⟩
  have : SmoothOfRelativeDimension 1 (X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  have : IsProper (X.left ↘ Spec (CommRingCat.of K)) := inferInstanceAs (IsProper X.hom)
  have : GeometricallyIntegral (X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (GeometricallyIntegral X.hom)
  -- (1) the kernel Jacobian is `Pic⁰`, (a) the printed height
  obtain ⟨V, rep, htc, -⟩ := exists_abelianVariety_picardDegreeZero (baseField := K) X.left
  obtain ⟨e, he⟩ := abVarIso_picZero_of_isJacobian hX hJac V rep htc
  have hx' : ZInQ.HeightDict.IsPrintedStableHeight (ofVendored V) x :=
    ZInQ.HeightDict.isPrintedStableHeight_of
      (ZInQ.HeightGlue.analyticUniformizationUnique_of_t35 (AvSplit.Final.h38 hUL hMT))
      (ZInQ.HeightGlue.uniformizationDim_of_t35 (AvSplit.Final.h38 hUL hMT))
      (isStableFaltingsHeight_of_iso e hx)
  -- (2) `g` is the genus of `X_K̄`
  have hgen : g = genusBar X := by
    have h2 := dim_eq_genusK hX hJac
    rw [hg] at h2
    rw [genusBar_eq hX]
    exact_mod_cast h2
  subst hgen
  -- (3) Stichtenoth: a Belyi function of `X_K̄` over `K̄`
  obtain ⟨hint, t', ht', hd'⟩ := belyiBaseChange_of_full hS K X t ht d hd hd0
  -- (b) the Belyi map
  have : IsProper (baseChangeCurve X (AlgebraicClosure K)).hom :=
    inferInstanceAs (IsProper ((AlgebraicGeometry.baseChange K (AlgebraicClosure K)).obj X).hom)
  have : SmoothOfRelativeDimension 1 (baseChangeCurve X (AlgebraicClosure K)).hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1
      ((AlgebraicGeometry.baseChange K (AlgebraicClosure K)).obj X).hom)
  obtain ⟨β, hβ⟩ := hM (AlgebraicClosure K) (baseChangeCurve X (AlgebraicClosure K)) t' ht' d hd' hd0
  -- (c) `X_K̄` is projective
  have hproj := exists_closedImmersion_projectiveSpace (baseChangeCurve X (AlgebraicClosure K))
  -- (d) `V_K̄ = Jac(X_K̄)`
  obtain ⟨W, repW, htcW, hVW⟩ := exists_jacBar X hX V rep htc (AlgebraicClosure K)
  exact hJ K X hproj W repW htcW V hVW hg1 β d hβ hd0 x hx'

end BelyiMaps

end JavanpeykarFix
