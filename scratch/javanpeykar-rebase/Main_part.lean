
/-! ## §2. The restated Javanpeykar leaf and the reduction -/

section Printed

open CategoryTheory AlgebraicGeometry Limits
open JavanpeykarDict JavanpeykarFix
open LeafModCurves (IsCurve IsBelyiFunction)
open ZInQ.LeafPush2 (ffAlgebra javanpeykarBound)

/-- **Leaf R18-Javanpeykar, printed form, over height-fix's printed stable height** (A. Javanpeykar,
*Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014),
Thm 1.1.1, p. 90; height identification p. 98 (arXiv:1403.6404v1 §2.3); locators recorded by the
locator audit, docs/research/locators.md row R18; no statement check recorded). Printed: for a smooth
projective connected curve `X/ℚ̄` of genus `g ≥ 1`, `h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`, where
`h_Fal(X)` is the stable Faltings height of `Jac(X)` and `deg_B(X)` the least degree of a finite
morphism `X → ℙ¹_ℚ̄` unramified over `ℙ¹ ∖ {0, 1, ∞}`.

This is `JavanpeykarFix.JavanpeykarPrintedMap` (javanpeykar-fix) verbatim, with height-dict's
`ZInQ.HeightDict.IsPrintedStableHeight` replaced by height-fix's `ZInQ.HeightFix.IsPrintedStableHeight`
(sound archimedean metric: the measure `(i/2)^g η ∧ η̄`, defined chart by chart, must exist; Néron
model over a field of semistable reduction read over the residue fields `k(𝔭)`, SGA 7 IX 2.2/3.2).
Stated for `X = X₀ ×_K ℚ̄` (`X₀` a smooth proper geometrically connected curve over a number field
`K`, `ℚ̄ = AlgebraicClosure K`):
* `X` smooth, connected, projective (a closed immersion into `ℙ(n; Spec ℚ̄)`, hypothesis);
* `Jac(X)`: `W`, an abelian variety over `ℚ̄` representing the degree-zero Picard functor of `X` with
  the tensor-product group law;
* `h_Fal(Jac X)`: the printed stable height of a model `V` of `W` over `K` (`V_ℚ̄ ≅ W`);
* `g = genusBar X₀ = dim H¹(X, 𝒪_X)`;
* a Belyi map `β : X → ℙ¹_ℚ̄ = Proj ℚ̄[X₀, X₁]` of degree `d` (`IsBelyiMap`), so `deg_B(X) ≤ d`; the
  bound is increasing in `deg_B`. -/
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
    ∀ x : ℝ, ZInQ.HeightFix.IsPrintedStableHeight (ofVendored V) x → x ≤ javanpeykarBound (genusBar X) d

/-- **The new leaf is never stronger than javanpeykar-fix's** (given T35 and Stacks 04KV): a height-fix
printed height is a kernel height (`ZInQ.HeightFix.isStableFaltingsHeight_of_printed`), hence a
height-dict printed height (`ZInQ.HeightDict.isPrintedStableHeight_of`). -/
theorem javanpeykarPrintedMap_of_fix (h : JavanpeykarFix.JavanpeykarPrintedMap)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) (hGC : AVGlue.GeomConnOfRationalPoint) :
    JavanpeykarPrintedMap := by
  intro K _ _ X _ _ hproj W repW htcW V hVW hg1 β d hβ hd0 x hx
  exact h K X hproj W repW htcW V hVW hg1 β d hβ hd0 x
    (ZInQ.HeightDict.isPrintedStableHeight_of
      (ZInQ.HeightGlue.analyticUniformizationUnique_of_t35 hT35)
      (ZInQ.HeightGlue.uniformizationDim_of_t35 hT35)
      (ZInQ.HeightFix.isStableFaltingsHeight_of_printed hT35 hGC hx))

/-- **`JavanpeykarBound` from the restated leaves.** Steps: (1) the kernel Jacobian is `Pic⁰`
(javanpeykar-dict); (a) kernel height ⇒ height-fix printed height (`isPrintedStableHeight_of`, T35
from `uniformizationLeafAll`, `mumfordTorsionAlgClosed`, and the glue `SemiAbelianDescendsPerfect`);
(2) `g` is the genus of `X_K̄`; (3) Stichtenoth (finite form, `full_of_finite`) with the full constant
field proved; (b) Belyi function to Belyi map (`belyiMapOfFunction_proof`); (c) projectivity;
(d) `V_K̄ = Jac(X_K̄)`. -/
theorem javanpeykarBound_of_printed_rebase (hJ : JavanpeykarPrintedMap)
    (hS : ConstantFieldExtensionUnramifiedFinite)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) (hD : ZInQ.HeightFix.SemiAbelianDescendsPerfect) :
    ZInQ.HeightSplit.JavanpeykarBound := by
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
  -- (1) the kernel Jacobian is `Pic⁰`; (a) the height-fix printed height
  obtain ⟨V, rep, htc, -⟩ := exists_abelianVariety_picardDegreeZero (baseField := K) X.left
  obtain ⟨e, he⟩ := abVarIso_picZero_of_isJacobian hX hJac V rep htc
  have hx' : ZInQ.HeightFix.IsPrintedStableHeight (ofVendored V) x :=
    ZInQ.HeightFix.isPrintedStableHeight_of (AvSplit.Final.h38 hUL hMT) hD
      (isStableFaltingsHeight_of_iso e hx)
  -- (2) `g` is the genus of `X_K̄`
  have hgen : g = genusBar X := by
    have h2 := dim_eq_genusK hX hJac
    rw [hg] at h2
    rw [genusBar_eq hX]
    exact_mod_cast h2
  subst hgen
  -- (3) Stichtenoth, finite form: a Belyi function of `X_K̄` over `K̄`
  obtain ⟨hint, t', ht', hd'⟩ := belyiBaseChange_of_full (full_of_finite hS) K X t ht d hd hd0
  -- (b) the Belyi map
  have : IsProper (baseChangeCurve X (AlgebraicClosure K)).hom :=
    inferInstanceAs (IsProper ((AlgebraicGeometry.baseChange K (AlgebraicClosure K)).obj X).hom)
  have : SmoothOfRelativeDimension 1 (baseChangeCurve X (AlgebraicClosure K)).hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1
      ((AlgebraicGeometry.baseChange K (AlgebraicClosure K)).obj X).hom)
  obtain ⟨β, hβ⟩ := belyiMapOfFunction_proof (AlgebraicClosure K)
    (baseChangeCurve X (AlgebraicClosure K)) t' ht' d hd' hd0
  -- (c) `X_K̄` is projective
  have hproj := exists_closedImmersion_projectiveSpace (baseChangeCurve X (AlgebraicClosure K))
  -- (d) `V_K̄ = Jac(X_K̄)`
  obtain ⟨W, repW, htcW, hVW⟩ := exists_jacBar X hX V rep htc (AlgebraicClosure K)
  exact hJ K X hproj W repW htcW V hVW hg1 β d hβ hd0 x hx'

end Printed
