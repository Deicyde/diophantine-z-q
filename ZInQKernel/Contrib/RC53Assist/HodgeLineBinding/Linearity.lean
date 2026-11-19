import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.Binding
import ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.ComplexDifferentialLine

/-!
# Linearity of the evaluation in the Hodge line, and the regular line

The isomorphism `originStalkEquiv : 𝒪_{𝒢,ξ} ≅ 𝒪_{A_L,o}` is compatible with the constants: it
sends `structMap c` (the image of `c ∈ 𝓞_L` under `𝓞_L → Γ(𝒢) → 𝒪_{𝒢,ξ}`) to the constant
`c ∈ L ⊆ 𝒪_{A_L,o}` (`originStalkEquiv_structMap`), because the projection of the generic fibre
and `𝒢.gen` are morphisms over `Spec 𝓞_L` and `Spec L`. Consequently `toModelCotangent` is
`𝓞_L`-linear and the evaluation in the Hodge line is `L`-linear (`hodgeEvalLinear`), since
`L` is the fraction field of `𝓞_L`.

The regular K��hler line of the Weierstrass curve (the constant multiples of the invariant
differential `ω`) is carried into the differentials regular at the origin by the Kähler transport
along `e`, and its evaluation in the Hodge line is `c • ω ↦ c • 𝒢.wedge ![f]`
(`hodgeEval_regularKaehler`). In particular the comparison is injective on the regular line.

Locator: EGA I, 3.6.5; Silverman, *The Arithmetic of Elliptic Curves*, second edition, III.1.5.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLineBinding

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing KaehlerDifferential
open TensorProduct
open ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice
open ZInQ.Contrib.RC53Assist.S2aNumberField
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra stalkAlgebra
  stalk_functionField_tower abelian_scheme_integral)

section Germs

/-- THEOREM (proved). The stalk map sends the germ of a global section to the germ of its
pull-back. Locator: Mathlib, `Scheme.Hom.germ_stalkMap_apply`. -/
theorem stalkMap_germ_top {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) (s : Γ(Y, ⊤)) :
    f.stalkMap x (Y.presheaf.germ ⊤ (f x) trivial s) = X.presheaf.germ ⊤ x trivial (f.appTop s) :=
  Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial s

/-- THEOREM (proved). The identification of stalks at equal points sends germs to germs.
Locator: Mathlib, `TopCat.Presheaf.germ_stalkSpecializes`. -/
theorem stalkCongr_germ_top {X : Scheme.{0}} {x y : X} (h : Inseparable x y) (s : Γ(X, ⊤)) :
    (X.presheaf.stalkCongr h).hom (X.presheaf.germ ⊤ x trivial s) =
      X.presheaf.germ ⊤ y trivial s := by
  have h1 := ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes X.presheaf
    (U := ⊤) (TopologicalSpace.Opens.mem_top x) h.ge) s
  rw [ConcreteCategory.comp_apply] at h1
  exact h1

end Germs

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- THEOREM (proved). The defining property of `originStalkEquiv`: after the stalk map of
`𝒢.gen` it is the stalk map of the projection of the generic fibre. Locator: `originStalkEquiv`. -/
theorem originStalkEquiv_spec (G : GroupModel E L) (a : G.genStalk) :
    G.gen.hom.left.stalkMap (genericFibreUnit G)
      (((E.baseChange L).X.left.presheaf.stalkCongr
        (Inseparable.of_eq (gen_genericFibreUnit_eq G).symm)).hom (originStalkEquiv G a)) =
    (pullback.fst G.G.hom (toGeneric L)).stalkMap (genericFibreUnit G)
      ((G.G.left.presheaf.stalkCongr (Inseparable.of_eq (fst_genericFibreUnit G).symm)).hom a) := by
  haveI hp : IsIso ((pullback.fst G.G.hom (toGeneric L)).stalkMap (genericFibreUnit G)) :=
    genericFibreStalkIso L G.G _
  haveI hφ : IsOpenImmersion ((Over.forget _).mapIso G.gen).hom := inferInstance
  haveI hφs : IsIso (((Over.forget _).mapIso G.gen).hom.stalkMap (genericFibreUnit G)) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp hφ).2 _
  let e1 : G.genStalk ≅ (genericFibre L G.G).left.presheaf.stalk (genericFibreUnit G) :=
    G.G.left.presheaf.stalkCongr (Inseparable.of_eq (fst_genericFibreUnit G).symm) ≪≫
      @asIso _ _ _ _ _ hp
  let e2 : (E.baseChange L).X.left.presheaf.stalk (identityPoint (E.baseChange L).X) ≅
      (genericFibre L G.G).left.presheaf.stalk (genericFibreUnit G) :=
    (E.baseChange L).X.left.presheaf.stalkCongr
        (Inseparable.of_eq (gen_genericFibreUnit_eq G).symm) ≪≫
      @asIso _ _ _ _ _ hφs
  have h : originStalkEquiv G a =
      e2.commRingCatIsoToRingEquiv.symm (e1.commRingCatIsoToRingEquiv a) := rfl
  rw [h]
  exact e2.commRingCatIsoToRingEquiv.apply_symm_apply (e1.commRingCatIsoToRingEquiv a)

/-- THEOREM (proved). **Compatibility with the constants**: `originStalkEquiv` sends the image of
`c ∈ 𝓞_L` in `𝒪_{𝒢,ξ}` to the constant `c ∈ L` of `𝒪_{A_L,o}`. The projection of the generic
fibre is a morphism over `Spec 𝓞_L` (the pullback square) and `𝒢.gen` is a morphism over
`Spec L`. Locator: `originStalkEquiv_spec`; Mathlib, `pullback.condition`, `Over.w`,
`Scheme.ΓSpecIso_inv_naturality`. -/
theorem originStalkEquiv_structMap (G : GroupModel E L) (c : 𝓞 L) :
    letI := stalkAlgebra (E.baseChange L).X.hom (identityPoint (E.baseChange L).X)
    originStalkEquiv G (G.structMap c) = algebraMap L _ (algebraMap (𝓞 L) L c) := by
  letI := stalkAlgebra (E.baseChange L).X.hom (identityPoint (E.baseChange L).X)
  haveI hφs : IsIso (G.gen.hom.left.stalkMap (genericFibreUnit G)) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
  have hinj : Function.Injective fun x =>
      G.gen.hom.left.stalkMap (genericFibreUnit G)
        (((E.baseChange L).X.left.presheaf.stalkCongr
          (Inseparable.of_eq (gen_genericFibreUnit_eq G).symm)).hom x) :=
    ((ConcreteCategory.bijective_of_isIso _).1).comp
      ((ConcreteCategory.bijective_of_isIso _).1)
  apply hinj
  dsimp only
  rw [originStalkEquiv_spec]
  have hs : (pullback.fst G.G.hom (toGeneric L)).appTop
      (G.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c)) =
      G.gen.hom.left.appTop ((E.baseChange L).X.hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of L)).inv (algebraMap (𝓞 L) L c))) := by
    have h1 := congrArg (fun m => m.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c))
      (pullback.condition (f := G.G.hom) (g := toGeneric L))
    have h2 := congrArg (fun m => m.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv (algebraMap (𝓞 L) L c))) (Over.w G.gen.hom)
    have h3 := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (𝓞 L) L))) c
    simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] at h1 h2 h3
    rw [h1, ← h3]
    exact h2.symm
  have hl := stalkCongr_germ_top (Inseparable.of_eq (fst_genericFibreUnit G).symm)
    (G.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c))
  have hr := stalkCongr_germ_top (Inseparable.of_eq (gen_genericFibreUnit_eq G).symm)
    ((E.baseChange L).X.hom.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv (algebraMap (𝓞 L) L c)))
  change _ = G.gen.hom.left.stalkMap (genericFibreUnit G)
    (((E.baseChange L).X.left.presheaf.stalkCongr
      (Inseparable.of_eq (gen_genericFibreUnit_eq G).symm)).hom
        ((E.baseChange L).X.left.presheaf.germ ⊤ (identityPoint (E.baseChange L).X) trivial
          ((E.baseChange L).X.hom.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of L)).inv (algebraMap (𝓞 L) L c)))))
  rw [GroupModel.structMap, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_apply,
    RingHom.comp_apply]
  erw [hl, hr, stalkMap_germ_top, stalkMap_germ_top, hs]
  rfl

/-- THEOREM (proved). `toModelCotangent` is `𝓞_L`-linear, `𝓞_L` acting on `𝔪_o/𝔪_o²` through
`𝓞_L ⊆ L` and on `𝒢.cotangent` through `structMap`. Locator: `originStalkEquiv_structMap`. -/
theorem toModelCotangent_smul (G : GroupModel E L) (c : 𝓞 L)
    (m : CotangentSpace
      ((E.baseChange L).X.left.presheaf.stalk (identityPoint (E.baseChange L).X))) :
    letI := stalkAlgebra (E.baseChange L).X.hom (identityPoint (E.baseChange L).X)
    toModelCotangent G (algebraMap (𝓞 L) L c • m) = c • toModelCotangent G m := by
  letI := stalkAlgebra (E.baseChange L).X.hom (identityPoint (E.baseChange L).X)
  obtain ⟨x, rfl⟩ := (maximalIdeal _).toCotangent_surjective m
  set r := algebraMap L ((E.baseChange L).X.left.presheaf.stalk
    (identityPoint (E.baseChange L).X)) (algebraMap (𝓞 L) L c) with hr_def
  have hr : (originStalkEquiv G).symm r = G.structMap c :=
    (RingEquiv.symm_apply_eq _).mpr (originStalkEquiv_structMap G c).symm
  rw [← algebraMap_smul ((E.baseChange L).X.left.presheaf.stalk
    (identityPoint (E.baseChange L).X)) (algebraMap (𝓞 L) L c), ← hr_def, ← map_smul]
  have e1 : toModelCotangent G ((maximalIdeal _).toCotangent (r • x)) =
      G.dCls ⟨(originStalkEquiv G).symm (r * x.1), originStalkEquiv_symm_mem G (r • x).2⟩ :=
    rfl
  have e2 : toModelCotangent G ((maximalIdeal _).toCotangent x) =
      G.dCls ⟨(originStalkEquiv G).symm x.1, originStalkEquiv_symm_mem G x.2⟩ := rfl
  rw [e1, e2]
  change _ = G.structMap c • (maximalIdeal G.genStalk).toCotangent
    ⟨(originStalkEquiv G).symm x.1, originStalkEquiv_symm_mem G x.2⟩
  rw [← map_smul]
  unfold GroupModel.dCls
  congr 1
  ext
  simp only [map_mul, hr, Submodule.coe_smul, smul_eq_mul]

/-- THEOREM (proved). `ι(m) = m` in degree one.
Locator: Mathlib, `exteriorPower.oneEquiv_ιMulti`. -/
theorem ιMulti_single_eq {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (m : M) :
    exteriorPower.ιMulti R 1 ![m] = (exteriorPower.oneEquiv R M).symm m := by
  rw [LinearEquiv.eq_symm_apply, exteriorPower.oneEquiv_ιMulti]
  rfl

/-- THEOREM (proved). `hodgeEval` is the composite of `originValue`, `toModelCotangent`, the
identification `⋀¹ = id` and `n ↦ 1 ⊗ n`. Locator: `ιMulti_single_eq`. -/
theorem hodgeEval_eq (G : GroupModel E L) (hdim : E.dim = 1)
    (η : regularAtOrigin (E.baseChange L)) :
    hodgeEval G hdim η = TensorProduct.mk (𝓞 L) L _ 1 ((exteriorPower.oneEquiv (𝓞 L)
      G.cotangent).symm (toModelCotangent G
        (originValue (E.baseChange L) (baseChange_dim_eq_one hdim) η))) := by
  unfold hodgeEval
  rw [ιMulti_single_eq]
  rfl

/-- THEOREM (proved). `hodgeEval` is additive. Locator: `hodgeEval_eq`. -/
theorem hodgeEval_add (G : GroupModel E L) (hdim : E.dim = 1)
    (η η' : regularAtOrigin (E.baseChange L)) :
    hodgeEval G hdim (η + η') = hodgeEval G hdim η + hodgeEval G hdim η' := by
  rw [hodgeEval_eq, hodgeEval_eq, hodgeEval_eq, map_add, map_add, map_add, map_add]

/-- THEOREM (proved). `hodgeEval` is `𝓞_L`-linear. Locator: `toModelCotangent_smul`. -/
theorem hodgeEval_smul_algebraMap (G : GroupModel E L) (hdim : E.dim = 1) (a : 𝓞 L)
    (η : regularAtOrigin (E.baseChange L)) :
    hodgeEval G hdim (algebraMap (𝓞 L) L a • η) = algebraMap (𝓞 L) L a • hodgeEval G hdim η := by
  letI := stalkAlgebra (E.baseChange L).X.hom (identityPoint (E.baseChange L).X)
  rw [hodgeEval_eq, hodgeEval_eq, map_smul, toModelCotangent_smul, map_smul, map_smul,
    algebraMap_smul]

/-- THEOREM (proved). `hodgeEval` is `L`-linear: `L` is the fraction field of `𝓞_L` and the Hodge
space is an `L`-vector space. Locator: `hodgeEval_smul_algebraMap`; Mathlib,
`IsFractionRing.div_surjective`. -/
theorem hodgeEval_smul (G : GroupModel E L) (hdim : E.dim = 1) (c : L)
    (η : regularAtOrigin (E.baseChange L)) :
    hodgeEval G hdim (c • η) = c • hodgeEval G hdim η := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) c
  have hb0 : algebraMap (𝓞 L) L b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key : algebraMap (𝓞 L) L b • hodgeEval G hdim
      ((algebraMap (𝓞 L) L a / algebraMap (𝓞 L) L b) • η) =
      algebraMap (𝓞 L) L b • ((algebraMap (𝓞 L) L a / algebraMap (𝓞 L) L b) •
        hodgeEval G hdim η) := by
    rw [← hodgeEval_smul_algebraMap, smul_smul, smul_smul, mul_div_cancel₀ _ hb0,
      hodgeEval_smul_algebraMap]
  have h := congrArg (fun z => (algebraMap (𝓞 L) L b)⁻¹ • z) key
  simpa only [inv_smul_smul₀ hb0] using h

/-- DEFINITION. The evaluation in the Hodge line as an `L`-linear map from the differentials
regular at the origin. Locator: `hodgeEval_add`, `hodgeEval_smul`. -/
def hodgeEvalLinear (G : GroupModel E L) (hdim : E.dim = 1) :
    regularAtOrigin (E.baseChange L) →ₗ[L] G.hodgeSpace 1 where
  toFun := hodgeEval G hdim
  map_add' := hodgeEval_add G hdim
  map_smul' := hodgeEval_smul G hdim

/-- THEOREM (proved). **The regular Kähler line.** Every differential `η` of the regular Kähler
line of `E'` (the constant multiples `c • ω`) is carried by the Kähler transport along `e` to a
differential regular at the origin, and its evaluation in the Hodge line is `c • 𝒢.wedge ![f]`.
Locator: `ComplexDifferentialLine.mem_regularKaehler_iff`, `hodgeEval_invariantDifferential`,
`hodgeEval_smul`. -/
theorem hodgeEval_regularKaehler (G : GroupModel E L) (hdim : E.dim = 1)
    (E' : WeierstrassCurve L) [E'.IsElliptic]
    (e : letI := abelian_scheme_integral (E.baseChange L).X
      letI := functionFieldAlgebra (E.baseChange L).X.hom
      E'.toAffine.FunctionField ≃ₐ[L] (E.baseChange L).X.left.functionField)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hfield : letI := abelian_scheme_integral (E.baseChange L).X
      i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E')
    (η : Ω[E'.toAffine.FunctionField⁄L])
    (hη : η ∈ AbelianCurveInputs.ComplexDifferentialLine.regularKaehlerSubmodule E'.toAffine) :
    letI := abelian_scheme_integral (E.baseChange L).X
    letI := functionFieldAlgebra (E.baseChange L).X.hom
    ∃ (c : L) (hreg : kaehlerTransport e η ∈ regularAtOrigin (E.baseChange L)),
      c • WeierstrassCurve.Affine.invariantDifferential E'.toAffine = η ∧
      hodgeEval G hdim ⟨_, hreg⟩ = c • G.wedge ![originParameter G E' i hO] := by
  haveI := abelian_scheme_integral (E.baseChange L).X
  letI := functionFieldAlgebra (E.baseChange L).X.hom
  obtain ⟨c, hc, -⟩ :=
    (AbelianCurveInputs.ComplexDifferentialLine.mem_regularKaehler_iff E'.toAffine η).mp hη
  obtain ⟨hreg, heval, -⟩ := hodgeEval_invariantDifferential G hdim E' e i hfield hO
  have hT : kaehlerTransport e η =
      c • kaehlerTransport e (WeierstrassCurve.Affine.invariantDifferential E'.toAffine) := by
    rw [← hc, map_smul]
  have hmem : kaehlerTransport e η ∈ regularAtOrigin (E.baseChange L) := by
    rw [hT]
    exact Submodule.smul_mem _ c hreg
  refine ⟨c, hmem, hc, ?_⟩
  have hsub : (⟨_, hmem⟩ : regularAtOrigin (E.baseChange L)) = c • ⟨_, hreg⟩ := Subtype.ext hT
  rw [hsub, hodgeEval_smul, heval]

/-- THEOREM (proved). The comparison is injective on the regular Kähler line: a differential of
the line whose evaluation in the Hodge line vanishes is zero. Locator: `hodgeEval_regularKaehler`,
`wedge_originParameter_ne_zero`. -/
theorem eq_zero_of_hodgeEval_eq_zero (G : GroupModel E L) (hdim : E.dim = 1)
    (E' : WeierstrassCurve L) [E'.IsElliptic]
    (e : letI := abelian_scheme_integral (E.baseChange L).X
      letI := functionFieldAlgebra (E.baseChange L).X.hom
      E'.toAffine.FunctionField ≃ₐ[L] (E.baseChange L).X.left.functionField)
    (i : (E.baseChange L).X.left ≅ Proj E'.toProjective.grading)
    (hfield : letI := abelian_scheme_integral (E.baseChange L).X
      i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom)
    (hO : i.hom (identityPoint (E.baseChange L).X) = pointO E')
    (η : Ω[E'.toAffine.FunctionField⁄L])
    (hη : η ∈ AbelianCurveInputs.ComplexDifferentialLine.regularKaehlerSubmodule E'.toAffine)
    (hreg : letI := abelian_scheme_integral (E.baseChange L).X
      letI := functionFieldAlgebra (E.baseChange L).X.hom
      kaehlerTransport e η ∈ regularAtOrigin (E.baseChange L))
    (h0 : hodgeEval G hdim ⟨_, hreg⟩ = 0) : η = 0 := by
  obtain ⟨c, hreg', hc, heval⟩ := hodgeEval_regularKaehler G hdim E' e i hfield hO η hη
  rw [show (⟨_, hreg⟩ : regularAtOrigin (E.baseChange L)) = ⟨_, hreg'⟩ from rfl, heval] at h0
  by_cases hc0 : c = 0
  · rw [← hc, hc0, zero_smul]
  · exfalso
    apply wedge_originParameter_ne_zero G E' i hO
    have h1 := congrArg (fun z => c⁻¹ • z) h0
    simpa only [inv_smul_smul₀ hc0, smul_zero] using h1

end ZInQ.Contrib.RC53Assist.HodgeLineBinding
