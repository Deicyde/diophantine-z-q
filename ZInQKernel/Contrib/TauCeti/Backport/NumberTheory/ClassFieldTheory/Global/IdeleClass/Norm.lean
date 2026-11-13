/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.Norm), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.Norm` (task ring-class).
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.Norm
public import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.NumberField.Global.Ideles.Norm.Galois
import ZInQKernel.Contrib.TauCeti.Backport.FieldTheory.Galois.AbsoluteGaloisGroup.Norm
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassField
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.GroundNorm

public section

noncomputable section

open IntermediateField NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)

-- The two private lemmas below are copied from the module (they are private there).

/-- An idele of `K`, extended to the bottom subextension of `Kˢ/K` or to `E`, is the same idele of
`Kˢ`. -/
private theorem ideleCoeffOf_bot_ideleExtension (E : Ω) (b : IdeleGroup (𝓞 K) K) :
    ideleCoeffOf K ⊥ (.ofMul (GlobalNumberFields.ideleExtension K
        ((⊥ : Ω) : IntermediateField K (SeparableClosure K)) b)) =
      ideleCoeffOf K E (.ofMul (GlobalNumberFields.ideleExtension K E b)) := by
  rw [← ideleCoeffOf_ideleTransition (bot_le : (⊥ : Ω) ≤ E)]
  refine congrArg _ (congrArg _ (Units.ext ?_))
  let _ := (IntermediateField.inclusion (bot_le : (⊥ : Ω) ≤ E)).toRingHom.toAlgebra
  -- Both ways round, `x ∈ K` goes to the element `x` of `Kˢ`.
  have : IsScalarTower K ((⊥ : Ω) : IntermediateField K (SeparableClosure K)) E :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  rw [coe_ideleTransition, adeleTransition_apply, ← GlobalNumberFields.coe_ideleExtension,
    ← MonoidHom.comp_apply, GlobalNumberFields.ideleExtension_comp]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
/-- The norm from the level of `W` to the level of `G_K`, where the fixed field of `W` is `E`, is
the norm map of idele classes `N_{E/K}`. It is stated in the ambient module, for any `W₀ = ⊤`, so
that it applies to the ground of a layer, which is `⊤` only propositionally. -/
private theorem coe_levelNorm_ideleClassLevelEquiv (E : Ω)
    {W W₀ : OpenSubgroup (AbsoluteGaloisGroup K)} (h : W ≤ W₀) (hW₀ : W₀ = ⊤)
    (hW : fixedField W.toSubgroup = E) (c : IdeleClassGroup (𝓞 E) E) :
    ((globalFormation K).levelNorm h (ideleClassLevelEquiv hW (.ofMul c)) :
        (globalFormation K).toRep.V) =
      (globalGroundEquiv K (.ofMul (GlobalNumberFields.ideleClassNormMap K E c)) :
        (globalFormation K).toRep.V) := by
  subst hW₀
  induction c using QuotientGroup.induction_on with | H a => ?_
  -- Restricting the coset representatives of `W` to `E` runs through `Gal(E/K)` once each.
  have hprod := prod_restrictNormal_out hW fun σ ↦
    (Units.map (GlobalNumberFields.adeleGaloisAction K E σ) a : IdeleGroup (𝓞 E) E)
  rw [Formation.levelNorm_top_apply_coe, finsum_eq_sum_of_fintype, ideleClassLevelEquiv_mk,
    ideleCoeffOfIntermediateField_coe, GlobalNumberFields.ideleClassNormMap_mk,
    globalGroundEquiv_mk, ideleCoeffOf_bot_ideleExtension,
    GlobalNumberFields.ideleExtension_ideleNormMap, ← hprod, ofMul_prod, map_sum (ideleCoeffOf K E),
    map_sum (ideleClassMk K), map_sum (ideleClassCoeffEquivGlobalFormation K)]
  -- Each coset representative acts on the class of `a` through its restriction to `E`.
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← ideleClassCoeffEquivGlobalFormation_smul, ← map_smul (ideleClassMk K), smul_ideleCoeffOf]

/-- **The norm to the ground level is the idele-class norm**: if the fixed field of the open
subgroup `W` of `G_K` is the finite Galois subextension `E`, then under the identifications of the
levels of `W` and `G_K` with `C_E` and `C_K`, the norm from the level of `W` to the ground level is
the norm map of idele classes `N_{E/K} : C_E → C_K`. -/
theorem levelNorm_top_ideleClassLevelEquiv (E : Ω) {W : OpenSubgroup (AbsoluteGaloisGroup K)}
    (h : W ≤ ⊤) (hW : fixedField W.toSubgroup = E) (c : IdeleClassGroup (𝓞 E) E) :
    (globalFormation K).levelNorm h (ideleClassLevelEquiv hW (.ofMul c)) =
      globalGroundEquiv K (.ofMul (GlobalNumberFields.ideleClassNormMap K E c)) :=
  Subtype.ext (coe_levelNorm_ideleClassLevelEquiv E h rfl hW c)

section FixedField

variable {F L : IntermediateField K (SeparableClosure K)} [NumberField F] [NumberField L]
  [Algebra F L] [IsScalarTower F L (SeparableClosure K)] (Lay : NormalLayer (AbsoluteGaloisGroup K))

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
/-- **The norm between two levels of the idele-class formation is the idele-class norm**: if the
open subgroups `W' ≤ W` of `G_K` have fixed fields `F ⊆ L`, then under the identifications of the
levels of `W` and `W'` with `C_F` and `C_L` (`ideleClassLevelEquiv`), the norm
`Formation.levelNorm` from the level of `W'` to that of `W` is the norm map of idele classes
`N_{L/F} : C_L → C_F`. The extension `L/F` need not be normal, nor `W'` normal in `W`. -/
theorem levelNorm_ideleClassLevelEquiv {W W' : OpenSubgroup (AbsoluteGaloisGroup K)}
    (h : W' ≤ W) (hF : fixedField W.toSubgroup = F) (hL : fixedField W'.toSubgroup = L)
    (c : IdeleClassGroup (𝓞 L) L) :
    (globalFormation K).levelNorm h (ideleClassLevelEquiv hL (.ofMul c)) =
      ideleClassLevelEquiv hF (.ofMul (GlobalNumberFields.ideleClassNormMap F L c)) := by
  refine Subtype.ext ?_
  induction c using QuotientGroup.induction_on with | H a => ?_
  -- Compute in the ideles of the normal closure `M` of `L/K`, which contains `F`.
  let M : Ω := FiniteGaloisIntermediateField.normalClosure K L
  have hLM : L ≤ M := FiniteGaloisIntermediateField.le_normalClosure K L
  have hFM : F ≤ M := (IntermediateField.le_of_isScalarTower (E := F) (E' := L)).trans hLM
  let := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  let := (IntermediateField.inclusion hFM).toRingHom.toAlgebra
  -- Read in `M`, the norm of `L/F` is the product of the conjugates by the coset representatives
  -- of `W'` in `W`, so the same holds for the idele norm.
  have hσ (y : L) : algebraMap F M (Algebra.norm F y) =
      ∏ q : W.toSubgroup ⧸ W'.toSubgroup.subgroupOf W.toSubgroup,
        ((q.out : AbsoluteGaloisGroup K).restrictNormal M).toRingEquiv (algebraMap L M y) := by
    refine Subtype.ext ((coe_norm_eq_prod_quotient_out hF hL y).trans ?_)
    rw [IntermediateField.coe_prod]
    exact Finset.prod_congr rfl fun q _ ↦
      (AlgEquiv.restrictNormal_commutes (q.out : AbsoluteGaloisGroup K) M (algebraMap L M y)).symm
  rw [Formation.levelNorm_apply_coe, finsum_eq_sum_of_fintype, ideleClassLevelEquiv_mk,
    GlobalNumberFields.ideleClassNormMap_mk, ideleClassLevelEquiv_mk,
    ← ideleCoeffOf_ideleExtension M hFM,
    GlobalNumberFields.ideleExtension_ideleNormMap_of_algebraMap_norm_eq_prod F L M _ hσ,
    ofMul_prod, map_sum, map_sum, map_sum]
  -- Each coset representative acts on the ideles of `M` through its restriction to `M`.
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← ideleCoeffOf_ideleExtension M hLM, ← ideleClassCoeffEquivGlobalFormation_smul,
    ← map_smul (ideleClassMk K), smul_ideleCoeffOf]
  exact congrArg (fun b ↦ ideleClassCoeffEquivGlobalFormation K (ideleClassMk K
    (ideleCoeffOf K M (.ofMul b)))) (Units.ext (GlobalNumberFields.adeleGaloisAction_apply K M _ _))

end FixedField

end TauCeti.ClassFieldTheory
