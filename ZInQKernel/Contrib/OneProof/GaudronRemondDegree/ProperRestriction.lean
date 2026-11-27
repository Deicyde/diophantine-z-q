import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.OriginalGenericFiber
import ZInQKernel.Contrib.SpreadOut.NumberField
import ZInQKernel.Contrib.OneProof.EGAIV_8_10_5_xii

/-! # Properness on a factorial localization of the original marked model -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped NumberField

namespace ZInQ.Contrib.IsogenyDegree

open ZInQ.DefFaltings ZInQ.H5Glue
open ZInQ.Contrib.SpreadOut ZInQ.Contrib.EGAProperLimit

/-- The canonical map from the factorial localization to the original integer base. -/
noncomputable def modelLocalizationMap (L : Type) [Field L] [NumberField L] (n : ℕ) :
    (NF.specDiag L).obj (Opposite.op n) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (NF.Rg L n)))

/-- The two maps into the original integer base agree. -/
theorem modelLocalization_generic_comp (L : Type) [Field L] [NumberField L] (n : ℕ) :
    (NF.specCone L).π.app (Opposite.op n) ≫ modelLocalizationMap L n = jL L := by
  have h : (NF.toL L n).comp (algebraMap (𝓞 L) (NF.Rg L n)) = algebraMap (𝓞 L) L :=
    RingHom.ext (fun x => NF.toL_alg L n x)
  change Spec.map (CommRingCat.ofHom (NF.toL L n)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (NF.Rg L n))) =
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- Apply EGA IV₃ 8.10.5 (xii) to the given model and its actual generic marking.
The output is properness of a base change of that very model. -/
theorem originalModel_exists_properLocalization {K L : Type} [Field K] [Field L]
    [NumberField L] [Algebra K L] {A : PkgI3.AbVar K} (N : GroupModel A L) :
    ∃ n : ℕ, IsProper ((Over.pullback (modelLocalizationMap L n)).obj N.G).hom := by
  let loc (k : ℕᵒᵖ) : (NF.specDiag L).obj k ⟶ Spec (CommRingCat.of (𝓞 L)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (NF.Rg L k.unop)))
  let i : ℕᵒᵖ := Opposite.op 0
  let X₀ := (Over.pullback (loc i)).obj N.G
  have wη : (NF.specCone L).π.app i ≫ loc i = jL L :=
    modelLocalization_generic_comp L 0
  letI : Smooth N.G.hom := N.smooth
  letI : IsSeparated N.G.hom := N.separated
  letI : QuasiCompact N.G.hom := N.qc
  have hpη : IsProper ((Over.pullback ((NF.specCone L).π.app i)).obj X₀).hom :=
    @isProper_of_iso _ _ _ (((pbNat _ _ _ wη).app N.G) ≪≫ N.gen) (A.baseChange L).proper
  obtain ⟨j, a, hp⟩ :=
    egaIV_8_10_5_xii_proof ℕ (NF.specDiag L) (NF.specCone L)
      (NF.specConeIsLimit L) i X₀
      (show LocallyOfFinitePresentation (pullback.snd N.G.hom (loc i)) from inferInstance)
      (show QuasiCompact (pullback.snd N.G.hom (loc i)) from inferInstance)
      (show QuasiSeparated (pullback.snd N.G.hom (loc i)) from inferInstance) hpη
  have wj : (NF.specDiag L).map a ≫ loc i = loc j := by
    have h : (NF.tr L (leOfHom a.unop)).comp (algebraMap (𝓞 L) (NF.Rg L i.unop)) =
        algebraMap (𝓞 L) (NF.Rg L j.unop) :=
      RingHom.ext (fun x => NF.tr_alg L (leOfHom a.unop) x)
    change Spec.map (CommRingCat.ofHom (NF.tr L (leOfHom a.unop))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (NF.Rg L i.unop))) =
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (NF.Rg L j.unop)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  exact ⟨j.unop, @isProper_of_iso _ _ _ ((pbNat _ _ _ wj).app N.G).symm hp⟩

end ZInQ.Contrib.IsogenyDegree
