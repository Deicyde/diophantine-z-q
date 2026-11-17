import ZInQKernel.Contrib.CloudB3W17bCanonicalImage.NativeSupport
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Algebra.Category.ModuleCat.Stalk
import ZInQKernel.Contrib.CloudB3W17bAnalyticIdeal.UnitStalk

/-!
Actual canonical stalk-map image of an algebraic inclusion into the unit sheaf.
The unit-stalk equivalence is consumed from the function lane's current-pin
Mathlib-only proof, not assumed or duplicated. All maps act on the actual native
module stalks and the canonical PresheafOfModules.stalkFunctor.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section
universe u

namespace ZInQ.Contrib.CloudB3W17bCanonicalImage

open ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal

/-- The actual unit-stalk equivalence sends the actual module germ of a section
of R to its actual ring germ. This consumes the proven cyclic generator formula. -/
theorem unitStalkEquiv_germ {T : TopCat.{u}} (R : T.Presheaf CommRingCat.{u})
    (x : T) (U : Opens T) (hx : x ∈ U) (r : R.obj (op U)) :
    ZInQ.Contrib.CloudB3W17bAnalyticIdeal.PM.unitStalkEquiv R x
        (TopCat.Presheaf.germ (ZInQ.Contrib.CloudB3W17bAnalyticIdeal.PM.unitPM R).presheaf
          U x hx (ZInQ.Contrib.CloudB3W17bAnalyticIdeal.PM.asUnitSec R r)) = R.germ U x hx r := by
  have h : (ZInQ.Contrib.CloudB3W17bAnalyticIdeal.PM.unitStalkEquiv R x).symm
      (R.germ U x hx r) =
      TopCat.Presheaf.germ (ZInQ.Contrib.CloudB3W17bAnalyticIdeal.PM.unitPM R).presheaf
        U x hx (ZInQ.Contrib.CloudB3W17bAnalyticIdeal.PM.asUnitSec R r) := by
    rw [ZInQ.Contrib.CloudB3W17bAnalyticIdeal.PM.unitStalkEquiv_symm_apply,
      ZInQ.Contrib.CloudB3W17bAnalyticIdeal.PM.smul_unitStalkGen]
  have h' := congrArg (ZInQ.Contrib.CloudB3W17bAnalyticIdeal.PM.unitStalkEquiv R x) h
  simpa only [LinearEquiv.apply_symm_apply] using h'.symm

variable {X : Scheme.{u}} {M : X.Modules}

/-- The real canonical stalk map, transported to the stalk ring by the proved unit equivalence. -/
def canonicalStalkImageMap (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  (ZInQ.Contrib.CloudB3W17bAnalyticIdeal.PM.unitStalkEquiv X.presheaf x).toLinearMap.comp
    (show TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x →ₗ[X.presheaf.stalk x]
      ZInQ.Contrib.CloudB3W17bAnalyticIdeal.PM.unitStalk X.presheaf x from
      ((PresheafOfModules.stalkFunctor (R := X.presheaf) x).map i.val).hom)

/-- Exact germ formula for the ACTUAL canonical stalk morphism and unit equivalence. -/
theorem canonicalStalkImageMap_germ
    (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X) (U : X.Opens)
    (hx : x ∈ U) (s : Γ(M, U)) :
    canonicalStalkImageMap i x (TopCat.Presheaf.germ M.val.presheaf U x hx s) =
      (X.presheaf.germ U x hx).hom (sectionMapToRing i U s) := by
  change ZInQ.Contrib.CloudB3W17bAnalyticIdeal.PM.unitStalkEquiv X.presheaf x
    (((PresheafOfModules.stalkFunctor (R := X.presheaf) x).map i.val)
      (TopCat.Presheaf.germ M.val.presheaf U x hx s)) = _
  rw [PresheafOfModules.stalkFunctor_map_germ]
  exact unitStalkEquiv_germ X.presheaf x U hx (sectionMapToRing i U s)

/-- The image of the ACTUAL canonical stalk map is exactly the native stalk-germ ideal. -/
theorem canonicalStalkImageMap_range
    (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    linearRangeIdeal (canonicalStalkImageMap i x) = sectionImageGermIdeal i x := by
  apply le_antisymm
  · rintro r ⟨m, rfl⟩
    obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
    rw [canonicalStalkImageMap_germ]
    exact Ideal.subset_span ⟨U, hx, s, rfl⟩
  · refine Ideal.span_le.mpr ?_
    rintro r ⟨U, hx, s, rfl⟩
    exact ⟨TopCat.Presheaf.germ M.val.presheaf U x hx s,
      canonicalStalkImageMap_germ i x U hx s⟩

/-- Transport by the ACTUAL unit-stalk equivalence preserves and reflects surjectivity. -/
theorem canonicalStalkImageMap_surjective_iff
    (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    Function.Surjective (canonicalStalkImageMap i x) ↔
      Function.Surjective ((PresheafOfModules.stalkFunctor (R := X.presheaf) x).map i.val) := by
  let e := ZInQ.Contrib.CloudB3W17bAnalyticIdeal.PM.unitStalkEquiv X.presheaf x
  constructor
  · intro h n
    obtain ⟨m, hm⟩ := h (e n)
    exact ⟨m, e.injective hm⟩
  · intro h r
    obtain ⟨m, hm⟩ := h (e.symm r)
    refine ⟨m, ?_⟩
    change e (((PresheafOfModules.stalkFunctor (R := X.presheaf) x).map i.val) m) = r
    rw [hm, e.apply_symm_apply]

/-- Native J zeros are exactly non-surjectivity of its ACTUAL canonical stalk inclusion. -/
theorem nativeIdeal_mem_support_iff_not_surjective_canonicalStalk
    [M.IsQuasicoherent] (i : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.affineOpens) (x : X) (hx : x ∈ U.1) :
    x ∈ (idealSheafOfQuasicoherentHom i).support ↔
      ¬ Function.Surjective ((PresheafOfModules.stalkFunctor (R := X.presheaf) x).map i.val) := by
  rw [nativeIdeal_mem_support_iff_stalkImage_ne_top i U x hx,
    ← canonicalStalkImageMap_range i x]
  exact (not_congr (LinearMap.range_eq_top)).trans
    (not_congr (canonicalStalkImageMap_surjective_iff i x))

end ZInQ.Contrib.CloudB3W17bCanonicalImage
