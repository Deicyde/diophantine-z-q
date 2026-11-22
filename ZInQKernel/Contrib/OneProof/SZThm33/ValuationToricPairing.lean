import ZInQKernel.Contrib.OneProof.SZThm33.ValuationToricRankOne
import ZInQKernel.Contrib.OneProof.SZThm33.ValuationTorsionFactors
import ZInQKernel.Contrib.OneProof.SZThm33.ValuationWeilProducts
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.TorusCoordinates
import ZInQKernel.Contrib.OneProof.SZThm33.TateIdentityComponent

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open HDec.WeilPairing ReductSplit SmoothGroup PkgI3 PkgI3.AbVar ZInQ.HeightSplit
open ZInQ.FaltingsRestate PicDict.DirectPairing ZInQ.ToricOrthogonality
open scoped CategoryTheory.MonObj

namespace SZRaynaud.Ambient

variable {K : Type} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {w : ValuationSubring (AlgebraicClosure K)} (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
  (A : AbVar K) (M : GroupModelO A O) [GeometricallyIntegral M.G.hom]

attribute [local instance] isCommMonObj_geomSpecialFibre
attribute [local instance] isCommMonObj_groupModelO

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
set_option linter.style.haveILetI false in
/-- The Weil pairing of a torsion section which specializes to a split torus
with any torsion section of the identity model is trivial. -/
theorem valuationWeilValue_eq_one_of_toric
    {n : ℕ} (hn : 0 < n) (hu : IsUnit (n : O)) (hchar : (n : K) ≠ 0)
    {r : ℕ} (toric : splitTorus (ResBarO O) r ⟶ (geomSpecialFibre M)) [IsMonHom toric]
    (x y : (Over.mk (base hw) ⟶ M.G)) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (z : (algPt (ResBarO O) (ResBarO O)) ⟶ splitTorus (ResBarO O) r) (b : (algPt (ResBarO O) (ResBarO O)) ⟶ (geomSpecialFibre M)) (hz : z ^ n = 1) (hb : b ^ n = 1)
    (hxr : restrictPoint res x = geomSpecialPointEquiv hw A M (z ≫ toric))
    (hyr : restrictPoint res y = geomSpecialPointEquiv hw A M b)
    (L : M.G.left.Modules) [SheafOfModules.IsInvertible L] :
    letI : SheafOfModules.IsInvertible (Relative.genericModelLine M L) := by
      unfold Relative.genericModelLine
      infer_instance
    value A (Scheme.Pic.mk (Relative.genericModelLine M L)) hn hchar
      (valuationTorsionPoint hw A M x hx) (valuationTorsionPoint hw A M y hy) = 1 := by
  obtain ⟨a, ha, hprod⟩ := exists_torus_torsion_coordinate_product z hz
  let d (i : Fin r) := torusCoordinate r i ≫ toric
  haveI (i : Fin r) : IsMonHom (torusCoordinate (k := (ResBarO O)) r i) := torusCoordinate_isMonHom i
  haveI (i : Fin r) : IsMonHom (d i) := inferInstanceAs (IsMonHom (torusCoordinate r i ≫ toric))
  let f (i : Fin r) : (algPt (ResBarO O) (ResBarO O)) ⟶ (geomSpecialFibre M) := a i ≫ d i
  have hf (i : Fin r) : f i ^ n = 1 := by
    change (mapGroupPoint (d i) (a i)) ^ n = 1
    rw [← map_pow, ha, map_one]
  have hfprod : z ≫ toric = ∏ i, f i := by
    change mapGroupPoint toric z = _
    rw [hprod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    change (a i ≫ torusCoordinate r i) ≫ toric = a i ≫ torusCoordinate r i ≫ toric
    exact Category.assoc _ _ _
  obtain ⟨u, hu', hxu⟩ := exists_valuationTorsionFactors hw A M hu x hx f hf (by rwa [← hfprod])
  have : SheafOfModules.IsInvertible (Relative.genericModelLine M L) := by
    unfold Relative.genericModelLine
    infer_instance
  let Lη := Scheme.Pic.mk (Relative.genericModelLine M L)
  refine valuationWeilValue_eq_one_of_prod hw A M hn hchar Lη x y hx hy u (fun i => (hu' i).1) hxu ?_
  intro i
  let e := rankOneTorusIso (ResBarO O)
  let d' : puncturedLine (ResBarO O) ⟶ (geomSpecialFibre M) := e.inv ≫ d i
  have : IsMonHom d' := inferInstanceAs (IsMonHom ((rankOneTorusIso (ResBarO O)).inv ≫ d i))
  let a' := geometricSection (O := O) (a i ≫ e.hom)
  let b' := geometricSection (O := O) b
  have ha' : a' ^ n = 1 := by
    change (geometricSection (O := O) (mapGroupPoint (rankOneTorusIso (ResBarO O)).hom (a i))) ^ n = 1
    rw [← map_pow, ← map_pow, ha, map_one, map_one]
  have hb' : b' ^ n = 1 := by
    change (geometricSection (O := O) b) ^ n = 1
    rw [← map_pow, hb, map_one]
  have hat : (a i ≫ e.hom) ≫ d' = f i := by
    simp only [d', Category.assoc, Iso.hom_inv_id_assoc, f]
  have haProj : a'.left ≫ d'.left ≫ (Limits.pullback.fst M.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))) =
      valuationGeometricResidue hw ≫ (valuationSectionEquiv hw A M (u i)).left ≫ (Limits.pullback.fst M.G.hom (base hw)) := by
    change (geometricSection (O := O) (a i ≫ e.hom)).left ≫ d'.left ≫ (Limits.pullback.fst M.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))) = _
    rw [geometricSection_left, ← Category.assoc, ← Over.comp_left, hat]
    exact (valuationSection_specializes hw A M (u i) (f i) (hu' i).2).symm
  have hbProj : b'.left ≫ (Limits.pullback.fst M.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))) =
      valuationGeometricResidue hw ≫ (valuationSectionEquiv hw A M y).left ≫ (Limits.pullback.fst M.G.hom (base hw)) := by
    change (geometricSection (O := O) b).left ≫ (Limits.pullback.fst M.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))) = _
    rw [geometricSection_left]
    exact (valuationSection_specializes hw A M y b hyr).symm
  exact valuationWeilValue_eq_one_of_rankOne hw A M hn hu hchar d' (u i) y (hu' i).1 hy
    a' b' ha' hb' haProj hbProj L

end SZRaynaud.Ambient
