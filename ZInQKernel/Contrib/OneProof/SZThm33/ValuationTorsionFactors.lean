import ZInQKernel.Contrib.OneProof.SZThm33.ValuationResidueFibre

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit SmoothGroup ZInQ.HeightSplit
open scoped CategoryTheory.MonObj

namespace SZRaynaud.Ambient

variable {K : Type} [Field K] {O : ValuationSubring K} {w : ValuationSubring (AlgebraicClosure K)}
  (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
  (A : PkgI3.AbVar K) (M : GroupModelO A O)

attribute [local instance] isCommMonObj_geomSpecialFibre
attribute [local instance] ZInQ.FaltingsRestate.isCommMonObj_groupModelO

set_option synthInstance.maxHeartbeats 150000 in
set_option maxHeartbeats 1500000 in
/-- A product decomposition of a geometric torsion point lifts
factor by factor over the henselian valuation ring. -/
theorem exists_valuationTorsionFactors {n : ℕ} (hn : IsUnit (n : O))
    {I : Type} [Fintype I] (x : (Over.mk (base hw) ⟶ M.G)) (hx : x ^ n = 1)
    (z : I → ((algPt (ResBarO O) (ResBarO O)) ⟶ geomSpecialFibre M)) (hz : ∀ i, z i ^ n = 1)
    (hres : restrictPoint res x = geomSpecialPointEquiv hw A M (∏ i, z i)) :
    ∃ y : I → (Over.mk (base hw) ⟶ M.G),
      (∀ i, y i ^ n = 1 ∧ restrictPoint res (y i) = geomSpecialPointEquiv hw A M (z i)) ∧
      x = ∏ i, y i := by
  let := henselianLocalRing_of_valuationSubring w
  let e := geomSpecialPointEquiv hw A M
  have lift (a : ((algPt (ResBarO O) (ResBarO O)) ⟶ geomSpecialFibre M)) (ha : a ^ n = 1) :
      ∃! y : (Over.mk (base hw) ⟶ M.G), y ^ n = 1 ∧ restrictPoint res y = e a := by
    apply existsUnique_torsion_point_over_residue (base hw) n hn (e a)
    rw [← map_pow, ha, map_one]
  choose y hy _ using fun i => lift (z i) (hz i)
  refine ⟨y, hy, ?_⟩
  have hzp : (∏ i, z i) ^ n = 1 := by
    rw [← Finset.prod_pow]
    simp only [hz, Finset.prod_const_one]
  have hpow (i : I) : y i ^ n = 1 := (hy i).1
  have hyp : (∏ i, y i) ^ n = 1 := by
    rw [← Finset.prod_pow]
    simp only [hpow, Finset.prod_const_one]
  have hyres : restrictPoint res (∏ i, y i) = e (∏ i, z i) := by
    rw [map_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => (hy i).2
  obtain ⟨p, _, hunique⟩ := lift (∏ i, z i) hzp
  exact (hunique x ⟨hx, hres⟩).trans (hunique (∏ i, y i) ⟨hyp, hyres⟩).symm

end SZRaynaud.Ambient
