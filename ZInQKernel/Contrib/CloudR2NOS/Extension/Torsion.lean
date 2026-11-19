import ZInQKernel.Contrib.CloudR2NOS.Extension.Inertia
import ZInQKernel.Contrib.CloudR2Raynaud.GrpPoints

/-!
# Original-object inertia transport to an extension field

New H5 arithmetic join using the H4 universe-generic point equivalence.
The maps and group data are those of `PkgI2.baseChange`, not replacement objects;
the geometric closure Ω and each natural order m are unchanged. The source
GenericPoints module is consumed via the parent/steward's immutable view until
the combined contribution graph is assembled. No model existence, henselianity,
perfection, characteristic assumption or good-descent claim is made here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace ZInQ.Contrib.CloudR2NOS.Extension

/-- Inertia-trivial torsion survives original-group base change on the SAME Ω. -/
theorem inertiaTrivialOn_baseChange
    {K E Ω : Type u} [Field K] [Field E] [Field Ω]
    [Algebra K E] [Algebra E Ω] [Algebra K Ω] [IsScalarTower K E Ω]
    (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A]
    (w : ValuationSubring Ω) (m : ℕ) (hm : PkgI2.InertiaTrivialOn A w m) :
    PkgI2.InertiaTrivialOn (PkgI2.baseChange A E) w m := by
  let e : PkgI2.Pts (PkgI2.baseChange A E) Ω ≃* PkgI2.Pts A Ω :=
    ZInQ.Contrib.CloudR2Raynaud.GrpPoints.bcPts A Ω
  intro σ hσ x hx
  have hx' : x ^ m = 1 := hx
  have heTorsion : e x ∈ PkgI2.torsion A Ω m := by
    change (e x) ^ m = 1
    rw [← map_pow, hx', map_one]
  have hcompat := ZInQ.Contrib.CloudR2Raynaud.GrpPoints.bcPts_galAct A Ω σ x
  change e (PkgI2.galAct (PkgI2.baseChange A E) σ x) =
    PkgI2.galAct A (σ.restrictScalars K) (e x) at hcompat
  apply e.injective
  rw [hcompat]
  exact hm (σ.restrictScalars K) (isInertia_restrictScalars w σ hσ) (e x) heTorsion

/-- The same original order and closure work for EVERY prolongation containing O,
then for inertia over E. No prime-power/order-family replacement occurs. -/
theorem inertiaTrivialOn_all_prolongations_baseChange
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    [Algebra E (AlgebraicClosure K)] [IsScalarTower K E (AlgebraicClosure K)]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A]
    (m : ℕ) (hm : PkgI2.InertiaTrivialOn A w m) :
    ∀ V : ValuationSubring (AlgebraicClosure K),
      (∀ r : O, algebraMap O (AlgebraicClosure K) r ∈ V) →
        PkgI2.InertiaTrivialOn (PkgI2.baseChange A E) V m := by
  intro V hV
  exact inertiaTrivialOn_baseChange A V m
    (ZInQ.Contrib.CloudR2NOS.Valuation.inertiaTrivialOn_all_prolongations O w hw A m hm V hV)

end ZInQ.Contrib.CloudR2NOS.Extension

#print axioms ZInQ.Contrib.CloudR2NOS.Extension.inertiaTrivialOn_baseChange
#print axioms ZInQ.Contrib.CloudR2NOS.Extension.inertiaTrivialOn_all_prolongations_baseChange
