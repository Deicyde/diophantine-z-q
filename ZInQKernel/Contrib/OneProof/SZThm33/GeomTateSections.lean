import ZInQKernel.Contrib.OneProof.SZThm33.GeomTateNaturality

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit SmoothGroup

namespace SZRaynaud.Ambient

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {O : ValuationSubring K} {w : ValuationSubring Ω}
  (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K) (M : GroupModelO A O)

/-- The point equivalence uses the actual projection of the geometric special
fibre and the chosen identification of the two residue fields. -/
theorem geomSpecialPointEquiv_left (x : (ZInQ.HeightSplit.algPt (ResBarO O) (ResBarO O)) ⟶ geomSpecialFibre M) :
    (geomSpecialPointEquiv hw A M x).left =
      Spec.map (CommRingCat.ofHom (geomResidueEquiv hw).symm.toRingHom) ≫
        x.left ≫ pullback.fst M.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))) :=
  rfl

variable [IsAlgClosed Ω] {ℓ : ℕ} [Fact ℓ.Prime] (hu : IsUnit (ℓ : O))

attribute [local instance] isCommMonObj_geomSpecialFibre
attribute [local instance] ZInQ.FaltingsRestate.isCommMonObj_groupModelO

/-- The geometric Tate specialization is realized by a single tower of
sections over the henselian valuation ring shared by the generic and residue points. -/
theorem exists_geomSpecialLiftTate
    (x : PkgI3.Tate.T ℓ (Additive ((ZInQ.HeightSplit.algPt (ResBarO O) (ResBarO O)) ⟶ geomSpecialFibre M))) :
    ∃ y : PkgI3.Tate.T ℓ (Additive (Over.mk (base hw) ⟶ M.G)),
      restrictTate res y = geomSpecialTateEquiv hw A M x ∧
      geomSpecialEmbedTate hw A M hu x =
        PkgI3.Tate.map (genPtHom hw A M).toAdditive (restrictTate gen y) := by
  let := henselianLocalRing_of_valuationSubring w
  let e := LinearEquiv.ofBijective _ (restrictTate_bijective_of_residue (X := M.G) (base hw) hu)
  let y := e.symm (geomSpecialTateEquiv hw A M x)
  exact ⟨y, e.apply_symm_apply _, rfl⟩

end SZRaynaud.Ambient
