import ZInQKernel.Contrib.OneProof.SZThm33.IdentitySpecialFibre
import ZInQKernel.Contrib.OneProof.SZThm33.SplitToricInclusion

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit CToPrinted ZInQ.HeightSplit ZInQ.FaltingsRestate

namespace SZRaynaud

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K} [IsDiscreteValuationRing O]

/-- The torus from a semistable presentation maps into the geometric
special fibre of the relative identity model, with its specified affine points. -/
theorem exists_identitySpecialToricInclusion (H M : GroupModelO A O)
    (i : H.G ⟶ M.G) [IsOpenImmersion i.left] [IsMonHom i]
    (hi : Set.range i.left = idCompSet M.G)
    {U : (Over (Spec (CommRingCat.of (ResBarO O))))} [GrpObj U] [ConnectedSpace U.left]
    (j : U ⟶ geomSpecialFibre M) [IsOpenImmersion j.left] [IsMonHom j]
    (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (ResBarO O) R], (Fin r → Rˣ) →* (algPt (ResBarO O) R ⟶ U))
    (hn : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra (ResBarO O) R] [Algebra (ResBarO O) R']
      (f : R →ₐ[(ResBarO O)] R') (t : Fin r → Rˣ),
      e R' (fun l => Units.map (f : R →* R') (t l)) = algPtMap f ≫ e R t) :
    ∃ t : splitTorus (ResBarO O) r ⟶ geomSpecialFibre H, IsMonHom t ∧
      ∀ (R : Type) [CommRing R] [Algebra (ResBarO O) R] (x : algPt (ResBarO O) R ⟶ splitTorus (ResBarO O) r),
        x ≫ t ≫ geomSpecialModelMap H M i = e R (splitTorusPoints R x) ≫ j := by
  obtain ⟨φ, hφ, hfac⟩ := exists_geomIdentityIso H M i hi j
  obtain ⟨t, ht, hpoints⟩ := exists_splitToricInclusion r e hn
  refine ⟨t ≫ φ.hom, inferInstance, ?_⟩
  intro R _ _ x
  rw [Category.assoc t, hfac, ← Category.assoc, hpoints R x]

end SZRaynaud
