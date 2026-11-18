import ToricBaseChange.ActualToricRankResidueV001
import FiniteIntermediateBindingV001

/-!
# The toric rank inequality over an actual finite intermediate field

`O ⊆ K` a discrete valuation ring, `w` a valuation subring of an extension field `Ωb` of `K` with
`w ∩ K = O`, `M` a finite intermediate field, and `O' = w ∩ M`. The discrete valuation ring property
of `O'` is derived (`FiniteExtensionValuation.finite_intermediate_restriction_isDVR`), not assumed;
the rest is `toricRank_le_residue` with `L = M`.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ToricBaseChange.ActualKernel

variable {K Ωb : Type} [Field K] [Field Ωb] [Algebra K Ωb]

theorem toricRank_le_finite_intermediate (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring Ωb) (hw : w.comap (algebraMap K Ωb) = O) (M : IntermediateField K Ωb)
    [FiniteDimensional K M] (O' : ValuationSubring M) (hO'w : O' = w.comap (algebraMap M Ωb))
    (hO : O'.comap (algebraMap K M) = O) (A : PkgI3.AbVar K)
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom] [IsSeparated N.hom]
    (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).obj N ≅ A.X)
    [IsMonHom gen.hom]
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f ≫ gen.hom)
    (N' : Over (Spec (CommRingCat.of O'))) [GrpObj N'] [Smooth N'.hom]
    (gen' : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' M)))).obj N' ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K M)))).obj A.X)
    [IsMonHom gen'.hom]
    (hN' : ∀ (Y : Over (Spec (CommRingCat.of O'))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N' =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' M)))).map f ≫ gen'.hom)
    (u : Comparison.bc (Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO))) N ⟶ N')
    (hu : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' M)))).map u ≫ gen'.hom =
        (Comparison.genIso (Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO)))
          (Spec.map (CommRingCat.ofHom (algebraMap O K))) (Spec.map (CommRingCat.ofHom (algebraMap O' M)))
          (Spec.map (CommRingCat.ofHom (algebraMap K M))) (Comparison.iota_square O O' hO) N A.X gen).hom)
    (U : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField O)))) [GrpObj U]
    (inc : U ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O (IsLocalRing.ResidueField O))))).obj N)
    [IsOpenImmersion inc.left] [IsMonHom inc] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) R],
      letI := algK (algebraMap (IsLocalRing.ResidueField O) (AlgebraicClosure (IsLocalRing.ResidueField O))) R
      (Fin r → Rˣ) →* (SpecPt (IsLocalRing.ResidueField O) R ⟶ U))
    (he_inj : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) R],
      Function.Injective (e R))
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) R]
        [CommRing S] [Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) S]
        (f : R →ₐ[AlgebraicClosure (IsLocalRing.ResidueField O)] S) (t : Fin r → Rˣ),
        letI := algK (algebraMap (IsLocalRing.ResidueField O) (AlgebraicClosure (IsLocalRing.ResidueField O))) R
        letI := algK (algebraMap (IsLocalRing.ResidueField O) (AlgebraicClosure (IsLocalRing.ResidueField O))) S
        e S (fun i => Units.map (f : R →* S) (t i)) =
          SpecPtMap (k := IsLocalRing.ResidueField O) ({ (f : R →+* S) with
            commutes' := fun a => f.commutes (algebraMap (IsLocalRing.ResidueField O)
              (AlgebraicClosure (IsLocalRing.ResidueField O)) a) } :
              R →ₐ[IsLocalRing.ResidueField O] S) ≫ e R t)
    (U' : Over (Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField O'))))) [GrpObj U']
    (inc' : U' ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap O' (AlgebraicClosure (IsLocalRing.ResidueField O')))))).obj N')
    [IsOpenImmersion inc'.left] [IsMonHom inc']
    (B' : PkgI3.AbVar (AlgebraicClosure (IsLocalRing.ResidueField O'))) (π : U' ⟶ B'.X) [IsMonHom π]
    (r' : ℕ) (e' : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure (IsLocalRing.ResidueField O')) R],
      (Fin r' → Rˣ) →* (SpecPt (AlgebraicClosure (IsLocalRing.ResidueField O')) R ⟶ U'))
    (he'_inj : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure (IsLocalRing.ResidueField O')) R],
      Function.Injective (e' R))
    (he'_ker : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure (IsLocalRing.ResidueField O')) R]
      (v : SpecPt (AlgebraicClosure (IsLocalRing.ResidueField O')) R ⟶ U'),
      v ≫ π = 1 ↔ v ∈ (e' R).range) :
    r ≤ r' := by
  haveI : IsDiscreteValuationRing O' := by
    subst hO'w
    exact FiniteExtensionValuation.finite_intermediate_restriction_isDVR O w hw M
  exact toricRank_le_residue O O' hO A N gen hN N' gen' hN' u hu U inc r e he_inj he_nat
    U' inc' B' π r' e' he'_inj he'_ker

end ToricBaseChange.ActualKernel
