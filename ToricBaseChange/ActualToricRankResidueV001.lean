import ToricBaseChange.ActualToricRankNativeV001
import ToricBaseChange.ValuationResidueBindingV006

/-!
# The native toric rank inequality at the actual residue fields

`k = κ(O)`, `Ω = κ(O')^alg`, `O' → Ω` the residue map, `jb = jbar : κ(O)^alg → κ(O')^alg` and the
square `geom_square`.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ToricBaseChange.ActualKernel

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem toricRank_le_residue (O : ValuationSubring K) (O' : ValuationSubring L)
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K L) = O) (A : PkgI3.AbVar K)
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom] [IsSeparated N.hom]
    (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).obj N ≅ A.X)
    [IsMonHom gen.hom]
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f ≫ gen.hom)
    (N' : Over (Spec (CommRingCat.of O'))) [GrpObj N'] [Smooth N'.hom]
    (gen' : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L)))).obj N' ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj A.X)
    [IsMonHom gen'.hom]
    (hN' : ∀ (Y : Over (Spec (CommRingCat.of O'))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N' =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L)))).map f ≫ gen'.hom)
    (u : Comparison.bc (Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO))) N ⟶ N')
    (hu : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L)))).map u ≫ gen'.hom =
        (Comparison.genIso (Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO)))
          (Spec.map (CommRingCat.ofHom (algebraMap O K))) (Spec.map (CommRingCat.ofHom (algebraMap O' L)))
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) (Comparison.iota_square O O' hO) N A.X gen).hom)
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
    r ≤ r' :=
  toricRank_le_native O O' hO A N gen hN N' gen' hN' u hu
    (algebraMap O (IsLocalRing.ResidueField O))
    (algebraMap O' (AlgebraicClosure (IsLocalRing.ResidueField O'))) (jbar O O' hO)
    (geom_square O O' hO) U inc r e he_inj he_nat U' inc' B'.X π r' e' he'_inj he'_ker

end ToricBaseChange.ActualKernel
