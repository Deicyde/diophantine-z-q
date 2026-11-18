import ToricBaseChange.ActualTorsionKernelV001

/-!
# The toric rank inequality for Néron models, with the kernel condition proved

`hker_native` and `toricRank_le_native`: see `ActualTorsionKernelV001`. The only data are the actual
models, their generic identifications and mapping properties, the comparison characterised by the
mapping property, the identity-component torus of the source special fibre (split over `k̄`), the
compatible geometric point, and the semi-abelian identity component of the geometric special fibre of
the target. No kernel, étaleness, injectivity or rank hypothesis.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ToricBaseChange.ActualKernel

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-- **The kernel condition, proved.** -/
theorem hker_native (O : ValuationSubring K) (O' : ValuationSubring L) [IsDiscreteValuationRing O']
    (hO : O'.comap (algebraMap K L) = O) (A : PkgI3.AbVar K)
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
    {k : Type} [Field k] (ρ : O →+* k)
    {Ω : Type} [Field Ω] (φ' : O' →+* Ω) (jb : AlgebraicClosure k →+* Ω)
    (hsq : Spec.map (CommRingCat.ofHom φ') ≫ Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO)) =
      sφ (φι jb) ≫ Spec.map (CommRingCat.ofHom ρ))
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U]
    (inc : U ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom ρ))).obj N)
    [IsOpenImmersion inc.left] [IsMonHom inc] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      letI := algK (algebraMap k (AlgebraicClosure k)) R
      (Fin r → Rˣ) →* (SpecPt k R ⟶ U))
    (he_inj : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], Function.Injective (e R))
    (m : ℕ) (hmu : IsUnit (m : O')) (t : Fin r → Ωˣ) (ht : t ^ m = 1)
    (hψ : torusΩ jb U r e Ω t ≫
      Comparison.specialComparison (Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO)))
        (Spec.map (CommRingCat.ofHom ρ)) (Spec.map (CommRingCat.ofHom φ')) (sφ (φι jb)) hsq
        N N' u U inc = 1) :
    t = 1 := by
  haveI : IsMonHom u := Comparison.isMonHom_comparison _ _ _ _ (Comparison.iota_square O O' hO)
    N A.X gen N' gen' hN' u hu
  exact torus_kernel_of_torsion_kernel _ N N' u m
    (fun T w hw hwu => torsion_kernel_native O O' hO A N gen hN N' gen' hN' u hu m hmu T w hw hwu)
    _ jb _ hsq U inc r e he_inj t ht hψ

end ToricBaseChange.ActualKernel
