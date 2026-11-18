import ToricBaseChange.ActualHkerNativeV001

/-!
# Torus survival with rank under base change of Néron models (native unbundled data)

`toricRank_le_native`: the toric rank `r` of the identity component of the special fibre of `N`
(torus split over `k̄`) is at most the toric rank `r'` of the semi-abelian identity component of the
geometric special fibre of `N'`. No ramification hypothesis on `O'/O`; the kernel condition is
`hker_native` with `m ∈ {2, 3}` invertible on `O'` (`exists_two_le_isUnit`).
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ToricBaseChange.ActualKernel

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem neZero_of_isUnit {R Ω : Type} [CommRing R] [Field Ω] (φ' : R →+* Ω) (m : ℕ)
    (hmu : IsUnit (m : R)) : NeZero (m : Ω) := by
  have h := hmu.map φ'
  rw [map_natCast] at h
  exact ⟨h.ne_zero⟩

/-- **Torus survival with rank.** -/
theorem toricRank_le_native (O : ValuationSubring K) (O' : ValuationSubring L)
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
    {k : Type} [Field k] (ρ : O →+* k)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (φ' : O' →+* Ω) (jb : AlgebraicClosure k →+* Ω)
    (hsq : Spec.map (CommRingCat.ofHom φ') ≫ Spec.map (CommRingCat.ofHom (Comparison.iota O O' hO)) =
      sφ (φι jb) ≫ Spec.map (CommRingCat.ofHom ρ))
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U]
    (inc : U ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom ρ))).obj N)
    [IsOpenImmersion inc.left] [IsMonHom inc] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      letI := algK (algebraMap k (AlgebraicClosure k)) R
      (Fin r → Rˣ) →* (SpecPt k R ⟶ U))
    (he_inj : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], Function.Injective (e R))
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
        [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
        letI := algK (algebraMap k (AlgebraicClosure k)) R
        letI := algK (algebraMap k (AlgebraicClosure k)) S
        e S (fun i => Units.map (f : R →* S) (t i)) =
          SpecPtMap (k := k) ({ (f : R →+* S) with
            commutes' := fun a => f.commutes (algebraMap k (AlgebraicClosure k) a) } : R →ₐ[k] S) ≫ e R t)
    (U' : Over (Spec (CommRingCat.of Ω))) [GrpObj U']
    (inc' : U' ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ'))).obj N')
    [IsOpenImmersion inc'.left] [IsMonHom inc']
    (B' : Over (Spec (CommRingCat.of Ω))) [GrpObj B'] [IsProper B'.hom] (π : U' ⟶ B') [IsMonHom π]
    (r' : ℕ) (e' : ∀ (R : Type) [CommRing R] [Algebra Ω R], (Fin r' → Rˣ) →* (SpecPt Ω R ⟶ U'))
    (he'_inj : ∀ (R : Type) [CommRing R] [Algebra Ω R], Function.Injective (e' R))
    (he'_ker : ∀ (R : Type) [CommRing R] [Algebra Ω R] (v : SpecPt Ω R ⟶ U'),
      v ≫ π = 1 ↔ v ∈ (e' R).range) :
    r ≤ r' := by
  obtain ⟨m, hm2, hmu⟩ := exists_two_le_isUnit O'
  haveI := neZero_of_isUnit φ' m hmu
  exact toricRank_le_of_comparison _ _ _ _ (Comparison.iota_square O O' hO) N A.X gen N' gen' hN' u hu
    (Spec.map (CommRingCat.ofHom ρ)) jb (Spec.map (CommRingCat.ofHom φ')) hsq U inc r e he_nat
    U' inc' B' π r' e' he'_inj he'_ker m hm2
    (fun t ht hψ => hker_native O O' hO A N gen hN N' gen' hN' u hu ρ φ' jb hsq U inc r e he_inj
      m hmu t ht hψ)

end ToricBaseChange.ActualKernel
