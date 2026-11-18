import ToricBaseChange.ToricRankSpecialV001
import ToricBaseChange.SpecialComparisonV001

/-!
# Torus survival under base change of models: the assembled statement

`N` is a smooth group model over `S` (generic identification `gen` a homomorphism), `N'` a group
model over `S'` with the Néron mapping property (`gen'` a homomorphism), `u : N ×_S S' → N'` the
comparison characterised by the mapping property (`hu`; it exists and is unique by
`exists_unique_comparison`). `U ⊆ N ×_S k` is a subgroup of the special fibre over the residue field
`k` with a torus of rank `r` split over `k̄`, and `N' ×_{S'} Ω` (`Ω` algebraically closed, over `k̄`)
has semi-abelian identity component with toric rank `r'`. If the special-fibre comparison kills no
nontrivial `m`-torsion point of the torus (`m ≥ 2` invertible in `Ω`), then `r ≤ r'`.

Proved here, not assumed: the comparison is a homomorphism (from the mapping property and `gen`,
`gen'`), the special-fibre comparison is a homomorphism, the torus is transported from `k̄` to `Ω`,
its image lies in the identity component `U'` and in the toric part `ker(U' → B')`, and the rank
count. Remaining input: `hker`.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Limits
open scoped CategoryTheory.Obj

namespace ToricBaseChange

theorem toricRank_le_of_comparison {S S' E E' : Scheme.{0}} (h : S' ⟶ S) (j : E ⟶ S) (j' : E' ⟶ S')
    (g : E' ⟶ E) (hgen : j' ≫ h = g ≫ j)
    (N : Over S) [GrpObj N] [Smooth N.hom] (AX : Over E) [GrpObj AX]
    (gen : (Over.pullback j).obj N ≅ AX) [IsMonHom gen.hom] (N' : Over S') [GrpObj N']
    (gen' : (Over.pullback j').obj N' ≅ (Over.pullback g).obj AX) [IsMonHom gen'.hom]
    (hN' : ∀ (Y : Over S') [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N' => (Over.pullback j').map f ≫ gen'.hom)
    (u : Comparison.bc h N ⟶ N')
    (hu : (Over.pullback j').map u ≫ gen'.hom = (Comparison.genIso h j j' g hgen N AX gen).hom)
    {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ S)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (jb : AlgebraicClosure k →+* Ω)
    (σ' : Spec (CommRingCat.of Ω) ⟶ S') (hsq : σ' ≫ h = sφ (φι jb) ≫ s)
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (inc : U ⟶ (Over.pullback s).obj N)
    [IsMonHom inc] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      letI := algK (algebraMap k (AlgebraicClosure k)) R
      (Fin r → Rˣ) →* (SpecPt k R ⟶ U))
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
        [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
        letI := algK (algebraMap k (AlgebraicClosure k)) R
        letI := algK (algebraMap k (AlgebraicClosure k)) S
        e S (fun i => Units.map (f : R →* S) (t i)) =
          SpecPtMap (k := k) ({ (f : R →+* S) with
            commutes' := fun a => f.commutes (algebraMap k (AlgebraicClosure k) a) } : R →ₐ[k] S) ≫ e R t)
    (U' : Over (Spec (CommRingCat.of Ω))) [GrpObj U'] (inc' : U' ⟶ (Over.pullback σ').obj N')
    [IsOpenImmersion inc'.left] [IsMonHom inc']
    (B' : Over (Spec (CommRingCat.of Ω))) [GrpObj B'] [IsProper B'.hom] (π : U' ⟶ B') [IsMonHom π]
    (r' : ℕ) (e' : ∀ (R : Type) [CommRing R] [Algebra Ω R], (Fin r' → Rˣ) →* (SpecPt Ω R ⟶ U'))
    (he'_inj : ∀ (R : Type) [CommRing R] [Algebra Ω R], Function.Injective (e' R))
    (he'_ker : ∀ (R : Type) [CommRing R] [Algebra Ω R] (v : SpecPt Ω R ⟶ U'),
      v ≫ π = 1 ↔ v ∈ (e' R).range)
    (m : ℕ) (hm : 2 ≤ m) [NeZero (m : Ω)]
    (hker : ∀ t : Fin r → Ωˣ, t ^ m = 1 →
      torusΩ jb U r e Ω t ≫ Comparison.specialComparison h s σ' (sφ (φι jb)) hsq N N' u U inc = 1 →
        t = 1) :
    r ≤ r' := by
  haveI := Comparison.isMonHom_comparison h j j' g hgen N AX gen N' gen' hN' u hu
  have hψ := Comparison.isMonHom_specialComparison h s σ' (sφ (φι jb)) hsq N N' u U inc
  exact toricRank_le_special jb U r e he_nat ((Over.pullback σ').obj N') U' inc' B' π r' e' he'_inj
    he'_ker (Comparison.specialComparison h s σ' (sφ (φι jb)) hsq N N' u U inc) hψ m hm hker

end ToricBaseChange
