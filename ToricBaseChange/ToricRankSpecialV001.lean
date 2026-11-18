import ToricBaseChange.TorusTransportV002

/-!
# Toric rank of special fibres under the comparison map (residue base change included)

`U` is the identity component of the special fibre of a semistable model over the residue field `k`
(its torus need not be split over `k`: it is given over `k̄`-algebras), `Ω` an algebraically closed
field with `jb : k̄ → Ω`, `G'` a group scheme over `Ω` (the geometric special fibre of the second
model) with semi-abelian identity component `U'` (abelian quotient `π'`, split torus `e'` of rank
`r'`), and `ψ : U_Ω → G'` a homomorphism (the base change to `Ω` of the comparison map restricted to
the identity component). If `ψ` kills no nontrivial `m`-torsion point of the transported torus
(`m ≥ 2` invertible in `Ω`), then `r ≤ r'`: the torus survives with its rank. The image of the torus
lies in `U'` and in `ker π'` (proved); the rank count is over `Ω`.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ToricBaseChange

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [IsAlgClosed Ω] (jb : AlgebraicClosure k →+* Ω)

/-- The transported torus `(Rˣ)^r → U_Ω(R)` for `Ω`-algebras `R`. -/
def torusΩ (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      letI := algK (algebraMap k (AlgebraicClosure k)) R
      (Fin r → Rˣ) →* (SpecPt k R ⟶ U))
    (R : Type) [CommRing R] [Algebra Ω R] :
    letI : GrpObj ((Over.pullback (sφ (φι jb))).obj U) := Functor.grpObjObj
    (Fin r → Rˣ) →* (SpecPt Ω R ⟶ (Over.pullback (sφ (φι jb))).obj U) :=
  letI : GrpObj ((Over.pullback (sφ (φι jb))).obj U) := Functor.grpObjObj
  (Φ (φι jb) U R).symm.toMonoidHom.comp (@e R _ (algBar jb R))

theorem torusΩ_natural (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (r : ℕ)
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
    (R S : Type) [CommRing R] [Algebra Ω R] [CommRing S] [Algebra Ω S] (f : R →ₐ[Ω] S)
    (t : Fin r → Rˣ) :
    torusΩ jb U r e S (fun i => Units.map (f : R →* S) (t i)) = SpecPtMap f ≫ torusΩ jb U r e R t := by
  letI : GrpObj ((Over.pullback (sφ (φι jb))).obj U) := Functor.grpObjObj
  letI := algK (φι jb) R
  letI := algK (φι jb) S
  simp only [torusΩ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
  apply (Φ (φι jb) U S).injective
  rw [MulEquiv.apply_symm_apply, Φ_natural, MulEquiv.apply_symm_apply]
  letI := algBar jb R
  letI := algBar jb S
  let f' : R →ₐ[AlgebraicClosure k] S :=
    { (f : R →+* S) with commutes' := fun a => f.commutes (jb a) }
  exact he_nat R S f' t

/-- **Torus survival with rank, on special fibres.** -/
theorem toricRank_le_special (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (r : ℕ)
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
    (G' U' : Over (Spec (CommRingCat.of Ω))) [GrpObj G'] [GrpObj U'] (inc : U' ⟶ G')
    [IsOpenImmersion inc.left] [IsMonHom inc]
    (B' : Over (Spec (CommRingCat.of Ω))) [GrpObj B'] [IsProper B'.hom] (π : U' ⟶ B') [IsMonHom π]
    (r' : ℕ) (e' : ∀ (R : Type) [CommRing R] [Algebra Ω R], (Fin r' → Rˣ) →* (SpecPt Ω R ⟶ U'))
    (he'_inj : ∀ (R : Type) [CommRing R] [Algebra Ω R], Function.Injective (e' R))
    (he'_ker : ∀ (R : Type) [CommRing R] [Algebra Ω R] (u : SpecPt Ω R ⟶ U'),
      u ≫ π = 1 ↔ u ∈ (e' R).range)
    (ψ : (Over.pullback (sφ (φι jb))).obj U ⟶ G')
    (hψ : letI : GrpObj ((Over.pullback (sφ (φι jb))).obj U) := Functor.grpObjObj; IsMonHom ψ)
    (m : ℕ) (hm : 2 ≤ m) [NeZero (m : Ω)]
    (hker : ∀ t : Fin r → Ωˣ, t ^ m = 1 → torusΩ jb U r e Ω t ≫ ψ = 1 → t = 1) :
    r ≤ r' := by
  letI : GrpObj ((Over.pullback (sφ (φι jb))).obj U) := Functor.grpObjObj
  exact toricRank_le_of_torusMap_open ((Over.pullback (sφ (φι jb))).obj U) r (torusΩ jb U r e)
    (torusΩ_natural jb U r e he_nat) G' U' inc B' π r' e' he'_inj he'_ker ψ m hm hker

end ToricBaseChange
