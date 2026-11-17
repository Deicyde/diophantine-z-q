import ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect

/-! Verbatim copies (semiab-descend) of the target and of the two definitions it uses, checked by `rfl`. -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open DictModels.RaynaudOr ZInQ.HeightSplit

namespace SemiAbDescendCopy

def HasSemiAbelianIdentityComponent {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] : Prop :=
  ∃ (U : Over (Spec (CommRingCat.of k))) (_ : GrpObj U) (inc : U ⟶ G),
    IsOpenImmersion inc.left ∧ IsMonHom inc ∧ ConnectedSpace U.left ∧
    ∃ (B : PkgI3.AbVar k) (π : U ⟶ B.X), IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧
    ∃ (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U)),
      (∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R)) ∧
      (∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
        u ≫ π = 1 ↔ u ∈ (e R).range) ∧
      (∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
        (t : Fin r → Rˣ), e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)

def HasSemiAbelianIdCompTorus {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] : Prop :=
  ∃ (U : Over (Spec (CommRingCat.of k))) (_ : GrpObj U) (inc : U ⟶ G),
    IsOpenImmersion inc.left ∧ IsMonHom inc ∧ ConnectedSpace U.left ∧
    ∃ (B : PkgI3.AbVar k) (π : U ⟶ B.X), IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧
    ∃ (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
        letI := algK (φbar k) R
        (Fin r → Rˣ) →* (algPt k R ⟶ U)),
      (∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], Function.Injective (e R)) ∧
      (∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
        letI := algK (φbar k) R
        ∀ u : algPt k R ⟶ U, u ≫ π = 1 ↔ u ∈ (e R).range) ∧
      (∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
        [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
        letI := algK (φbar k) R
        letI := algK (φbar k) S
        e S (fun i => Units.map (f : R →* S) (t i)) =
          algPtMap (k := k) ({ (f : R →+* S) with commutes' := fun a => f.commutes (φbar k a) } :
            R →ₐ[k] S) ≫ e R t)

def SemiAbelianDescendsPerfect : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom],
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj G) := Functor.grpObjObj
    HasSemiAbelianIdentityComponent ((Over.pullback (sφ (φbar k))).obj G) →
      HasSemiAbelianIdCompTorus G

example : @HasSemiAbelianIdentityComponent = @ZInQ.HeightSplit.HasSemiAbelianIdentityComponent := rfl
example : @HasSemiAbelianIdCompTorus = @DictModels.RaynaudOr.HasSemiAbelianIdCompTorus := rfl
example : SemiAbelianDescendsPerfect = ZInQ.HeightFix.SemiAbelianDescendsPerfect := rfl

/-- The copy (with the copied definitions) is the statement proved. -/
example (hC : ZInQ.SemiAbDescend.ChevalleyPerfect) : SemiAbelianDescendsPerfect :=
  ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley hC

end SemiAbDescendCopy
