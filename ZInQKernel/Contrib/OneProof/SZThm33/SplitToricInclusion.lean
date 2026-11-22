import ZInQKernel.Contrib.OneProof.FaltingsDict2SplitTorus

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit ZInQ.SemiAbDescend ZInQ.FaltingsRestate

namespace SZRaynaud

variable {k : Type} [Field k]

private theorem hom_ext_of_affine_points {X Y : (Over (Spec (CommRingCat.of k)))} {f g : X ⟶ Y}
    (h : ∀ (R : Type) [CommRing R] [Algebra k R] (p : algPt k R ⟶ X), p ≫ f = p ≫ g) :
    f = g := by
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (cov X) _ _ fun x => ?_
  let := isAffine_coverObj X x
  obtain ⟨R, _, _, ⟨a⟩⟩ := exists_iso_algPt (coverObj X x)
  have he := h R (a.inv ≫ coverMap X x)
  rw [Category.assoc, Category.assoc, cancel_epi] at he
  exact congrArg CommaMorphism.left he

/-- Evaluating the natural split-torus presentation on the universal tuple
produces the geometric group homomorphism, with its action on every affine test point. -/
theorem exists_splitToricInclusion {U : (Over (Spec (CommRingCat.of k)))} [GrpObj U] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U))
    (hn : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
      (f : R →ₐ[k] S) (t : Fin r → Rˣ),
      e S (fun j => Units.map (f : R →* S) (t j)) = algPtMap f ≫ e R t) :
    ∃ i : splitTorus k r ⟶ U, IsMonHom i ∧
      ∀ (R : Type) [CommRing R] [Algebra k R] (x : algPt k R ⟶ splitTorus k r),
        x ≫ i = e R (splitTorusPoints R x) := by
  let A := TorusRing k r
  let M := splitTorus k r
  let u : Fin r → Aˣ := splitTorusPoints A (𝟙 M)
  let i : M ⟶ U := e A u
  have formula (R : Type) [CommRing R] [Algebra k R] (x : algPt k R ⟶ M) :
      x ≫ i = e R (splitTorusPoints R x) := by
    obtain ⟨f, hx⟩ := exists_algPtMap (K := k) (R := R) (S := A) x
    calc
      x ≫ i = algPtMap f ≫ e A u := congrArg (fun (z : algPt k R ⟶ M) => z ≫ e A u) hx
      _ = e R (fun j => Units.map (f : A →* R) (u j)) := (hn A R f u).symm
      _ = e R (splitTorusPoints R x) := by
        rw [← splitTorusPoints_natural (p := 𝟙 M)]
        have hx' : algPtMap (k := k) f ≫ 𝟙 M = x := (Category.comp_id _).trans hx.symm
        exact congrArg (fun z : algPt k R ⟶ M => e R (splitTorusPoints R z)) hx'
  have iOne (R : Type) [CommRing R] [Algebra k R] :
      (1 : algPt k R ⟶ M) ≫ i = 1 := by rw [formula, map_one, map_one]
  have iMul (R : Type) [CommRing R] [Algebra k R] (x y : algPt k R ⟶ M) :
      (x * y) ≫ i = (x ≫ i) * (y ≫ i) := by rw [formula, map_mul, map_mul, formula, formula]
  refine ⟨i, ⟨?_, ?_⟩, formula⟩
  · apply hom_ext_of_affine_points
    intro R _ _ x
    simp only [← Category.assoc, MonObj.one_eq_one, MonObj.comp_one]
    exact iOne R
  · apply hom_ext_of_affine_points
    intro R _ _ x
    simp only [← Category.assoc, MonObj.mul_eq_mul, MonObj.comp_mul]
    simpa only [tensorHom_fst, tensorHom_snd, Category.assoc] using iMul R
      (x ≫ fst M M) (x ≫ snd M M)

end SZRaynaud
