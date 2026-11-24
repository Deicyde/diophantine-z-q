import ZInQKernel.Contrib.OneProof.FaltingsDict2SplitTorus

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace ZInQ.ToricOrthogonality

open ZInQ.FaltingsRestate ZInQ.HeightSplit ZInQ.SemiAbDescend

variable {k : Type} [Field k]

private theorem hom_ext_of_algPt {X Y : (Over (Spec (CommRingCat.of k)))} {f g : X ⟶ Y}
    (h : ∀ (R : Type) [CommRing R] [Algebra k R] (p : algPt k R ⟶ X), p ≫ f = p ≫ g) :
    f = g := by
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (cov X) _ _ fun x => ?_
  let := isAffine_coverObj X x
  obtain ⟨R, _, _, ⟨a⟩⟩ := exists_iso_algPt (coverObj X x)
  have he := h R (a.inv ≫ coverMap X x)
  rw [Category.assoc, Category.assoc, cancel_epi] at he
  exact congrArg CommaMorphism.left he

/-- Embed the rank-one split torus as the indicated coordinate. -/
def torusCoordinate (r : ℕ) (i : Fin r) : splitTorus k 1 ⟶ splitTorus k r :=
  (splitTorusPoints (TorusRing k 1)).symm
    (fun j => if j = i then splitTorusPoints (TorusRing k 1) (𝟙 (splitTorus k 1)) 0 else 1)

theorem torusCoordinate_points {r : ℕ} (i j : Fin r) {R : Type} [CommRing R] [Algebra k R]
    (p : algPt k R ⟶ splitTorus k 1) :
    splitTorusPoints R (p ≫ torusCoordinate r i) j =
      if j = i then splitTorusPoints R p 0 else 1 := by
  obtain ⟨f, rfl⟩ := exists_algPtMap (K := k) (R := R) (S := TorusRing k 1) p
  have h₁ := congrFun (splitTorusPoints_natural f (torusCoordinate (k := k) r i)) j
  have h₂ := congrFun (splitTorusPoints_natural f (𝟙 (splitTorus k 1))) 0
  erw [Category.comp_id] at h₂
  erw [h₁]
  simp only [torusCoordinate, MulEquiv.apply_symm_apply]
  split_ifs
  · exact h₂.symm
  · exact map_one _

theorem torusCoordinate_isMonHom {r : ℕ} (i : Fin r) : IsMonHom (torusCoordinate (k := k) r i) := by
  let d := torusCoordinate (k := k) r i
  have hOne (R : Type) [CommRing R] [Algebra k R] :
      (1 : algPt k R ⟶ splitTorus k 1) ≫ d = 1 := by
    apply (splitTorusPoints R).injective
    funext j
    rw [torusCoordinate_points, map_one, map_one]
    split_ifs <;> rfl
  have hMul (R : Type) [CommRing R] [Algebra k R] (x y : algPt k R ⟶ splitTorus k 1) :
      (x * y) ≫ d = (x ≫ d) * (y ≫ d) := by
    apply (splitTorusPoints R).injective
    funext j
    rw [torusCoordinate_points, map_mul, map_mul, Pi.mul_apply]
    change (if j = i then splitTorusPoints R x 0 * splitTorusPoints R y 0 else 1) =
      splitTorusPoints R (x ≫ torusCoordinate r i) j *
        splitTorusPoints R (y ≫ torusCoordinate r i) j
    rw [torusCoordinate_points, torusCoordinate_points]
    split_ifs <;> simp
  constructor
  · apply hom_ext_of_algPt
    intro R _ _ x
    simp only [← Category.assoc, MonObj.one_eq_one, MonObj.comp_one]
    exact hOne R
  · apply hom_ext_of_algPt
    intro R _ _ x
    simp only [← Category.assoc, MonObj.mul_eq_mul, MonObj.comp_mul]
    simpa only [tensorHom_fst, tensorHom_snd, Category.assoc] using hMul R
      (x ≫ fst (splitTorus k 1) (splitTorus k 1)) (x ≫ snd (splitTorus k 1) (splitTorus k 1))

instance splitTorus_isCommMonObj (r : ℕ) : IsCommMonObj (splitTorus k r) := by
  constructor
  apply hom_ext_of_algPt
  intro R _ _ x
  apply (splitTorusPoints R).injective
  simp only [← Category.assoc, MonObj.mul_eq_mul, MonObj.comp_mul]
  simp only [Category.assoc, braiding_hom_fst, braiding_hom_snd, map_mul]
  rw [mul_comm]

/-- Each torsion point on a split torus is a product of points of the same
torsion level in the coordinate subtori. -/
theorem exists_torus_torsion_coordinate_product {r n : ℕ} {R : Type} [CommRing R] [Algebra k R]
    (x : algPt k R ⟶ splitTorus k r) (hx : x ^ n = 1) :
    ∃ t : Fin r → (algPt k R ⟶ splitTorus k 1), (∀ j, t j ^ n = 1) ∧
      x = ∏ j, t j ≫ torusCoordinate r j := by
  let t (j : Fin r) : algPt k R ⟶ splitTorus k 1 :=
    (splitTorusPoints R).symm (fun _ => splitTorusPoints R x j)
  have ht (j : Fin r) (i : Fin 1) : splitTorusPoints R (t j) i = splitTorusPoints R x j := by
    simp [t]
  refine ⟨t, ?_, ?_⟩
  · intro j
    apply (splitTorusPoints R).injective
    funext i
    rw [map_pow, map_one, Pi.pow_apply, Pi.one_apply, ht]
    have hpow : (splitTorusPoints R x) ^ n = 1 := by rw [← map_pow, hx, map_one]
    exact congrFun hpow j
  · apply (splitTorusPoints R).injective
    funext i
    rw [map_prod, Finset.prod_apply, Finset.prod_eq_single i]
    · rw [torusCoordinate_points, ite_eq_left rfl, ht]
    · intro j _ hj
      rw [torusCoordinate_points, ite_eq_right (Ne.symm hj)]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.exists_torus_torsion_coordinate_product
