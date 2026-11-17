import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Units of the group ring of an elementary abelian 2-group (Lane RC7, manuscript §9)

This file formalizes the invertibility statements over the group ring `S = O[G]` used in §9 of the
manuscript (`diophantine_zq.tex`, the 11/5 version):

* tex 5404–5414 (`ex:limits-fixed-field-budget`): "the augmentation ideal is contained in the
  Jacobson radical of `R`", so pivots and elementary operations found after augmentation lift, and
  the lifted matrices "are invertible because their augmented determinants are units";
* tex 5509–5512 (`ex:limits-fixed-field-clearing`): "the canceled block is invertible over `S`",
  so its determinant and inverse are integral over `S`;
* tex 5466–5469: "every sign evaluation of a matrix over `Λ[G]` has the same reduction modulo two as
  its augmentation, because each sign is congruent to one modulo two", i.e. `B_x = B_0 + 2 V_x`.

Setting: `O` is any commutative ring in which `2` lies in the Jacobson radical, phrased as
`∀ y, IsUnit (1 + 2 * y)` (true for the 2-adically complete local coefficient rings of the
manuscript), and `G` is a finite commutative monoid with `g * g = 1` for all `g` (that is, a finite
elementary abelian 2-group).  The augmentation `aug : O[G] →ₐ[O] O` is induced by the trivial
character and `signEval x` by a sign character `x : G →* ℤˣ`.

Route: `O[G]` is a finite, hence integral, `O`-algebra, so its maximal ideals contract to maximal
ideals of `O` and `2` lies in the Jacobson radical of `O[G]`.  For `y` in the augmentation ideal,
`y ^ 2 ∈ 2 O[G]` because `(g - 1) ^ 2 = 2 (1 - g)`; hence `(1 + y) (1 - y) = 1 - y ^ 2` is a unit.
Everything here is PROVED.
-/

namespace ZInQ.Manuscript.RC.Determinant

open MonoidAlgebra

variable {O : Type*} [CommRing O] {G : Type*} [CommMonoid G]

/-! ### The augmentation -/

/-- The augmentation `O[G] → O`: the `O`-algebra map induced by the trivial character `G → O`,
sending every group element to `1`. -/
noncomputable def aug : MonoidAlgebra O G →ₐ[O] O := MonoidAlgebra.lift O O G 1

/-- **Tex 5404–5414 (PROVED).**  The augmentation of `c • g` is `c`. -/
@[simp] theorem aug_single (g : G) (c : O) : aug (MonoidAlgebra.single g c) = c := by
  simp [aug]

/-- **Tex 5404–5414 (PROVED).**  The augmentation of a group element is `1`. -/
theorem aug_of (g : G) : aug (MonoidAlgebra.of O G g) = 1 := by
  simp [aug]

/-! ### `2` lies in the Jacobson radical of `O[G]` -/

/-- **Tex 5404–5406 (PROVED).**  If `2` lies in the Jacobson radical of `O`, it lies in the
Jacobson radical of `O[G]` for every finite commutative `G`: `O[G]` is a finite, hence integral,
`O`-algebra, so every maximal ideal of `O[G]` contracts to a maximal ideal of `O`. -/
theorem two_mem_jacobson [Finite G] (h2 : ∀ y : O, IsUnit (1 + 2 * y)) :
    (2 : MonoidAlgebra O G) ∈ (⊥ : Ideal (MonoidAlgebra O G)).jacobson := by
  have h2O : (2 : O) ∈ (⊥ : Ideal O).jacobson := by
    rw [Ideal.mem_jacobson_bot]
    intro y; rw [add_comm]; exact h2 y
  have hint : (algebraMap O (MonoidAlgebra O G)).IsIntegral := fun x =>
    Algebra.IsIntegral.isIntegral x
  rw [Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨-, hm⟩
  have hc := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap O _) hint m
  have hle : (⊥ : Ideal O).jacobson ≤ Ideal.comap (algebraMap O (MonoidAlgebra O G)) m :=
    sInf_le ⟨bot_le, hc⟩
  have := hle h2O
  rwa [Ideal.mem_comap, map_ofNat] at this

/-- **Tex 5404–5406 (PROVED).**  `2` lies in the Jacobson radical of `S = O[G]`: for every
`s ∈ O[G]`, the element `1 + 2 s` is a unit. -/
theorem isUnit_one_add_two_mul [Finite G] (h2 : ∀ y : O, IsUnit (1 + 2 * y))
    (s : MonoidAlgebra O G) : IsUnit (1 + 2 * s) := by
  have := Ideal.mem_jacobson_bot.mp (two_mem_jacobson (G := G) h2) s
  rwa [add_comm] at this

/-! ### The augmentation ideal -/

/-- **Tex 5404–5406 (PROVED).**  For an elementary abelian 2-group `G`, the square of every element
of the augmentation ideal lies in `2 O[G]`.  Indeed `(g - 1) ^ 2 = 2 (1 - g)`, the set of `y` with
`y ^ 2 ∈ 2 O[G]` is closed under sums and `O`-multiples, and `y = ∑ c_g (g - 1)` when
`aug y = 0`. -/
theorem sq_mem_two_of_aug_eq_zero (hG : ∀ g : G, g * g = 1) (y : MonoidAlgebra O G)
    (hy : aug y = 0) : ∃ z, y * y = 2 * z := by
  have key : ∀ y : MonoidAlgebra O G, ∃ z,
      (y - algebraMap O _ (aug y)) * (y - algebraMap O _ (aug y)) = 2 * z := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of g =>
      refine ⟨1 - MonoidAlgebra.of O G g, ?_⟩
      have hg : MonoidAlgebra.of O G g * MonoidAlgebra.of O G g = 1 := by
        rw [← map_mul, hG, map_one]
      rw [aug_of, map_one]
      linear_combination hg
    | add a b ha hb =>
      obtain ⟨z₁, h₁⟩ := ha
      obtain ⟨z₂, h₂⟩ := hb
      refine ⟨z₁ + (a - algebraMap O _ (aug a)) * (b - algebraMap O _ (aug b)) + z₂, ?_⟩
      rw [map_add, map_add]
      linear_combination h₁ + h₂
    | smul r a ha =>
      obtain ⟨z, hz⟩ := ha
      refine ⟨algebraMap O _ r ^ 2 * z, ?_⟩
      rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]
      linear_combination algebraMap O (MonoidAlgebra O G) r ^ 2 * hz
  simpa [hy] using key y

/-- **Tex 5404–5414 (PROVED).**  An element of `O[G]` whose augmentation is a unit of `O` is a unit
of `O[G]`.  After scaling, `aug t = 1`; with `y = t - 1` one has `y ^ 2 = 2 z`, so
`t (1 - y) = 1 - y ^ 2 = 1 - 2 z` is a unit. -/
theorem isUnit_of_isUnit_aug [Finite G] (h2 : ∀ y : O, IsUnit (1 + 2 * y))
    (hG : ∀ g : G, g * g = 1) (s : MonoidAlgebra O G) (hs : IsUnit (aug s)) : IsUnit s := by
  obtain ⟨u, hu⟩ := hs
  set t : MonoidAlgebra O G := algebraMap O _ (↑u⁻¹ : O) * s with ht_def
  have ht : aug t = 1 := by
    rw [ht_def, map_mul, AlgHom.commutes, ← hu]
    simp
  obtain ⟨z, hz⟩ := sq_mem_two_of_aug_eq_zero hG (t - 1) (by rw [map_sub, ht, map_one, sub_self])
  have h1 : IsUnit (t * (1 - (t - 1))) := by
    have : t * (1 - (t - 1)) = 1 + 2 * (-z) := by linear_combination -hz
    rw [this]; exact isUnit_one_add_two_mul h2 _
  have htu : IsUnit t := isUnit_of_mul_isUnit_left h1
  have hcu : IsUnit (algebraMap O (MonoidAlgebra O G) (u : O)) := u.isUnit.map _
  have hs : s = algebraMap O (MonoidAlgebra O G) (u : O) * t := by
    rw [ht_def, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  rw [hs]; exact hcu.mul htu

/-- **Tex 5404–5414 (PROVED).**  An element of `O[G]` is a unit if and only if its augmentation
is a unit of `O`. -/
theorem isUnit_iff_isUnit_aug [Finite G] (h2 : ∀ y : O, IsUnit (1 + 2 * y))
    (hG : ∀ g : G, g * g = 1) (s : MonoidAlgebra O G) : IsUnit s ↔ IsUnit (aug s) :=
  ⟨fun hs => hs.map aug, isUnit_of_isUnit_aug h2 hG s⟩

/-- **Tex 5404–5406 (PROVED).**  The augmentation ideal is contained in the Jacobson radical
of `O[G]`. -/
theorem ker_aug_le_jacobson [Finite G] (h2 : ∀ y : O, IsUnit (1 + 2 * y))
    (hG : ∀ g : G, g * g = 1) :
    RingHom.ker (aug : MonoidAlgebra O G →ₐ[O] O) ≤ (⊥ : Ideal (MonoidAlgebra O G)).jacobson := by
  intro y hy
  rw [RingHom.mem_ker] at hy
  rw [Ideal.mem_jacobson_bot]
  intro s
  apply isUnit_of_isUnit_aug h2 hG
  simp [hy]

/-! ### Matrices over `O[G]` -/

/-- **Tex 5412–5414 and 5509–5512 (PROVED).**  A square matrix over `O[G]` whose augmented
determinant is a unit has a unit determinant over `S = O[G]`. -/
theorem isUnit_det_of_isUnit_aug [Finite G] (h2 : ∀ y : O, IsUnit (1 + 2 * y))
    (hG : ∀ g : G, g * g = 1) {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n (MonoidAlgebra O G)) (hB : IsUnit (B.map aug).det) : IsUnit B.det := by
  apply isUnit_of_isUnit_aug h2 hG
  rw [AlgHom.map_det]
  exact hB

/-- **Tex 5412–5414 and 5509–5512 (PROVED).**  A square matrix over `O[G]` whose augmented
determinant is a unit is invertible over `S = O[G]` (its inverse has entries in `S`). -/
theorem matrix_isUnit_of_isUnit_aug [Finite G] (h2 : ∀ y : O, IsUnit (1 + 2 * y))
    (hG : ∀ g : G, g * g = 1) {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n (MonoidAlgebra O G)) (hB : IsUnit (B.map aug).det) : IsUnit B := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_det_of_isUnit_aug h2 hG B hB

/-- **Tex 5412–5414 and 5509–5512 (PROVED).**  A square matrix over `O[G]` is invertible if and
only if its augmented determinant is a unit of `O`. -/
theorem matrix_isUnit_iff_isUnit_aug [Finite G] (h2 : ∀ y : O, IsUnit (1 + 2 * y))
    (hG : ∀ g : G, g * g = 1) {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n (MonoidAlgebra O G)) : IsUnit B ↔ IsUnit (B.map aug).det := by
  refine ⟨fun hB => ?_, matrix_isUnit_of_isUnit_aug h2 hG B⟩
  rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
  exact ((Matrix.isUnit_iff_isUnit_det B).mp hB).map aug

/-! ### Sign evaluations -/

/-- Evaluation of `O[G]` at a sign character `x : G →* ℤˣ`: the `O`-algebra map sending each
group element `g` to `x g = ±1`. -/
noncomputable def signEval (x : G →* ℤˣ) : MonoidAlgebra O G →ₐ[O] O :=
  MonoidAlgebra.lift O O G
    ((Units.coeHom O).comp ((Units.map (Int.castRingHom O).toMonoidHom).comp x))

/-- **Tex 5466–5469 (PROVED).**  The sign evaluation of `c • g` is `c · x g`. -/
@[simp] theorem signEval_single (x : G →* ℤˣ) (g : G) (c : O) :
    signEval x (MonoidAlgebra.single g c) = c * ((x g : ℤ) : O) := by
  simp [signEval]

/-- **Tex 5466–5469 (PROVED).**  The sign evaluation of a group element `g` is the sign `x g`. -/
theorem signEval_of (x : G →* ℤˣ) (g : G) :
    signEval x (MonoidAlgebra.of O G g) = ((x g : ℤ) : O) := by
  simp

/-- **Tex 5466–5469 (PROVED).**  Every sign evaluation has the same reduction modulo two as the
augmentation, because each sign is congruent to one modulo two: `signEval x s - aug s ∈ 2 O`. -/
theorem signEval_sub_aug_mem (x : G →* ℤˣ) (s : MonoidAlgebra O G) :
    ∃ v : O, signEval x s - aug s = 2 * v := by
  induction s using MonoidAlgebra.induction_on with
  | of g =>
    rcases Int.units_eq_one_or (x g) with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨-1, by simp [h]; norm_num⟩
  | add a b ha hb =>
    obtain ⟨v₁, h₁⟩ := ha
    obtain ⟨v₂, h₂⟩ := hb
    exact ⟨v₁ + v₂, by rw [map_add, map_add]; linear_combination h₁ + h₂⟩
  | smul r a ha =>
    obtain ⟨v, hv⟩ := ha
    exact ⟨r * v, by rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]; linear_combination r * hv⟩

/-- **Tex 5466–5469 (PROVED).**  Matrix form: for every matrix `B` over `O[G]` and every sign
character `x`, `B_x = B_0 + 2 V_x` for a matrix `V_x` over `O`, where `B_x` is the sign evaluation
and `B_0` the augmentation of `B`. -/
theorem matrix_signEval_eq_aug_add_two_smul (x : G →* ℤˣ) {m n : Type*}
    (B : Matrix m n (MonoidAlgebra O G)) :
    ∃ V : Matrix m n O, B.map (signEval x) = B.map aug + (2 : O) • V := by
  choose v hv using fun i j => signEval_sub_aug_mem x (B i j)
  refine ⟨Matrix.of v, ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  linear_combination hv i j

end ZInQ.Manuscript.RC.Determinant
