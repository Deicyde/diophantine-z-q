import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.CentralDeterminants

/-!
# The central Frobenius determinants are nonzero, without the Hasse bound

Proposition `ex:arith-paired-functional`, tex L3763–3764 ("the nonzero central Frobenius
determinants give integral adjugate contractions"); Lemma `ex:arith-central-specialization`, tex
L3929–3930; Proposition `ex:limits-uniform-lower-bound`, tex L5185–5186 ("the central Frobenius
determinants are nonzero and hence units in `R`").

`ELLIOT` gap: the text gives no reason. `PairedFunctional/CentralDeterminants.lean` fills it with
the Hasse bound `a_r² ≤ 4r`, taken as a hypothesis (Hasse's theorem is not in the library). This
file shows that the Hasse bound is not needed. Only the two trivial point-count bounds are used.

At the moving prime `r` (residue field `k` with `q = |k|` elements), Frobenius `Φ` acts on the
rank-two coefficient module with characteristic polynomial `x² − a x + q`, `a = ±a_r`, where
`a_r = q + 1 − |Ẽ(k)|` is the trace of Frobenius of the reduction `Ẽ` (this is how the text reads
`a`). The two central determinants are `det(Φ − 1) = 1 − a + q` and `det(Φ − q) = q(q + 1 − a)`.
Both vanish only if `a = q + 1`, that is:

* `a = a_r` and `|Ẽ(k)| = 0`, impossible since `Ẽ(k)` contains the point at infinity
  (`one_le_card_point`); or
* `a = −a_r` and `|Ẽ(k)| = 2q + 2`, impossible since each `x ∈ k` gives at most two points
  (the Weierstrass equation is a monic quadratic in `y`), so `|Ẽ(k)| ≤ 2q + 1`
  (`card_point_le`).

Results:
* `card_point_le`, `one_le_card_point` (PROVED): `1 ≤ |W(k)| ≤ 2q + 1` for every Weierstrass curve
  `W` over a finite field `k` (nonsingular points plus the point at infinity, Mathlib's
  `WeierstrassCurve.Affine.Point`).
* **`centralFrobeniusDeterminantsNonzeroCount_proof` (PROVED)**: for `Φ ∈ M₂(ℤ)` with `det Φ = q`
  and `tr Φ = ±(q + 1 − |W(k)|)`, both central determinants are nonzero. There is no Hasse
  hypothesis and no condition on `W` (good reduction is not needed for the count bounds).
* Non-vacuity: `centralFrobeniusCount_example` — for every Weierstrass curve over every finite
  field, `Φ = [[0, −q], [1, a_r]]` satisfies the hypotheses. Concrete instance: `y² = x³ − x` over
  `𝔽₃` (`exCurve3`).

The identification `tr Φ = ±a_r` (the characteristic polynomial of Frobenius on `T₂E` at a good
prime) is the standard reading of the text's `a = ±a_r`. It is a hypothesis here, as it is in the
Hasse version.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.FrobCount

open Polynomial Matrix WeierstrassCurve.Affine
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (det_sub_scalar_fin_two)

open Classical

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve.Affine F)

/-- The Weierstrass equation at fixed `x`, as a monic quadratic in `y`. -/
def yPoly (x : F) : F[X] :=
  C 1 * X ^ 2 + C (W.a₁ * x + W.a₃) * X + C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))

omit [Fintype F] in
theorem natDegree_yPoly (x : F) : (yPoly W x).natDegree = 2 :=
  natDegree_quadratic one_ne_zero

omit [Fintype F] in
theorem yPoly_ne_zero (x : F) : yPoly W x ≠ 0 :=
  ne_zero_of_natDegree_gt (n := 0) (by rw [natDegree_yPoly]; norm_num)

/-- **At most two points over each `x`.** -/
theorem card_fiber_le (x : F) : (Finset.univ.filter fun y => Equation W x y).card ≤ 2 := by
  calc (Finset.univ.filter fun y => Equation W x y).card
      ≤ (yPoly W x).roots.toFinset.card := Finset.card_le_card fun y hy => by
        rw [Finset.mem_filter] at hy
        rw [Multiset.mem_toFinset, mem_roots (yPoly_ne_zero W x), IsRoot, yPoly]
        have h := (equation_iff' (W := W) x y).1 hy.2
        simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
        linear_combination h
    _ ≤ Multiset.card (yPoly W x).roots := Multiset.toFinset_card_le _
    _ ≤ (yPoly W x).natDegree := card_roots' _
    _ = 2 := natDegree_yPoly W x

/-- **At most `2q` affine points.** -/
theorem card_equation_le :
    (Finset.univ.filter fun xy : F × F => Equation W xy.1 xy.2).card ≤ 2 * Fintype.card F := by
  set s := Finset.univ.filter fun xy : F × F => Equation W xy.1 xy.2
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  calc ∑ x, (s.filter fun xy => xy.1 = x).card ≤ ∑ _x : F, 2 := by
        refine Finset.sum_le_sum fun x _ => ?_
        calc (s.filter fun xy => xy.1 = x).card
            ≤ ((Finset.univ.filter fun y => Equation W x y).image fun y => (x, y)).card := by
              refine Finset.card_le_card fun xy hxy => ?_
              simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
              obtain ⟨h, rfl⟩ := hxy
              simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨xy.2, h, rfl⟩
          _ ≤ (Finset.univ.filter fun y => Equation W x y).card := Finset.card_image_le
          _ ≤ 2 := card_fiber_le W x
    _ = 2 * Fintype.card F := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- Points are the point at infinity or a nonsingular affine point. -/
def pointEquiv : (Point W) ≃ Option {xy : F × F // Nonsingular W xy.1 xy.2} where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x, y), h⟩
  invFun
    | none => .zero
    | some p => .some p.1.1 p.1.2 p.2
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | ⟨⟨_, _⟩, _⟩) <;> rfl

instance : Finite (Point W) := Finite.of_equiv _ (pointEquiv W).symm

/-- **The point at infinity**: `1 ≤ |W(k)|`. -/
theorem one_le_card_point : 1 ≤ Nat.card (Point W) :=
  haveI : Nonempty (Point W) := ⟨.zero⟩
  Nat.card_pos

/-- **`|W(k)| ≤ 2q + 1`.** -/
theorem card_point_le : Nat.card (Point W) ≤ 2 * Fintype.card F + 1 := by
  rw [Nat.card_congr (pointEquiv W), Nat.card_eq_fintype_card, Fintype.card_option]
  have h1 : Fintype.card {xy : F × F // Nonsingular W xy.1 xy.2} ≤
      Fintype.card {xy : F × F // Equation W xy.1 xy.2} :=
    Fintype.card_subtype_mono _ _ (fun xy h => h.1)
  have h3 : Fintype.card {xy : F × F // Equation W xy.1 xy.2} =
      (Finset.univ.filter fun xy : F × F => Equation W xy.1 xy.2).card :=
    Fintype.card_subtype _
  have h2 := card_equation_le W
  omega

/-- **The central Frobenius determinants from point counts** (tex L3763–3764, L3929–3930,
L5185–5186): for a Weierstrass curve `W` over a finite field with `q` elements and `Φ ∈ M₂(ℤ)` with
`det Φ = q` and `tr Φ = ±(q + 1 − |W(k)|)`, `det(Φ − 1) ≠ 0` and `det(Φ − q) ≠ 0`. -/
def CentralFrobeniusDeterminantsNonzeroCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (W : WeierstrassCurve.Affine F)
    (Φ : Matrix (Fin 2) (Fin 2) ℤ), Φ.det = Fintype.card F →
    (Φ.trace = (Fintype.card F : ℤ) + 1 - Nat.card (Point W) ∨
      Φ.trace = -((Fintype.card F : ℤ) + 1 - Nat.card (Point W))) →
    (Φ - (1 : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 ∧
      (Φ - (Fintype.card F : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0

/-- **PROVED, with no Hasse hypothesis.** -/
theorem centralFrobeniusDeterminantsNonzeroCount_proof :
    CentralFrobeniusDeterminantsNonzeroCount := by
  intro F _ _ W Φ hdet htr
  have hq : (0 : ℤ) < (Fintype.card F : ℤ) := by
    have : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast this
  have hlo : (1 : ℤ) ≤ Nat.card (Point W) := by exact_mod_cast one_le_card_point W
  have hhi : (Nat.card (Point W) : ℤ) ≤ 2 * (Fintype.card F : ℤ) + 1 := by
    exact_mod_cast card_point_le W
  generalize (Fintype.card F : ℤ) = q at *
  generalize (Nat.card (Point W) : ℤ) = N at *
  have key : Φ.trace ≠ q + 1 := by
    intro h
    rcases htr with h' | h' <;> rw [h'] at h <;> omega
  have h1 : (Φ - (1 : Matrix (Fin 2) (Fin 2) ℤ)).det = 1 - Φ.trace + q := by
    have := det_sub_scalar_fin_two Φ 1
    rw [one_smul] at this
    rw [this, hdet]; ring
  refine ⟨?_, ?_⟩
  · rw [h1]; intro h; exact key (by linarith)
  · rw [det_sub_scalar_fin_two, hdet]
    have : q ^ 2 - Φ.trace * q + q = q * (q + 1 - Φ.trace) := by ring
    rw [this]
    exact mul_ne_zero hq.ne' (fun h => key (by linarith))

/-- **Non-vacuity**: for every Weierstrass curve over every finite field, the companion matrix
`[[0, −q], [1, a_r]]` of `x² − a_r x + q` satisfies the hypotheses. -/
theorem centralFrobeniusCount_example :
    (!![0, -(Fintype.card F : ℤ); 1, (Fintype.card F : ℤ) + 1 - Nat.card (Point W)] :
        Matrix (Fin 2) (Fin 2) ℤ).det = Fintype.card F ∧
      (!![0, -(Fintype.card F : ℤ); 1, (Fintype.card F : ℤ) + 1 - Nat.card (Point W)] :
        Matrix (Fin 2) (Fin 2) ℤ).trace = (Fintype.card F : ℤ) + 1 - Nat.card (Point W) := by
  constructor
  · rw [Matrix.det_fin_two_of]; ring
  · rw [Matrix.trace_fin_two_of]; ring

/-- A concrete curve: `y² = x³ − x` over `𝔽₃`. -/
def exCurve3 : WeierstrassCurve.Affine (ZMod 3) := ⟨0, 0, 0, -1, 0⟩

/-- The concrete instance of the hypotheses and conclusion over `𝔽₃`. -/
theorem exCurve3_nonzero :
    let Φ : Matrix (Fin 2) (Fin 2) ℤ :=
      !![0, -(Fintype.card (ZMod 3) : ℤ);
        1, (Fintype.card (ZMod 3) : ℤ) + 1 - Nat.card (Point exCurve3)]
    (Φ - (1 : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 ∧
      (Φ - (Fintype.card (ZMod 3) : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 :=
  centralFrobeniusDeterminantsNonzeroCount_proof (ZMod 3) exCurve3 _
    (centralFrobeniusCount_example exCurve3).1 (Or.inl (centralFrobeniusCount_example exCurve3).2)

end ZInQ.Contrib.CloudB3RC53.FrobCount
