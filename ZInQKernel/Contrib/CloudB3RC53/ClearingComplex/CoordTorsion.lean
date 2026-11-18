import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.TorsionCancel
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.Patterns

/-!
# Elliot's determinant computation of the Knudsen–Mumford coordinate

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:limits-fixed-field-clearing`, tex
L5545–5617. For the remaining complex in block form over a field `K` (`BlockComplex K`:
`D⁰ = E₀`, `D¹ = B₁ ⊕ H₁ ⊕ E₁`, `D² = B₂ ⊕ H₂ ⊕ E₂`, `D³ = B₃`) with invertible Smith blocks
`A₀, A₁, A₂`, a cycle `z ∈ D¹` and a closed functional `μ` on `D²`, the Knudsen–Mumford coordinate
of `[z] ⊗ [μ]` (lane Torsion's `kmCoord`, the torsion of the augmented complex) is computed by
cancelling `A₀`, `A₁`, `A₂` in turn (`torsion_cancelE`, `torsion_cancelO`):

* `kmCoord_block` (PROVED): `kmCoord = −(α β if h = 0, else 0) · δ₀ δ₁⁻¹ δ₂`, where
  `α = z_H − C A₀⁻¹ z_B`, `β = μ_H − μ_E A₂⁻¹ B_H` (tex 5577–5581) and `h = d¹_{H₂H₁} −
  d¹_{H₂E₁} A₁⁻¹ d¹_{B₂H₁}` is the remaining map `H₁ → H₂` (tex 5584: "the final complex `H` has
  just the map `H₁ → H₂`");
* `alpha_eq_zero_of_hRem_ne_zero` (PROVED): if the remaining map is nonzero then `α = 0` (tex
  5613–5615: "Its cycle `α_x` is then zero over the fraction field").

The orientation is the one transported through the three cancellations (`σBlock`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion

variable {K : Type*} [Field K]

namespace BlockComplex

variable (D : BlockComplex K)

/-- The block complex as a four-term complex (lane Torsion's `FourCx`). -/
def toFour : FourCx K (Fin D.m0) (Fin D.m0 ⊕ Unit ⊕ Fin D.m1) (Fin D.m1 ⊕ Unit ⊕ Fin D.m2)
    (Fin D.m2) where
  d0 := D.d0
  d1 := D.d1
  d2 := D.d2
  d10 := D.d1_d0
  d21 := D.d2_d1

/-- `α = z_H − C A₀⁻¹ z_B`. -/
def alphaB (z : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → K) : K :=
  z (Sum.inr (Sum.inl ())) - (fun j => D.d0 (Sum.inr (Sum.inl ())) j) ⬝ᵥ (D.A0⁻¹ *ᵥ (z ∘ Sum.inl))

/-- `β = μ_H − μ_E A₂⁻¹ B_H`. -/
def betaB (μ : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → K) : K :=
  μ (Sum.inr (Sum.inl ())) -
    (fun e => μ (Sum.inr (Sum.inr e))) ⬝ᵥ (D.A2⁻¹ *ᵥ fun j => D.d2 j (Sum.inr (Sum.inl ())))

/-- The remaining map `H₁ → H₂` after cancelling `A₁`. -/
def hRem : K :=
  D.d1 (Sum.inr (Sum.inl ())) (Sum.inr (Sum.inl ())) -
    (fun e => D.d1 (Sum.inr (Sum.inl ())) (Sum.inr (Sum.inr e))) ⬝ᵥ
      (D.A1⁻¹ *ᵥ fun b => D.d1 (Sum.inl b) (Sum.inr (Sum.inl ())))

end BlockComplex

/-! ### The final two-line complex -/

section Final

open Classical in
/-- **The torsion of a complex `K --α--> H₁ --h--> H₂ --β--> K`** (degrees `0, 1, 2, 3`, even
basis `(K₀, H₂)`, odd basis `(H₁, K₃)`, oriented by `K₀ ↦ H₁`, `H₂ ↦ K₃`): `α β` if `h = 0`, and
`0` otherwise. -/
theorem torsion_final (S : BasedCx K (Unit ⊕ Unit) (Unit ⊕ Unit))
    (hE : S.degE = Sum.elim (fun _ => 0) (fun _ => 2))
    (hO : S.degO = Sum.elim (fun _ => 1) (fun _ => 3)) :
    torsion S (Equiv.refl _) =
      if S.dEO (Sum.inr ()) (Sum.inl ()) = 0 then
        S.dOE (Sum.inl ()) (Sum.inl ()) * S.dOE (Sum.inr ()) (Sum.inr ()) else 0 := by
  -- vanishing entries by degree
  have zOE : ∀ i j, S.degO i ≠ S.degE j + 1 → S.dOE i j = 0 := fun i j h => by
    by_contra hne; exact h (S.deg_dOE i j hne)
  have zEO : ∀ i j, S.degE i ≠ S.degO j + 1 → S.dEO i j = 0 := fun i j h => by
    by_contra hne; exact h (S.deg_dEO i j hne)
  have o12 : S.dOE (Sum.inl ()) (Sum.inr ()) = 0 := zOE _ _ (by rw [hE, hO]; simp)
  have o21 : S.dOE (Sum.inr ()) (Sum.inl ()) = 0 := zOE _ _ (by rw [hE, hO]; simp)
  have e11 : S.dEO (Sum.inl ()) (Sum.inl ()) = 0 := zEO _ _ (by rw [hE, hO]; simp)
  have e12 : S.dEO (Sum.inl ()) (Sum.inr ()) = 0 := zEO _ _ (by rw [hE, hO]; simp)
  have e22 : S.dEO (Sum.inr ()) (Sum.inr ()) = 0 := zEO _ _ (by rw [hE, hO]; simp)
  set a := S.dOE (Sum.inl ()) (Sum.inl ())
  set b := S.dOE (Sum.inr ()) (Sum.inr ())
  set h := S.dEO (Sum.inr ()) (Sum.inl ())
  -- a contraction forces `a ≠ 0` and `b ≠ 0`
  have hcon : ∀ c : Contraction S, a ≠ 0 ∧ b ≠ 0 := by
    intro c
    have eE := congrFun (congrFun c.htpy_E (Sum.inl ())) (Sum.inl ())
    have eO := congrFun (congrFun c.htpy_O (Sum.inr ())) (Sum.inr ())
    simp only [Matrix.add_apply, Matrix.mul_apply, Fintype.sum_sum_type, Finset.univ_unique,
      Finset.sum_singleton, Matrix.one_apply_eq, PUnit.default_eq_unit, e11, e12, o21, e22,
      zero_mul, mul_zero, add_zero, zero_add] at eE eO
    constructor
    · intro ha
      rw [show S.dOE (Sum.inl PUnit.unit) (Sum.inl ()) = 0 from ha] at eE; simp at eE
    · intro hb
      rw [show S.dOE (Sum.inr ()) (Sum.inr PUnit.unit) = 0 from hb] at eO; simp at eO
  -- `d² = 0` gives `h a = 0`
  have hha : h * a = 0 := by
    have := congrFun (congrFun S.dd_E (Sum.inr ())) (Sum.inl ())
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton,
      Matrix.zero_apply, PUnit.default_eq_unit, o21, mul_zero, add_zero] at this
    exact this
  split_ifs with hh
  · by_cases hab : a ≠ 0 ∧ b ≠ 0
    · -- the explicit contraction
      let c : Contraction S :=
        { hOE := 0
          hEO := Matrix.of fun i j => match i, j with
            | Sum.inl (), Sum.inl () => a⁻¹
            | Sum.inr (), Sum.inr () => b⁻¹
            | _, _ => 0
          deg_hOE := fun _ _ h => absurd rfl h
          deg_hEO := by
            rintro (i | i) (j | j) hne <;> simp at hne <;> rw [hE, hO] <;> simp
          htpy_E := by
            ext (i | i) (j | j) <;>
              simp [Matrix.mul_apply, Fintype.sum_sum_type, o12, o21, hab.1, hab.2, a, b]
          htpy_O := by
            ext (i | i) (j | j) <;>
              simp [Matrix.mul_apply, Fintype.sum_sum_type, o12, o21, hab.1, hab.2, a, b] }
      rw [← tau_eq_torsion S c]
      unfold tau
      have hM : (S.dOE + c.hOE).submatrix (⇑(Equiv.refl (Unit ⊕ Unit))) id =
          fromBlocks (of fun _ _ => a) 0 0 (of fun _ _ => b) := by
        ext (i | i) (j | j) <;> simp [c, o12, o21, a, b]
      rw [hM, det_fromBlocks_zero₂₁, det_unique, det_unique]
      rfl
    · have : a * b = 0 := by
        by_contra hne
        exact hab ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩
      rw [this]
      have hS : ¬ Nonempty (Contraction S) := fun ⟨c⟩ => hab (hcon c)
      unfold torsion
      simp only [hS, dite_false]
  · have ha : a = 0 := (mul_eq_zero.mp hha).resolve_left hh
    have hS : ¬ Nonempty (Contraction S) := fun ⟨c⟩ => (hcon c).1 ha
    unfold torsion
    simp only [hS, dite_false]

end Final

/-! ### The relabellings of the three cancellations -/

section Equivs

variable (m0 m1 m2 : ℕ)

/-- Step 1, even: `(E₀ ⊕ K₀) ⊕ (B₂ ⊕ H₂ ⊕ E₂) ≃ (K₀ ⊕ (B₂ ⊕ H₂ ⊕ E₂)) ⊕ E₀`. -/
def eE1 : (Fin m0 ⊕ Unit) ⊕ (Fin m1 ⊕ Unit ⊕ Fin m2) ≃
    (Unit ⊕ (Fin m1 ⊕ Unit ⊕ Fin m2)) ⊕ Fin m0 where
  toFun
    | .inl (.inl e) => .inr e
    | .inl (.inr u) => .inl (.inl u)
    | .inr x => .inl (.inr x)
  invFun
    | .inr e => .inl (.inl e)
    | .inl (.inl u) => .inl (.inr u)
    | .inl (.inr x) => .inr x
  left_inv := by rintro ((e | u) | x) <;> rfl
  right_inv := by rintro ((u | x) | e) <;> rfl

/-- Step 1, odd: `(B₁ ⊕ H₁ ⊕ E₁) ⊕ (B₃ ⊕ K₃) ≃ ((H₁ ⊕ E₁) ⊕ (B₃ ⊕ K₃)) ⊕ B₁`. -/
def eO1 : (Fin m0 ⊕ Unit ⊕ Fin m1) ⊕ (Fin m2 ⊕ Unit) ≃
    ((Unit ⊕ Fin m1) ⊕ (Fin m2 ⊕ Unit)) ⊕ Fin m0 where
  toFun
    | .inl (.inl b) => .inr b
    | .inl (.inr r) => .inl (.inl r)
    | .inr x => .inl (.inr x)
  invFun
    | .inr b => .inl (.inl b)
    | .inl (.inl r) => .inl (.inr r)
    | .inl (.inr x) => .inr x
  left_inv := by rintro ((b | r) | x) <;> rfl
  right_inv := by rintro ((r | x) | b) <;> rfl

/-- Step 2, even: `K₀ ⊕ (B₂ ⊕ H₂ ⊕ E₂) ≃ (K₀ ⊕ (H₂ ⊕ E₂)) ⊕ B₂`. -/
def eE2 : Unit ⊕ (Fin m1 ⊕ Unit ⊕ Fin m2) ≃ (Unit ⊕ (Unit ⊕ Fin m2)) ⊕ Fin m1 where
  toFun
    | .inl u => .inl (.inl u)
    | .inr (.inl b) => .inr b
    | .inr (.inr r) => .inl (.inr r)
  invFun
    | .inl (.inl u) => .inl u
    | .inr b => .inr (.inl b)
    | .inl (.inr r) => .inr (.inr r)
  left_inv := by rintro (u | (b | r)) <;> rfl
  right_inv := by rintro ((u | r) | b) <;> rfl

/-- Step 2, odd: `(H₁ ⊕ E₁) ⊕ (B₃ ⊕ K₃) ≃ (H₁ ⊕ (B₃ ⊕ K₃)) ⊕ E₁`. -/
def eO2 : (Unit ⊕ Fin m1) ⊕ (Fin m2 ⊕ Unit) ≃ (Unit ⊕ (Fin m2 ⊕ Unit)) ⊕ Fin m1 where
  toFun
    | .inl (.inl u) => .inl (.inl u)
    | .inl (.inr e) => .inr e
    | .inr x => .inl (.inr x)
  invFun
    | .inl (.inl u) => .inl (.inl u)
    | .inr e => .inl (.inr e)
    | .inl (.inr x) => .inr x
  left_inv := by rintro ((u | e) | x) <;> rfl
  right_inv := by rintro ((u | x) | e) <;> rfl

/-- Step 3, even: `K₀ ⊕ (H₂ ⊕ E₂) ≃ (K₀ ⊕ H₂) ⊕ E₂`. -/
def eE3 : Unit ⊕ (Unit ⊕ Fin m2) ≃ (Unit ⊕ Unit) ⊕ Fin m2 where
  toFun
    | .inl u => .inl (.inl u)
    | .inr (.inl u) => .inl (.inr u)
    | .inr (.inr e) => .inr e
  invFun
    | .inl (.inl u) => .inl u
    | .inl (.inr u) => .inr (.inl u)
    | .inr e => .inr (.inr e)
  left_inv := by rintro (u | (u | e)) <;> rfl
  right_inv := by rintro ((u | u) | e) <;> rfl

/-- Step 3, odd: `H₁ ⊕ (B₃ ⊕ K₃) ≃ (H₁ ⊕ K₃) ⊕ B₃`. -/
def eO3 : Unit ⊕ (Fin m2 ⊕ Unit) ≃ (Unit ⊕ Unit) ⊕ Fin m2 where
  toFun
    | .inl u => .inl (.inl u)
    | .inr (.inl b) => .inr b
    | .inr (.inr u) => .inl (.inr u)
  invFun
    | .inl (.inl u) => .inl u
    | .inr b => .inr (.inl b)
    | .inl (.inr u) => .inr (.inr u)
  left_inv := by rintro (u | (b | u)) <;> rfl
  right_inv := by rintro ((u | u) | b) <;> rfl

/-- The orientations of the remaining complexes. -/
def σ2 : Unit ⊕ (Unit ⊕ Fin m2) ≃ Unit ⊕ (Fin m2 ⊕ Unit) :=
  (eE3 m2).trans (((Equiv.refl (Unit ⊕ Unit)).sumCongr (Equiv.refl (Fin m2))).trans (eO3 m2).symm)

def σ1 : Unit ⊕ (Fin m1 ⊕ Unit ⊕ Fin m2) ≃ (Unit ⊕ Fin m1) ⊕ (Fin m2 ⊕ Unit) :=
  (eE2 m1 m2).trans (((σ2 m2).sumCongr (Equiv.refl (Fin m1))).trans (eO2 m1 m2).symm)

/-- **The orientation of the augmented block complex** (transported through the cancellations). -/
def σBlock : (Fin m0 ⊕ Unit) ⊕ (Fin m1 ⊕ Unit ⊕ Fin m2) ≃
    (Fin m0 ⊕ Unit ⊕ Fin m1) ⊕ (Fin m2 ⊕ Unit) :=
  (eE1 m0 m1 m2).trans (((σ1 m1 m2).sumCongr (Equiv.refl (Fin m0))).trans (eO1 m0 m1 m2).symm)

theorem transport_eq {κe κo α β E : Type*} (eE : κe ≃ α ⊕ E) (eO : κo ≃ β ⊕ E) (τ : α ≃ β) :
    eE.symm.trans ((eE.trans ((τ.sumCongr (Equiv.refl E)).trans eO.symm)).trans eO) =
      τ.sumCongr (Equiv.refl E) := by
  ext x; simp

end Equivs

/-! ### The three cancellations -/

section Chain

variable (D : BlockComplex K) (z : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → K)
  (μ : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → K) (hz : D.toFour.d1 *ᵥ z = 0)
  (hμ : μ ᵥ* D.toFour.d1 = 0)

/-- The augmented complex, relabelled for the first cancellation. -/
def C1 : BasedCx K ((Unit ⊕ (Fin D.m1 ⊕ Unit ⊕ Fin D.m2)) ⊕ Fin D.m0)
    (((Unit ⊕ Fin D.m1) ⊕ (Fin D.m2 ⊕ Unit)) ⊕ Fin D.m0) :=
  (D.toFour.aug z μ hz hμ).toBased.reindex (eE1 D.m0 D.m1 D.m2) (eO1 D.m0 D.m1 D.m2)

theorem C1_degE (e : Fin D.m0) : (C1 D z μ hz hμ).degE (Sum.inr e) = 0 := rfl
theorem C1_degO (b : Fin D.m0) : (C1 D z μ hz hμ).degO (Sum.inr b) = 0 + 1 := rfl
theorem C1_blkA : blkA (C1 D z μ hz hμ) = D.A0 := by
  ext b e; rfl

variable {D} (hA0 : IsUnit D.A0.det) (hA1 : IsUnit D.A1.det) (hA2 : IsUnit D.A2.det)

/-- After the first cancellation. -/
def S1 : BasedCx K (Unit ⊕ (Fin D.m1 ⊕ Unit ⊕ Fin D.m2)) ((Unit ⊕ Fin D.m1) ⊕ (Fin D.m2 ⊕ Unit)) :=
  schurE (C := C1 D z μ hz hμ) 0 (C1_degE D z μ hz hμ) (C1_degO D z μ hz hμ)
    (by rw [C1_blkA]; exact hA0)

/-- Relabelled for the second cancellation. -/
def C2 : BasedCx K ((Unit ⊕ (Unit ⊕ Fin D.m2)) ⊕ Fin D.m1) ((Unit ⊕ (Fin D.m2 ⊕ Unit)) ⊕ Fin D.m1) :=
  (S1 z μ hz hμ hA0).reindex (eE2 D.m1 D.m2) (eO2 D.m1 D.m2)

theorem C2_degO (e : Fin D.m1) : (C2 z μ hz hμ hA0).degO (Sum.inr e) = 1 := rfl
theorem C2_degE (b : Fin D.m1) : (C2 z μ hz hμ hA0).degE (Sum.inr b) = 1 + 1 := rfl
theorem C2_blk : (C2 z μ hz hμ hA0).dEO.toBlocks₂₂ = D.A1 := by
  ext b e; rfl

/-- After the second cancellation. -/
def S2 : BasedCx K (Unit ⊕ (Unit ⊕ Fin D.m2)) (Unit ⊕ (Fin D.m2 ⊕ Unit)) :=
  schurO (C2 z μ hz hμ hA0) 1 (C2_degO z μ hz hμ hA0) (C2_degE z μ hz hμ hA0)
    (by rw [C2_blk]; exact hA1)

/-- Relabelled for the third cancellation. -/
def C3 : BasedCx K ((Unit ⊕ Unit) ⊕ Fin D.m2) ((Unit ⊕ Unit) ⊕ Fin D.m2) :=
  (S2 z μ hz hμ hA0 hA1).reindex (eE3 D.m2) (eO3 D.m2)

theorem C3_degE (e : Fin D.m2) : (C3 z μ hz hμ hA0 hA1).degE (Sum.inr e) = 2 := by
  change (2 : ℤ) + 1 + -1 = 2; norm_num
theorem C3_degO (b : Fin D.m2) : (C3 z μ hz hμ hA0 hA1).degO (Sum.inr b) = 2 + 1 := by
  change (3 : ℤ) + 1 + -1 = 2 + 1; norm_num

theorem C3_blkA : blkA (C3 z μ hz hμ hA0 hA1) = D.A2 := by
  ext b e
  change (S1 z μ hz hμ hA0).dOE (Sum.inr (Sum.inl b)) (Sum.inr (Sum.inr (Sum.inr e))) = _
  simp [S1, schurE, C1, BasedCx.reindex, FourCx.aug, FourCx.toBased, BlockComplex.toFour,
    eE1, eO1, Matrix.mul_apply, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, BlockComplex.A2]

/-- After the third cancellation: the two-line complex. -/
def S3 : BasedCx K (Unit ⊕ Unit) (Unit ⊕ Unit) :=
  schurE (C := C3 z μ hz hμ hA0 hA1) 2 (C3_degE z μ hz hμ hA0 hA1) (C3_degO z μ hz hμ hA0 hA1)
    (by rw [C3_blkA]; exact hA2)

theorem S3_degE : (S3 z μ hz hμ hA0 hA1 hA2).degE = Sum.elim (fun _ => 0) (fun _ => 2) := by
  funext i; rcases i with u | u
  · change (0 : ℤ) + 1 + -1 = 0; norm_num
  · change (2 : ℤ) + 1 + -1 = 2; norm_num

theorem S3_degO : (S3 z μ hz hμ hA0 hA1 hA2).degO = Sum.elim (fun _ => 1) (fun _ => 3) := by
  funext i; rcases i with u | u
  · change (1 : ℤ) + 1 + -1 = 1; norm_num
  · change (3 : ℤ) + 1 + -1 = 3; norm_num

theorem mul_inv_mul_apply {m n l : Type*} [Fintype n] [DecidableEq n] (Q : Matrix m n K)
    (A : Matrix n n K) (T : Matrix n l K) (i : m) (j : l) :
    (Q * A⁻¹ * T) i j = (fun e => Q i e) ⬝ᵥ (A⁻¹ *ᵥ fun b => T b j) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, dotProduct, mulVec]

theorem S1_dOE (i j) : (S1 z μ hz hμ hA0).dOE i j =
    (C1 D z μ hz hμ).dOE (Sum.inl i) (Sum.inl j) -
      (fun e => (C1 D z μ hz hμ).dOE (Sum.inl i) (Sum.inr e)) ⬝ᵥ
        (D.A0⁻¹ *ᵥ fun b => (C1 D z μ hz hμ).dOE (Sum.inr b) (Sum.inl j)) := by
  change ((C1 D z μ hz hμ).dOE.toBlocks₁₁ - (C1 D z μ hz hμ).dOE.toBlocks₁₂ *
    (blkA (C1 D z μ hz hμ))⁻¹ * (C1 D z μ hz hμ).dOE.toBlocks₂₁) i j = _
  rw [Matrix.sub_apply, mul_inv_mul_apply, C1_blkA]
  rfl

theorem S2_dOE (i j) : (S2 z μ hz hμ hA0 hA1).dOE i j =
    (C2 z μ hz hμ hA0).dOE (Sum.inl i) (Sum.inl j) := rfl

theorem S2_dEO (i j) : (S2 z μ hz hμ hA0 hA1).dEO i j =
    (C2 z μ hz hμ hA0).dEO (Sum.inl i) (Sum.inl j) -
      (fun e => (C2 z μ hz hμ hA0).dEO (Sum.inl i) (Sum.inr e)) ⬝ᵥ
        (D.A1⁻¹ *ᵥ fun b => (C2 z μ hz hμ hA0).dEO (Sum.inr b) (Sum.inl j)) := by
  change ((C2 z μ hz hμ hA0).dEO.toBlocks₁₁ - (C2 z μ hz hμ hA0).dEO.toBlocks₁₂ *
    ((C2 z μ hz hμ hA0).dEO.toBlocks₂₂)⁻¹ * (C2 z μ hz hμ hA0).dEO.toBlocks₂₁) i j = _
  rw [Matrix.sub_apply, mul_inv_mul_apply, C2_blk]
  rfl

theorem S3_dOE (i j) : (S3 z μ hz hμ hA0 hA1 hA2).dOE i j =
    (C3 z μ hz hμ hA0 hA1).dOE (Sum.inl i) (Sum.inl j) -
      (fun e => (C3 z μ hz hμ hA0 hA1).dOE (Sum.inl i) (Sum.inr e)) ⬝ᵥ
        (D.A2⁻¹ *ᵥ fun b => (C3 z μ hz hμ hA0 hA1).dOE (Sum.inr b) (Sum.inl j)) := by
  change ((C3 z μ hz hμ hA0 hA1).dOE.toBlocks₁₁ - (C3 z μ hz hμ hA0 hA1).dOE.toBlocks₁₂ *
    (blkA (C3 z μ hz hμ hA0 hA1))⁻¹ * (C3 z μ hz hμ hA0 hA1).dOE.toBlocks₂₁) i j = _
  rw [Matrix.sub_apply, mul_inv_mul_apply, C3_blkA]
  rfl

theorem S3_dEO (i j) : (S3 z μ hz hμ hA0 hA1 hA2).dEO i j =
    (C3 z μ hz hμ hA0 hA1).dEO (Sum.inl i) (Sum.inl j) := rfl

/-- **The class coordinate**: `α`. -/
theorem S3_alpha : (S3 z μ hz hμ hA0 hA1 hA2).dOE (Sum.inl ()) (Sum.inl ()) = D.alphaB z := by
  rw [S3_dOE]
  have h0 : ∀ e, (C3 z μ hz hμ hA0 hA1).dOE (Sum.inl (Sum.inl ())) (Sum.inr e) = 0 := by
    intro e
    by_contra hne
    have := (C3 z μ hz hμ hA0 hA1).deg_dOE _ _ hne
    rw [C3_degE] at this
    change (1 : ℤ) + 1 + -1 = 2 + 1 at this
    norm_num at this
  have hz0 : (fun e => (C3 z μ hz hμ hA0 hA1).dOE (Sum.inl (Sum.inl ())) (Sum.inr e)) = 0 :=
    funext h0
  rw [hz0, zero_dotProduct, sub_zero]
  change (S1 z μ hz hμ hA0).dOE (Sum.inl (Sum.inl ())) (Sum.inl ()) = _
  rw [S1_dOE]
  rfl

/-- **The functional coordinate**: `β`. -/
theorem S3_beta : (S3 z μ hz hμ hA0 hA1 hA2).dOE (Sum.inr ()) (Sum.inr ()) = D.betaB μ := by
  rw [S3_dOE]
  have e1 : (C3 z μ hz hμ hA0 hA1).dOE (Sum.inl (Sum.inr ())) (Sum.inl (Sum.inr ())) =
      μ (Sum.inr (Sum.inl ())) := by
    change (S1 z μ hz hμ hA0).dOE (Sum.inr (Sum.inr ())) (Sum.inr (Sum.inr (Sum.inl ()))) = _
    have hf : (fun e => (C1 D z μ hz hμ).dOE (Sum.inl (Sum.inr (Sum.inr ()))) (Sum.inr e)) =
        fun _ => 0 := rfl
    rw [S1_dOE, hf]
    simp only [dotProduct, zero_mul, Finset.sum_const_zero, sub_zero]
    rfl
  have e2 : (fun e => (C3 z μ hz hμ hA0 hA1).dOE (Sum.inl (Sum.inr ())) (Sum.inr e)) =
      fun e => μ (Sum.inr (Sum.inr e)) := by
    funext e
    change (S1 z μ hz hμ hA0).dOE (Sum.inr (Sum.inr ())) (Sum.inr (Sum.inr (Sum.inr e))) = _
    have hf : (fun e => (C1 D z μ hz hμ).dOE (Sum.inl (Sum.inr (Sum.inr ()))) (Sum.inr e)) =
        fun _ => 0 := rfl
    rw [S1_dOE, hf]
    simp only [dotProduct, zero_mul, Finset.sum_const_zero, sub_zero]
    rfl
  have e3 : (fun b => (C3 z μ hz hμ hA0 hA1).dOE (Sum.inr b) (Sum.inl (Sum.inr ()))) =
      fun j => D.d2 j (Sum.inr (Sum.inl ())) := by
    funext b
    change (S1 z μ hz hμ hA0).dOE (Sum.inr (Sum.inl b)) (Sum.inr (Sum.inr (Sum.inl ()))) = _
    have hf : (fun e => (C1 D z μ hz hμ).dOE (Sum.inl (Sum.inr (Sum.inl b))) (Sum.inr e)) =
        fun _ => 0 := rfl
    rw [S1_dOE, hf]
    simp only [dotProduct, zero_mul, Finset.sum_const_zero, sub_zero]
    rfl
  rw [e1, e2, e3]
  rfl

/-- **The remaining map** `H₁ → H₂`. -/
theorem S3_h : (S3 z μ hz hμ hA0 hA1 hA2).dEO (Sum.inr ()) (Sum.inl ()) = D.hRem := by
  rw [S3_dEO]
  change (S2 z μ hz hμ hA0 hA1).dEO (Sum.inr (Sum.inl ())) (Sum.inl ()) = _
  rw [S2_dEO]
  rfl

include hA0 hA1 hA2 in
open Classical in
/-- **Elliot's computation of the Knudsen–Mumford coordinate** (PROVED): cancelling the Smith
blocks `A₀, A₁, A₂` in turn,
`kmCoord = −((α β if h = 0, else 0) · δ₀ · δ₁⁻¹ · δ₂)`. -/
theorem kmCoord_block :
    kmCoord D.toFour z μ hz hμ (σBlock D.m0 D.m1 D.m2) =
      -((if D.hRem = 0 then D.alphaB z * D.betaB μ else 0) * D.A0.det * (D.A1.det)⁻¹ *
        D.A2.det) := by
  unfold kmCoord
  congr 1
  have t0 : torsion (C1 D z μ hz hμ) ((σ1 D.m1 D.m2).sumCongr (Equiv.refl _)) =
      torsion (D.toFour.aug z μ hz hμ).toBased (σBlock D.m0 D.m1 D.m2) := by
    have := torsion_reindex' (D.toFour.aug z μ hz hμ).toBased (σBlock D.m0 D.m1 D.m2)
      (eE1 D.m0 D.m1 D.m2) (eO1 D.m0 D.m1 D.m2)
    rw [σBlock, transport_eq] at this
    exact this
  have t1 := torsion_cancelE (C := C1 D z μ hz hμ) 0 (C1_degE D z μ hz hμ) (C1_degO D z μ hz hμ)
    (by rw [C1_blkA]; exact hA0) (by decide) (σ1 D.m1 D.m2)
  have t2a : torsion (C2 z μ hz hμ hA0) ((σ2 D.m2).sumCongr (Equiv.refl _)) =
      torsion (S1 z μ hz hμ hA0) (σ1 D.m1 D.m2) := by
    have := torsion_reindex' (S1 z μ hz hμ hA0) (σ1 D.m1 D.m2) (eE2 D.m1 D.m2) (eO2 D.m1 D.m2)
    rw [σ1, transport_eq] at this
    exact this
  have t2 := torsion_cancelO (C2 z μ hz hμ hA0) 1 (C2_degO z μ hz hμ hA0)
    (C2_degE z μ hz hμ hA0) odd_one (by rw [C2_blk]; exact hA1) (σ2 D.m2)
  have t3a : torsion (C3 z μ hz hμ hA0 hA1) ((Equiv.refl (Unit ⊕ Unit)).sumCongr (Equiv.refl _)) =
      torsion (S2 z μ hz hμ hA0 hA1) (σ2 D.m2) := by
    have := torsion_reindex' (S2 z μ hz hμ hA0 hA1) (σ2 D.m2) (eE3 D.m2) (eO3 D.m2)
    rw [σ2, transport_eq] at this
    exact this
  have t3 := torsion_cancelE (C := C3 z μ hz hμ hA0 hA1) 2 (C3_degE z μ hz hμ hA0 hA1)
    (C3_degO z μ hz hμ hA0 hA1) (by rw [C3_blkA]; exact hA2) (by decide) (Equiv.refl _)
  have t4 := torsion_final (S3 z μ hz hμ hA0 hA1 hA2) (S3_degE z μ hz hμ hA0 hA1 hA2)
    (S3_degO z μ hz hμ hA0 hA1 hA2)
  rw [S3_alpha, S3_beta, S3_h] at t4
  rw [← t0, t1]
  change torsion (S1 z μ hz hμ hA0) (σ1 D.m1 D.m2) * _ = _
  rw [← t2a, t2]
  change torsion (S2 z μ hz hμ hA0 hA1) (σ2 D.m2) * _ * _ = _
  rw [← t3a, t3]
  change torsion (S3 z μ hz hμ hA0 hA1 hA2) (Equiv.refl _) * _ * _ * _ = _
  rw [t4, C3_blkA, C2_blk, C1_blkA]
  ring

include μ hz hμ hA0 hA1 hA2 in
/-- **If the remaining map is nonzero, the class coordinate vanishes** (PROVED; `d² = 0` in the
two-line complex). -/
theorem alpha_eq_zero_of_hRem_ne_zero (hh : D.hRem ≠ 0) : D.alphaB z = 0 := by
  have hdd := congrFun (congrFun (S3 z μ hz hμ hA0 hA1 hA2).dd_E (Sum.inr ())) (Sum.inl ())
  have o21 : (S3 z μ hz hμ hA0 hA1 hA2).dOE (Sum.inr ()) (Sum.inl ()) = 0 := by
    by_contra hne
    have := (S3 z μ hz hμ hA0 hA1 hA2).deg_dOE _ _ hne
    rw [S3_degE, S3_degO] at this
    simp at this
  have e11 : (S3 z μ hz hμ hA0 hA1 hA2).dEO (Sum.inr ()) (Sum.inr ()) = 0 := by
    by_contra hne
    have := (S3 z μ hz hμ hA0 hA1 hA2).deg_dEO _ _ hne
    rw [S3_degE, S3_degO] at this
    simp at this
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton,
    Matrix.zero_apply, PUnit.default_eq_unit] at hdd
  rw [e11, zero_mul, add_zero, S3_h, S3_alpha] at hdd
  exact (mul_eq_zero.mp hdd).resolve_left hh

end Chain

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
