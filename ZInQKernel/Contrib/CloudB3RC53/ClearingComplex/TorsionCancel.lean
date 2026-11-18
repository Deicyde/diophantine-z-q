import ZInQKernel.Contrib.CloudB3RC53.Torsion.KummerDisks
import ZInQKernel.Contrib.CloudB3RC53.Torsion.Exists
import ZInQKernel.Contrib.OneProof.RC.Determinant.Schur

/-!
# Cancelling an invertible block changes the torsion by its determinant

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:limits-fixed-field-clearing`, tex
L5545–5595: "cancel the whole block `A_i` once. For that differential the two elementary matrices
are … Both elementary matrices have determinant one. In the adjacent differentials, the equation
`d² = 0` makes the components into and out of this canceled pair zero … a disk in degrees `i, i+1`
contributes `δ_i^{(−1)^i}`."

Over a field `K`, for a based complex (lane Torsion's `BasedCx`) whose even and odd bases are
`α ⊕ E` and `β ⊕ E`, with the block `A : E → E` of `d` from the even summand `E` (all in degree `k`)
to the odd summand `E` (degree `k + 1`) invertible:

* `schurE C`: the remaining complex on `(α, β)`, `d = P − Q A⁻¹ T` (even to odd) and the old
  `X` (odd to even), with `d² = 0` (PROVED from `d² = 0` and the degrees);
* `torsion_cancelE`: `torsion C = torsion (schurE C) · det A` (PROVED: the two elementary matrices
  are a graded change of basis of determinant one carrying `C` to `schurE C ⊕ disk(A)`; lane
  Torsion's `tau_rebase`, `torsion_sum`; contractions transported in both directions);
* `shiftCx`, `torsion_shift`: exchanging the even and odd parts (degrees shifted by an odd
  integer) inverts the torsion
  (`tau_mul_tauOdd`); `torsion_cancelO`: the mirrored cancellation (block from odd to even)
  divides by `det A`;
* `torsion_reindex'`: relabelling without a contraction hypothesis.

All statements are PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion

variable {K : Type*} [Field K]

section Generic

variable {κe κo κe' κo' : Type*} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]
  [Fintype κe'] [Fintype κo'] [DecidableEq κe'] [DecidableEq κo']

/-! ### Relabelling without a contraction -/

theorem reindex_reindex_symm (C : BasedCx K κe κo) (eE : κe ≃ κe') (eO : κo ≃ κo') :
    (C.reindex eE eO).reindex eE.symm eO.symm = C := by
  apply BasedCx.ext'
  · funext i; simp [BasedCx.reindex]
  · funext i; simp [BasedCx.reindex]
  · ext i j; simp [BasedCx.reindex]
  · ext i j; simp [BasedCx.reindex]

/-- **Relabelling does not change the torsion** (no contraction hypothesis). -/
theorem torsion_reindex' (C : BasedCx K κe κo) (σ : κe ≃ κo) (eE : κe ≃ κe') (eO : κo ≃ κo') :
    torsion (C.reindex eE eO) (eE.symm.trans (σ.trans eO)) = torsion C σ := by
  by_cases hC : Nonempty (Contraction C)
  · exact torsion_reindex C hC.some σ eE eO
  · have hC' : ¬ Nonempty (Contraction (C.reindex eE eO)) := by
      rintro ⟨h⟩
      exact hC ⟨reindex_reindex_symm C eE eO ▸ h.reindex eE.symm eO.symm⟩
    unfold torsion
    simp only [hC, hC', dite_false]

/-! ### The first summand of a contractible sum -/

/-- The `(1,1)` block of a contraction of a direct sum is a contraction of the first summand. -/
def Contraction.fst {C : BasedCx K κe κo} {C' : BasedCx K κe' κo'} (h : Contraction (C.sum C')) :
    Contraction C where
  hOE := h.hOE.toBlocks₁₁
  hEO := h.hEO.toBlocks₁₁
  deg_hOE i j hij := h.deg_hOE (Sum.inl i) (Sum.inl j) hij
  deg_hEO i j hij := h.deg_hEO (Sum.inl i) (Sum.inl j) hij
  htpy_E := by
    ext i j
    have e := congrFun (congrFun h.htpy_E (Sum.inl i)) (Sum.inl j)
    simpa [BasedCx.sum, Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁, Matrix.one_apply]
      using e
  htpy_O := by
    ext i j
    have e := congrFun (congrFun h.htpy_O (Sum.inl i)) (Sum.inl j)
    simpa [BasedCx.sum, Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁, Matrix.one_apply]
      using e

/-! ### Exchanging the even and odd parts -/

/-- The complex with even and odd parts exchanged (degrees shifted by an odd `c`). -/
def shiftCx (C : BasedCx K κe κo) (c : ℤ) (hc : Odd c) : BasedCx K κo κe where
  degE i := C.degO i + c
  degO i := C.degE i + c
  even_degE i := (C.odd_degO i).add_odd hc
  odd_degO i := (C.even_degE i).add_odd hc
  dOE := C.dEO
  dEO := C.dOE
  dd_E := C.dd_O
  dd_O := C.dd_E
  deg_dOE i j h := by have := C.deg_dEO i j h; show C.degE i + c = C.degO j + c + 1; omega
  deg_dEO i j h := by have := C.deg_dOE i j h; show C.degO i + c = C.degE j + c + 1; omega

/-- The shifted contraction. -/
def shiftContr {C : BasedCx K κe κo} (c : ℤ) (hc : Odd c) (h : Contraction C) :
    Contraction (shiftCx C c hc) where
  hOE := h.hEO
  hEO := h.hOE
  deg_hOE i j hh := by have := h.deg_hEO i j hh; change C.degE i + c = C.degO j + c + -1; omega
  deg_hEO i j hh := by have := h.deg_hOE i j hh; change C.degO i + c = C.degE j + c + -1; omega
  htpy_E := h.htpy_O
  htpy_O := h.htpy_E

/-- A contraction of the shift gives one of the complex. -/
def unshiftContr {C : BasedCx K κe κo} (c : ℤ) (hc : Odd c) (h : Contraction (shiftCx C c hc)) :
    Contraction C where
  hOE := h.hEO
  hEO := h.hOE
  deg_hOE i j hh := by
    have := h.deg_hEO i j hh; change C.degO i + c = C.degE j + c + -1 at this; omega
  deg_hEO i j hh := by
    have := h.deg_hOE i j hh; change C.degE i + c = C.degO j + c + -1 at this; omega
  htpy_E := h.htpy_O
  htpy_O := h.htpy_E

theorem tau_shift_mul (C : BasedCx K κe κo) (c : ℤ) (hc : Odd c) (h : Contraction C)
    (σ : κe ≃ κo) : tau (shiftCx C c hc) (shiftContr c hc h) σ.symm * tau C h σ = 1 := by
  have e : tau (shiftCx C c hc) (shiftContr c hc h) σ.symm = tauOdd C h σ := by
    unfold tau tauOdd
    change ((C.dEO + h.hEO).submatrix σ.symm id).det = ((C.dEO + h.hEO).submatrix id σ).det
    rw [← det_submatrix_equiv_self σ ((C.dEO + h.hEO).submatrix σ.symm id)]
    congr 1
    ext i j
    simp
  rw [e, mul_comm, tau_mul_tauOdd]

/-- **Exchanging the even and odd parts inverts the torsion.** -/
theorem torsion_shift (C : BasedCx K κe κo) (c : ℤ) (hc : Odd c) (σ : κe ≃ κo) :
    torsion (shiftCx C c hc) σ.symm = (torsion C σ)⁻¹ := by
  by_cases hC : Nonempty (Contraction C)
  · obtain ⟨h⟩ := hC
    rw [← tau_eq_torsion _ (shiftContr c hc h), ← tau_eq_torsion _ h]
    exact eq_inv_of_mul_eq_one_left (tau_shift_mul C c hc h σ)
  · have hS : ¬ Nonempty (Contraction (shiftCx C c hc)) := fun ⟨h⟩ => hC ⟨unshiftContr c hc h⟩
    unfold torsion
    simp only [hC, hS, dite_false, _root_.inv_zero]

/-! ### Inverting a graded change of basis -/

/-- The inverse change of basis. -/
def basisInv {C : BasedCx K κe κo} (P : GradedBasisChange C) :
    GradedBasisChange (C.rebase P) where
  Pe := P.Qe
  Qe := P.Pe
  Po := P.Qo
  Qo := P.Po
  hPQe := mul_eq_one_comm.mp P.hPQe
  hPQo := mul_eq_one_comm.mp P.hPQo
  deg_Pe := P.deg_Qe
  deg_Qe := P.deg_Pe
  deg_Po := P.deg_Qo
  deg_Qo := P.deg_Po

theorem rebase_inv' (C : BasedCx K κe κo) (P : GradedBasisChange C) :
    (C.rebase P).rebase (basisInv P) = C := by
  have hE : P.Qe * P.Pe = 1 := mul_eq_one_comm.mp P.hPQe
  have hO : P.Qo * P.Po = 1 := mul_eq_one_comm.mp P.hPQo
  apply BasedCx.ext'
  · rfl
  · rfl
  · change P.Qo * (P.Po * C.dOE * P.Qe) * P.Pe = C.dOE
    simp only [Matrix.mul_assoc]
    rw [hE, Matrix.mul_one, ← Matrix.mul_assoc, hO, Matrix.one_mul]
  · change P.Qe * (P.Pe * C.dEO * P.Qo) * P.Po = C.dEO
    simp only [Matrix.mul_assoc]
    rw [hO, Matrix.mul_one, ← Matrix.mul_assoc, hE, Matrix.one_mul]

end Generic

/-! ### The disk of an invertible matrix -/

section Disk

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The disk `E --A--> E` from degree `k` (even) to `k + 1`. -/
def diskM (k : ℤ) (hk : Even k) (A : Matrix E E K) : BasedCx K E E where
  degE _ := k
  degO _ := k + 1
  even_degE _ := hk
  odd_degO _ := hk.add_one
  dOE := A
  dEO := 0
  dd_E := by simp
  dd_O := by simp
  deg_dOE _ _ _ := rfl
  deg_dEO _ _ h := absurd rfl h

/-- Its contraction `A⁻¹`. -/
def diskMContraction (k : ℤ) (hk : Even k) (A : Matrix E E K) (hA : IsUnit A.det) :
    Contraction (diskM k hk A) where
  hOE := 0
  hEO := A⁻¹
  deg_hOE _ _ h := absurd rfl h
  deg_hEO _ _ _ := by change k = k + 1 + -1; ring
  htpy_E := by
    change (0 : Matrix E E K) * 0 + A⁻¹ * A = 1
    rw [nonsing_inv_mul _ hA]; simp
  htpy_O := by
    change A * A⁻¹ + 0 * 0 = 1
    rw [mul_nonsing_inv _ hA]; simp

/-- **The disk of `A` has torsion `det A`.** -/
theorem torsion_diskM (k : ℤ) (hk : Even k) (A : Matrix E E K) (hA : IsUnit A.det) :
    torsion (diskM k hk A) (Equiv.refl E) = A.det := by
  rw [← tau_eq_torsion _ (diskMContraction k hk A hA)]
  unfold tau
  change ((A + 0).submatrix (Equiv.refl E) id).det = _
  rw [add_zero]
  rfl

end Disk

/-! ### Cancelling an invertible block from even to odd degree -/

section Cancel

variable {α β E : Type*} [Fintype α] [Fintype β] [Fintype E] [DecidableEq α] [DecidableEq β]
  [DecidableEq E]

variable (C : BasedCx K (α ⊕ E) (β ⊕ E)) (k : ℤ) (hdegE : ∀ e, C.degE (Sum.inr e) = k)
  (hdegO : ∀ e, C.degO (Sum.inr e) = k + 1)

/-- The block `A : E → E` of `d` from the even to the odd summand. -/
abbrev blkA : Matrix E E K := C.dOE.toBlocks₂₂

include hdegE hdegO in
theorem dEO_toBlocks₂₂_eq_zero : C.dEO.toBlocks₂₂ = 0 := by
  ext i j
  by_contra hne
  have := C.deg_dEO (Sum.inr i) (Sum.inr j) hne
  rw [hdegE, hdegO] at this
  omega

theorem dOE_eq : C.dOE = fromBlocks C.dOE.toBlocks₁₁ C.dOE.toBlocks₁₂ C.dOE.toBlocks₂₁
    C.dOE.toBlocks₂₂ := (fromBlocks_toBlocks _).symm

theorem dEO_eq : C.dEO = fromBlocks C.dEO.toBlocks₁₁ C.dEO.toBlocks₁₂ C.dEO.toBlocks₂₁
    C.dEO.toBlocks₂₂ := (fromBlocks_toBlocks _).symm

/-- The block equations of `d_{OE} d_{EO} = 0`. -/
theorem dd_O_blocks :
    C.dOE.toBlocks₂₁ * C.dEO.toBlocks₁₁ + C.dOE.toBlocks₂₂ * C.dEO.toBlocks₂₁ = 0 ∧
    C.dOE.toBlocks₁₁ * C.dEO.toBlocks₁₁ + C.dOE.toBlocks₁₂ * C.dEO.toBlocks₂₁ = 0 := by
  have h := C.dd_O
  rw [dOE_eq C, dEO_eq C, fromBlocks_multiply] at h
  have h1 := congrArg toBlocks₂₁ h
  have h2 := congrArg toBlocks₁₁ h
  simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₁₁] at h1 h2
  exact ⟨by rw [h1]; rfl, by rw [h2]; rfl⟩

/-- The block equations of `d_{EO} d_{OE} = 0`. -/
theorem dd_E_blocks :
    C.dEO.toBlocks₁₁ * C.dOE.toBlocks₁₂ + C.dEO.toBlocks₁₂ * C.dOE.toBlocks₂₂ = 0 ∧
    C.dEO.toBlocks₁₁ * C.dOE.toBlocks₁₁ + C.dEO.toBlocks₁₂ * C.dOE.toBlocks₂₁ = 0 ∧
    C.dEO.toBlocks₂₁ * C.dOE.toBlocks₁₂ + C.dEO.toBlocks₂₂ * C.dOE.toBlocks₂₂ = 0 := by
  have h := C.dd_E
  rw [dOE_eq C, dEO_eq C, fromBlocks_multiply] at h
  have h1 := congrArg toBlocks₁₂ h
  have h2 := congrArg toBlocks₁₁ h
  have h3 := congrArg toBlocks₂₂ h
  simp only [toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂] at h1 h2 h3
  exact ⟨by rw [h1]; rfl, by rw [h2]; rfl, by rw [h3]; rfl⟩

variable {C}

include hdegE hdegO in
/-- The degree of `Q A⁻¹ T`. -/
theorem hasDeg_QAT :
    HasDeg (C.dOE.toBlocks₁₂ * (blkA C)⁻¹ * C.dOE.toBlocks₂₁) (C.degO ∘ Sum.inl)
      (C.degE ∘ Sum.inl) 1 := by
  have hQ : HasDeg C.dOE.toBlocks₁₂ (C.degO ∘ Sum.inl) (fun _ : E => k) 1 := by
    intro i j h
    have := C.deg_dOE (Sum.inl i) (Sum.inr j) h
    rw [hdegE] at this; exact this
  have hAi : HasDeg (blkA C)⁻¹ (fun _ : E => k) (fun _ : E => k + 1) (-1) := by
    intro _ _ _; ring
  have hT : HasDeg C.dOE.toBlocks₂₁ (fun _ : E => k + 1) (C.degE ∘ Sum.inl) 1 := by
    intro i j h
    have := C.deg_dOE (Sum.inr i) (Sum.inl j) h
    rw [hdegO] at this; exact this
  exact ((hQ.mul hAi).mul hT).of_eq (by ring)

variable (hA : IsUnit (blkA C).det)

include hdegE hdegO hA in
/-- **The remaining complex after cancelling `A`**: `d = P − Q A⁻¹ T` and the old `X`. -/
def schurE : BasedCx K α β where
  degE := C.degE ∘ Sum.inl
  degO := C.degO ∘ Sum.inl
  even_degE i := C.even_degE _
  odd_degO i := C.odd_degO _
  dOE := C.dOE.toBlocks₁₁ - C.dOE.toBlocks₁₂ * (blkA C)⁻¹ * C.dOE.toBlocks₂₁
  dEO := C.dEO.toBlocks₁₁
  dd_E := by
    obtain ⟨h1, h2, -⟩ := dd_E_blocks C
    -- `Y = − X Q A⁻¹`
    have hY : C.dEO.toBlocks₁₂ = -(C.dEO.toBlocks₁₁ * C.dOE.toBlocks₁₂ * (blkA C)⁻¹) := by
      have := congrArg (· * (blkA C)⁻¹) h1
      simp only [Matrix.add_mul, Matrix.zero_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ hA, Matrix.mul_one] at this
      rw [eq_neg_iff_add_eq_zero, add_comm, Matrix.mul_assoc]; exact this
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [hY, Matrix.neg_mul] at h2
    rw [← h2]; abel
  dd_O := by
    obtain ⟨h1, h2⟩ := dd_O_blocks C
    -- `U = − A⁻¹ T X`
    have hU : C.dEO.toBlocks₂₁ = -((blkA C)⁻¹ * C.dOE.toBlocks₂₁ * C.dEO.toBlocks₁₁) := by
      have := congrArg ((blkA C)⁻¹ * ·) h1
      simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc,
        nonsing_inv_mul _ hA, Matrix.one_mul] at this
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact this
    rw [Matrix.sub_mul]
    rw [hU, Matrix.mul_neg] at h2
    simp only [Matrix.mul_assoc] at h2 ⊢
    rw [← h2]; abel
  deg_dOE := by
    refine HasDeg.sub ?_ (hasDeg_QAT k hdegE hdegO)
    intro i j h; exact C.deg_dOE (Sum.inl i) (Sum.inl j) h
  deg_dEO i j h := C.deg_dEO (Sum.inl i) (Sum.inl j) h

/-- The graded change of basis of the cancellation (two elementary matrices). -/
def cancelBasis : GradedBasisChange C where
  Pe := fromBlocks 1 0 ((blkA C)⁻¹ * C.dOE.toBlocks₂₁) 1
  Qe := fromBlocks 1 0 (-((blkA C)⁻¹ * C.dOE.toBlocks₂₁)) 1
  Po := fromBlocks 1 (-(C.dOE.toBlocks₁₂ * (blkA C)⁻¹)) 0 1
  Qo := fromBlocks 1 (C.dOE.toBlocks₁₂ * (blkA C)⁻¹) 0 1
  hPQe := by rw [fromBlocks_multiply]; simp [← fromBlocks_one]
  hPQo := by rw [fromBlocks_multiply]; simp [← fromBlocks_one]
  deg_Pe := by
    rintro (i | i) (j | j) h
    · simpa using (hasDeg_one (C.degE ∘ Sum.inl) i j (by simpa using h))
    · exact absurd (by simp) h
    · simp only [fromBlocks_apply₂₁] at h
      obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have := C.deg_dOE (Sum.inr l) (Sum.inl j) (right_ne_zero_of_mul hl)
      rw [hdegO] at this
      change C.degE (Sum.inr i) = C.degE (Sum.inl j) + 0
      rw [hdegE]; omega
    · have hij : i = j := by
        by_contra hne; exact h (by simp [hne])
      subst hij; simp
  deg_Qe := by
    rintro (i | i) (j | j) h
    · simpa using (hasDeg_one (C.degE ∘ Sum.inl) i j (by simpa using h))
    · exact absurd (by simp) h
    · simp only [fromBlocks_apply₂₁, Matrix.neg_apply, neg_ne_zero] at h
      obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have := C.deg_dOE (Sum.inr l) (Sum.inl j) (right_ne_zero_of_mul hl)
      rw [hdegO] at this
      change C.degE (Sum.inr i) = C.degE (Sum.inl j) + 0
      rw [hdegE]; omega
    · have hij : i = j := by
        by_contra hne; exact h (by simp [hne])
      subst hij; simp
  deg_Po := by
    rintro (i | i) (j | j) h
    · simpa using (hasDeg_one (C.degO ∘ Sum.inl) i j (by simpa using h))
    · simp only [fromBlocks_apply₁₂, Matrix.neg_apply, neg_ne_zero] at h
      obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have := C.deg_dOE (Sum.inl i) (Sum.inr l) (left_ne_zero_of_mul hl)
      rw [hdegE] at this
      change C.degO (Sum.inl i) = C.degO (Sum.inr j) + 0
      rw [hdegO]; omega
    · exact absurd (by simp) h
    · have hij : i = j := by
        by_contra hne; exact h (by simp [hne])
      subst hij; simp
  deg_Qo := by
    rintro (i | i) (j | j) h
    · simpa using (hasDeg_one (C.degO ∘ Sum.inl) i j (by simpa using h))
    · simp only [fromBlocks_apply₁₂] at h
      obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have := C.deg_dOE (Sum.inl i) (Sum.inr l) (left_ne_zero_of_mul hl)
      rw [hdegE] at this
      change C.degO (Sum.inl i) = C.degO (Sum.inr j) + 0
      rw [hdegO]; omega
    · exact absurd (by simp) h
    · have hij : i = j := by
        by_contra hne; exact h (by simp [hne])
      subst hij; simp

variable (hk : Even k)

include hA in
theorem rebase_eq :
    C.rebase (cancelBasis k hdegE hdegO) =
      (schurE k hdegE hdegO hA).sum (diskM k hk (blkA C)) := by
  obtain ⟨h1, -, h3⟩ := dd_E_blocks C
  obtain ⟨h1', -⟩ := dd_O_blocks C
  have hV := dEO_toBlocks₂₂_eq_zero C k hdegE hdegO
  have hY : C.dEO.toBlocks₁₁ * (C.dOE.toBlocks₁₂ * (blkA C)⁻¹) + C.dEO.toBlocks₁₂ = 0 := by
    have := congrArg (· * (blkA C)⁻¹) h1
    simp only [Matrix.add_mul, Matrix.zero_mul, Matrix.mul_assoc, mul_nonsing_inv _ hA,
      Matrix.mul_one] at this
    exact this
  have hU : (blkA C)⁻¹ * C.dOE.toBlocks₂₁ * C.dEO.toBlocks₁₁ + C.dEO.toBlocks₂₁ = 0 := by
    have := congrArg ((blkA C)⁻¹ * ·) h1'
    simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc, nonsing_inv_mul _ hA,
      Matrix.one_mul] at this
    exact this
  have hUQ : C.dEO.toBlocks₂₁ * C.dOE.toBlocks₁₂ = 0 := by
    rw [hV, Matrix.zero_mul, add_zero] at h3; exact h3
  apply BasedCx.ext'
  · funext x; rcases x with x | x
    · rfl
    · exact hdegE x
  · funext x; rcases x with x | x
    · rfl
    · exact hdegO x
  · change fromBlocks 1 (-(C.dOE.toBlocks₁₂ * (blkA C)⁻¹)) 0 1 * C.dOE *
      fromBlocks 1 0 (-((blkA C)⁻¹ * C.dOE.toBlocks₂₁)) 1 =
      fromBlocks (C.dOE.toBlocks₁₁ - C.dOE.toBlocks₁₂ * (blkA C)⁻¹ * C.dOE.toBlocks₂₁) 0 0
        (blkA C)
    rw [dOE_eq C]
    exact ZInQ.Manuscript.RC.Determinant.schur_block_identity _ _ _ _ hA
  · change fromBlocks 1 0 ((blkA C)⁻¹ * C.dOE.toBlocks₂₁) 1 * C.dEO *
      fromBlocks 1 (C.dOE.toBlocks₁₂ * (blkA C)⁻¹) 0 1 = fromBlocks C.dEO.toBlocks₁₁ 0 0 0
    rw [dEO_eq C, hV, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero, add_zero,
      zero_add]
    rw [hU]
    refine fromBlocks_inj.mpr ⟨rfl, hY, by simp, ?_⟩
    simp only [Matrix.zero_mul, zero_add]
    have hY' : C.dEO.toBlocks₁₂ = -(C.dEO.toBlocks₁₁ * (C.dOE.toBlocks₁₂ * (blkA C)⁻¹)) :=
      eq_neg_of_add_eq_zero_right hY
    have hU' : (blkA C)⁻¹ * C.dOE.toBlocks₂₁ * C.dEO.toBlocks₁₁ = -C.dEO.toBlocks₂₁ :=
      eq_neg_of_add_eq_zero_left hU
    rw [hY', Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', Matrix.neg_mul,
      Matrix.neg_mul, neg_neg, hUQ, Matrix.zero_mul]

include hA hk in
/-- **Cancelling an invertible block from even to odd degree multiplies the torsion by its
determinant**: `torsion C = torsion (schurE C) · det A`. -/
theorem torsion_cancelE (σ' : α ≃ β) :
    torsion C (σ'.sumCongr (Equiv.refl E)) =
      torsion (schurE k hdegE hdegO hA) σ' * (blkA C).det := by
  set P := cancelBasis k hdegE hdegO with hP
  have heq := rebase_eq k hdegE hdegO hA hk
  have hPo : P.Po.det = 1 := by
    change (fromBlocks 1 (-(C.dOE.toBlocks₁₂ * (blkA C)⁻¹)) 0 1).det = 1
    rw [det_fromBlocks_zero₂₁, det_one, det_one, mul_one]
  have hQe : P.Qe.det = 1 := by
    change (fromBlocks 1 0 (-((blkA C)⁻¹ * C.dOE.toBlocks₂₁)) 1).det = 1
    rw [det_fromBlocks_zero₁₂, det_one, det_one, mul_one]
  by_cases hC : Nonempty (Contraction C)
  · obtain ⟨h⟩ := hC
    have h2 : Contraction ((schurE k hdegE hdegO hA).sum (diskM k hk (blkA C))) :=
      heq ▸ h.rebase P
    have h' := Contraction.fst h2
    calc torsion C (σ'.sumCongr (Equiv.refl E))
        = tau (C.rebase P) (h.rebase P) (σ'.sumCongr (Equiv.refl E)) := by
          rw [tau_rebase, hPo, hQe, one_mul, mul_one, tau_eq_torsion]
      _ = torsion (C.rebase P) (σ'.sumCongr (Equiv.refl E)) := tau_eq_torsion _ _ _
      _ = torsion ((schurE k hdegE hdegO hA).sum (diskM k hk (blkA C)))
            (σ'.sumCongr (Equiv.refl E)) := by rw [heq]
      _ = _ := by
          rw [torsion_sum _ _ h' (diskMContraction k hk _ hA), torsion_diskM k hk _ hA]
  · have hS : ¬ Nonempty (Contraction (schurE k hdegE hdegO hA)) := by
      rintro ⟨h'⟩
      have h2 : Contraction (C.rebase P) := heq ▸ h'.sum (diskMContraction k hk _ hA)
      exact hC ⟨rebase_inv' C P ▸ h2.rebase (basisInv P)⟩
    unfold torsion
    simp only [hC, hS, dite_false, zero_mul]

end Cancel

/-! ### Cancelling an invertible block from odd to even degree -/

section CancelOdd

variable {α β E : Type*} [Fintype α] [Fintype β] [Fintype E] [DecidableEq α] [DecidableEq β]
  [DecidableEq E]

variable (C : BasedCx K (α ⊕ E) (β ⊕ E)) (k : ℤ) (hdegO : ∀ e, C.degO (Sum.inr e) = k)
  (hdegE : ∀ e, C.degE (Sum.inr e) = k + 1) (hk : Odd k)
  (hA : IsUnit (C.dEO.toBlocks₂₂).det)

include hdegO in
theorem shift_degE : ∀ e, (shiftCx C 1 odd_one).degE (Sum.inr e) = k + 1 := fun e => by
  change C.degO (Sum.inr e) + 1 = k + 1; rw [hdegO]

include hdegE in
theorem shift_degO : ∀ e, (shiftCx C 1 odd_one).degO (Sum.inr e) = k + 1 + 1 := fun e => by
  change C.degE (Sum.inr e) + 1 = k + 1 + 1; rw [hdegE]

include hdegO hdegE hA in
/-- **The remaining complex after cancelling an invertible block from odd to even degree**
(`d = X − Y A⁻¹ U` from odd to even, the old even-to-odd part). -/
def schurO : BasedCx K α β :=
  shiftCx (schurE (C := shiftCx C 1 odd_one) (k + 1) (shift_degE C k hdegO)
    (shift_degO C k hdegE) hA) (-1) (by decide)

include hdegO hdegE hA hk in
/-- **Cancelling an invertible block from odd to even degree divides the torsion by its
determinant.** -/
theorem torsion_cancelO (σ' : α ≃ β) :
    torsion C (σ'.sumCongr (Equiv.refl E)) =
      torsion (schurO C k (hdegO := hdegO) (hdegE := hdegE) (hA := hA)) σ' * ((C.dEO.toBlocks₂₂).det)⁻¹ := by
  have hk1 : Even (k + 1) := hk.add_one
  have e1 := torsion_shift C 1 odd_one (σ'.sumCongr (Equiv.refl E))
  have e2 := torsion_cancelE (C := shiftCx C 1 odd_one) (k + 1) (shift_degE C k hdegO)
    (shift_degO C k hdegE) hA hk1 σ'.symm
  have e3 := torsion_shift (schurE (C := shiftCx C 1 odd_one) (k + 1) (shift_degE C k hdegO)
    (shift_degO C k hdegE) hA) (-1) (by decide) σ'.symm
  rw [Equiv.symm_symm] at e3
  rw [Equiv.sumCongr_symm, Equiv.refl_symm] at e1
  rw [e1] at e2
  have e2' : torsion C (σ'.sumCongr (Equiv.refl E)) =
      (torsion (schurE (C := shiftCx C 1 odd_one) (k + 1) (shift_degE C k hdegO)
        (shift_degO C k hdegE) hA) σ'.symm * (blkA (shiftCx C 1 odd_one)).det)⁻¹ := by
    rw [← e2, inv_inv]
  rw [e2', mul_inv, schurO, e3]
  rfl

end CancelOdd

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
