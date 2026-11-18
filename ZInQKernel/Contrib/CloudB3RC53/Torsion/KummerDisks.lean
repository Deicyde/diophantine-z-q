import ZInQKernel.Contrib.CloudB3RC53.Torsion.KnudsenMumford
import ZInQKernel.Contrib.CloudB3RC53.Calibration.Bookkeeping

/-!
# Torsion, part 5: acyclic summands and the torsion disks of the Kummer coordinate

* `FourCx.sum`, `aug_sum_eq`, `kmCoord_sum`: adding an acyclic summand `C'` (with `z, λ`
  extended by zero) multiplies the Knudsen–Mumford coordinate by the torsion of `C'`.
* `disk01`, `disk12`, `disk23`: the torsion disks `R --δ--> R` with cokernel in degree
  `i = 1, 2, 3`, of torsion `δ`, `δ⁻¹`, `δ`, i.e. `δ^{(−1)^{i+1}}` (tex L4058–4060).
* `kummerModel`, `kmCoord_kummerModel`: for the two-term core `[R^n --D--> R^n]` plus torsion disks
  `δ₁, δ₂, δ₃` in degrees one, two, three, `kmCoord = u · δ₁ · δ₂⁻¹ · δ₃`.
* `v2_kmCoord_kummerModel` (tex L4051–4064): over `ℚ₂[[t]]`, the central valuation of the
  coordinate is `v₂ u(0) + Σ_i (−1)^{i+1} v₂ δ_i(0)`; with disk lengths `g, s, g` this is
  `diskContribution 1 g + diskContribution 2 s + diskContribution 3 g = 2g − s`.
* `hK_of_kummerModel`, `hvprim_of_kummerModel`: the Kummer-coordinate valuation input `hK` of
  `Calibration.hvprim_of_support_triangle` in its exact type, and RC0's `hvprim`, from the model
  (class and functional `a z₀`, `b λ₀` with `z₀ ⊗ λ₀ = u₀ adj D`, `v₂ u₀(0) = 0`,
  `v₂ a(0) = v₂ b(0) = j + v₂L + v₂m`).

The identification of the ordinary Kummer complex with `kummerModel` (core plus disks, in the
retained bases) is the remaining model input; it is stated against the Selmer-complex interface
`SelData` as `KummerModelIdentification` (`KummerIdentification.lean`), so that it can be
discharged by instantiation.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.Torsion

open Matrix

variable {R : Type*} [CommRing R]

/-- Equality of based complexes from their data. -/
theorem BasedCx.ext' {κe κo : Type*} [Fintype κe] [Fintype κo] {C C' : BasedCx R κe κo}
    (h1 : C.degE = C'.degE) (h2 : C.degO = C'.degO) (h3 : C.dOE = C'.dOE)
    (h4 : C.dEO = C'.dEO) : C = C' := by
  cases C; cases C'; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

section Sum

variable {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type*}
  [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [Fintype ι0'] [Fintype ι1'] [Fintype ι2'] [Fintype ι3']
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3']

/-- The direct sum of four-term complexes. -/
def FourCx.sum (C : FourCx R ι0 ι1 ι2 ι3) (C' : FourCx R ι0' ι1' ι2' ι3') :
    FourCx R (ι0 ⊕ ι0') (ι1 ⊕ ι1') (ι2 ⊕ ι2') (ι3 ⊕ ι3') where
  d0 := fromBlocks C.d0 0 0 C'.d0
  d1 := fromBlocks C.d1 0 0 C'.d1
  d2 := fromBlocks C.d2 0 0 C'.d2
  d10 := by rw [fromBlocks_multiply]; simp [C.d10, C'.d10]
  d21 := by rw [fromBlocks_multiply]; simp [C.d21, C'.d21]

omit [Fintype ι0] [Fintype ι3] [Fintype ι0'] [Fintype ι3'] [DecidableEq ι0] [DecidableEq ι1]
  [DecidableEq ι2] [DecidableEq ι3] [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2']
  [DecidableEq ι3'] in
theorem FourCx.sum_hz (C : FourCx R ι0 ι1 ι2 ι3) (C' : FourCx R ι0' ι1' ι2' ι3') {z : ι1 → R}
    (hz : C.d1 *ᵥ z = 0) : (C.sum C').d1 *ᵥ Sum.elim z 0 = 0 := by
  ext (i | i)
  · simpa [FourCx.sum, mulVec, dotProduct, Fintype.sum_sum_type] using congrFun hz i
  · simp [FourCx.sum, mulVec, dotProduct, Fintype.sum_sum_type]

omit [Fintype ι0] [Fintype ι3] [Fintype ι0'] [Fintype ι3'] [DecidableEq ι0] [DecidableEq ι1]
  [DecidableEq ι2] [DecidableEq ι3] [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2']
  [DecidableEq ι3'] in
theorem FourCx.sum_hlam (C : FourCx R ι0 ι1 ι2 ι3) (C' : FourCx R ι0' ι1' ι2' ι3')
    {lam : ι2 → R} (hlam : lam ᵥ* C.d1 = 0) : Sum.elim lam 0 ᵥ* (C.sum C').d1 = 0 := by
  ext (i | i)
  · simpa [FourCx.sum, vecMul, dotProduct, Fintype.sum_sum_type] using congrFun hlam i
  · simp [FourCx.sum, vecMul, dotProduct, Fintype.sum_sum_type]

variable (ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3')

/-- Even bases: `((C⁰ ⊕ R) ⊕ C²) ⊕ (C'⁰ ⊕ C'²) ≃ ((C⁰ ⊕ C'⁰) ⊕ R) ⊕ (C² ⊕ C'²)`. -/
def sumEvenEquiv : ((ι0 ⊕ Unit) ⊕ ι2) ⊕ (ι0' ⊕ ι2') ≃ ((ι0 ⊕ ι0') ⊕ Unit) ⊕ (ι2 ⊕ ι2') where
  toFun
    | .inl (.inl (.inl a)) => .inl (.inl (.inl a))
    | .inl (.inl (.inr u)) => .inl (.inr u)
    | .inl (.inr b) => .inr (.inl b)
    | .inr (.inl a) => .inl (.inl (.inr a))
    | .inr (.inr b) => .inr (.inr b)
  invFun
    | .inl (.inl (.inl a)) => .inl (.inl (.inl a))
    | .inl (.inl (.inr a)) => .inr (.inl a)
    | .inl (.inr u) => .inl (.inl (.inr u))
    | .inr (.inl b) => .inl (.inr b)
    | .inr (.inr b) => .inr (.inr b)
  left_inv := by rintro (((a | u) | b) | (a | b)) <;> rfl
  right_inv := by rintro (((a | a) | u) | (b | b)) <;> rfl

/-- Odd bases: `(C¹ ⊕ (C³ ⊕ R)) ⊕ (C'¹ ⊕ C'³) ≃ (C¹ ⊕ C'¹) ⊕ ((C³ ⊕ C'³) ⊕ R)`. -/
def sumOddEquiv : (ι1 ⊕ (ι3 ⊕ Unit)) ⊕ (ι1' ⊕ ι3') ≃ (ι1 ⊕ ι1') ⊕ ((ι3 ⊕ ι3') ⊕ Unit) where
  toFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr (.inl c)) => .inr (.inl (.inl c))
    | .inl (.inr (.inr u)) => .inr (.inr u)
    | .inr (.inl a) => .inl (.inr a)
    | .inr (.inr c) => .inr (.inl (.inr c))
  invFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr a) => .inr (.inl a)
    | .inr (.inl (.inl c)) => .inl (.inr (.inl c))
    | .inr (.inl (.inr c)) => .inr (.inr c)
    | .inr (.inr u) => .inl (.inr (.inr u))
  left_inv := by rintro ((a | (c | u)) | (a | c)) <;> rfl
  right_inv := by rintro ((a | a) | ((c | c) | u)) <;> rfl

variable {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3'}

/-- The orientation of the sum. -/
def sumOrient (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) (σ' : ι0' ⊕ ι2' ≃ ι1' ⊕ ι3') :
    ((ι0 ⊕ ι0') ⊕ Unit) ⊕ (ι2 ⊕ ι2') ≃ (ι1 ⊕ ι1') ⊕ ((ι3 ⊕ ι3') ⊕ Unit) :=
  (sumEvenEquiv ι0 ι2 ι0' ι2').symm.trans ((σ.sumCongr σ').trans (sumOddEquiv ι1 ι3 ι1' ι3'))

omit [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] [DecidableEq ι0']
  [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3'] in
/-- **The augmented complex of `C ⊕ C'`** (with `z, λ` extended by zero) is the sum of the
augmented complex of `C` and of `C'`, up to relabelling the bases. -/
theorem aug_sum_eq (C : FourCx R ι0 ι1 ι2 ι3) (C' : FourCx R ι0' ι1' ι2' ι3') (z : ι1 → R)
    (lam : ι2 → R) (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) :
    ((C.sum C').aug (Sum.elim z 0) (Sum.elim lam 0) (C.sum_hz C' hz) (C.sum_hlam C' hlam)).toBased
      = (((C.aug z lam hz hlam).toBased).sum C'.toBased).reindex (sumEvenEquiv ι0 ι2 ι0' ι2')
          (sumOddEquiv ι1 ι3 ι1' ι3') := by
  apply BasedCx.ext'
  · funext x; rcases x with (((a | a) | u) | (b | b)) <;> rfl
  · funext x; rcases x with ((a | a) | ((c | c) | u)) <;> rfl
  · ext x y
    rcases x with ((a | a) | ((c | c) | u)) <;> rcases y with (((a' | a') | u') | (b | b)) <;>
      simp [FourCx.toBased, FourCx.aug, FourCx.sum, BasedCx.sum, BasedCx.reindex, sumEvenEquiv,
        sumOddEquiv]
  · ext x y
    rcases x with (((a' | a') | u') | (b | b)) <;> rcases y with ((a | a) | ((c | c) | u)) <;>
      simp [FourCx.toBased, FourCx.aug, FourCx.sum, BasedCx.sum, BasedCx.reindex, sumEvenEquiv,
        sumOddEquiv]

/-- **Adding an acyclic summand multiplies the Knudsen–Mumford coordinate by its torsion.** -/
theorem kmCoord_sum [IsDomain R] (C : FourCx R ι0 ι1 ι2 ι3) (C' : FourCx R ι0' ι1' ι2' ι3')
    (z : ι1 → R) (lam : ι2 → R) (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0)
    (h : Contraction (C.aug z lam hz hlam).toBased) (h' : Contraction C'.toBased)
    (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) (σ' : ι0' ⊕ ι2' ≃ ι1' ⊕ ι3') :
    kmCoord (C.sum C') (Sum.elim z 0) (Sum.elim lam 0) (C.sum_hz C' hz) (C.sum_hlam C' hlam)
        (sumOrient σ σ') = kmCoord C z lam hz hlam σ * torsion C'.toBased σ' := by
  unfold kmCoord sumOrient
  rw [aug_sum_eq C C' z lam hz hlam, torsion_reindex _ (h.sum h'), torsion_sum _ _ h h', neg_mul]

/-- The contraction of the augmented sum (for iterating `kmCoord_sum`). -/
def augSumContraction (C : FourCx R ι0 ι1 ι2 ι3) (C' : FourCx R ι0' ι1' ι2' ι3')
    (z : ι1 → R) (lam : ι2 → R) (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0)
    (h : Contraction (C.aug z lam hz hlam).toBased) (h' : Contraction C'.toBased) :
    Contraction ((C.sum C').aug (Sum.elim z 0) (Sum.elim lam 0) (C.sum_hz C' hz)
      (C.sum_hlam C' hlam)).toBased :=
  (aug_sum_eq C C' z lam hz hlam) ▸ (h.sum h').reindex _ _

end Sum

/-! ### The torsion disks in degrees one, two, three -/

section Disks

/-- The disk with cokernel in degree one: `C⁰ = R --δ--> R = C¹`. -/
def disk01 (δ : R) : FourCx R Unit Unit Empty Empty where
  d0 := sc δ
  d1 := 0
  d2 := 0
  d10 := by simp
  d21 := by simp

/-- The disk with cokernel in degree two: `C¹ = R --δ--> R = C²`. -/
def disk12 (δ : R) : FourCx R Empty Unit Unit Empty where
  d0 := 0
  d1 := sc δ
  d2 := 0
  d10 := by simp
  d21 := by simp

/-- The disk with cokernel in degree three: `C² = R --δ--> R = C³`. -/
def disk23 (δ : R) : FourCx R Empty Empty Unit Unit where
  d0 := 0
  d1 := 0
  d2 := sc δ
  d10 := by simp
  d21 := by simp

/-- The contraction `δ⁻¹` of `disk01 δ`. -/
def disk01Contraction (δ : Rˣ) : Contraction (disk01 (δ : R)).toBased where
  hOE := 0
  hEO := fromBlocks (sc ((δ⁻¹ : Rˣ) : R)) 0 0 0
  deg_hOE _ _ h := absurd rfl h
  deg_hEO := by
    rintro (u | e) (u' | e') h
    all_goals first | exact e.elim | exact e'.elim | rfl
  htpy_E := by
    ext (u | e) (u' | e')
    all_goals try first | exact e.elim | exact e'.elim
    simp [FourCx.toBased, disk01, sc, mul_apply, Fintype.sum_sum_type]
  htpy_O := by
    ext (u | e) (u' | e')
    all_goals try first | exact e.elim | exact e'.elim
    simp [FourCx.toBased, disk01, sc, mul_apply, Fintype.sum_sum_type]

/-- The contraction `δ⁻¹` of `disk12 δ`. -/
def disk12Contraction (δ : Rˣ) : Contraction (disk12 (δ : R)).toBased where
  hOE := fromBlocks 0 (sc ((δ⁻¹ : Rˣ) : R)) 0 0
  hEO := 0
  deg_hOE := by
    rintro (u | e) (e' | u') h
    all_goals first | exact e.elim | exact e'.elim | rfl
  deg_hEO _ _ h := absurd rfl h
  htpy_E := by
    ext (e | u) (e' | u')
    all_goals try first | exact e.elim | exact e'.elim
    simp [FourCx.toBased, disk12, sc, mul_apply, Fintype.sum_sum_type]
  htpy_O := by
    ext (u | e) (u' | e')
    all_goals try first | exact e.elim | exact e'.elim
    simp [FourCx.toBased, disk12, sc, mul_apply, Fintype.sum_sum_type]

/-- The contraction `δ⁻¹` of `disk23 δ`. -/
def disk23Contraction (δ : Rˣ) : Contraction (disk23 (δ : R)).toBased where
  hOE := 0
  hEO := fromBlocks 0 0 0 (sc ((δ⁻¹ : Rˣ) : R))
  deg_hOE _ _ h := absurd rfl h
  deg_hEO := by
    rintro (e | u) (e' | u') h
    all_goals first | exact e.elim | exact e'.elim | rfl
  htpy_E := by
    ext (e | u) (e' | u')
    all_goals try first | exact e.elim | exact e'.elim
    simp [FourCx.toBased, disk23, sc, mul_apply, Fintype.sum_sum_type]
  htpy_O := by
    ext (e | u) (e' | u')
    all_goals try first | exact e.elim | exact e'.elim
    simp [FourCx.toBased, disk23, sc, mul_apply, Fintype.sum_sum_type]

/-- **The disk with cokernel in degree one has torsion `δ`.** -/
theorem torsion_disk01 [IsDomain R] (δ : Rˣ) :
    torsion (disk01 (δ : R)).toBased (Equiv.refl _) = δ := by
  rw [← tau_eq_torsion _ (disk01Contraction δ)]
  unfold tau
  rw [← det_submatrix_equiv_self (Equiv.sumEmpty Unit Empty).symm, det_unique]
  simp [FourCx.toBased, disk01, disk01Contraction, sc]

/-- **The disk with cokernel in degree two has torsion `δ⁻¹`.** -/
theorem torsion_disk12 [IsDomain R] (δ : Rˣ) :
    torsion (disk12 (δ : R)).toBased (Equiv.sumComm _ _) = ((δ⁻¹ : Rˣ) : R) := by
  rw [← tau_eq_torsion _ (disk12Contraction δ)]
  unfold tau
  rw [← det_submatrix_equiv_self (Equiv.emptySum Empty Unit).symm, det_unique]
  simp [FourCx.toBased, disk12, disk12Contraction, sc]

/-- **The disk with cokernel in degree three has torsion `δ`.** -/
theorem torsion_disk23 [IsDomain R] (δ : Rˣ) :
    torsion (disk23 (δ : R)).toBased (Equiv.refl _) = δ := by
  rw [← tau_eq_torsion _ (disk23Contraction δ)]
  unfold tau
  rw [← det_submatrix_equiv_self (Equiv.emptySum Empty Unit).symm, det_unique]
  simp [FourCx.toBased, disk23, disk23Contraction, sc]

end Disks

/-! ### The Kummer model: two-term core plus torsion disks in degrees one, two, three -/

section KummerModel

variable {n : ℕ}

/-- The core `[R^n --D--> R^n]` (degrees one, two) plus torsion disks `δ₁, δ₂, δ₃` with cokernels
in degrees one, two, three. -/
def kummerModel (D : Matrix (Fin n) (Fin n) R) (δ₁ δ₂ δ₃ : R) :=
  (((twoTerm D).sum (disk01 δ₁)).sum (disk12 δ₂)).sum (disk23 δ₃)

/-- The class extended by zero. -/
def kz (z : Fin n → R) : ((Fin n ⊕ Unit) ⊕ Unit) ⊕ Empty → R :=
  Sum.elim (Sum.elim (Sum.elim z 0) 0) 0

/-- The functional extended by zero. -/
def kw (w : Fin n → R) : ((Fin n ⊕ Empty) ⊕ Unit) ⊕ Unit → R :=
  Sum.elim (Sum.elim (Sum.elim w 0) 0) 0

theorem kummerModel_hz (D : Matrix (Fin n) (Fin n) R) (δ₁ δ₂ δ₃ : R) {z : Fin n → R}
    (hz : (twoTerm D).d1 *ᵥ z = 0) : (kummerModel D δ₁ δ₂ δ₃).d1 *ᵥ kz z = 0 :=
  FourCx.sum_hz _ _ (FourCx.sum_hz _ _ (FourCx.sum_hz _ _ hz))

theorem kummerModel_hw (D : Matrix (Fin n) (Fin n) R) (δ₁ δ₂ δ₃ : R) {w : Fin n → R}
    (hw : w ᵥ* (twoTerm D).d1 = 0) : kw w ᵥ* (kummerModel D δ₁ δ₂ δ₃).d1 = 0 :=
  FourCx.sum_hlam _ _ (FourCx.sum_hlam _ _ (FourCx.sum_hlam _ _ hw))

/-- The orientation of the Kummer model. -/
def σK (n : ℕ) := sumOrient (sumOrient (sumOrient (σ₀ n) (Equiv.refl (Unit ⊕ Empty)))
  (Equiv.sumComm Empty Unit)) (Equiv.refl (Empty ⊕ Unit))

/-- **The coordinate of the Kummer model** (tex L4051–4064): over a domain, if the augmented core
is acyclic and `z ⊗ λ = u · adj D`, then `kmCoord = u · δ₁ · δ₂⁻¹ · δ₃`, i.e. each disk with
cokernel in degree `i` contributes `δ_i^{(−1)^{i+1}}`. -/
theorem kmCoord_kummerModel [IsDomain R] (D : Matrix (Fin n) (Fin n) R) (z w : Fin n → R) (u : R)
    (hz : (twoTerm D).d1 *ᵥ z = 0) (hw : w ᵥ* (twoTerm D).d1 = 0)
    (h : Contraction ((twoTerm D).aug z w hz hw).toBased)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord D z w u) (δ₁ δ₂ δ₃ : Rˣ) :
    kmCoord (kummerModel D (δ₁ : R) δ₂ δ₃) (kz z) (kw w) (kummerModel_hz D _ _ _ hz)
        (kummerModel_hw D _ _ _ hw) (σK n) = u * δ₁ * ((δ₂⁻¹ : Rˣ) : R) * δ₃ := by
  have h1 := augSumContraction (twoTerm D) (disk01 (δ₁ : R)) z w hz hw h (disk01Contraction δ₁)
  have h2 := augSumContraction _ (disk12 (δ₂ : R)) _ _ _ _ h1 (disk12Contraction δ₂)
  unfold kummerModel kz kw σK
  rw [kmCoord_sum _ _ _ _ _ _ h2 (disk23Contraction δ₃),
    kmCoord_sum _ _ _ _ _ _ h1 (disk12Contraction δ₂),
    kmCoord_sum _ _ _ _ _ _ h (disk01Contraction δ₁), kmCoord_twoTerm D z w u hz hw h hu,
    torsion_disk01, torsion_disk12, torsion_disk23]

end KummerModel

/-! ### Central valuations over `ℚ₂[[t]]` -/

section Valuation

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Contrib.CloudB3RC53.Calibration

variable {n : ℕ}

theorem v2_central_inv (δ : (PowerSeries ℚ_[2])ˣ) {g : ℤ} (hg : v2 (central δ) = g) :
    v2 (central ((δ⁻¹ : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2])) = ((-g : ℤ) : WithTop ℤ) := by
  have h := congrArg (fun f => v2 (central f)) δ.mul_inv
  simp only [central_mul, v2_mul, hg] at h
  have h1 : v2 (central (1 : PowerSeries ℚ_[2])) = 0 := by simp [central, v2]
  rw [h1] at h
  have hne : v2 (central ((δ⁻¹ : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2])) ≠ ⊤ := by
    intro htop; rw [htop, WithTop.add_top] at h; exact WithTop.top_ne_coe h
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hm] at h ⊢
  have h' : g + m = 0 := by exact_mod_cast h
  congr 1; omega

/-- **The torsion disks of the Kummer coordinate** (tex L4051–4064): over `ℚ₂[[t]]`, with the core
coordinate of central valuation `c` and disks of central valuations `g₁, s, g₃` in degrees one,
two, three, the coordinate has central valuation
`c + diskContribution 1 g₁ + diskContribution 2 s + diskContribution 3 g₃`. -/
theorem v2_kmCoord_kummerModel (D : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2]))
    (z w : Fin n → PowerSeries ℚ_[2]) (u : PowerSeries ℚ_[2])
    (hz : (twoTerm D).d1 *ᵥ z = 0) (hw : w ᵥ* (twoTerm D).d1 = 0)
    (h : Contraction ((twoTerm D).aug z w hz hw).toBased)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord D z w u)
    (δ₁ δ₂ δ₃ : (PowerSeries ℚ_[2])ˣ) {c g₁ s g₃ : ℤ} (hc : v2 (central u) = c)
    (h₁ : v2 (central δ₁) = g₁) (h₂ : v2 (central δ₂) = s) (h₃ : v2 (central δ₃) = g₃) :
    v2 (central (kmCoord (kummerModel D (δ₁ : PowerSeries ℚ_[2]) δ₂ δ₃) (kz z) (kw w)
        (kummerModel_hz D _ _ _ hz) (kummerModel_hw D _ _ _ hw) (σK n))) =
      ((c + (Central.diskContribution 1 g₁ + Central.diskContribution 2 s +
        Central.diskContribution 3 g₃) : ℤ) : WithTop ℤ) := by
  rw [kmCoord_kummerModel D z w u hz hw h hu δ₁ δ₂ δ₃]
  simp only [central_mul, v2_mul, hc, h₁, v2_central_inv δ₂ h₂, h₃]
  rw [show Central.diskContribution 1 g₁ + Central.diskContribution 2 s +
      Central.diskContribution 3 g₃ = g₁ - s + g₃ by simp [Central.diskContribution]; ring]
  norm_cast
  ring

/-- The class-functional coordinate under scaling of the class and the functional. -/
theorem isClassFunctionalCoord_smul {K : Type*} [CommRing K] (D : Matrix (Fin n) (Fin n) K)
    {z₀ w₀ : Fin n → K} {u₀ : K} (a b : K)
    (h : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord D z₀ w₀ u₀) :
    ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord D (a • z₀) (b • w₀) (a * b * u₀) := by
  unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord at h ⊢
  ext i j
  have := congrFun (congrFun h i) j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply] at this ⊢
  linear_combination a * b * this

/-- **The Kummer-coordinate input `hK` of `Calibration.hvprim_of_support_triangle`**, in its exact
type, from the Kummer model: class `a z₀` and functional `b λ₀` with `z₀ ⊗ λ₀ = u₀ adj D`,
`v₂ u₀(0) = 0`, `v₂ a(0) = v₂ b(0) = j + v₂L + v₂m` (the class and functional valuations), and
torsion disks of central lengths `g_A, s_A, g_A` in degrees one, two, three. -/
theorem hK_of_kummerModel (D : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2]))
    (z₀ w₀ : Fin n → PowerSeries ℚ_[2]) (u₀ a b : PowerSeries ℚ_[2])
    (hz : (twoTerm D).d1 *ᵥ (a • z₀) = 0) (hw : (b • w₀) ᵥ* (twoTerm D).d1 = 0)
    (h : Contraction ((twoTerm D).aug (a • z₀) (b • w₀) hz hw).toBased)
    (hu₀ : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord D z₀ w₀ u₀)
    (δ₁ δ₂ δ₃ : (PowerSeries ℚ_[2])ˣ) (j vL vm gA sA : ℤ) (hu₀v : v2 (central u₀) = 0)
    (ha : v2 (central a) = ((j + vL + vm : ℤ) : WithTop ℤ))
    (hb : v2 (central b) = ((j + vL + vm : ℤ) : WithTop ℤ))
    (h₁ : v2 (central δ₁) = gA) (h₂ : v2 (central δ₂) = sA) (h₃ : v2 (central δ₃) = gA) :
    v2 (central (kmCoord (kummerModel D (δ₁ : PowerSeries ℚ_[2]) δ₂ δ₃) (kz (a • z₀))
        (kw (b • w₀)) (kummerModel_hz D _ _ _ hz) (kummerModel_hw D _ _ _ hw) (σK n))) =
      (((j + vL + vm) + (j + vL + vm) +
        (Central.diskContribution 1 gA + Central.diskContribution 2 sA +
          Central.diskContribution 3 gA) : ℤ) : WithTop ℤ) := by
  have hc : v2 (central (a * b * u₀)) = (((j + vL + vm) + (j + vL + vm) : ℤ) : WithTop ℤ) := by
    simp only [central_mul, v2_mul, ha, hb, hu₀v, add_zero]
    norm_cast
  exact v2_kmCoord_kummerModel D _ _ _ hz hw h (isClassFunctionalCoord_smul D a b hu₀) δ₁ δ₂ δ₃
    hc h₁ h₂ h₃

/-- **RC0's `hvprim` from the Kummer model** (tex L4051–4078): the Kummer coordinate's valuation
(`hK_of_kummerModel`), the support triangle `det(D_W) · u_prim = u_K` and the quotient length
`2 v₂N + 4ω` (`Calibration.hvprim_of_support_triangle`; the length is computed in
`Calibration/Lengths.lean`). -/
theorem hvprim_of_kummerModel (D : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2]))
    (z₀ w₀ : Fin n → PowerSeries ℚ_[2]) (u₀ a b : PowerSeries ℚ_[2])
    (hz : (twoTerm D).d1 *ᵥ (a • z₀) = 0) (hw : (b • w₀) ᵥ* (twoTerm D).d1 = 0)
    (h : Contraction ((twoTerm D).aug (a • z₀) (b • w₀) hz hw).toBased)
    (hu₀ : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord D z₀ w₀ u₀)
    (δ₁ δ₂ δ₃ : (PowerSeries ℚ_[2])ˣ) (j vL vm gA sA vN ω : ℤ) (hu₀v : v2 (central u₀) = 0)
    (ha : v2 (central a) = ((j + vL + vm : ℤ) : WithTop ℤ))
    (hb : v2 (central b) = ((j + vL + vm : ℤ) : WithTop ℤ))
    (h₁ : v2 (central δ₁) = gA) (h₂ : v2 (central δ₂) = sA) (h₃ : v2 (central δ₃) = gA)
    {uprim δW : PowerSeries ℚ_[2]}
    (htri : δW * uprim = kmCoord (kummerModel D (δ₁ : PowerSeries ℚ_[2]) δ₂ δ₃) (kz (a • z₀))
        (kw (b • w₀)) (kummerModel_hz D _ _ _ hz) (kummerModel_hw D _ _ _ hw) (σK n))
    (hδ : v2 (central δW) = ((2 * vN + 4 * ω : ℤ) : WithTop ℤ)) :
    v2 (central uprim) = ((primValuation j vL vm gA sA vN ω : ℤ) : WithTop ℤ) :=
  hvprim_of_support_triangle j vL vm gA sA vN ω
    (hK_of_kummerModel D z₀ w₀ u₀ a b hz hw h hu₀ δ₁ δ₂ δ₃ j vL vm gA sA hu₀v ha hb h₁ h₂ h₃)
    htri hδ

end Valuation

/-! ### Non-vacuity -/

/-- **Non-vacuity of `kmCoord_kummerModel`**: the core `D = (0)`, `z = λ = u = 1` (with the
contraction `twoTermContraction_example`) and arbitrary unit disks. -/
theorem kmCoord_kummerModel_example [IsDomain R] (δ₁ δ₂ δ₃ : Rˣ) :
    kmCoord (kummerModel (0 : Matrix (Fin 1) (Fin 1) R) (δ₁ : R) δ₂ δ₃) (kz 1) (kw 1)
        (kummerModel_hz _ _ _ _ twoTerm_zero_hz) (kummerModel_hw _ _ _ _ twoTerm_zero_hw) (σK 1) =
      δ₁ * ((δ₂⁻¹ : Rˣ) : R) * δ₃ := by
  rw [kmCoord_kummerModel _ 1 1 1 _ _ twoTermContraction_example _ δ₁ δ₂ δ₃, one_mul]
  unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
  ext i j
  fin_cases i; fin_cases j
  simp [vecMulVec_apply, adjugate_fin_one]

end ZInQ.Contrib.CloudB3RC53.Torsion

