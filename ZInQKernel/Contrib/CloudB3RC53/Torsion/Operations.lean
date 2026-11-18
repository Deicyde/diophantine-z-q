import ZInQKernel.Contrib.CloudB3RC53.Torsion.Basic

/-!
# Torsion, part 2: reindexing, graded change of basis, direct sums, disks

* `BasedCx.reindex`, `tau_reindex`: relabelling the bases (with the transported orientation)
  does not change the torsion.
* `GradedBasisChange`, `BasedCx.rebase`, `tau_rebase`, `tau_rebase_graded`: under a graded change
  of basis `P = (P_k)` the torsion changes by `∏_{k odd} det P_k / ∏_{k even} det P_k`, i.e. by
  `∏_k (det P_k)^{(−1)^{k+1}}`.
* `BasedCx.sum`, `tau_sum`: the torsion is multiplicative over direct sums.
* `disk`, `tau_disk_even`, `tau_disk_odd`: the disk `e ↦ δ b` from degree `i` to degree `i + 1`
  (`δ` a unit) is acyclic with torsion `δ` for `i` even and `δ⁻¹` for `i` odd, i.e.
  `δ^{(−1)^i}`; the disks are genuine instances of `BasedCx` with a `Contraction`.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.Torsion

open Matrix

variable {R : Type*} [CommRing R]
variable {κe κo κe' κo' : Type*} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]
  [Fintype κe'] [Fintype κo'] [DecidableEq κe'] [DecidableEq κo']

/-! ### Reindexing -/

/-- Relabel the even and odd bases. -/
def BasedCx.reindex (C : BasedCx R κe κo) (eE : κe ≃ κe') (eO : κo ≃ κo') :
    BasedCx R κe' κo' where
  degE := C.degE ∘ eE.symm
  degO := C.degO ∘ eO.symm
  even_degE _ := C.even_degE _
  odd_degO _ := C.odd_degO _
  dOE := C.dOE.submatrix eO.symm eE.symm
  dEO := C.dEO.submatrix eE.symm eO.symm
  dd_E := by rw [submatrix_mul_equiv, C.dd_E]; ext; simp
  dd_O := by rw [submatrix_mul_equiv, C.dd_O]; ext; simp
  deg_dOE i j h := C.deg_dOE _ _ h
  deg_dEO i j h := C.deg_dEO _ _ h

/-- The relabelled contraction. -/
def Contraction.reindex {C : BasedCx R κe κo} (h : Contraction C) (eE : κe ≃ κe')
    (eO : κo ≃ κo') : Contraction (C.reindex eE eO) where
  hOE := h.hOE.submatrix eO.symm eE.symm
  hEO := h.hEO.submatrix eE.symm eO.symm
  deg_hOE i j hh := h.deg_hOE _ _ hh
  deg_hEO i j hh := h.deg_hEO _ _ hh
  htpy_E := by
    change C.dEO.submatrix eE.symm eO.symm * h.hOE.submatrix eO.symm eE.symm +
      h.hEO.submatrix eE.symm eO.symm * C.dOE.submatrix eO.symm eE.symm = 1
    rw [submatrix_mul_equiv, submatrix_mul_equiv]
    ext i j
    have := congrFun (congrFun h.htpy_E (eE.symm i)) (eE.symm j)
    simpa [Matrix.one_apply] using this
  htpy_O := by
    change C.dOE.submatrix eO.symm eE.symm * h.hEO.submatrix eE.symm eO.symm +
      h.hOE.submatrix eO.symm eE.symm * C.dEO.submatrix eE.symm eO.symm = 1
    rw [submatrix_mul_equiv, submatrix_mul_equiv]
    ext i j
    have := congrFun (congrFun h.htpy_O (eO.symm i)) (eO.symm j)
    simpa [Matrix.one_apply] using this

/-- **Relabelling the bases does not change the torsion** (orientation transported). -/
theorem tau_reindex (C : BasedCx R κe κo) (h : Contraction C) (σ : κe ≃ κo) (eE : κe ≃ κe')
    (eO : κo ≃ κo') :
    tau (C.reindex eE eO) (h.reindex eE eO) (eE.symm.trans (σ.trans eO)) = tau C h σ := by
  unfold tau
  have : ((C.reindex eE eO).dOE + (h.reindex eE eO).hOE).submatrix
      (eE.symm.trans (σ.trans eO)) id =
      ((C.dOE + h.hOE).submatrix σ id).submatrix eE.symm eE.symm := by
    ext i j
    simp [BasedCx.reindex, Contraction.reindex]
  rw [this, det_submatrix_equiv_self]

/-- Torsion form of `tau_reindex`. -/
theorem torsion_reindex [IsDomain R] (C : BasedCx R κe κo) (h : Contraction C) (σ : κe ≃ κo)
    (eE : κe ≃ κe') (eO : κo ≃ κo') :
    torsion (C.reindex eE eO) (eE.symm.trans (σ.trans eO)) = torsion C σ := by
  rw [← tau_eq_torsion _ (h.reindex eE eO), ← tau_eq_torsion _ h, tau_reindex]

/-! ### Graded change of basis -/

/-- A graded change of basis: invertible degree-zero matrices on the even and odd bases. -/
structure GradedBasisChange (C : BasedCx R κe κo) where
  Pe : Matrix κe κe R
  Qe : Matrix κe κe R
  Po : Matrix κo κo R
  Qo : Matrix κo κo R
  hPQe : Pe * Qe = 1
  hPQo : Po * Qo = 1
  deg_Pe : HasDeg Pe C.degE C.degE 0
  deg_Qe : HasDeg Qe C.degE C.degE 0
  deg_Po : HasDeg Po C.degO C.degO 0
  deg_Qo : HasDeg Qo C.degO C.degO 0

/-- The complex in the new bases: `d' = P d P⁻¹`. -/
def BasedCx.rebase (C : BasedCx R κe κo) (P : GradedBasisChange C) : BasedCx R κe κo where
  degE := C.degE
  degO := C.degO
  even_degE := C.even_degE
  odd_degO := C.odd_degO
  dOE := P.Po * C.dOE * P.Qe
  dEO := P.Pe * C.dEO * P.Qo
  dd_E := by
    have hQP : P.Qo * P.Po = 1 := mul_eq_one_comm.mp P.hPQo
    calc P.Pe * C.dEO * P.Qo * (P.Po * C.dOE * P.Qe)
        = P.Pe * C.dEO * (P.Qo * P.Po) * C.dOE * P.Qe := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P.Pe, C.dd_E]; simp
  dd_O := by
    have hQP : P.Qe * P.Pe = 1 := mul_eq_one_comm.mp P.hPQe
    calc P.Po * C.dOE * P.Qe * (P.Pe * C.dEO * P.Qo)
        = P.Po * C.dOE * (P.Qe * P.Pe) * C.dEO * P.Qo := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P.Po, C.dd_O]; simp
  deg_dOE := ((P.deg_Po.mul C.deg_dOE).mul P.deg_Qe).of_eq (by ring)
  deg_dEO := ((P.deg_Pe.mul C.deg_dEO).mul P.deg_Qo).of_eq (by ring)

/-- The contraction in the new bases. -/
def Contraction.rebase {C : BasedCx R κe κo} (h : Contraction C) (P : GradedBasisChange C) :
    Contraction (C.rebase P) where
  hOE := P.Po * h.hOE * P.Qe
  hEO := P.Pe * h.hEO * P.Qo
  deg_hOE := ((P.deg_Po.mul h.deg_hOE).mul P.deg_Qe).of_eq (by ring)
  deg_hEO := ((P.deg_Pe.mul h.deg_hEO).mul P.deg_Qo).of_eq (by ring)
  htpy_E := by
    have hQP : P.Qo * P.Po = 1 := mul_eq_one_comm.mp P.hPQo
    change P.Pe * C.dEO * P.Qo * (P.Po * h.hOE * P.Qe) +
      P.Pe * h.hEO * P.Qo * (P.Po * C.dOE * P.Qe) = 1
    calc _ = P.Pe * (C.dEO * (P.Qo * P.Po) * h.hOE + h.hEO * (P.Qo * P.Po) * C.dOE) * P.Qe := by
          simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
      _ = 1 := by rw [hQP, Matrix.mul_one, Matrix.mul_one, h.htpy_E, Matrix.mul_one, P.hPQe]
  htpy_O := by
    have hQP : P.Qe * P.Pe = 1 := mul_eq_one_comm.mp P.hPQe
    change P.Po * C.dOE * P.Qe * (P.Pe * h.hEO * P.Qo) +
      P.Po * h.hOE * P.Qe * (P.Pe * C.dEO * P.Qo) = 1
    calc _ = P.Po * (C.dOE * (P.Qe * P.Pe) * h.hEO + h.hOE * (P.Qe * P.Pe) * C.dEO) * P.Qo := by
          simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
      _ = 1 := by rw [hQP, Matrix.mul_one, Matrix.mul_one, h.htpy_O, Matrix.mul_one, P.hPQo]

/-- **Change of basis**: `τ(C') = det P_od · τ(C) · det P_ev⁻¹`. -/
theorem tau_rebase (C : BasedCx R κe κo) (h : Contraction C) (P : GradedBasisChange C)
    (σ : κe ≃ κo) : tau (C.rebase P) (h.rebase P) σ = P.Po.det * tau C h σ * P.Qe.det := by
  unfold tau
  change ((P.Po * C.dOE * P.Qe + P.Po * h.hOE * P.Qe).submatrix σ id).det = _
  have : (P.Po * C.dOE * P.Qe + P.Po * h.hOE * P.Qe).submatrix σ id =
      P.Po.submatrix σ σ * (C.dOE + h.hOE).submatrix σ id * P.Qe := by
    rw [submatrix_mul_equiv, ← Matrix.add_mul, ← Matrix.mul_add,
      Matrix.submatrix_mul _ _ σ id id Function.bijective_id, submatrix_id_id]
  rw [this, det_mul, det_mul, det_submatrix_equiv_self]

/-- **Graded change of basis**: `τ(C') · ∏_{k} det P_{ev,k} = (∏_{k} det P_{od,k}) · τ(C)`, the
products over the degree blocks; i.e. `τ` changes by `∏_k (det P_k)^{(−1)^{k+1}}`. -/
theorem tau_rebase_graded (C : BasedCx R κe κo) (h : Contraction C) (P : GradedBasisChange C)
    (σ : κe ≃ κo) :
    tau (C.rebase P) (h.rebase P) σ *
        ∏ k ∈ Finset.univ.image C.degE, (P.Pe.toSquareBlock C.degE k).det =
      (∏ k ∈ Finset.univ.image C.degO, (P.Po.toSquareBlock C.degO k).det) * tau C h σ := by
  rw [← P.deg_Pe.det_eq_prod, ← P.deg_Po.det_eq_prod, tau_rebase]
  have : P.Qe.det * P.Pe.det = 1 := by
    rw [← det_mul, mul_eq_one_comm.mp P.hPQe, det_one]
  calc P.Po.det * tau C h σ * P.Qe.det * P.Pe.det
      = P.Po.det * tau C h σ * (P.Qe.det * P.Pe.det) := by ring
    _ = _ := by rw [this, mul_one]

/-! ### Direct sums -/

theorem hasDeg_fromBlocks {m n m' n' : Type*} {A : Matrix m n R} {D : Matrix m' n' R}
    {bm : m → ℤ} {bn : n → ℤ} {bm' : m' → ℤ} {bn' : n' → ℤ} {a : ℤ}
    (hA : HasDeg A bm bn a) (hD : HasDeg D bm' bn' a) :
    HasDeg (fromBlocks A 0 0 D) (Sum.elim bm bm') (Sum.elim bn bn') a := by
  rintro (i | i) (j | j) hij
  · exact hA i j hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact hD i j hij

/-- The direct sum of based complexes. -/
def BasedCx.sum (C : BasedCx R κe κo) (C' : BasedCx R κe' κo') :
    BasedCx R (κe ⊕ κe') (κo ⊕ κo') where
  degE := Sum.elim C.degE C'.degE
  degO := Sum.elim C.degO C'.degO
  even_degE := by rintro (i | i); exacts [C.even_degE i, C'.even_degE i]
  odd_degO := by rintro (i | i); exacts [C.odd_degO i, C'.odd_degO i]
  dOE := fromBlocks C.dOE 0 0 C'.dOE
  dEO := fromBlocks C.dEO 0 0 C'.dEO
  dd_E := by rw [fromBlocks_multiply]; simp [C.dd_E, C'.dd_E]
  dd_O := by rw [fromBlocks_multiply]; simp [C.dd_O, C'.dd_O]
  deg_dOE := hasDeg_fromBlocks C.deg_dOE C'.deg_dOE
  deg_dEO := hasDeg_fromBlocks C.deg_dEO C'.deg_dEO

/-- The direct sum of contractions. -/
def Contraction.sum {C : BasedCx R κe κo} {C' : BasedCx R κe' κo'} (h : Contraction C)
    (h' : Contraction C') : Contraction (C.sum C') where
  hOE := fromBlocks h.hOE 0 0 h'.hOE
  hEO := fromBlocks h.hEO 0 0 h'.hEO
  deg_hOE := hasDeg_fromBlocks h.deg_hOE h'.deg_hOE
  deg_hEO := hasDeg_fromBlocks h.deg_hEO h'.deg_hEO
  htpy_E := by
    change fromBlocks C.dEO 0 0 C'.dEO * fromBlocks h.hOE 0 0 h'.hOE +
      fromBlocks h.hEO 0 0 h'.hEO * fromBlocks C.dOE 0 0 C'.dOE = 1
    rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add]
    simp [h.htpy_E, h'.htpy_E]
  htpy_O := by
    change fromBlocks C.dOE 0 0 C'.dOE * fromBlocks h.hEO 0 0 h'.hEO +
      fromBlocks h.hOE 0 0 h'.hOE * fromBlocks C.dEO 0 0 C'.dEO = 1
    rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add]
    simp [h.htpy_O, h'.htpy_O]

/-- **Multiplicativity over direct sums.** -/
theorem tau_sum (C : BasedCx R κe κo) (C' : BasedCx R κe' κo') (h : Contraction C)
    (h' : Contraction C') (σ : κe ≃ κo) (σ' : κe' ≃ κo') :
    tau (C.sum C') (h.sum h') (σ.sumCongr σ') = tau C h σ * tau C' h' σ' := by
  unfold tau
  have : ((C.sum C').dOE + (h.sum h').hOE).submatrix (σ.sumCongr σ') id =
      fromBlocks ((C.dOE + h.hOE).submatrix σ id) 0 0 ((C'.dOE + h'.hOE).submatrix σ' id) := by
    ext (i | i) (j | j) <;> simp [BasedCx.sum, Contraction.sum]
  rw [this, det_fromBlocks_zero₂₁]

theorem torsion_sum [IsDomain R] (C : BasedCx R κe κo) (C' : BasedCx R κe' κo')
    (h : Contraction C) (h' : Contraction C') (σ : κe ≃ κo) (σ' : κe' ≃ κo') :
    torsion (C.sum C') (σ.sumCongr σ') = torsion C σ * torsion C' σ' := by
  rw [← tau_eq_torsion _ (h.sum h'), ← tau_eq_torsion _ h, ← tau_eq_torsion _ h', tau_sum]

/-! ### Disks -/

/-- The scalar `1 × 1` matrix. -/
def sc (x : R) : Matrix Unit Unit R := of fun _ _ => x

theorem sc_mul (x y : R) : sc x * sc y = sc (x * y) := by ext; simp [sc, mul_apply]

theorem sc_one : sc (1 : R) = 1 := by ext; simp [sc]

theorem sc_zero : sc (0 : R) = 0 := by ext; simp [sc]

/-- The disk `R --δ--> R` from degree `i` to degree `i + 1`, `i` even. -/
def diskEven (i : ℤ) (hi : Even i) (δ : R) : BasedCx R Unit Unit where
  degE _ := i
  degO _ := i + 1
  even_degE _ := hi
  odd_degO _ := hi.add_one
  dOE := sc δ
  dEO := 0
  dd_E := by simp
  dd_O := by simp
  deg_dOE _ _ _ := rfl
  deg_dEO _ _ h := absurd rfl h

/-- The disk `R --δ--> R` from degree `i` to degree `i + 1`, `i` odd. -/
def diskOdd (i : ℤ) (hi : Odd i) (δ : R) : BasedCx R Unit Unit where
  degE _ := i + 1
  degO _ := i
  even_degE _ := hi.add_one
  odd_degO _ := hi
  dOE := 0
  dEO := sc δ
  dd_E := by simp
  dd_O := by simp
  deg_dOE _ _ h := absurd rfl h
  deg_dEO _ _ _ := rfl

/-- The contraction `δ⁻¹` of a disk with unit `δ`, `i` even. -/
def diskEvenContraction (i : ℤ) (hi : Even i) (δ : Rˣ) : Contraction (diskEven i hi (δ : R)) where
  hOE := 0
  hEO := sc ((δ⁻¹ : Rˣ) : R)
  deg_hOE _ _ h := absurd rfl h
  deg_hEO _ _ _ := by change i = i + 1 + -1; ring
  htpy_E := by
    change (0 : Matrix Unit Unit R) * 0 + sc ((δ⁻¹ : Rˣ) : R) * sc (δ : R) = 1
    rw [sc_mul, Units.inv_mul, sc_one]; simp
  htpy_O := by
    change sc (δ : R) * sc ((δ⁻¹ : Rˣ) : R) + 0 * 0 = 1
    rw [sc_mul, Units.mul_inv, sc_one]; simp

/-- The contraction `δ⁻¹` of a disk with unit `δ`, `i` odd. -/
def diskOddContraction (i : ℤ) (hi : Odd i) (δ : Rˣ) : Contraction (diskOdd i hi (δ : R)) where
  hOE := sc ((δ⁻¹ : Rˣ) : R)
  hEO := 0
  deg_hOE _ _ _ := by change i = i + 1 + -1; ring
  deg_hEO _ _ h := absurd rfl h
  htpy_E := by
    change sc (δ : R) * sc ((δ⁻¹ : Rˣ) : R) + 0 * 0 = 1
    rw [sc_mul, Units.mul_inv, sc_one]; simp
  htpy_O := by
    change (0 : Matrix Unit Unit R) * 0 + sc ((δ⁻¹ : Rˣ) : R) * sc (δ : R) = 1
    rw [sc_mul, Units.inv_mul, sc_one]; simp

/-- **A disk starting in even degree has torsion `δ`.** -/
theorem tau_disk_even (i : ℤ) (hi : Even i) (δ : Rˣ) :
    tau (diskEven i hi (δ : R)) (diskEvenContraction i hi δ) (Equiv.refl Unit) = δ := by
  unfold tau
  change ((sc (δ : R) + 0).submatrix (Equiv.refl Unit) id).det = _
  simp [sc]

/-- **A disk starting in odd degree has torsion `δ⁻¹`.** -/
theorem tau_disk_odd (i : ℤ) (hi : Odd i) (δ : Rˣ) :
    tau (diskOdd i hi (δ : R)) (diskOddContraction i hi δ) (Equiv.refl Unit) =
      ((δ⁻¹ : Rˣ) : R) := by
  unfold tau
  change ((0 + sc ((δ⁻¹ : Rˣ) : R)).submatrix (Equiv.refl Unit) id).det = _
  simp [sc]

end ZInQ.Contrib.CloudB3RC53.Torsion
