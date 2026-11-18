import Mathlib

/-!
# Torsion, part 1: based acyclic complexes and their torsion

The torsion of an exact bounded complex of finite free modules with bases (the determinant-line
coordinate of `diophantine_zq.tex`, used for the class-functional coordinate, tex L3877–3892, and
the torsion disks of the calibration, tex L4051–4064). A bounded complex `C^•` with bases is
recorded by its even part `C^{ev} = ⊕_{k even} C^k` (basis `κe`, degrees `degE`) and its odd part
`C^{od} = ⊕_{k odd} C^k` (basis `κo`, degrees `degO`), with the differential split into
`dOE : C^{ev} → C^{od}` and `dEO : C^{od} → C^{ev}`, both of degree `+1`.

A **chain contraction** `h` (degree `−1`, `dh + hd = 1`) exists exactly when the complex is
exact (over a field); the **torsion** is

  `τ(C, h) = det(d + h : C^{ev} → C^{od})`,

computed in the bases, with the orientation `σ : κe ≃ κo` identifying the two bases (the sign
convention; a different orientation changes `τ` by the sign of a permutation).

* `HasDeg`: a matrix between graded bases is homogeneous of a given degree; products and sums.
* `det_one_add_of_mul_self_eq_zero`: over a domain, `det (1 + N) = 1` when `N² = 0`.
* `tau_mul_tauOdd` (Milnor, Turaev Lemma 1.3): `det(d + h)|_{ev} · det(d + h')|_{od} = 1` for any
  two contractions; `tau_indep`: `τ` does not depend on the contraction; `isUnit_tau`.
* `torsion`: the torsion of an acyclic based complex (any contraction), `tau_eq_torsion`.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.Torsion

open Matrix

variable {R : Type*} [CommRing R]

/-! ### Homogeneous matrices -/

section HasDeg

variable {l m n p : Type*}

/-- The matrix `X` (rows graded by `bm`, columns by `bn`) is homogeneous of degree `a`. -/
def HasDeg (X : Matrix m n R) (bm : m → ℤ) (bn : n → ℤ) (a : ℤ) : Prop :=
  ∀ i j, X i j ≠ 0 → bm i = bn j + a

theorem HasDeg.mul [Fintype n] {X : Matrix m n R} {Y : Matrix n p R} {bm : m → ℤ} {bn : n → ℤ}
    {bp : p → ℤ} {a c : ℤ} (hX : HasDeg X bm bn a) (hY : HasDeg Y bn bp c) :
    HasDeg (X * Y) bm bp (a + c) := by
  intro i j hij
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
  have h1 := hX i k (left_ne_zero_of_mul hk)
  have h2 := hY k j (right_ne_zero_of_mul hk)
  rw [h1, h2]; ring

theorem HasDeg.add {X Y : Matrix m n R} {bm : m → ℤ} {bn : n → ℤ} {a : ℤ}
    (hX : HasDeg X bm bn a) (hY : HasDeg Y bm bn a) : HasDeg (X + Y) bm bn a := by
  intro i j hij
  by_cases hx : X i j = 0
  · exact hY i j (by simpa [hx] using hij)
  · exact hX i j hx

theorem HasDeg.neg {X : Matrix m n R} {bm : m → ℤ} {bn : n → ℤ} {a : ℤ}
    (hX : HasDeg X bm bn a) : HasDeg (-X) bm bn a :=
  fun i j hij => hX i j (by simpa using hij)

theorem HasDeg.sub {X Y : Matrix m n R} {bm : m → ℤ} {bn : n → ℤ} {a : ℤ}
    (hX : HasDeg X bm bn a) (hY : HasDeg Y bm bn a) : HasDeg (X - Y) bm bn a := by
  rw [sub_eq_add_neg]; exact hX.add hY.neg

theorem hasDeg_zero (bm : m → ℤ) (bn : n → ℤ) (a : ℤ) : HasDeg (0 : Matrix m n R) bm bn a :=
  fun _ _ h => absurd rfl h

theorem hasDeg_one [DecidableEq m] (b : m → ℤ) : HasDeg (1 : Matrix m m R) b b 0 := by
  intro i j hij
  by_cases h : i = j
  · subst h; simp
  · exact absurd (one_apply_ne h) hij

theorem HasDeg.of_eq {X : Matrix m n R} {bm : m → ℤ} {bn : n → ℤ} {a b : ℤ}
    (hX : HasDeg X bm bn a) (h : a = b) : HasDeg X bm bn b := h ▸ hX

/-- A degree-zero endomorphism is block triangular for the grading. -/
theorem HasDeg.blockTriangular {X : Matrix m m R} {b : m → ℤ} (hX : HasDeg X b b 0) :
    X.BlockTriangular b := by
  intro i j hij
  by_contra h
  have := hX i j h
  omega

/-- A degree-zero endomorphism has determinant the product of its graded blocks. -/
theorem HasDeg.det_eq_prod [Fintype m] [DecidableEq m] {X : Matrix m m R} {b : m → ℤ}
    (hX : HasDeg X b b 0) :
    X.det = ∏ k ∈ Finset.univ.image b, (X.toSquareBlock b k).det :=
  hX.blockTriangular.det

/-- Blocks of a product with a degree-zero left factor. -/
theorem HasDeg.toSquareBlock_mul [Fintype m] {X Y : Matrix m m R} {b : m → ℤ}
    (hX : HasDeg X b b 0) (k : ℤ) :
    (X * Y).toSquareBlock b k = X.toSquareBlock b k * Y.toSquareBlock b k := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [toSquareBlock_def, of_apply, mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun l => b l = k) (fun l => X i l * Y l j)]
  have : ∑ l : {l // ¬ b l = k}, X i l * Y l j = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    have : X i l = 0 := by
      by_contra hne
      have := hX i l hne
      exact l.2 (by omega)
    rw [this, zero_mul]
  rw [this, add_zero]

end HasDeg

/-! ### `det (1 + N) = 1` for `N² = 0` over a domain -/

theorem det_one_add_of_mul_self_eq_zero [IsDomain R] {m : Type*} [Fintype m] [DecidableEq m]
    (N : Matrix m m R) (hN : N * N = 0) : (1 + N).det = 1 := by
  set P : Matrix m m (Polynomial R) := 1 + (Polynomial.X : Polynomial R) • N.map Polynomial.C
  set Q : Matrix m m (Polynomial R) := 1 - (Polynomial.X : Polynomial R) • N.map Polynomial.C
  have hNN : N.map Polynomial.C * N.map Polynomial.C = 0 := by
    rw [← Matrix.map_mul, hN, Matrix.map_zero _ (map_zero Polynomial.C)]
  have hPQ : P * Q = 1 := by
    simp only [P, Q, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hNN, smul_zero]
    abel_nf
  have hunit : IsUnit P.det := isUnit_iff_exists_inv.mpr ⟨Q.det, by rw [← det_mul, hPQ, det_one]⟩
  obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.mp hunit
  have hev : ∀ t : R, (Polynomial.evalRingHom t).mapMatrix P = 1 + t • N := by
    intro t
    simp only [P, map_add, map_one]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  have h0 := RingHom.map_det (Polynomial.evalRingHom 0) P
  have h1 := RingHom.map_det (Polynomial.evalRingHom 1) P
  rw [hev, zero_smul, add_zero, det_one, ← hr, Polynomial.coe_evalRingHom,
    Polynomial.eval_C] at h0
  rw [hev, one_smul, ← hr, Polynomial.coe_evalRingHom, Polynomial.eval_C, h0] at h1
  exact h1.symm

/-! ### Based complexes, contractions, torsion -/

/-- A bounded complex of finite free `R`-modules with bases, split into even part (basis `κe`,
degrees `degE`, all even) and odd part (basis `κo`, degrees `degO`, all odd); the differential
`dOE : C^{ev} → C^{od}`, `dEO : C^{od} → C^{ev}` has degree `+1` and squares to zero. -/
structure BasedCx (R : Type*) [CommRing R] (κe κo : Type*) [Fintype κe] [Fintype κo] where
  degE : κe → ℤ
  degO : κo → ℤ
  even_degE : ∀ i, Even (degE i)
  odd_degO : ∀ i, Odd (degO i)
  dOE : Matrix κo κe R
  dEO : Matrix κe κo R
  dd_E : dEO * dOE = 0
  dd_O : dOE * dEO = 0
  deg_dOE : HasDeg dOE degO degE 1
  deg_dEO : HasDeg dEO degE degO 1

variable {κe κo : Type*} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]

/-- A chain contraction: `h` of degree `−1` with `dh + hd = 1`. -/
structure Contraction (C : BasedCx R κe κo) where
  hOE : Matrix κo κe R
  hEO : Matrix κe κo R
  deg_hOE : HasDeg hOE C.degO C.degE (-1)
  deg_hEO : HasDeg hEO C.degE C.degO (-1)
  htpy_E : C.dEO * hOE + hEO * C.dOE = 1
  htpy_O : C.dOE * hEO + hOE * C.dEO = 1

/-- The torsion `det(d + h : C^{ev} → C^{od})` in the given bases, oriented by `σ`. -/
def tau (C : BasedCx R κe κo) (h : Contraction C) (σ : κe ≃ κo) : R :=
  ((C.dOE + h.hOE).submatrix σ id).det

/-- The odd torsion `det(d + h : C^{od} → C^{ev})`. -/
def tauOdd (C : BasedCx R κe κo) (h : Contraction C) (σ : κe ≃ κo) : R :=
  ((C.dEO + h.hEO).submatrix id σ).det

/-- **The torsion is well defined** (Milnor; Turaev, *Introduction to combinatorial torsions*,
Lemma 1.3): for two contractions `h, h'`, `(d + h')(d + h)` on `C^{ev}` is block triangular for
the degree with unipotent diagonal blocks, so `det(d + h)|_{ev} · det(d + h')|_{od} = 1`. -/
theorem tau_mul_tauOdd [IsDomain R] (C : BasedCx R κe κo) (h h' : Contraction C)
    (σ : κe ≃ κo) : tau C h σ * tauOdd C h' σ = 1 := by
  unfold tau tauOdd
  rw [mul_comm, ← det_mul, submatrix_mul_equiv, submatrix_id_id]
  set N := (h'.hEO - h.hEO) * C.dOE
  set L := h'.hEO * h.hOE
  have hM : (C.dEO + h'.hEO) * (C.dOE + h.hOE) = 1 + N + L := by
    have e := h.htpy_E
    simp only [N, L, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, C.dd_E]
    rw [← e]; abel_nf
  have hN : HasDeg N C.degE C.degE 0 :=
    ((h'.deg_hEO.sub h.deg_hEO).mul C.deg_dOE).of_eq (by ring)
  have hL : HasDeg L C.degE C.degE (-2) := (h'.deg_hEO.mul h.deg_hOE).of_eq (by ring)
  have hNN : N * N = 0 := by
    -- `d δ + δ d = 0` for the difference `δ = h' − h`
    have hδ : C.dOE * (h'.hEO - h.hEO) = -((h'.hOE - h.hOE) * C.dEO) := by
      have e1 := h.htpy_O; have e2 := h'.htpy_O
      rw [Matrix.mul_sub, Matrix.sub_mul]
      rw [← sub_eq_zero]
      have : C.dOE * h'.hEO + h'.hOE * C.dEO - (C.dOE * h.hEO + h.hOE * C.dEO) = 0 := by
        rw [e1, e2, sub_self]
      rw [← this]; abel_nf
    simp only [N]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc C.dOE, hδ]
    simp [Matrix.mul_assoc, C.dd_E]
  rw [hM]
  have hbt : (1 + N + L).BlockTriangular C.degE := by
    intro i j hij
    have h1 : (1 : Matrix κe κe R) i j = 0 := one_apply_ne (by rintro rfl; exact lt_irrefl _ hij)
    have h2 : N i j = 0 := by
      by_contra hne; have := hN i j hne; omega
    have h3 : L i j = 0 := by
      by_contra hne; have := hL i j hne; omega
    simp [h1, h2, h3]
  rw [hbt.det]
  refine Finset.prod_eq_one fun k _ => ?_
  have hblock : (1 + N + L).toSquareBlock C.degE k = 1 + N.toSquareBlock C.degE k := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    have h3 : L i j = 0 := by
      by_contra hne; have := hL i j hne; omega
    simp only [toSquareBlock_def, of_apply, Matrix.add_apply, h3, add_zero]
    by_cases hij : i = j
    · subst hij; simp
    · rw [one_apply_ne hij, one_apply_ne (fun h => hij (congrArg Subtype.val h))]
  rw [hblock]
  apply det_one_add_of_mul_self_eq_zero
  rw [← hN.toSquareBlock_mul, hNN]
  rfl

/-- **The torsion does not depend on the contraction.** -/
theorem tau_indep [IsDomain R] (C : BasedCx R κe κo) (h h' : Contraction C) (σ : κe ≃ κo) :
    tau C h σ = tau C h' σ := by
  have e1 := tau_mul_tauOdd C h h σ
  have e2 := tau_mul_tauOdd C h' h σ
  calc tau C h σ = tau C h σ * (tau C h' σ * tauOdd C h σ) := by rw [e2, mul_one]
    _ = tau C h' σ * (tau C h σ * tauOdd C h σ) := by ring
    _ = tau C h' σ := by rw [e1, mul_one]

theorem isUnit_tau [IsDomain R] (C : BasedCx R κe κo) (h : Contraction C) (σ : κe ≃ κo) :
    IsUnit (tau C h σ) :=
  isUnit_iff_exists_inv.mpr ⟨_, tau_mul_tauOdd C h h σ⟩

/-- The torsion of an acyclic (contractible) based complex, oriented by `σ`. -/
noncomputable def torsion (C : BasedCx R κe κo) (σ : κe ≃ κo) : R := by
  classical
  exact if hC : Nonempty (Contraction C) then tau C hC.some σ else 0

theorem tau_eq_torsion [IsDomain R] (C : BasedCx R κe κo) (h : Contraction C) (σ : κe ≃ κo) :
    tau C h σ = torsion C σ := by
  unfold torsion
  split
  · exact tau_indep C h _ σ
  · exact absurd (⟨h⟩ : Nonempty (Contraction C)) ‹_›

end ZInQ.Contrib.CloudB3RC53.Torsion
