import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# Positive rational two-by-two Gaussian factorization

The identities are equalities of actual invertible rational matrices, verified
entry by entry. An integral determinant-one left factor makes the Gaussian
pivot positive. All other factors are rational transvections, a positive
scalar and a positive diagonal ratio; the latter is reduced to positive
integer diagonals and their inverses.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.RationalGaussian

abbrev GLQ := GL (Fin 2) ℚ
abbrev GLR := GL (Fin 2) ℝ

/-- The actual rational-to-real matrix homomorphism. -/
def mapR : GLQ →* GLR := Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

@[simp] lemma mapR_entry (A : GLQ) (i j : Fin 2) : mapR A i j=(A i j : ℝ) := rfl

@[simp] lemma slQ_entry (γ : SL(2,ℤ)) (i j : Fin 2) : mapGL ℚ γ i j=(γ i j : ℚ) := rfl

@[simp] lemma mapR_sl (γ : SL(2,ℤ)) : mapR (mapGL ℚ γ)=mapGL ℝ γ := by
  ext i j
  simp

/-- Determinant as the actual rational value of the determinant unit. -/
def detQ (A : GLQ) : ℚ := (A.det : ℚ)

lemma detQ_eq (A : GLQ) : detQ A=A 0 0*A 1 1-A 0 1*A 1 0 := by
  rw [detQ,Matrix.GeneralLinearGroup.val_det_apply,Matrix.det_fin_two]

@[simp] lemma detQ_mul (A B : GLQ) : detQ (A*B)=detQ A*detQ B := by simp [detQ]
@[simp] lemma detQ_sl (γ : SL(2,ℤ)) : detQ (mapGL ℚ γ)=1 := by simp [detQ]

lemma det_mapR (A : GLQ) : ((mapR A).det : ℝ)=(detQ A : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply,Matrix.det_fin_two,detQ_eq]
  simp

lemma mapR_det_pos (A : GLQ) (hA : 0<detQ A) : 0<((mapR A).det : ℝ) := by
  rw [det_mapR]
  exact_mod_cast hA

/-- The rational upper transvection. -/
def upperQ (x : ℚ) : GLQ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1,x;0,1] (by simp)
@[simp] lemma coe_upperQ (x : ℚ) : (upperQ x : Matrix (Fin 2) (Fin 2) ℚ)=!![1,x;0,1] := rfl

/-- The rational lower transvection. -/
def lowerQ (x : ℚ) : GLQ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1,0;x,1] (by simp)
@[simp] lemma coe_lowerQ (x : ℚ) : (lowerQ x : Matrix (Fin 2) (Fin 2) ℚ)=!![1,0;x,1] := rfl

/-- Positive rational scalar matrix, with an actual unit coefficient. -/
def scalarQ (t : ℚ) (ht : 0<t) : GLQ := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 t ht.ne')
@[simp] lemma coe_scalarQ (t : ℚ) (ht : 0<t) :
    (scalarQ t ht : Matrix (Fin 2) (Fin 2) ℚ)=!![t,0;0,t] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarQ]

/-- Positive rational diagonal ratio. -/
def diagonalQ (q : ℚ) (hq : 0<q) : GLQ := TauCeti.diagGL ![Units.mk0 q hq.ne',1]
@[simp] lemma coe_diagonalQ (q : ℚ) (hq : 0<q) :
    (diagonalQ q hq : Matrix (Fin 2) (Fin 2) ℚ)=!![q,0;0,1] := by
  rw [diagonalQ,TauCeti.diagGL_coe,Matrix.diagonal_fin_two]
  simp

@[simp] lemma coe_integer_diagonal (n : ℕ) [NeZero n] :
    (TauCeti.scaleGLRat n : Matrix (Fin 2) (Fin 2) ℚ)=!![(n : ℚ),0;0,1] := by
  rw [TauCeti.scaleGLRat,TauCeti.diagGL_coe,Matrix.diagonal_fin_two]
  simp

@[simp] lemma mapR_integer_diagonal (n : ℕ) [NeZero n] :
    mapR (TauCeti.scaleGLRat n)=TauCeti.scaleGL n := TauCeti.map_ratCast_scaleGLRat n

/-- The exact denominator conjugation for a rational upper translation. -/
theorem upperQ_fraction (m : ℤ) (n : ℕ) [NeZero n] :
    (TauCeti.scaleGLRat n)⁻¹ * mapGL ℚ (ModularGroup.T^m) * TauCeti.scaleGLRat n = upperQ ((m : ℚ)/n) := by
  have hnQ : (n : ℚ)≠0 := by exact_mod_cast NeZero.ne n
  rw [mul_assoc,inv_mul_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two]
  all_goals field_simp [hnQ]

/-- The pinned S has entries (0,-1;1,0), so the lower parameter has this sign. -/
theorem lowerQ_S (x : ℚ) :
    mapGL ℚ ModularGroup.S * upperQ (-x) * (mapGL ℚ ModularGroup.S)⁻¹=lowerQ x := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,ModularGroup.coe_S]

/-- Positive rational coefficients have positive integer numerator and denominator. -/
theorem positive_fraction (q : ℚ) (hq : 0<q) :
    ∃ m n : ℕ,0<m ∧ 0<n ∧ (m : ℚ)/(n : ℚ)=q := by
  have hmZ : 0<q.num := Rat.num_pos.mpr hq
  have hm : 0<q.num.toNat := by omega
  refine ⟨q.num.toNat,q.den,hm,Rat.den_pos q,?_⟩
  rw [show (q.num.toNat : ℚ)=(q.num : ℚ) by exact_mod_cast Int.toNat_of_nonneg (le_of_lt hmZ)]
  exact Rat.num_div_den q

/-- Every positive rational diagonal is an exact ratio of two positive integer diagonals. -/
theorem diagonalQ_fraction (q : ℚ) (hq : 0<q) :
    ∃ (m n : ℕ) (hm : 0<m) (hn : 0<n),
      letI : NeZero m := ⟨hm.ne'⟩
      letI : NeZero n := ⟨hn.ne'⟩
      TauCeti.scaleGLRat m*(TauCeti.scaleGLRat n)⁻¹=diagonalQ q hq := by
  obtain ⟨m,n,hm,hn,hqeq⟩ := positive_fraction q hq
  refine ⟨m,n,hm,hn,?_⟩
  let _ : NeZero m := ⟨hm.ne'⟩
  let _ : NeZero n := ⟨hn.ne'⟩
  have hnQ : (n : ℚ)≠0 := by exact_mod_cast hn.ne'
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  rw [← hqeq]
  field_simp [hnQ]

/-- The integral central sign matrix has determinant one in dimension two. -/
def negI : SL(2,ℤ) := ⟨!![-1,0;0,-1],by norm_num [Matrix.det_fin_two]⟩
@[simp] lemma coe_negI : (negI : Matrix (Fin 2) (Fin 2) ℤ)=!![-1,0;0,-1] := rfl

/-- An actual integral determinant-one left factor makes the Gaussian pivot positive. -/
theorem exists_positive_pivot (A : GLQ) (hA : 0<detQ A) :
    ∃ γ : SL(2,ℤ),0<(mapGL ℚ γ*A) 0 0 := by
  by_cases ha : A 0 0=0
  · have hc : A 1 0≠0 := by
      intro hc
      have hd : detQ A=0 := by rw [detQ_eq];simp [ha,hc]
      rw [hd] at hA
      exact (lt_irrefl _ hA)
    rcases lt_or_gt_of_ne hc with hc | hc
    · refine ⟨ModularGroup.S,?_⟩
      simpa [Matrix.mul_apply,Fin.sum_univ_two,ModularGroup.coe_S] using neg_pos.mpr hc
    · refine ⟨negI*ModularGroup.S,?_⟩
      simpa [Matrix.mul_apply,Fin.sum_univ_two,ModularGroup.coe_S] using hc
  · rcases lt_or_gt_of_ne ha with ha | ha
    · refine ⟨negI,?_⟩
      simpa [Matrix.mul_apply,Fin.sum_univ_two] using neg_pos.mpr ha
    · refine ⟨1,?_⟩
      simpa using ha

/-- The actual positive-pivot Gaussian identity. The order and all four entries
are verified; the lower-right equality uses the actual determinant. -/
theorem gaussian_positive (A : GLQ) (hA : 0<detQ A) (ha : 0<A 0 0) :
    A=lowerQ (A 1 0/A 0 0)*scalarQ (detQ A/A 0 0) (div_pos hA ha)*
      diagonalQ ((A 0 0)^2/detQ A) (div_pos (sq_pos_of_pos ha) hA)*upperQ (A 0 1/A 0 0) := by
  have hdiag : ((scalarQ (detQ A/A 0 0) (div_pos hA ha)*
      diagonalQ ((A 0 0)^2/detQ A) (div_pos (sq_pos_of_pos ha) hA) : GLQ) :
        Matrix (Fin 2) (Fin 2) ℚ)=!![A 0 0,0;0,detQ A/A 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
    all_goals field_simp [ha.ne',hA.ne']
  calc
    A=lowerQ (A 1 0/A 0 0)*(scalarQ (detQ A/A 0 0) (div_pos hA ha)*
        diagonalQ ((A 0 0)^2/detQ A) (div_pos (sq_pos_of_pos ha) hA))*upperQ (A 0 1/A 0 0) := by
      apply Units.ext
      change (A : Matrix (Fin 2) (Fin 2) ℚ)=
        (lowerQ (A 1 0/A 0 0) : Matrix (Fin 2) (Fin 2) ℚ)*
          ((scalarQ (detQ A/A 0 0) (div_pos hA ha)*
            diagonalQ ((A 0 0)^2/detQ A) (div_pos (sq_pos_of_pos ha) hA) : GLQ) :
              Matrix (Fin 2) (Fin 2) ℚ)*(upperQ (A 0 1/A 0 0) : Matrix (Fin 2) (Fin 2) ℚ)
      rw [hdiag,coe_lowerQ,coe_upperQ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
      all_goals try rw [detQ_eq]
      all_goals field_simp [ha.ne']
      all_goals ring
    _ = _ := by group

/-- Full positive-determinant rational factorization, including zero or negative
initial pivots. No factorization hypothesis is an input. -/
theorem exists_positive_gaussian (A : GLQ) (hA : 0<detQ A) :
    ∃ (γ : SL(2,ℤ)) (x y t q : ℚ) (ht : 0<t) (hq : 0<q),
      A=mapGL ℚ γ*lowerQ x*scalarQ t ht*diagonalQ q hq*upperQ y := by
  obtain ⟨γ,hpivot⟩ := exists_positive_pivot A hA
  let B : GLQ := mapGL ℚ γ*A
  have hB : 0<detQ B := by simpa [B] using hA
  have hb : 0<B 0 0 := hpivot
  have hGauss := gaussian_positive B hB hb
  refine ⟨γ⁻¹,B 1 0/B 0 0,B 0 1/B 0 0,detQ B/B 0 0,(B 0 0)^2/detQ B,
    div_pos hB hb,div_pos (sq_pos_of_pos hb) hB,?_⟩
  have hEq : A=mapGL ℚ γ⁻¹*B := by simp [B,map_inv]
  calc
    A=mapGL ℚ γ⁻¹*B := hEq
    _ = mapGL ℚ γ⁻¹*(lowerQ (B 1 0/B 0 0)*scalarQ (detQ B/B 0 0) (div_pos hB hb)*
        diagonalQ ((B 0 0)^2/detQ B) (div_pos (sq_pos_of_pos hb) hB)*upperQ (B 0 1/B 0 0)) :=
      congrArg (fun C : GLQ => mapGL ℚ γ⁻¹*C) hGauss
    _ = _ := by simp only [mul_assoc]

end ZInQ.Contrib.HeckePrimeRationality.RationalGaussian
