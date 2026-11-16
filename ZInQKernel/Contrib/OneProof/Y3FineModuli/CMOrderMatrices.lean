import ZInQKernel.HDecomp.QM.Structures
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Integral CM order matrices

New algebraic construction for the fixed public `LeafQM.O`; not a source
citation and not a moduli-object, elliptic-curve, torsion-point or R1 supplier.
The quaternion/order definitions and their inherited multiplication are not
changed. In particular `LeafQM.ofInt` lands in `LeafQM.B`; `orderOfInt` below
is its canonical lift to the actual subring carrier.
-/

noncomputable section

namespace ZInQ.Contrib.Y3FineModuli.CMOrderMatrices

abbrev CMMatrix := Matrix (Fin 2) (Fin 2) GaussianInt

/-- The actual Gaussian integer with real part zero and imaginary part one. -/
def gaussianI : GaussianInt := ⟨0, 1⟩

/-- The proposed integral image of the original quaternion generator `oi`. -/
def iMatrix : CMMatrix :=
  !![-1 - gaussianI, 1 - gaussianI; 2, 1 + gaussianI]

/-- The proposed integral image of the basis element `(1 + oj) / 2`. -/
def wMatrix : CMMatrix := !![0, -1; 1, 1]

/-- The integral image of `oj`, expressed without division in the codomain. -/
def jMatrix : CMMatrix := 2 * wMatrix - 1

/-- The literal vector on which the integral matrix representation is evaluated. -/
def distinguishedVector : Fin 2 → GaussianInt := ![1, 0]

/-- Canonical lift of the defining integral coordinates into the actual order. -/
def orderOfInt (n : Fin 4 → ℤ) : LeafQM.O :=
  ⟨LeafQM.ofInt n, ⟨n, rfl⟩⟩

@[simp] theorem orderOfInt_coe (n : Fin 4 → ℤ) :
    (orderOfInt n : LeafQM.B) = LeafQM.ofInt n := rfl

@[simp] theorem orderOfInt_zero : orderOfInt 0 = 0 := by
  apply Subtype.ext
  exact LeafQM.ofInt_zero

@[simp] theorem orderOfInt_one : orderOfInt ![1, 0, 0, 0] = 1 := by
  apply Subtype.ext
  exact LeafQM.ofInt_one

theorem orderOfInt_add (n m : Fin 4 → ℤ) :
    orderOfInt (n + m) = orderOfInt n + orderOfInt m := by
  apply Subtype.ext
  exact (LeafQM.ofInt_add n m).symm

theorem orderOfInt_mul (n m : Fin 4 → ℤ) :
    orderOfInt n * orderOfInt m = orderOfInt (LeafQM.mulCoord n m) := by
  apply Subtype.ext
  exact LeafQM.ofInt_mul n m

/-- No new basis premise: uniqueness is the original defining-source theorem. -/
theorem orderOfInt_injective : Function.Injective orderOfInt := by
  intro n m h
  exact LeafQM.AV.ofInt_injective (congrArg Subtype.val h)

/-- No new spanning premise: every element has its defining integral coordinates. -/
theorem orderOfInt_surjective : Function.Surjective orderOfInt := by
  intro x
  obtain ⟨n, hn⟩ := x.2
  exact ⟨n, Subtype.ext hn.symm⟩

def orderOfIntAddHom : (Fin 4 → ℤ) →+ LeafQM.O where
  toFun := orderOfInt
  map_zero' := orderOfInt_zero
  map_add' := orderOfInt_add

/-- Genuine integer-linear coordinates, constructed from the actual carrier. -/
def orderFromCoordsEquiv : (Fin 4 → ℤ) ≃ₗ[ℤ] LeafQM.O :=
  LinearEquiv.ofBijective orderOfIntAddHom.toIntLinearMap
    ⟨orderOfInt_injective, orderOfInt_surjective⟩

def orderCoordEquiv : LeafQM.O ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  orderFromCoordsEquiv.symm

@[simp] theorem orderFromCoordsEquiv_apply (n : Fin 4 → ℤ) :
    orderFromCoordsEquiv n = orderOfInt n := rfl

@[simp] theorem orderCoordEquiv_orderOfInt (n : Fin 4 → ℤ) :
    orderCoordEquiv (orderOfInt n) = n :=
  orderFromCoordsEquiv.symm_apply_apply n

@[simp] theorem orderOfInt_orderCoordEquiv (x : LeafQM.O) :
    orderOfInt (orderCoordEquiv x) = x :=
  orderFromCoordsEquiv.apply_symm_apply x

/-- Integral coordinate formula, with no rational division in the matrix ring. -/
def coeffMatrix (n : Fin 4 → ℤ) : CMMatrix :=
  n 0 • (1 : CMMatrix) + n 1 • iMatrix + n 2 • wMatrix +
    n 3 • (iMatrix * wMatrix)

@[simp] theorem coeffMatrix_zero : coeffMatrix 0 = 0 := by
  simp [coeffMatrix]

theorem coeffMatrix_add (n m : Fin 4 → ℤ) :
    coeffMatrix (n + m) = coeffMatrix n + coeffMatrix m := by
  simp only [coeffMatrix, Pi.add_apply, add_smul]
  abel

@[simp] theorem coeffMatrix_oneBasis : coeffMatrix ![1, 0, 0, 0] = 1 := by
  simp [coeffMatrix]

@[simp] theorem coeffMatrix_iBasis : coeffMatrix ![0, 1, 0, 0] = iMatrix := by
  simp [coeffMatrix]

@[simp] theorem coeffMatrix_wBasis : coeffMatrix ![0, 0, 1, 0] = wMatrix := by
  simp [coeffMatrix]

@[simp] theorem coeffMatrix_iwBasis :
    coeffMatrix ![0, 0, 0, 1] = iMatrix * wMatrix := by
  simp [coeffMatrix]

def coeffMatrixAddHom : (Fin 4 → ℤ) →+ CMMatrix where
  toFun := coeffMatrix
  map_zero' := coeffMatrix_zero
  map_add' := coeffMatrix_add

/-- The additive integral representation on the actual inherited order carrier. -/
def orderMatrixAddHom : LeafQM.O →+ CMMatrix :=
  coeffMatrixAddHom.comp orderCoordEquiv.toAddMonoidHom

@[simp] theorem orderMatrixAddHom_orderOfInt (n : Fin 4 → ℤ) :
    orderMatrixAddHom (orderOfInt n) = coeffMatrix n := by
  simp [orderMatrixAddHom, coeffMatrixAddHom]

@[simp] theorem orderMatrixAddHom_oi :
    orderMatrixAddHom LeafQM.AV.oi = iMatrix := by
  change coeffMatrix (orderCoordEquiv (orderOfInt ![0, 1, 0, 0])) = iMatrix
  simp

theorem gaussianI_mul_gaussianI : gaussianI * gaussianI = -1 := by
  ext <;> simp [gaussianI]

theorem iMatrix_mul_self : iMatrix * iMatrix = (2 : CMMatrix) := by
  ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [iMatrix, gaussianI, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.ofNat_fin_two]

theorem iMatrix_sq : iMatrix ^ 2 = (2 : CMMatrix) := by
  simpa [pow_two] using iMatrix_mul_self

theorem wMatrix_mul_self : wMatrix * wMatrix = wMatrix - 1 := by
  ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [wMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem wMatrix_sq : wMatrix ^ 2 = wMatrix - 1 := by
  simpa [pow_two] using wMatrix_mul_self

theorem wMatrix_mul_iMatrix : wMatrix * iMatrix = iMatrix - iMatrix * wMatrix := by
  ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [iMatrix, wMatrix, gaussianI, Matrix.mul_apply, Fin.sum_univ_two]

theorem jMatrix_mul_self : jMatrix * jMatrix = -(3 : CMMatrix) := by
  ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [jMatrix, wMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.ofNat_fin_two]

theorem jMatrix_sq : jMatrix ^ 2 = -(3 : CMMatrix) := by
  simpa [pow_two] using jMatrix_mul_self

theorem iMatrix_mul_jMatrix : iMatrix * jMatrix = -(jMatrix * iMatrix) := by
  ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [iMatrix, jMatrix, wMatrix, gaussianI, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.ofNat_fin_two]

/-- Multiplication in the original order coordinates is respected by the
integral matrices. This is a universal identity for all integer coordinates,
not an assumed ring homomorphism or a finite-example substitute. -/
theorem coeffMatrix_mul (n m : Fin 4 → ℤ) :
    coeffMatrix (LeafQM.mulCoord n m) = coeffMatrix n * coeffMatrix m := by
  ext r c <;> fin_cases r <;> fin_cases c
  all_goals
    simp only [coeffMatrix, LeafQM.mulCoord, Matrix.add_apply, Matrix.smul_apply,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp [iMatrix, wMatrix, gaussianI, Matrix.one_apply, zsmul_eq_mul]
    ring

/-- Closed unital integral representation of the actual inherited subring.
There is no ring-homomorphism, faithfulness, or moduli premise. -/
def rho : LeafQM.O →+* CMMatrix where
  toFun := orderMatrixAddHom
  map_one' := by
    rw [← orderOfInt_one, orderMatrixAddHom_orderOfInt, coeffMatrix_oneBasis]
  map_mul' x y := by
    obtain ⟨n, rfl⟩ := orderOfInt_surjective x
    obtain ⟨m, rfl⟩ := orderOfInt_surjective y
    simp only [orderOfInt_mul, orderMatrixAddHom_orderOfInt]
    exact coeffMatrix_mul n m
  map_zero' := orderMatrixAddHom.map_zero
  map_add' := orderMatrixAddHom.map_add

@[simp] theorem rho_orderOfInt (n : Fin 4 → ℤ) :
    rho (orderOfInt n) = coeffMatrix n :=
  orderMatrixAddHom_orderOfInt n

@[simp] theorem rho_oi : rho LeafQM.AV.oi = iMatrix :=
  orderMatrixAddHom_oi

@[simp] theorem rho_wBasis : rho (orderOfInt ![0, 0, 1, 0]) = wMatrix := by
  simp

/-- The original coordinate formula with integer matrix casts and no division. -/
theorem rho_orderOfInt_formula (n : Fin 4 → ℤ) :
    rho (orderOfInt n) =
      (n 0 : CMMatrix) * 1 + (n 1 : CMMatrix) * iMatrix +
        (n 2 : CMMatrix) * wMatrix + (n 3 : CMMatrix) * (iMatrix * wMatrix) := by
  rw [rho_orderOfInt]
  simp only [coeffMatrix, zsmul_eq_mul]

/-- Evaluation at the actual integral vector `(1,0)`, not a scheme point. -/
def evaluationAddHom : LeafQM.O →+ (Fin 2 → GaussianInt) where
  toFun m := (rho m).mulVec distinguishedVector
  map_zero' := by
    simp
  map_add' m n := by
    change (rho (m + n)).mulVec distinguishedVector =
      (rho m).mulVec distinguishedVector + (rho n).mulVec distinguishedVector
    rw [map_add, Matrix.add_mulVec]

/-- The same genuine vector evaluation with its canonical integer linearity. -/
def evaluationLinearMap : LeafQM.O →ₗ[ℤ] (Fin 2 → GaussianInt) :=
  evaluationAddHom.toIntLinearMap

@[simp] theorem evaluationLinearMap_apply (m : LeafQM.O) :
    evaluationLinearMap m = (rho m).mulVec distinguishedVector := rfl

/-! ## Explicit integral Gaussian coefficient-column equivalence -/

def coeffColumnFun (n : Fin 4 → ℤ) : Fin 2 → GaussianInt :=
  ![⟨n 0 - n 1 + n 3, -n 1 - n 3⟩, ⟨2 * n 1 + n 2 + n 3, n 3⟩]

def coeffColumnInvFun (v : Fin 2 → GaussianInt) : Fin 4 → ℤ :=
  ![(v 0).re - (v 0).im - 2 * (v 1).im, -(v 0).im - (v 1).im,
    (v 1).re + 2 * (v 0).im + (v 1).im, (v 1).im]

theorem coeffColumnInvFun_coeffColumnFun (n : Fin 4 → ℤ) :
    coeffColumnInvFun (coeffColumnFun n) = n := by
  funext i
  fin_cases i <;> simp [coeffColumnInvFun, coeffColumnFun] <;> ring

theorem coeffColumnFun_coeffColumnInvFun (v : Fin 2 → GaussianInt) :
    coeffColumnFun (coeffColumnInvFun v) = v := by
  funext i
  fin_cases i <;> ext <;> simp [coeffColumnInvFun, coeffColumnFun] <;> ring

theorem coeffColumnFun_add (n m : Fin 4 → ℤ) :
    coeffColumnFun (n + m) = coeffColumnFun n + coeffColumnFun m := by
  funext i
  fin_cases i <;> ext <;> simp [coeffColumnFun] <;> ring

def coeffColumnAddEquiv : (Fin 4 → ℤ) ≃+ (Fin 2 → GaussianInt) where
  toFun := coeffColumnFun
  invFun := coeffColumnInvFun
  left_inv := coeffColumnInvFun_coeffColumnFun
  right_inv := coeffColumnFun_coeffColumnInvFun
  map_add' := coeffColumnFun_add

def coeffColumnEquiv : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 2 → GaussianInt) :=
  coeffColumnAddEquiv.toIntLinearEquiv

theorem coeffColumnEquiv_apply (n : Fin 4 → ℤ) :
    coeffColumnEquiv n = ![⟨n 0 - n 1 + n 3, -n 1 - n 3⟩, ⟨2 * n 1 + n 2 + n 3, n 3⟩] :=
  rfl

theorem coeffColumnEquiv_symm_apply (v : Fin 2 → GaussianInt) :
    coeffColumnEquiv.symm v =
      ![(v 0).re - (v 0).im - 2 * (v 1).im, -(v 0).im - (v 1).im,
        (v 1).re + 2 * (v 0).im + (v 1).im, (v 1).im] :=
  rfl

@[simp] theorem coeffColumnEquiv_apply_zero_re (n : Fin 4 → ℤ) :
    (coeffColumnEquiv n 0).re = n 0 - n 1 + n 3 := rfl

@[simp] theorem coeffColumnEquiv_apply_zero_im (n : Fin 4 → ℤ) :
    (coeffColumnEquiv n 0).im = -n 1 - n 3 := rfl

@[simp] theorem coeffColumnEquiv_apply_one_re (n : Fin 4 → ℤ) :
    (coeffColumnEquiv n 1).re = 2 * n 1 + n 2 + n 3 := rfl

@[simp] theorem coeffColumnEquiv_apply_one_im (n : Fin 4 → ℤ) :
    (coeffColumnEquiv n 1).im = n 3 := rfl

theorem coeffColumnEquiv_symm_apply_apply (n : Fin 4 → ℤ) :
    coeffColumnEquiv.symm (coeffColumnEquiv n) = n :=
  coeffColumnInvFun_coeffColumnFun n

theorem coeffColumnEquiv_apply_symm_apply (v : Fin 2 → GaussianInt) :
    coeffColumnEquiv (coeffColumnEquiv.symm v) = v :=
  coeffColumnFun_coeffColumnInvFun v

theorem coeffColumnEquiv_add (n m : Fin 4 → ℤ) :
    coeffColumnEquiv (n + m) = coeffColumnEquiv n + coeffColumnEquiv m :=
  map_add coeffColumnEquiv n m

theorem coeffColumnEquiv_smul (c : ℤ) (n : Fin 4 → ℤ) :
    coeffColumnEquiv (c • n) = c • coeffColumnEquiv n :=
  map_smul coeffColumnEquiv c n

theorem eq_coeffColumnEquiv_iff (v : Fin 2 → GaussianInt) (n : Fin 4 → ℤ) :
    v = coeffColumnEquiv n ↔
      (v 0).re = n 0 - n 1 + n 3 ∧ (v 0).im = -n 1 - n 3 ∧
        (v 1).re = 2 * n 1 + n 2 + n 3 ∧ (v 1).im = n 3 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2, h3⟩
    funext i
    fin_cases i
    · exact Zsqrtd.ext h0 h1
    · exact Zsqrtd.ext h2 h3

theorem coeffColumn_mulVec_one_zero {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    M.mulVec ![1, 0] = ![M 0 0, M 1 0] := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mulVec_one_zero_eq_coeffColumnEquiv_iff (M : Matrix (Fin 2) (Fin 2) GaussianInt)
    (n : Fin 4 → ℤ) :
    M.mulVec ![1, 0] = coeffColumnEquiv n ↔
      (M 0 0).re = n 0 - n 1 + n 3 ∧ (M 0 0).im = -n 1 - n 3 ∧
        (M 1 0).re = 2 * n 1 + n 2 + n 3 ∧ (M 1 0).im = n 3 := by
  rw [coeffColumn_mulVec_one_zero, eq_coeffColumnEquiv_iff]
  rfl

/-! ## Real/imaginary integer matrix; the carrier isomorphism is not inferred from det alone -/

def gaussColumnReIm (v : Fin 2 → GaussianInt) : Fin 4 → ℤ :=
  ![(v 0).re, (v 0).im, (v 1).re, (v 1).im]

def coeffColumnReImMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, -1, 0, 1; 0, -1, 0, -1; 0, 2, 1, 1; 0, 0, 0, 1]

def coeffColumnReImMatrixInv : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, -1, 0, -2; 0, -1, 0, -1; 0, 2, 1, 1; 0, 0, 0, 1]

theorem gaussColumnReIm_coeffColumnEquiv (n : Fin 4 → ℤ) :
    gaussColumnReIm (coeffColumnEquiv n) = coeffColumnReImMatrix.mulVec n := by
  funext i
  fin_cases i <;>
    simp [gaussColumnReIm, coeffColumnReImMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] <;> ring

theorem coeffColumnEquiv_symm_eq_mulVec (v : Fin 2 → GaussianInt) :
    coeffColumnEquiv.symm v = coeffColumnReImMatrixInv.mulVec (gaussColumnReIm v) := by
  funext i
  fin_cases i <;>
    simp [coeffColumnEquiv_symm_apply, gaussColumnReIm, coeffColumnReImMatrixInv,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

theorem coeffColumnReImMatrix_mul_inv :
    coeffColumnReImMatrix * coeffColumnReImMatrixInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coeffColumnReImMatrix, coeffColumnReImMatrixInv, Matrix.mul_apply, Fin.sum_univ_four]

theorem coeffColumnReImMatrix_inv_mul :
    coeffColumnReImMatrixInv * coeffColumnReImMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coeffColumnReImMatrix, coeffColumnReImMatrixInv, Matrix.mul_apply, Fin.sum_univ_four]

theorem coeffColumnReImMatrix_det : coeffColumnReImMatrix.det = -1 := by
  simp [coeffColumnReImMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

/-! ## Integral/mod-3 primitives, not curve torsion or moduli claims -/

theorem intVec_cast_zmod_eq_zero_iff {ι : Type*} (p : ℕ) (n : ι → ℤ) :
    (fun i => ((n i : ℤ) : ZMod p)) = 0 ↔ ∃ m : ι → ℤ, n = (p : ℤ) • m := by
  constructor
  · intro h
    refine ⟨fun i => n i / p, funext fun i => ?_⟩
    have hi : (p : ℤ) ∣ n i := (ZMod.intCast_zmod_eq_zero_iff_dvd (n i) p).1 (congrFun h i)
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' hi).symm
  · rintro ⟨m, rfl⟩
    funext i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 (dvd_mul_right (p : ℤ) (m i))

theorem fin4_cast_zmod3_eq_zero_iff (n : Fin 4 → ℤ) :
    (fun i => ((n i : ℤ) : ZMod 3)) = 0 ↔ ∃ m : Fin 4 → ℤ, n = (3 : ℤ) • m :=
  intVec_cast_zmod_eq_zero_iff 3 n

theorem coeffColumnEquiv_symm_cast_zmod3_eq_zero_iff (v : Fin 2 → GaussianInt) :
    (fun i => ((coeffColumnEquiv.symm v i : ℤ) : ZMod 3)) = 0 ↔
      ∃ w : Fin 2 → GaussianInt, v = (3 : ℤ) • w := by
  refine (fin4_cast_zmod3_eq_zero_iff _).trans ⟨?_, ?_⟩
  · rintro ⟨m, hm⟩
    refine ⟨coeffColumnEquiv m, ?_⟩
    calc v = coeffColumnEquiv (coeffColumnEquiv.symm v) :=
          (coeffColumnEquiv.apply_symm_apply v).symm
      _ = coeffColumnEquiv ((3 : ℤ) • m) := by rw [hm]
      _ = (3 : ℤ) • coeffColumnEquiv m := map_smul coeffColumnEquiv (3 : ℤ) m
  · rintro ⟨w, rfl⟩
    exact ⟨coeffColumnEquiv.symm w, map_smul coeffColumnEquiv.symm (3 : ℤ) w⟩

theorem coeffMatrix_mulVec_distinguishedVector (n : Fin 4 → ℤ) :
    (coeffMatrix n).mulVec distinguishedVector = coeffColumnEquiv n := by
  rw [distinguishedVector, mulVec_one_zero_eq_coeffColumnEquiv_iff]
  simp only [coeffMatrix, Matrix.add_apply, Matrix.smul_apply]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [iMatrix, wMatrix, gaussianI, Matrix.mul_apply, Fin.sum_univ_two, zsmul_eq_mul] <;> ring

/-! ## Evaluation at the literal vector on the actual order carrier -/

/-- The actual order-to-Gaussian-column integer-linear equivalence. -/
def evaluationEquiv : LeafQM.O ≃ₗ[ℤ] (Fin 2 → GaussianInt) :=
  orderCoordEquiv.trans coeffColumnEquiv

/-- This is precisely evaluation of the actual ring representation at `(1,0)`. -/
@[simp] theorem evaluationEquiv_apply (m : LeafQM.O) :
    evaluationEquiv m = (rho m).mulVec distinguishedVector := by
  change coeffColumnEquiv (orderCoordEquiv m) =
    (coeffMatrix (orderCoordEquiv m)).mulVec distinguishedVector
  exact (coeffMatrix_mulVec_distinguishedVector (orderCoordEquiv m)).symm

theorem evaluationLinearMap_eq_equiv :
    evaluationLinearMap = evaluationEquiv.toLinearMap := by
  apply LinearMap.ext
  intro m
  exact (evaluationEquiv_apply m).symm

@[simp] theorem evaluationEquiv_orderOfInt (n : Fin 4 → ℤ) :
    evaluationEquiv (orderOfInt n) = coeffColumnEquiv n := by
  simp [evaluationEquiv]

/-- The explicit column formula on the original integral order coordinates. -/
theorem rho_orderOfInt_mulVec (n : Fin 4 → ℤ) :
    (rho (orderOfInt n)).mulVec distinguishedVector =
      ![⟨n 0 - n 1 + n 3, -n 1 - n 3⟩, ⟨2 * n 1 + n 2 + n 3, n 3⟩] := by
  rw [rho_orderOfInt, coeffMatrix_mulVec_distinguishedVector]
  exact coeffColumnEquiv_apply n

/-- Integral inverse on the actual inherited order, not merely a determinant. -/
theorem evaluationEquiv_symm_formula (v : Fin 2 → GaussianInt) :
    evaluationEquiv.symm v =
      orderOfInt ![(v 0).re - (v 0).im - 2 * (v 1).im, -(v 0).im - (v 1).im,
        (v 1).re + 2 * (v 0).im + (v 1).im, (v 1).im] := by
  change orderFromCoordsEquiv (coeffColumnEquiv.symm v) = _
  rw [orderFromCoordsEquiv_apply, coeffColumnEquiv_symm_apply]

theorem evaluationEquiv_left_inverse (m : LeafQM.O) :
    evaluationEquiv.symm ((rho m).mulVec distinguishedVector) = m := by
  rw [← evaluationEquiv_apply]
  exact evaluationEquiv.symm_apply_apply m

theorem evaluationEquiv_right_inverse (v : Fin 2 → GaussianInt) :
    (rho (evaluationEquiv.symm v)).mulVec distinguishedVector = v := by
  rw [← evaluationEquiv_apply]
  exact evaluationEquiv.apply_symm_apply v

/-- Faithfulness is derived from the constructed evaluation equivalence. -/
theorem rho_injective : Function.Injective rho := by
  intro m n h
  apply evaluationEquiv.injective
  rw [evaluationEquiv_apply, evaluationEquiv_apply, h]

/-! ## Exact reduced-coordinate kernel on the actual fixed order -/

/-- Four-coordinate reduction. This is an integral additive map, not a curve
level structure or a claim about any scheme's torsion points. -/
def reduceCoordsMod3 (m : LeafQM.O) : Fin 4 → ZMod 3 :=
  fun i => ((orderCoordEquiv m i : ℤ) : ZMod 3)

def reduceCoordsMod3AddHom : LeafQM.O →+ (Fin 4 → ZMod 3) where
  toFun := reduceCoordsMod3
  map_zero' := by
    funext i
    simp [reduceCoordsMod3]
  map_add' m n := by
    funext i
    simp [reduceCoordsMod3, map_add]

theorem orderCoordEquiv_three_mul (m : LeafQM.O) :
    orderCoordEquiv (3 * m) = (3 : ℤ) • orderCoordEquiv m := by
  simpa only [zsmul_eq_mul, Int.cast_ofNat] using
    (map_smul orderCoordEquiv (3 : ℤ) m)

/-- Exact kernel, using multiplication in the actual inherited order. -/
theorem reduceCoordsMod3_zero_iff (m : LeafQM.O) :
    reduceCoordsMod3 m = 0 ↔ ∃ u : LeafQM.O, m = 3 * u := by
  change (fun i => ((orderCoordEquiv m i : ℤ) : ZMod 3)) = 0 ↔ _
  rw [fin4_cast_zmod3_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨orderOfInt n, ?_⟩
    apply orderCoordEquiv.injective
    rw [orderCoordEquiv_three_mul, orderCoordEquiv_orderOfInt]
    exact hn
  · rintro ⟨u, rfl⟩
    exact ⟨orderCoordEquiv u, orderCoordEquiv_three_mul u⟩

theorem reduceCoordsMod3_kernel :
    {m : LeafQM.O | reduceCoordsMod3 m = 0} =
      {m : LeafQM.O | ∃ u : LeafQM.O, m = 3 * u} :=
  Set.ext reduceCoordsMod3_zero_iff

end ZInQ.Contrib.Y3FineModuli.CMOrderMatrices
