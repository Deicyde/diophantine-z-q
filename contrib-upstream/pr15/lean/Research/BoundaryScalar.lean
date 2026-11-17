import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.FieldSimp

/-!
# Boundary scalars from common normal forms

This independent research module proves matrix identities over a field. The
index type is arbitrary finite, with two distinct distinguished indices `p,q`.
All remaining indices represent the retained common strict block.

The input `D * B = T * N` is a normal-form presentation, with source basis `B`
and common target basis `T`. The actual cycle is `B *ᵥ e_p`; functionals are
closed for the actual differential. The conclusions concern every entry of
their outer products with the cycles, in the classical adjugate convention.
No determinant-coordinate ratio is an input.

The construction of these basis matrices from `[D0 | AF]`, `[D0 | AS]`, actual
cycles `(hF,v)`, `(hS,Jv)`, and a complement `x` is not formalized here. In that
ordinary algebraic bridge, `B_F=[I,zF,(0,x)]`, `B_S=[I,zS,(0,Jx)]`,
`T=[D0,AF*x,AS*Jx]`, `det B_F=eta`, and `det B_S=delta*eta`.
The theorem below accepts the normal-form equations and these determinant
identities as explicit hypotheses. It does not construct arithmetic complexes,
duality functionals, integral comparison maps, or a determinant functor.
-/

namespace Research.BoundaryScalar

open Matrix

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The coordinate vector at a distinguished index. -/
def axis (p : ι) : ι → K := Pi.single p 1

/-- Identity on the strict coordinates and the final complement, zero at the
actual-cycle coordinate. This is `diag(I_m, [[0,0],[0,1]])`. -/
def singularNormal (p : ι) : Matrix ι ι K :=
  diagonal fun i => if i = p then 0 else 1

/-- The elementary target-basis exchange, defined without an inverse API. -/
def exchange (p q : ι) : Matrix ι ι K :=
  (1 : Matrix ι ι K).submatrix (Equiv.swap p q) id

/-- The finite normal form `diag(I_m, [[0,1],[0,0]])`. -/
def finiteNormal (p q : ι) : Matrix ι ι K :=
  exchange p q * singularNormal p

theorem exchange_mul (p q : ι) (A : Matrix ι ι K) :
    exchange p q * A = A.submatrix (Equiv.swap p q) id := by
  simpa [exchange] using
    (Matrix.one_submatrix_mul (Equiv.swap p q) (Equiv.refl ι) A)

theorem exchange_self (p q : ι) :
    exchange (K := K) p q * exchange p q = 1 := by
  rw [exchange_mul]
  ext i j
  change (1 : Matrix ι ι K) ((Equiv.swap p q) ((Equiv.swap p q) i)) j =
    (1 : Matrix ι ι K) i j
  rw [Equiv.swap_apply_self]

theorem vecMul_exchange (p q : ι) (l : ι → K) :
    l ᵥ* exchange p q = l ∘ Equiv.swap p q := by
  simp [exchange, Matrix.submatrix_vecMul_equiv, Equiv.symm_swap,
    Matrix.vecMul_one]

theorem axis_exchange (p q : ι) :
    axis (K := K) p ᵥ* exchange p q = axis q := by
  rw [vecMul_exchange]
  ext i
  have hs : (Equiv.swap p q) i = p ↔ i = q := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  change (Pi.single p (1 : K) : ι → K) ((Equiv.swap p q) i) =
    (Pi.single q (1 : K) : ι → K) i
  simp only [Pi.single_apply]
  simp only [hs]

theorem det_exchange (p q : ι) (hpq : p ≠ q) :
    (exchange (K := K) p q).det = -1 := by
  simp [exchange, Matrix.det_permute, Equiv.Perm.sign_swap hpq]

theorem adjugate_exchange (p q : ι) (hpq : p ≠ q) :
    (exchange (K := K) p q).adjugate = -exchange p q := by
  have h := congrArg (fun A : Matrix ι ι K => A * exchange p q)
    (Matrix.adjugate_mul (exchange (K := K) p q))
  simpa [Matrix.mul_assoc, exchange_self, det_exchange p q hpq] using h

theorem adjugate_singularNormal (p : ι) :
    (singularNormal (K := K) p).adjugate = vecMulVec (axis p) (axis p) := by
  have hprod (i : ι) :
      (∏ j ∈ Finset.univ.erase i, (if j = p then (0 : K) else 1)) =
        if i = p then 1 else 0 := by
    by_cases hip : i = p
    · subst i
      simp only [ite_true]
      apply Finset.prod_eq_one
      intro j hj
      simp [Finset.ne_of_mem_erase hj]
    · simp only [hip, ite_false]
      exact Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨Ne.symm hip, Finset.mem_univ p⟩) (by simp)
  rw [singularNormal, Matrix.adjugate_diagonal]
  ext i j
  simp only [hprod, Matrix.diagonal_apply, Matrix.vecMulVec_apply, axis,
    Pi.single_apply]
  split_ifs <;> simp_all

theorem adjugate_finiteNormal (p q : ι) (hpq : p ≠ q) :
    (finiteNormal (K := K) p q).adjugate =
      -vecMulVec (axis p) (axis q) := by
  rw [finiteNormal, Matrix.adjugate_mul_distrib, adjugate_singularNormal,
    adjugate_exchange p q hpq, Matrix.mul_neg, Matrix.vecMulVec_mul, axis_exchange]

/-- A closed functional in the singular normal form has only its `p` entry. -/
theorem singular_closed_row (p : ι) (l : ι → K)
    (hl : l ᵥ* singularNormal p = 0) :
    l = l p • axis p := by
  ext i
  by_cases hip : i = p
  · subst i
    simp [axis]
  · have hi := congrFun hl i
    simpa [singularNormal, Matrix.vecMul_diagonal, hip, axis,
      Pi.single_apply, Ne.symm hip] using hi

/-- A closed functional in the finite normal form has only its `q` entry. -/
theorem finite_closed_row (p q : ι) (_hpq : p ≠ q) (l : ι → K)
    (hl : l ᵥ* finiteNormal p q = 0) :
    l = l q • axis q := by
  have hsing : (l ᵥ* exchange p q) ᵥ* singularNormal p = 0 := by
    simpa [finiteNormal, Matrix.vecMul_vecMul] using hl
  have hrow := singular_closed_row p (l ᵥ* exchange p q) hsing
  have h := congrArg (fun v : ι → K => v ᵥ* exchange p q) hrow
  rw [Matrix.vecMul_vecMul, exchange_self, Matrix.vecMul_one,
    Matrix.smul_vecMul, axis_exchange, vecMul_exchange] at h
  simpa using h

/-- Transport a proved canonical class-functional tensor identity. Only the
target determinant is divided out; strict factors remain in both determinants. -/
theorem tensor_of_normal_form
    (D B T N : Matrix ι ι K) (z l z' l' : ι → K) (c : K)
    (hDB : D * B = T * N) (hz : z = B *ᵥ z') (hl : l ᵥ* T = l')
    (hcanonical : vecMulVec z' l' = c • N.adjugate) (hT : T.det ≠ 0) :
    vecMulVec z l = (c * B.det / T.det) • D.adjugate := by
  have hAdj : B.adjugate * D.adjugate = N.adjugate * T.adjugate := by
    simpa only [Matrix.adjugate_mul_distrib] using congrArg Matrix.adjugate hDB
  have hscale : T.det • (B * N.adjugate) = B.det • (D.adjugate * T) := by
    have h := congrArg (fun A : Matrix ι ι K => B * A * T) hAdj
    calc
      T.det • (B * N.adjugate) = B * (N.adjugate * (T.adjugate * T)) := by
        rw [Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul]
      _ = B * (B.adjugate * D.adjugate) * T := by rw [hAdj]; simp [Matrix.mul_assoc]
      _ = B.det • (D.adjugate * T) := by
        rw [← Matrix.mul_assoc B, Matrix.mul_adjugate, Matrix.smul_mul,
          Matrix.one_mul, Matrix.smul_mul]
  apply (Matrix.isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero hT).left).right
  change vecMulVec z l * T = ((c * B.det / T.det) • D.adjugate) * T
  rw [Matrix.vecMulVec_mul, hl, hz, ← Matrix.mul_vecMulVec, hcanonical,
    Matrix.mul_smul, Matrix.smul_mul]
  have hscaled := congrArg (fun A : Matrix ι ι K => (c / T.det) • A) hscale
  simpa [smul_smul, div_eq_mul_inv, hT, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- The finite tensor coordinate follows from the actual closed functional and
the finite normal form, rather than from a supplied coordinate equality. -/
theorem finite_tensor
    (p q : ι) (hpq : p ≠ q) (D B T : Matrix ι ι K) (z l : ι → K)
    (hDB : D * B = T * finiteNormal p q) (hz : z = B *ᵥ axis p)
    (hclosed : l ᵥ* D = 0) (hT : T.det ≠ 0) :
    vecMulVec z l =
      (-(l ᵥ* T) q * B.det / T.det) • D.adjugate := by
  have hclosed' : (l ᵥ* T) ᵥ* finiteNormal p q = 0 := by
    rw [Matrix.vecMul_vecMul, ← hDB, ← Matrix.vecMul_vecMul, hclosed]
    simp
  apply tensor_of_normal_form D B T (finiteNormal p q) z l
    (axis p) (l ᵥ* T) (-(l ᵥ* T) q) hDB hz rfl _ hT
  rw [finite_closed_row p q hpq _ hclosed', Matrix.vecMulVec_smul,
    adjugate_finiteNormal p q hpq]
  simp [axis]

/-- The singular tensor coordinate in the same target basis. -/
theorem singular_tensor
    (p : ι) (D B T : Matrix ι ι K) (z l : ι → K)
    (hDB : D * B = T * singularNormal p) (hz : z = B *ᵥ axis p)
    (hclosed : l ᵥ* D = 0) (hT : T.det ≠ 0) :
    vecMulVec z l =
      ((l ᵥ* T) p * B.det / T.det) • D.adjugate := by
  have hclosed' : (l ᵥ* T) ᵥ* singularNormal p = 0 := by
    rw [Matrix.vecMul_vecMul, ← hDB, ← Matrix.vecMul_vecMul, hclosed]
    simp
  apply tensor_of_normal_form D B T (singularNormal p) z l
    (axis p) (l ᵥ* T) ((l ᵥ* T) p) hDB hz rfl _ hT
  rw [singular_closed_row p _ hclosed', Matrix.vecMulVec_smul,
    adjugate_singularNormal]
  simp [axis]

/-- Cancellation of the retained source and target volumes. The `delta` factor
is the separately specified determinant-line comparison scalar. -/
theorem scalar_comparison (delta eta theta qF qS : K)
    (hdelta : delta ≠ 0) (heta : eta ≠ 0) (htheta : theta ≠ 0) (hqS : qS ≠ 0) :
    delta * (-qF * eta / theta) / (qS * (delta * eta) / theta) = -qF / qS := by
  field_simp

/-- An invertible target basis cannot annihilate a nonzero row. -/
theorem row_eq_zero_of_target (T : Matrix ι ι K) (l : ι → K)
    (hT : T.det ≠ 0) (hl : l ᵥ* T = 0) : l = 0 := by
  have h := congrArg (fun v : ι → K => v ᵥ* T.adjugate) hl
  rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul,
    Matrix.vecMul_one] at h
  ext i
  have hi := congrFun h i
  simpa [hT] using hi

/-- The actual finite cross-boundary evaluation is nonzero. -/
theorem finite_cross_ne_zero
    (p q : ι) (hpq : p ≠ q) (D B T : Matrix ι ι K) (l : ι → K)
    (hDB : D * B = T * finiteNormal p q)
    (hclosed : l ᵥ* D = 0) (hT : T.det ≠ 0) (hl : l ≠ 0) :
    (l ᵥ* T) q ≠ 0 := by
  intro hq
  have hclosed' : (l ᵥ* T) ᵥ* finiteNormal p q = 0 := by
    rw [Matrix.vecMul_vecMul, ← hDB, ← Matrix.vecMul_vecMul, hclosed]
    simp
  have hrow : l ᵥ* T = 0 := by
    calc
      l ᵥ* T = (l ᵥ* T) q • axis q := finite_closed_row p q hpq _ hclosed'
      _ = 0 := by rw [hq, zero_smul]
  exact hl (row_eq_zero_of_target T l hT hrow)

/-- The actual singular cross-boundary evaluation is nonzero. -/
theorem singular_cross_ne_zero
    (p : ι) (D B T : Matrix ι ι K) (l : ι → K)
    (hDB : D * B = T * singularNormal p)
    (hclosed : l ᵥ* D = 0) (hT : T.det ≠ 0) (hl : l ≠ 0) :
    (l ᵥ* T) p ≠ 0 := by
  intro hp
  have hclosed' : (l ᵥ* T) ᵥ* singularNormal p = 0 := by
    rw [Matrix.vecMul_vecMul, ← hDB, ← Matrix.vecMul_vecMul, hclosed]
    simp
  have hrow : l ᵥ* T = 0 := by
    calc
      l ᵥ* T = (l ᵥ* T) p • axis p := singular_closed_row p _ hclosed'
      _ = 0 := by rw [hp, zero_smul]
  exact hl (row_eq_zero_of_target T l hT hrow)

/-- A source basis sends the selected cycle axis to a nonzero actual cycle. -/
theorem basis_cycle_ne_zero (p : ι) (B : Matrix ι ι K) (z : ι → K)
    (hz : z = B *ᵥ axis p) (hB : B.det ≠ 0) : z ≠ 0 := by
  intro hz0
  have h : B.adjugate *ᵥ z = B.det • axis p := by
    rw [hz, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hp := congrFun h p
  exact hB (by simpa [hz0, axis] using hp.symm)

/-- A nonzero class-functional tensor determines its adjugate scalar uniquely. -/
theorem tensor_coordinate_unique (D : Matrix ι ι K) (z l : ι → K) (u v : K)
    (hnonzero : vecMulVec z l ≠ 0)
    (hu : vecMulVec z l = u • D.adjugate)
    (hv : vecMulVec z l = v • D.adjugate) : u = v := by
  have hAdj : D.adjugate ≠ 0 := by
    intro hz
    apply hnonzero
    simpa [hz] using hu
  exact smul_left_injective K hAdj (hu.symm.trans hv)

/-- Characterization of the unique finite adjugate coordinate. In particular,
this can be applied to a coordinate previously defined by the tensor identity. -/
theorem finite_coordinate_iff
    (p q : ι) (hpq : p ≠ q) (D B T : Matrix ι ι K) (z l : ι → K) (u : K)
    (hDB : D * B = T * finiteNormal p q) (hz : z = B *ᵥ axis p)
    (hclosed : l ᵥ* D = 0) (hT : T.det ≠ 0) (hB : B.det ≠ 0) (hl : l ≠ 0) :
    vecMulVec z l = u • D.adjugate ↔ u = -(l ᵥ* T) q * B.det / T.det := by
  have hformula := finite_tensor p q hpq D B T z l hDB hz hclosed hT
  constructor
  · intro hu
    exact tensor_coordinate_unique D z l u _
      (Matrix.vecMulVec_ne_zero (basis_cycle_ne_zero p B z hz hB) hl) hu hformula
  · intro hu
    simpa [hu] using hformula

/-- Characterization of the unique singular adjugate coordinate. -/
theorem singular_coordinate_iff
    (p : ι) (D B T : Matrix ι ι K) (z l : ι → K) (u : K)
    (hDB : D * B = T * singularNormal p) (hz : z = B *ᵥ axis p)
    (hclosed : l ᵥ* D = 0) (hT : T.det ≠ 0) (hB : B.det ≠ 0) (hl : l ≠ 0) :
    vecMulVec z l = u • D.adjugate ↔ u = (l ᵥ* T) p * B.det / T.det := by
  have hformula := singular_tensor p D B T z l hDB hz hclosed hT
  constructor
  · intro hu
    exact tensor_coordinate_unique D z l u _
      (Matrix.vecMulVec_ne_zero (basis_cycle_ne_zero p B z hz hB) hl) hu hformula
  · intro hu
    simpa [hu] using hformula

/-- The general boundary-scalar formula, after the explicitly supplied
common-strict-to-normal-form bridge. Both full tensors, both nonzero actual
cross evaluations, both nonzero coordinates, and their comparison are proved.
`delta` is the specified determinant-line comparison, not a constructed functor. -/
theorem boundary_scalar_formula
    (p q : ι) (hpq : p ≠ q)
    (DF DS BF BS T : Matrix ι ι K) (zF zS lF lS : ι → K)
    (delta eta : K) (hdelta : delta ≠ 0) (heta : eta ≠ 0) (hT : T.det ≠ 0)
    (hDF : DF * BF = T * finiteNormal p q)
    (hDS : DS * BS = T * singularNormal p)
    (hzF : zF = BF *ᵥ axis p) (hzS : zS = BS *ᵥ axis p)
    (hlF : lF ᵥ* DF = 0) (hlS : lS ᵥ* DS = 0)
    (hlFne : lF ≠ 0) (hlSne : lS ≠ 0)
    (hBF : BF.det = eta) (hBS : BS.det = delta * eta) :
    let qF := (lF ᵥ* T) q
    let qS := (lS ᵥ* T) p
    let uF := -eta * qF / T.det
    let uS := delta * eta * qS / T.det
    vecMulVec zF lF = uF • DF.adjugate ∧
      vecMulVec zS lS = uS • DS.adjugate ∧
      qF ≠ 0 ∧ qS ≠ 0 ∧ uF ≠ 0 ∧ uS ≠ 0 ∧
      delta * uF / uS = -qF / qS := by
  dsimp
  have hqF := finite_cross_ne_zero p q hpq DF BF T lF hDF hlF hT hlFne
  have hqS := singular_cross_ne_zero p DS BS T lS hDS hlS hT hlSne
  refine ⟨?_, ?_, hqF, hqS, ?_, ?_, ?_⟩
  · simpa [hBF, mul_comm] using finite_tensor p q hpq DF BF T zF lF hDF hzF hlF hT
  · simpa [hBS, mul_assoc, mul_comm, mul_left_comm] using
      singular_tensor p DS BS T zS lS hDS hzS hlS hT
  · exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr heta) hqF) hT
  · exact div_ne_zero (mul_ne_zero (mul_ne_zero hdelta heta) hqS) hT
  · simpa [mul_assoc, mul_comm, mul_left_comm] using
      scalar_comparison delta eta T.det _ _ hdelta heta hT hqS

/-- Equal nonzero cross-boundary evaluations give the orientation unit `-1`.
No integral-unit hypothesis on the common cross evaluation is imposed. -/
theorem normalized_scalar_comparison (delta eta theta q : K)
    (hdelta : delta ≠ 0) (heta : eta ≠ 0) (htheta : theta ≠ 0) (hq : q ≠ 0) :
    delta * (-q * eta / theta) / (q * (delta * eta) / theta) = -1 := by
  rw [scalar_comparison delta eta theta q q hdelta heta htheta hq]
  simp [hq]

/-- An explicit unit over the coefficient ring lifts the comparison scalar.
This conclusion is stronger than the vacuous field statement that a nonzero
ratio is a `K`-unit. The common cross evaluation may be a nonunit over `R`. -/
theorem scalar_comparison_of_unit {R : Type*} [CommRing R]
    (f : R →+* K) (e : Rˣ) (delta eta theta qF qS : K)
    (hdelta : delta ≠ 0) (heta : eta ≠ 0) (htheta : theta ≠ 0) (hqS : qS ≠ 0)
    (hunit : qF = f (e : R) * qS) :
    delta * (-qF * eta / theta) / (qS * (delta * eta) / theta) =
      f ((-e : Rˣ) : R) := by
  rw [scalar_comparison delta eta theta qF qS hdelta heta htheta hqS, hunit]
  simp [div_eq_mul_inv, hqS]

end Research.BoundaryScalar
