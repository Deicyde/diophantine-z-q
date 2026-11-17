import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.SharpLevelFiveBound
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# A power basis for modular forms on `Γ₁(5)` from two weight-one forms

Let `A, B` be modular forms of weight one on `Γ₁(5)` whose `q`-expansions at `∞` satisfy
`a₀(A) = 0`, `a₁(A) = 1` and `a₀(B) = 1`. Then for every `n : ℕ` the products
`P_j = A^j B^(n-j)` (`0 ≤ j ≤ n`) form a basis of the weight-`n` forms: every `f` has unique
complex coordinates `c` with `f = Σ_j c_j A^j B^(n-j)` pointwise.

The first `n + 1` coefficients of `P_j` form a lower unitriangular matrix (`P_j = q^j (1 + …)`),
and the sharp level-five bound (`eq_zero_of_coeff_eq_zero`) makes the first `n + 1` coefficients
injective on weight-`n` forms. If `A`, `B` and `f` have rational `q`-expansions, the coordinates
are rational. Only the three stated leading coefficients of `A` and `B` are assumed.
-/

noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Matrix

namespace ZInQ.Contrib.HeckePrimeRationality.ThetaFivePowerBasis

set_option quotPrecheck false in
local notation "Γ₅" => (Gamma1 5).map (mapGL ℝ)

theorem oneMemG5 : (1 : ℝ) ∈ (Γ₅ : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
  TauCeti.one_mem_strictPeriods_Gamma1_map 5

variable (A B : ModularForm Γ₅ 1)

/-- The product `A^j B^(n-j)` as a form of weight `n`. -/
def P (n : ℕ) (j : Fin (n + 1)) : ModularForm Γ₅ (n : ℤ) :=
  ModularForm.mcast (by have := j.isLt; omega) ((A.pow j).mul (B.pow (n - j)))

theorem P_apply (n : ℕ) (j : Fin (n + 1)) (τ : ℍ) :
    P A B n j τ = A τ ^ (j : ℕ) * B τ ^ (n - (j : ℕ)) := by
  simp [P, ModularForm.mcast_apply]

theorem qExpansion_P (n : ℕ) (j : Fin (n + 1)) :
    qExpansion 1 (P A B n j) = (qExpansion 1 A) ^ (j : ℕ) * (qExpansion 1 B) ^ (n - (j : ℕ)) := by
  change qExpansion 1 ((A.pow j).mul (B.pow (n - j))) = _
  rw [ModularForm.qExpansion_mul one_pos oneMemG5, ModularForm.qExpansion_pow one_pos oneMemG5,
    ModularForm.qExpansion_pow one_pos oneMemG5]

section Leading

variable {A B}
variable (hA0 : PowerSeries.coeff 0 (qExpansion 1 A) = 0)
  (hA1 : PowerSeries.coeff 1 (qExpansion 1 A) = 1)
  (hB0 : PowerSeries.coeff 0 (qExpansion 1 B) = 1)
include hA0 hA1 hB0

/-- `P_j = q^j (1 + O(q))`: the coefficient of `q^m` is `0` for `m < j` and `1` for `m = j`. -/
theorem coeff_P (n : ℕ) (j : Fin (n + 1)) (m : ℕ) :
    PowerSeries.coeff m (qExpansion 1 (P A B n j)) =
      if m < (j : ℕ) then 0 else if m = (j : ℕ) then 1 else
        PowerSeries.coeff m (qExpansion 1 (P A B n j)) := by
  obtain ⟨a', ha'⟩ : (PowerSeries.X : PowerSeries ℂ) ∣ qExpansion 1 A :=
    PowerSeries.X_dvd_iff.mpr (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hA0)
  have ha'0 : PowerSeries.constantCoeff a' = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_succ_X_mul, ← ha']
    exact hA1
  have hb0 : PowerSeries.constantCoeff (qExpansion 1 B) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hB0
  have hq : qExpansion 1 (P A B n j) =
      PowerSeries.X ^ (j : ℕ) * (a' ^ (j : ℕ) * (qExpansion 1 B) ^ (n - (j : ℕ))) := by
    rw [qExpansion_P, ha', mul_pow, mul_assoc]
  split_ifs with h1 h2
  · rw [hq, PowerSeries.coeff_X_pow_mul', ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · rw [hq, PowerSeries.coeff_X_pow_mul', ite_eq_left_of_eq_true _ _ (eq_true (by omega)), h2, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, map_pow, ha'0, hb0,
      one_pow, one_pow, mul_one]
  · rfl

theorem coeff_P_of_lt (n : ℕ) (j : Fin (n + 1)) {m : ℕ} (hm : m < (j : ℕ)) :
    PowerSeries.coeff m (qExpansion 1 (P A B n j)) = 0 := by
  rw [coeff_P hA0 hA1 hB0, ite_eq_left_of_eq_true _ _ (eq_true hm)]

theorem coeff_P_self (n : ℕ) (j : Fin (n + 1)) :
    PowerSeries.coeff (j : ℕ) (qExpansion 1 (P A B n j)) = 1 := by
  rw [coeff_P hA0 hA1 hB0, ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl _)),
    ite_eq_left_of_eq_true _ _ (eq_true rfl)]

end Leading

/-- The coefficient matrix `M m j = a_m(P_j)`, `0 ≤ m, j ≤ n`. -/
def M (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun m j => PowerSeries.coeff (m : ℕ) (qExpansion 1 (P A B n j))

/-- The linear combination `Σ_j c_j P_j`. -/
def S (n : ℕ) (c : Fin (n + 1) → ℂ) : ModularForm Γ₅ (n : ℤ) := ∑ j, c j • P A B n j

/-- Evaluation at a point as an additive map. -/
def evalHom (k : ℤ) (τ : ℍ) : ModularForm Γ₅ k →+ ℂ :=
  AddMonoidHom.mk' (fun f => f τ) (fun _ _ => rfl)

theorem S_apply (n : ℕ) (c : Fin (n + 1) → ℂ) (τ : ℍ) :
    S A B n c τ = ∑ j, c j * A τ ^ (j : ℕ) * B τ ^ (n - (j : ℕ)) := by
  have h := map_sum (evalHom (n : ℤ) τ) (fun j => c j • P A B n j) Finset.univ
  change evalHom (n : ℤ) τ (S A B n c) = _
  rw [S, h]
  refine Finset.sum_congr rfl fun j _ => ?_
  change c j • P A B n j τ = _
  rw [P_apply, smul_eq_mul, mul_assoc]

theorem coeff_S (n : ℕ) (c : Fin (n + 1) → ℂ) (m : ℕ) :
    PowerSeries.coeff m (qExpansion 1 (S A B n c)) =
      ∑ j, c j * PowerSeries.coeff m (qExpansion 1 (P A B n j)) := by
  have h := map_sum (ModularForm.qExpansionAddHom one_pos oneMemG5 (n : ℤ))
    (fun j => c j • P A B n j) Finset.univ
  rw [S]
  rw [ModularForm.qExpansionAddHom_apply] at h
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ModularForm.qExpansionAddHom_apply,
    show ⇑(c j • P A B n j) = c j • ⇑(P A B n j) from rfl,
    ModularForm.qExpansion_smul one_pos oneMemG5, PowerSeries.coeff_smul, smul_eq_mul]

theorem coeff_S_eq_mulVec (n : ℕ) (c : Fin (n + 1) → ℂ) (m : Fin (n + 1)) :
    PowerSeries.coeff (m : ℕ) (qExpansion 1 (S A B n c)) = (M A B n *ᵥ c) m := by
  rw [coeff_S, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [M, mul_comm]

section Basis

variable {A B}
variable (hA0 : PowerSeries.coeff 0 (qExpansion 1 A) = 0)
  (hA1 : PowerSeries.coeff 1 (qExpansion 1 A) = 1)
  (hB0 : PowerSeries.coeff 0 (qExpansion 1 B) = 1)
include hA0 hA1 hB0

theorem M_isLowerTriangular (n : ℕ) : (M A B n).IsLowerTriangular := by
  intro i j hij
  exact coeff_P_of_lt hA0 hA1 hB0 n j (by simpa using hij)

theorem M_det (n : ℕ) : (M A B n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (M_isLowerTriangular hA0 hA1 hB0 n)]
  exact Finset.prod_eq_one fun j _ => coeff_P_self hA0 hA1 hB0 n j

theorem M_isUnit (n : ℕ) : IsUnit (M A B n) := by
  rw [Matrix.isUnit_iff_isUnit_det, M_det hA0 hA1 hB0]
  exact isUnit_one

omit hA0 hA1 hB0 in
/-- Coordinates satisfying the pointwise identity solve the coefficient system. -/
theorem mulVec_eq_of_apply {n : ℕ} (f : ModularForm Γ₅ (n : ℤ)) (c : Fin (n + 1) → ℂ)
    (hc : ∀ τ : ℍ, f τ = ∑ j, c j * A τ ^ (j : ℕ) * B τ ^ (n - (j : ℕ))) :
    M A B n *ᵥ c = fun m : Fin (n + 1) => PowerSeries.coeff (m : ℕ) (qExpansion 1 f) := by
  have hf : f = S A B n c := ModularForm.ext fun τ => by rw [hc, S_apply]
  funext m
  rw [hf, coeff_S_eq_mulVec]

/-- **Power basis.** Every weight-`n` form on `Γ₁(5)` has unique complex coordinates in the
products `A^j B^(n-j)`. -/
theorem existsUnique_coords (n : ℕ) (f : ModularForm Γ₅ (n : ℤ)) :
    ∃! c : Fin (n + 1) → ℂ, ∀ τ : ℍ,
      f τ = ∑ j, c j * A τ ^ (j : ℕ) * B τ ^ (n - (j : ℕ)) := by
  have hU := M_isUnit hA0 hA1 hB0 n
  obtain ⟨c, hcM⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hU
    (fun m : Fin (n + 1) => PowerSeries.coeff (m : ℕ) (qExpansion 1 f))
  refine ⟨c, ?_, ?_⟩
  · have hzero : f - S A B n c = 0 := by
      refine CoeffRational.SharpLevelFiveBound.eq_zero_of_coeff_eq_zero (n : ℤ)
        (by positivity) _ fun m hm => ?_
      have hm' : m < n + 1 := by simp at hm; omega
      rw [show ⇑(f - S A B n c) = ⇑f - ⇑(S A B n c) from rfl,
        ModularForm.qExpansion_sub one_pos oneMemG5, map_sub]
      have := coeff_S_eq_mulVec A B n c ⟨m, hm'⟩
      rw [hcM] at this
      simp only at this
      rw [← this, sub_self]
    have hf : f = S A B n c := sub_eq_zero.mp hzero
    intro τ
    rw [hf, S_apply]
  · intro c' hc'
    apply Matrix.mulVec_injective_iff_isUnit.mpr hU
    rw [mulVec_eq_of_apply f c' hc', hcM]

/-- Rationality of the coordinates when `A`, `B` and `f` have rational `q`-expansions. -/
theorem coords_rat (hAq : ∀ m : ℕ, ∃ q : ℚ, PowerSeries.coeff m (qExpansion 1 A) = q)
    (hBq : ∀ m : ℕ, ∃ q : ℚ, PowerSeries.coeff m (qExpansion 1 B) = q)
    {n : ℕ} (f : ModularForm Γ₅ (n : ℤ))
    (hfq : ∀ m : ℕ, ∃ q : ℚ, PowerSeries.coeff m (qExpansion 1 f) = q)
    (c : Fin (n + 1) → ℂ) (hc : ∀ τ : ℍ, f τ = ∑ j, c j * A τ ^ (j : ℕ) * B τ ^ (n - (j : ℕ))) :
    ∀ j, ∃ q : ℚ, c j = q := by
  let φ : ℚ →+* ℂ := Rat.castHom ℂ
  let aQ : PowerSeries ℚ := PowerSeries.mk fun m => (hAq m).choose
  let bQ : PowerSeries ℚ := PowerSeries.mk fun m => (hBq m).choose
  have ha : qExpansion 1 A = PowerSeries.map φ aQ := by
    ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact (hAq m).choose_spec
  have hb : qExpansion 1 B = PowerSeries.map φ bQ := by
    ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact (hBq m).choose_spec
  let MQ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
    fun m j => PowerSeries.coeff (m : ℕ) (aQ ^ (j : ℕ) * bQ ^ (n - (j : ℕ)))
  have hMmap : (M A B n) = MQ.map φ := by
    ext m j
    simp only [M, MQ]
    rw [qExpansion_P, ha, hb, ← map_pow, ← map_pow, ← map_mul, PowerSeries.coeff_map]
    rfl
  have hinj : Function.Injective φ := φ.injective
  have hMQlow : MQ.IsLowerTriangular := by
    intro i j hij
    apply hinj
    rw [map_zero]
    have := M_isLowerTriangular hA0 hA1 hB0 n hij
    rw [hMmap] at this
    simpa using this
  have hMQdiag : ∀ j, MQ j j = 1 := by
    intro j
    apply hinj
    rw [map_one]
    have := coeff_P_self hA0 hA1 hB0 n j
    have h2 : (M A B n) j j = 1 := this
    rw [hMmap] at h2
    simpa using h2
  have hdetQ : MQ.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ hMQlow]
    exact Finset.prod_eq_one fun j _ => hMQdiag j
  have hUQ : IsUnit MQ := by
    rw [Matrix.isUnit_iff_isUnit_det, hdetQ]; exact isUnit_one
  obtain ⟨cQ, hcQ⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hUQ
    (fun m : Fin (n + 1) => (hfq m).choose)
  have hcast : M A B n *ᵥ (φ ∘ cQ) = M A B n *ᵥ c := by
    rw [mulVec_eq_of_apply f c hc]
    funext m
    rw [hMmap, ← RingHom.map_mulVec, hcQ]
    exact ((hfq m).choose_spec).symm
  have hc' : φ ∘ cQ = c := Matrix.mulVec_injective_iff_isUnit.mpr (M_isUnit hA0 hA1 hB0 n) hcast
  intro j
  exact ⟨cQ j, by rw [← hc']; rfl⟩

end Basis

end ZInQ.Contrib.HeckePrimeRationality.ThetaFivePowerBasis
