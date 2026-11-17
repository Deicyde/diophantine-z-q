import ZInQKernel.Contrib.OneProof.RC.Symbols.Core
import Mathlib
namespace ZInQ.Manuscript.RC.Symbols
open Finset Matrix

/-- Physical coordinates of the auxiliary groups: group `i`, position `k` (tex 10661–10664). -/
abbrev Phys (b : ℕ) := Fin b × Fin 3
/-- `e_i = (1,1,1)` on group `i`. -/
def grp {b : ℕ} (i : Fin b) : Phys b → ZMod 2 := fun p => if p.1 = i then 1 else 0
/-- `u_i = (1,1,0)` on group `i`. -/
def uvec {b : ℕ} (i : Fin b) : Phys b → ZMod 2 := fun p => if p.1 = i ∧ p.2 ≠ 2 then 1 else 0
/-- `v_i = (0,1,1)` on group `i`. -/
def vvec {b : ℕ} (i : Fin b) : Phys b → ZMod 2 := fun p => if p.1 = i ∧ p.2 ≠ 0 then 1 else 0

/-- The in-group vector `u = (1,1,0)`. -/
def uu3 : Fin 3 → ZMod 2 := ![1, 1, 0]
/-- The in-group vector `v = (0,1,1)`. -/
def vv3 : Fin 3 → ZMod 2 := ![0, 1, 1]

/-- The prescribed symmetric matrix: bilinear matrix `I_b` on the `e_i` and `H(T,B)` on the
`u_i, v_i` (tex 10664–10669). Concretely `Q = Σ e_i e_iᵀ + Σ T_ij (v_i u_jᵀ + u_j v_iᵀ) +
Σ B_ij u_i u_jᵀ`, using that the dot-dual basis of `(e,u,v)` in one group is `(e,v,u)`. -/
noncomputable def Qmat {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) :
    Matrix (Phys b) (Phys b) (ZMod 2) :=
  fun p q => (if p.1 = q.1 then 1 else 0) + T p.1 q.1 * vv3 p.2 * uu3 q.2 +
    T q.1 p.1 * uu3 p.2 * vv3 q.2 + B p.1 q.1 * uu3 p.2 * uu3 q.2

/-! ### Group coordinates -/

/-- Pairing with `e_i`. -/
def gA {b : ℕ} (z : Phys b → ZMod 2) (i : Fin b) : ZMod 2 := z (i, 0) + z (i, 1) + z (i, 2)
/-- Pairing with `u_i` (the `v_i`-coordinate). -/
def gB {b : ℕ} (z : Phys b → ZMod 2) (i : Fin b) : ZMod 2 := z (i, 0) + z (i, 1)
/-- Pairing with `v_i` (the `u_i`-coordinate). -/
def gC {b : ℕ} (z : Phys b → ZMod 2) (i : Fin b) : ZMod 2 := z (i, 1) + z (i, 2)

lemma dot_eq_sum {b : ℕ} (x y : Phys b → ZMod 2) :
    x ⬝ᵥ y = ∑ j, (x (j, 0) * y (j, 0) + x (j, 1) * y (j, 1) + x (j, 2) * y (j, 2)) := by
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three]

lemma grp_dot {b : ℕ} (i : Fin b) (z : Phys b → ZMod 2) : grp i ⬝ᵥ z = gA z i := by
  rw [dot_eq_sum, Finset.sum_eq_single i]
  · simp [grp, gA]
  · intro j _ hj; simp [grp, hj]
  · simp

lemma uvec_dot {b : ℕ} (i : Fin b) (z : Phys b → ZMod 2) : uvec i ⬝ᵥ z = gB z i := by
  rw [dot_eq_sum, Finset.sum_eq_single i]
  · simp [uvec, gB]
  · intro j _ hj; simp [uvec, hj]
  · simp

lemma vvec_dot {b : ℕ} (i : Fin b) (z : Phys b → ZMod 2) : vvec i ⬝ᵥ z = gC z i := by
  rw [dot_eq_sum, Finset.sum_eq_single i]
  · simp [vvec, gC]
  · intro j _ hj; simp [vvec, hj]
  · simp

/-- The action of `Qmat` in group coordinates. -/
lemma Qmat_mulVec_apply {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) (z : Phys b → ZMod 2)
    (i : Fin b) (k : Fin 3) :
    (Qmat T B *ᵥ z) (i, k) = gA z i + vv3 k * (T *ᵥ gB z) i +
      uu3 k * ((Tᵀ *ᵥ gC z) i + (B *ᵥ gB z) i) := by
  have : (Qmat T B *ᵥ z) (i, k) = ∑ j, ((if i = j then gA z j else 0) +
      vv3 k * (T i j * gB z j) + uu3 k * (T j i * gC z j) + uu3 k * (B i j * gB z j)) := by
    simp only [mulVec, dotProduct, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.sum_univ_three, Qmat, gA, gB, gC, uu3, vv3]
    split_ifs <;> simp <;> ring
  rw [this]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, mulVec, dotProduct, transpose_apply]
  ring

lemma gA_grp {b : ℕ} (j m : Fin b) : gA (grp j) m = if m = j then 1 else 0 := by
  by_cases h : m = j <;> simp [gA, grp, h] <;> decide
lemma gB_grp {b : ℕ} (j m : Fin b) : gB (grp j) m = 0 := by
  by_cases h : m = j <;> simp [gB, grp, h] <;> decide
lemma gC_grp {b : ℕ} (j m : Fin b) : gC (grp j) m = 0 := by
  by_cases h : m = j <;> simp [gC, grp, h] <;> decide
lemma gA_uvec {b : ℕ} (j m : Fin b) : gA (uvec j) m = 0 := by
  by_cases h : m = j <;> simp [gA, uvec, h] <;> decide
lemma gB_uvec {b : ℕ} (j m : Fin b) : gB (uvec j) m = 0 := by
  by_cases h : m = j <;> simp [gB, uvec, h] <;> decide
lemma gC_uvec {b : ℕ} (j m : Fin b) : gC (uvec j) m = if m = j then 1 else 0 := by
  by_cases h : m = j <;> simp [gC, uvec, h]
lemma gA_vvec {b : ℕ} (j m : Fin b) : gA (vvec j) m = 0 := by
  by_cases h : m = j <;> simp [gA, vvec, h] <;> decide
lemma gB_vvec {b : ℕ} (j m : Fin b) : gB (vvec j) m = if m = j then 1 else 0 := by
  by_cases h : m = j <;> simp [gB, vvec, h]
lemma gC_vvec {b : ℕ} (j m : Fin b) : gC (vvec j) m = 0 := by
  by_cases h : m = j <;> simp [gC, vvec, h] <;> decide

lemma gA_Qmat {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) (z : Phys b → ZMod 2) (i : Fin b) :
    gA (Qmat T B *ᵥ z) i = gA z i := by
  have h : gA (Qmat T B *ᵥ z) i = (Qmat T B *ᵥ z) (i, 0) + (Qmat T B *ᵥ z) (i, 1) +
    (Qmat T B *ᵥ z) (i, 2) := rfl
  rw [h, Qmat_mulVec_apply, Qmat_mulVec_apply, Qmat_mulVec_apply]
  simp only [uu3, vv3]
  generalize gA z i = x; generalize (T *ᵥ gB z) i = y
  generalize (Tᵀ *ᵥ gC z) i + (B *ᵥ gB z) i = w
  revert x y w; decide

lemma gB_Qmat {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) (z : Phys b → ZMod 2) (i : Fin b) :
    gB (Qmat T B *ᵥ z) i = (T *ᵥ gB z) i := by
  have h : gB (Qmat T B *ᵥ z) i = (Qmat T B *ᵥ z) (i, 0) + (Qmat T B *ᵥ z) (i, 1) := rfl
  rw [h, Qmat_mulVec_apply, Qmat_mulVec_apply]
  simp only [uu3, vv3]
  generalize gA z i = x; generalize (T *ᵥ gB z) i = y
  generalize (Tᵀ *ᵥ gC z) i + (B *ᵥ gB z) i = w
  revert x y w; decide

lemma gC_Qmat {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) (z : Phys b → ZMod 2) (i : Fin b) :
    gC (Qmat T B *ᵥ z) i = (Tᵀ *ᵥ gC z) i + (B *ᵥ gB z) i := by
  have h : gC (Qmat T B *ᵥ z) i = (Qmat T B *ᵥ z) (i, 1) + (Qmat T B *ᵥ z) (i, 2) := rfl
  rw [h, Qmat_mulVec_apply, Qmat_mulVec_apply]
  simp only [uu3, vv3]
  generalize gA z i = x; generalize (T *ᵥ gB z) i = y
  generalize (Tᵀ *ᵥ gC z) i + (B *ᵥ gB z) i = w
  revert x y w; decide

lemma zmod2_aux {a b c : ZMod 2} (h1 : a + b + c = 0) (h2 : a + b = 0) (h3 : b + c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  revert a b c; decide

/-- A vector with vanishing group coordinates is zero. -/
lemma eq_zero_of_coords {b : ℕ} (z : Phys b → ZMod 2) (h1 : ∀ i, gA z i = 0)
    (h2 : ∀ i, gB z i = 0) (h3 : ∀ i, gC z i = 0) : z = 0 := by
  funext ⟨i, k⟩
  obtain ⟨h0, h1', h2'⟩ := zmod2_aux (h1 i) (h2 i) (h3 i)
  match k with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1'
  | ⟨2, _⟩ => exact h2'

lemma funext_gA_grp {b : ℕ} (j : Fin b) : gA (grp j) = fun m => if m = j then 1 else 0 :=
  funext (gA_grp j)
lemma funext_gB_grp {b : ℕ} (j : Fin b) : gB (grp j) = 0 := funext (gB_grp j)
lemma funext_gC_grp {b : ℕ} (j : Fin b) : gC (grp j) = 0 := funext (gC_grp j)
lemma funext_gA_uvec {b : ℕ} (j : Fin b) : gA (uvec j) = 0 := funext (gA_uvec j)
lemma funext_gB_uvec {b : ℕ} (j : Fin b) : gB (uvec j) = 0 := funext (gB_uvec j)
lemma funext_gC_uvec {b : ℕ} (j : Fin b) : gC (uvec j) = fun m => if m = j then 1 else 0 :=
  funext (gC_uvec j)
lemma funext_gA_vvec {b : ℕ} (j : Fin b) : gA (vvec j) = 0 := funext (gA_vvec j)
lemma funext_gB_vvec {b : ℕ} (j : Fin b) : gB (vvec j) = fun m => if m = j then 1 else 0 :=
  funext (gB_vvec j)
lemma funext_gC_vvec {b : ℕ} (j : Fin b) : gC (vvec j) = 0 := funext (gC_vvec j)

lemma mulVec_delta {b : ℕ} (M : Matrix (Fin b) (Fin b) (ZMod 2)) (j i : Fin b) :
    (M *ᵥ fun m => if m = j then 1 else 0) i = M i j := by
  simp [mulVec, dotProduct]

/-- `Q` is symmetric when `B` is (tex 10664–10669). Kind: PROVED. -/
theorem Qmat_transpose {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) (hB : Bᵀ = B) :
    (Qmat T B)ᵀ = Qmat T B := by
  ext p q
  have h : B q.1 p.1 = B p.1 q.1 := by
    have := congrFun (congrFun hB p.1) q.1
    simpa [transpose_apply] using this
  have e : (if q.1 = p.1 then (1 : ZMod 2) else 0) = if p.1 = q.1 then 1 else 0 := by
    simp [eq_comm]
  simp only [transpose_apply, Qmat, h, e]
  ring

/-- `h_i = Q e_i = e_i` (tex 10670–10671). Kind: PROVED. -/
theorem Qmat_mulVec_grp {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) (i : Fin b) :
    Qmat T B *ᵥ grp i = grp i := by
  funext ⟨j, k⟩
  rw [Qmat_mulVec_apply, funext_gB_grp, funext_gC_grp, gA_grp]
  simp [grp]

/-- The bilinear matrix of `Q` in the basis `e_i, u_i, v_i` is `I_b ⊕ H(T,B)`
(tex 10664–10669). Kind: PROVED. -/
theorem Qmat_form {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) (i j : Fin b) :
    grp i ⬝ᵥ (Qmat T B *ᵥ grp j) = (if i = j then 1 else 0) ∧
    grp i ⬝ᵥ (Qmat T B *ᵥ uvec j) = 0 ∧ grp i ⬝ᵥ (Qmat T B *ᵥ vvec j) = 0 ∧
    uvec i ⬝ᵥ (Qmat T B *ᵥ uvec j) = 0 ∧ uvec i ⬝ᵥ (Qmat T B *ᵥ vvec j) = T i j ∧
    vvec i ⬝ᵥ (Qmat T B *ᵥ vvec j) = B i j := by
  simp only [grp_dot, uvec_dot, vvec_dot, gA_Qmat, gB_Qmat, gC_Qmat, gA_grp, funext_gA_uvec,
    funext_gA_vvec, funext_gB_uvec, funext_gB_vvec, funext_gC_vvec, mulVec_zero, mulVec_delta,
    Pi.zero_apply, zero_add]
  simp

/-! ### Principal submatrices -/

/-- Principal submatrix on the active groups `J`. -/
def Qsub {b : ℕ} (Q : Matrix (Phys b) (Phys b) (ZMod 2)) (J : Finset (Fin b)) :
    Matrix {p : Phys b // p.1 ∈ J} {p : Phys b // p.1 ∈ J} (ZMod 2) :=
  Q.submatrix Subtype.val Subtype.val
/-- Restriction of a column to the active groups. -/
def restr {b : ℕ} (J : Finset (Fin b)) (x : Phys b → ZMod 2) : {p : Phys b // p.1 ∈ J} → ZMod 2 :=
  fun p => x p.1

/-- Extension by zero from the active groups. -/
def extJ {b : ℕ} (J : Finset (Fin b)) (v : {p : Phys b // p.1 ∈ J} → ZMod 2) :
    Phys b → ZMod 2 :=
  fun q => if h : q.1 ∈ J then v ⟨q, h⟩ else 0

lemma Qsub_mulVec_apply {b : ℕ} (Q : Matrix (Phys b) (Phys b) (ZMod 2)) (J : Finset (Fin b))
    (v : {p : Phys b // p.1 ∈ J} → ZMod 2) (p : {p : Phys b // p.1 ∈ J}) :
    (Qsub Q J *ᵥ v) p = (Q *ᵥ extJ J v) p.1 := by
  simp only [mulVec, dotProduct, Qsub, submatrix_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun q : Phys b => q.1 ∈ J)]
  have h2 : ∑ q : {q : Phys b // q.1 ∉ J}, Q p.1 q.1 * extJ J v q.1 = 0 :=
    Finset.sum_eq_zero fun q _ => by simp [extJ, q.2]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [extJ, q.2]

lemma extJ_restr {b : ℕ} (J : Finset (Fin b)) (x : Phys b → ZMod 2)
    (hx : ∀ q : Phys b, q.1 ∉ J → x q = 0) : extJ J (restr J x) = x := by
  funext q
  by_cases h : q.1 ∈ J
  · simp [extJ, restr, h]
  · simp [extJ, h, hx q h]

lemma Qsub_mulVec_restr {b : ℕ} (Q : Matrix (Phys b) (Phys b) (ZMod 2)) (J : Finset (Fin b))
    (x : Phys b → ZMod 2) (hx : ∀ q : Phys b, q.1 ∉ J → x q = 0) :
    Qsub Q J *ᵥ restr J x = restr J (Q *ᵥ x) := by
  funext p
  rw [Qsub_mulVec_apply, extJ_restr J x hx]
  rfl

lemma restr_dot {b : ℕ} (J : Finset (Fin b)) (x y : Phys b → ZMod 2)
    (hy : ∀ q : Phys b, q.1 ∉ J → y q = 0) : restr J x ⬝ᵥ restr J y = x ⬝ᵥ y := by
  simp only [dotProduct, restr]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun q : Phys b => q.1 ∈ J) (fun q => x q * y q)]
  have h2 : ∑ q : {q : Phys b // q.1 ∉ J}, x q.1 * y q.1 = 0 :=
    Finset.sum_eq_zero fun q _ => by simp [hy q.1 q.2]
  rw [h2, add_zero]

/-- Determinant one of a principal submatrix from injectivity of the network blocks. -/
lemma Qsub_det_eq_one {n : ℕ} (T B : Matrix (Fin n) (Fin n) (ZMod 2)) (J : Finset (Fin n))
    (h : ∀ a c : Fin n → ZMod 2, (∀ j, j ∉ J → a j = 0) → (∀ j, j ∉ J → c j = 0) →
      (∀ i ∈ J, (T *ᵥ c) i = 0) → (∀ i ∈ J, (Tᵀ *ᵥ a) i + (B *ᵥ c) i = 0) → a = 0 ∧ c = 0) :
    (Qsub (Qmat T B) J).det = 1 := by
  have hne : (Qsub (Qmat T B) J).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hv
    have hz : ∀ q : Phys n, q.1 ∉ J → extJ J v q = 0 := fun q hq => by simp [extJ, hq]
    have hQz : ∀ i ∈ J, ∀ k, (Qmat T B *ᵥ extJ J v) (i, k) = 0 := by
      intro i hi k
      have := congrFun hQv ⟨(i, k), hi⟩
      rwa [Qsub_mulVec_apply] at this
    have hA : ∀ i ∈ J, gA (Qmat T B *ᵥ extJ J v) i = 0 := fun i hi => by
      simp [gA, hQz i hi]
    have hB' : ∀ i ∈ J, gB (Qmat T B *ᵥ extJ J v) i = 0 := fun i hi => by
      simp [gB, hQz i hi]
    have hC : ∀ i ∈ J, gC (Qmat T B *ᵥ extJ J v) i = 0 := fun i hi => by
      simp [gC, hQz i hi]
    simp only [gA_Qmat, gB_Qmat, gC_Qmat] at hA hB' hC
    obtain ⟨ha, hc⟩ := h (gC (extJ J v)) (gB (extJ J v))
      (fun j hj => by simp [gC, hz (j, 1) hj, hz (j, 2) hj])
      (fun j hj => by simp [gB, hz (j, 0) hj, hz (j, 1) hj]) hB' hC
    have hz0 : extJ J v = 0 := by
      refine eq_zero_of_coords _ (fun i => ?_) (fun i => congrFun hc i) (fun i => congrFun ha i)
      by_cases hi : i ∈ J
      · exact hA i hi
      · simp [gA, hz (i, 0) hi, hz (i, 1) hi, hz (i, 2) hi]
    funext p
    have := congrFun hz0 p.1
    simpa [extJ, p.2] using this
  generalize (Qsub (Qmat T B) J).det = d at hne
  revert d; decide

end ZInQ.Manuscript.RC.Symbols
