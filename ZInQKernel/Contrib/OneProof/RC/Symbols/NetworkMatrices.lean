import ZInQKernel.Contrib.OneProof.RC.Symbols.Core
import Mathlib

/-!
# Lane RC2: the network matrices of the existence proof (tex 10657–10720)

Physical space `F_2^{3b}`, one three-dimensional group per index `i`, with `e_i = (1,1,1)`,
`u_i = (1,1,0)`, `v_i = (0,1,1)`. In one group the dot-dual basis of `(e,u,v)` is `(e,v,u)`, so
the prescribed matrix (bilinear matrix `I_b` on the `e_i` and `H(T,B)` on the `u_i, v_i`) is
`Q = Σ e_i e_iᵀ + Σ T_ij (v_i u_jᵀ + u_j v_iᵀ) + Σ B_ij u_i u_jᵀ` (`Qmat`), and the extra column
`c` dual to `u_1` is `v_1` (`cvec`).

Proof method: everything is reduced to linear equations in the group coordinates
(`gA`, `gB`, `gC` = pairings with `e`, `u`, `v`). Determinant one of `Q_J` follows from
injectivity (a nonzero element of `F_2` is one); `adj Q = r rᵀ` for the singular network from
`Q · adj Q = 0`, `ker Q = span r`, symmetry and one nonzero principal cofactor; the change of
`Q_J⁻¹` for the varying network from an explicit solution of `Q_J w = c`.
-/
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

/-- Dot product on the physical space, group by group (tex 10661–10664). Kind: PROVED (helper). -/
lemma dot_eq_sum {b : ℕ} (x y : Phys b → ZMod 2) :
    x ⬝ᵥ y = ∑ j, (x (j, 0) * y (j, 0) + x (j, 1) * y (j, 1) + x (j, 2) * y (j, 2)) := by
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three]

/-- Pairing with `e_i` is the group sum `gA` (tex 10664–10666). Kind: PROVED (helper). -/
lemma grp_dot {b : ℕ} (i : Fin b) (z : Phys b → ZMod 2) : grp i ⬝ᵥ z = gA z i := by
  rw [dot_eq_sum, Finset.sum_eq_single i]
  · simp [grp, gA]
  · intro j _ hj; simp [grp, hj]
  · simp

/-- Pairing with `u_i` is `gB` (tex 10664–10666). Kind: PROVED (helper). -/
lemma uvec_dot {b : ℕ} (i : Fin b) (z : Phys b → ZMod 2) : uvec i ⬝ᵥ z = gB z i := by
  rw [dot_eq_sum, Finset.sum_eq_single i]
  · simp [uvec, gB]
  · intro j _ hj; simp [uvec, hj]
  · simp

/-- Pairing with `v_i` is `gC` (tex 10664–10666). Kind: PROVED (helper). -/
lemma vvec_dot {b : ℕ} (i : Fin b) (z : Phys b → ZMod 2) : vvec i ⬝ᵥ z = gC z i := by
  rw [dot_eq_sum, Finset.sum_eq_single i]
  · simp [vvec, gC]
  · intro j _ hj; simp [vvec, hj]
  · simp

/-- The action of `Qmat` in group coordinates (tex 10664–10669). Kind: PROVED (helper). -/
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

/-- Group coordinates of `e_j` (tex 10664–10666). Kind: PROVED (helper). -/
lemma gA_grp {b : ℕ} (j m : Fin b) : gA (grp j) m = if m = j then 1 else 0 := by
  by_cases h : m = j
  · subst h; simp [gA, grp]; decide
  · simp [gA, grp, h]
/-- Group coordinates of `e_j` (tex 10664–10666). Kind: PROVED (helper). -/
lemma gB_grp {b : ℕ} (j m : Fin b) : gB (grp j) m = 0 := by
  by_cases h : m = j
  · subst h; simp [gB, grp]; decide
  · simp [gB, grp, h]
/-- Group coordinates of `e_j` (tex 10664–10666). Kind: PROVED (helper). -/
lemma gC_grp {b : ℕ} (j m : Fin b) : gC (grp j) m = 0 := by
  by_cases h : m = j
  · subst h; simp [gC, grp]; decide
  · simp [gC, grp, h]
/-- Group coordinates of `u_j` (tex 10664–10666). Kind: PROVED (helper). -/
lemma gA_uvec {b : ℕ} (j m : Fin b) : gA (uvec j) m = 0 := by
  by_cases h : m = j
  · subst h; simp [gA, uvec]; decide
  · simp [gA, uvec, h]
/-- Group coordinates of `u_j` (tex 10664–10666). Kind: PROVED (helper). -/
lemma gB_uvec {b : ℕ} (j m : Fin b) : gB (uvec j) m = 0 := by
  by_cases h : m = j
  · subst h; simp [gB, uvec]; decide
  · simp [gB, uvec, h]
/-- Group coordinates of `u_j` (tex 10664–10666). Kind: PROVED (helper). -/
lemma gC_uvec {b : ℕ} (j m : Fin b) : gC (uvec j) m = if m = j then 1 else 0 := by
  by_cases h : m = j <;> simp [gC, uvec, h]
/-- Group coordinates of `v_j` (tex 10664–10666). Kind: PROVED (helper). -/
lemma gA_vvec {b : ℕ} (j m : Fin b) : gA (vvec j) m = 0 := by
  by_cases h : m = j
  · subst h; simp [gA, vvec]; decide
  · simp [gA, vvec, h]
/-- Group coordinates of `v_j` (tex 10664–10666). Kind: PROVED (helper). -/
lemma gB_vvec {b : ℕ} (j m : Fin b) : gB (vvec j) m = if m = j then 1 else 0 := by
  by_cases h : m = j <;> simp [gB, vvec, h]
/-- Group coordinates of `v_j` (tex 10664–10666). Kind: PROVED (helper). -/
lemma gC_vvec {b : ℕ} (j m : Fin b) : gC (vvec j) m = 0 := by
  by_cases h : m = j
  · subst h; simp [gC, vvec]; decide
  · simp [gC, vvec, h]

/-- `Q` fixes the `e`-pairings (tex 10664–10671). Kind: PROVED (helper). -/
lemma gA_Qmat {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) (z : Phys b → ZMod 2) (i : Fin b) :
    gA (Qmat T B *ᵥ z) i = gA z i := by
  have h : gA (Qmat T B *ᵥ z) i = (Qmat T B *ᵥ z) (i, 0) + (Qmat T B *ᵥ z) (i, 1) +
    (Qmat T B *ᵥ z) (i, 2) := rfl
  rw [h, Qmat_mulVec_apply, Qmat_mulVec_apply, Qmat_mulVec_apply]
  simp only [uu3, vv3]
  generalize gA z i = x; generalize (T *ᵥ gB z) i = y
  generalize (Tᵀ *ᵥ gC z) i + (B *ᵥ gB z) i = w
  revert x y w; decide

/-- `Q` acts on the `u`-pairings through `T` (tex 10664–10669). Kind: PROVED (helper). -/
lemma gB_Qmat {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) (z : Phys b → ZMod 2) (i : Fin b) :
    gB (Qmat T B *ᵥ z) i = (T *ᵥ gB z) i := by
  have h : gB (Qmat T B *ᵥ z) i = (Qmat T B *ᵥ z) (i, 0) + (Qmat T B *ᵥ z) (i, 1) := rfl
  rw [h, Qmat_mulVec_apply, Qmat_mulVec_apply]
  simp only [uu3, vv3]
  generalize gA z i = x; generalize (T *ᵥ gB z) i = y
  generalize (Tᵀ *ᵥ gC z) i + (B *ᵥ gB z) i = w
  revert x y w; decide

/-- `Q` acts on the `v`-pairings through `Tᵀ` and `B` (tex 10664–10669). Kind: PROVED (helper). -/
lemma gC_Qmat {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) (z : Phys b → ZMod 2) (i : Fin b) :
    gC (Qmat T B *ᵥ z) i = (Tᵀ *ᵥ gC z) i + (B *ᵥ gB z) i := by
  have h : gC (Qmat T B *ᵥ z) i = (Qmat T B *ᵥ z) (i, 1) + (Qmat T B *ᵥ z) (i, 2) := rfl
  rw [h, Qmat_mulVec_apply, Qmat_mulVec_apply]
  simp only [uu3, vv3]
  generalize gA z i = x; generalize (T *ᵥ gB z) i = y
  generalize (Tᵀ *ᵥ gC z) i + (B *ᵥ gB z) i = w
  revert x y w; decide

/-- Arithmetic in `F_2` used to read off group coordinates (tex 10664–10666). Kind: PROVED
    (helper). -/
lemma zmod2_aux {a b c : ZMod 2} (h1 : a + b + c = 0) (h2 : a + b = 0) (h3 : b + c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  revert a b c; decide

/-- A vector with vanishing group coordinates is zero: `(e,u,v)` is a basis of each group
(tex 10664–10666). Kind: PROVED (helper). -/
lemma eq_zero_of_coords {b : ℕ} (z : Phys b → ZMod 2) (h1 : ∀ i, gA z i = 0)
    (h2 : ∀ i, gB z i = 0) (h3 : ∀ i, gC z i = 0) : z = 0 := by
  funext ⟨i, k⟩
  obtain ⟨h0, h1', h2'⟩ := zmod2_aux (h1 i) (h2 i) (h3 i)
  match k with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1'
  | ⟨2, _⟩ => exact h2'

/-- Function form of `gA_grp` (tex 10664–10666). Kind: PROVED (helper). -/
lemma funext_gA_grp {b : ℕ} (j : Fin b) : gA (grp j) = fun m => if m = j then 1 else 0 :=
  funext (gA_grp j)
/-- Function form of `gB_grp` (tex 10664–10666). Kind: PROVED (helper). -/
lemma funext_gB_grp {b : ℕ} (j : Fin b) : gB (grp j) = 0 := funext (gB_grp j)
/-- Function form of `gC_grp` (tex 10664–10666). Kind: PROVED (helper). -/
lemma funext_gC_grp {b : ℕ} (j : Fin b) : gC (grp j) = 0 := funext (gC_grp j)
/-- Function form of `gA_uvec` (tex 10664–10666). Kind: PROVED (helper). -/
lemma funext_gA_uvec {b : ℕ} (j : Fin b) : gA (uvec j) = 0 := funext (gA_uvec j)
/-- Function form of `gB_uvec` (tex 10664–10666). Kind: PROVED (helper). -/
lemma funext_gB_uvec {b : ℕ} (j : Fin b) : gB (uvec j) = 0 := funext (gB_uvec j)
/-- Function form of `gC_uvec` (tex 10664–10666). Kind: PROVED (helper). -/
lemma funext_gC_uvec {b : ℕ} (j : Fin b) : gC (uvec j) = fun m => if m = j then 1 else 0 :=
  funext (gC_uvec j)
/-- Function form of `gA_vvec` (tex 10664–10666). Kind: PROVED (helper). -/
lemma funext_gA_vvec {b : ℕ} (j : Fin b) : gA (vvec j) = 0 := funext (gA_vvec j)
/-- Function form of `gB_vvec` (tex 10664–10666). Kind: PROVED (helper). -/
lemma funext_gB_vvec {b : ℕ} (j : Fin b) : gB (vvec j) = fun m => if m = j then 1 else 0 :=
  funext (gB_vvec j)
/-- Function form of `gC_vvec` (tex 10664–10666). Kind: PROVED (helper). -/
lemma funext_gC_vvec {b : ℕ} (j : Fin b) : gC (vvec j) = 0 := funext (gC_vvec j)

/-- A matrix applied to a standard basis column (tex 10667–10669). Kind: PROVED (helper). -/
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

/-- The principal submatrix acts as `Q` on columns extended by zero (tex 10671–10676). Kind:
    PROVED (helper). -/
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

/-- Extension by zero inverts restriction for columns supported on `J` (tex 10671–10676). Kind:
    PROVED (helper). -/
lemma extJ_restr {b : ℕ} (J : Finset (Fin b)) (x : Phys b → ZMod 2)
    (hx : ∀ q : Phys b, q.1 ∉ J → x q = 0) : extJ J (restr J x) = x := by
  funext q
  by_cases h : q.1 ∈ J
  · simp [extJ, restr, h]
  · simp [extJ, h, hx q h]

/-- `Q_J` on a restricted column supported on `J` (tex 10671–10676). Kind: PROVED (helper). -/
lemma Qsub_mulVec_restr {b : ℕ} (Q : Matrix (Phys b) (Phys b) (ZMod 2)) (J : Finset (Fin b))
    (x : Phys b → ZMod 2) (hx : ∀ q : Phys b, q.1 ∉ J → x q = 0) :
    Qsub Q J *ᵥ restr J x = restr J (Q *ᵥ x) := by
  funext p
  rw [Qsub_mulVec_apply, extJ_restr J x hx]
  rfl

/-- Restriction preserves pairings with columns supported on `J` (tex 10671–10676). Kind: PROVED
    (helper). -/
lemma restr_dot {b : ℕ} (J : Finset (Fin b)) (x y : Phys b → ZMod 2)
    (hy : ∀ q : Phys b, q.1 ∉ J → y q = 0) : restr J x ⬝ᵥ restr J y = x ⬝ᵥ y := by
  simp only [dotProduct, restr]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun q : Phys b => q.1 ∈ J) (fun q => x q * y q)]
  have h2 : ∑ q : {q : Phys b // q.1 ∉ J}, x q.1 * y q.1 = 0 :=
    Finset.sum_eq_zero fun q _ => by simp [hy q.1 q.2]
  rw [h2, add_zero]

/-- `det Q_J = 1` as soon as the network blocks are injective on `J`: over `F_2` a nonzero
determinant is one, and `Q_J z = 0` forces the `e`-, `u`- and `v`-coordinates of `z` to vanish
(the bilinear matrix is `I_J ⊕ H(T_J,B_J)`, tex 10664–10676, 10688–10691, 10707).
Kind: PROVED (helper). -/
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

/-! ### The two networks -/

/-- Cyclic shift. -/
def Pcyc (b : ℕ) : Matrix (Fin b) (Fin b) (ZMod 2) :=
  fun i j => if j.val = (i.val + 1) % b then 1 else 0
/-- Consecutive lower shift. -/
def Llow (b : ℕ) : Matrix (Fin b) (Fin b) (ZMod 2) := fun i j => if i.val = j.val + 1 then 1 else 0
/-- Singular network (tex 10685–10702): `T = I + P`, one diagonal entry one in `B`. -/
noncomputable def Qsing (b : ℕ) (hb : 0 < b) : Matrix (Phys b) (Phys b) (ZMod 2) :=
  Qmat (1 + Pcyc b) (Matrix.single ⟨0, hb⟩ ⟨0, hb⟩ 1)
/-- Varying network (tex 10704–10720): `T = I + L`, `B_ε = ε E_{bb}`. -/
noncomputable def Qvar (b : ℕ) (hb : 0 < b) (ε : ZMod 2) : Matrix (Phys b) (Phys b) (ZMod 2) :=
  Qmat (1 + Llow b) (ε • Matrix.single ⟨b - 1, by omega⟩ ⟨b - 1, by omega⟩ 1)
/-- `r = ∑ u_i`. -/
def rvec (b : ℕ) : Phys b → ZMod 2 := fun p => ∑ i, uvec i p
/-- The extra column `c`, dual to `u_1`, supported on the first group (tex 10678). It is `v_1`,
since the dot-dual basis of `(e,u,v)` in one group is `(e,v,u)`. -/
def cvec (b : ℕ) (hb : 0 < b) : Phys b → ZMod 2 := vvec ⟨0, hb⟩

/-- `x + y = 0` forces `x = y` in `F_2`. Kind: PROVED (helper). -/
lemma zmod2_eq_of_add {x y : ZMod 2} (h : x + y = 0) : x = y := by
  revert x y; decide

/-! #### The lower shift -/

/-- The lower shift applied to a column (tex 10704–10707). Kind: PROVED (helper). -/
lemma Llow_mulVec {n : ℕ} (c : Fin n → ZMod 2) (i : Fin n) :
    (Llow n *ᵥ c) i = if h : 0 < i.val then c ⟨i.val - 1, by omega⟩ else 0 := by
  simp only [mulVec, dotProduct, Llow, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.val - 1, by omega⟩]
    · rw [ite_eq_left (by dsimp only; omega)]
    · intro j _ hj
      rw [ite_eq_right]
      intro h'
      apply hj; ext; dsimp only; omega
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right]; omega

/-- The transposed lower shift applied to a column (tex 10704–10707). Kind: PROVED (helper). -/
lemma LlowT_mulVec {n : ℕ} (c : Fin n → ZMod 2) (i : Fin n) :
    ((Llow n)ᵀ *ᵥ c) i = if h : i.val + 1 < n then c ⟨i.val + 1, h⟩ else 0 := by
  simp only [mulVec, dotProduct, Llow, transpose_apply, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.val + 1, h⟩]
    · rw [ite_eq_left rfl]
    · intro j _ hj
      rw [ite_eq_right]
      intro h'
      apply hj; ext; dsimp only; omega
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right]; have := j.isLt; omega

/-- Injectivity of the restricted lower-shift blocks: every `T_J` is unipotent
(tex 10707–10708). Kind: PROVED (helper). -/
lemma Llow_inj {n : ℕ} (J : Finset (Fin n)) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (a c : Fin n → ZMod 2) (ha : ∀ j, j ∉ J → a j = 0) (hc : ∀ j, j ∉ J → c j = 0)
    (h1 : ∀ i ∈ J, ((1 + Llow n) *ᵥ c) i = 0)
    (h2 : ∀ i ∈ J, ((1 + Llow n)ᵀ *ᵥ a) i + (B *ᵥ c) i = 0) : a = 0 ∧ c = 0 := by
  have hc0 : c = 0 := by
    have key : ∀ k, ∀ i : Fin n, i.val = k → c i = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro i hik
        by_cases hi : i ∈ J
        · have := h1 i hi
          rw [add_mulVec, one_mulVec, Pi.add_apply, Llow_mulVec] at this
          rw [zmod2_eq_of_add this]
          split_ifs with hpos
          · exact ih (i.val - 1) (by omega) _ rfl
          · rfl
        · exact hc i hi
    funext i; exact key _ i rfl
  refine ⟨?_, hc0⟩
  have key : ∀ k, ∀ i : Fin n, n - i.val = k → a i = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hik
      by_cases hi : i ∈ J
      · have := h2 i hi
        rw [hc0, mulVec_zero, Pi.zero_apply, add_zero, transpose_add, transpose_one,
          add_mulVec, one_mulVec, Pi.add_apply, LlowT_mulVec] at this
        rw [zmod2_eq_of_add this]
        split_ifs with hlt
        · exact ih (n - (i.val + 1)) (by omega) _ rfl
        · rfl
      · exact ha i hi
  funext i; exact key _ i rfl

/-! #### The cyclic shift -/

/-- Cyclic successor. -/
def csucc {n : ℕ} (i : Fin n) : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ (by have := i.isLt; omega)⟩
/-- Cyclic predecessor. -/
def cpred {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ (by have := i.isLt; omega)⟩

/-- Value of the cyclic successor (tex 10685–10686). Kind: PROVED (helper). -/
lemma succ_val {n : ℕ} (j : Fin n) : (j.val + 1) % n = if j.val + 1 = n then 0 else j.val + 1 := by
  have := j.isLt
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- Value of the cyclic predecessor (tex 10685–10686). Kind: PROVED (helper). -/
lemma pred_val {n : ℕ} (i : Fin n) : (i.val + n - 1) % n = if i.val = 0 then n - 1 else i.val - 1 := by
  have := i.isLt
  split_ifs with h
  · rw [h, Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
  · rw [show i.val + n - 1 = (i.val - 1) + n by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

/-- The cyclic successor and predecessor are inverse (tex 10685–10686). Kind: PROVED (helper). -/
lemma csucc_eq_iff {n : ℕ} (i j : Fin n) : csucc j = i ↔ j = cpred i := by
  have := i.isLt; have := j.isLt
  simp only [Fin.ext_iff, csucc, cpred, succ_val, pred_val]
  split_ifs <;> omega

/-- The cyclic shift applied to a column (tex 10685–10686). Kind: PROVED (helper). -/
lemma Pcyc_mulVec {n : ℕ} (c : Fin n → ZMod 2) (i : Fin n) : (Pcyc n *ᵥ c) i = c (csucc i) := by
  simp only [mulVec, dotProduct, Pcyc, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (csucc i)]
  · exact ite_eq_left rfl
  · intro j _ hj
    rw [ite_eq_right]
    intro h; apply hj; ext; exact h
  · simp

/-- The transposed cyclic shift applied to a column (tex 10685–10686). Kind: PROVED (helper). -/
lemma PcycT_mulVec {n : ℕ} (c : Fin n → ZMod 2) (i : Fin n) :
    ((Pcyc n)ᵀ *ᵥ c) i = c (cpred i) := by
  simp only [mulVec, dotProduct, Pcyc, transpose_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (cpred i)]
  · rw [ite_eq_left]
    have := (csucc_eq_iff i (cpred i)).mpr rfl
    rw [Fin.ext_iff] at this
    exact this.symm
  · intro j _ hj
    rw [ite_eq_right]
    intro h; apply hj
    exact (csucc_eq_iff i j).mp (Fin.ext h.symm)
  · simp

/-- Each row of the cyclic shift has one entry one (tex 10685–10686). Kind: PROVED (helper). -/
lemma Pcyc_rowsum {n : ℕ} (j : Fin n) : ∑ i, Pcyc n j i = 1 := by
  simp only [Pcyc]
  rw [Finset.sum_eq_single (csucc j)]
  · exact ite_eq_left rfl
  · intro i _ hi; rw [ite_eq_right]; intro h; apply hi; ext; exact h
  · simp

/-- Each column of the cyclic shift has one entry one (tex 10685–10686). Kind: PROVED (helper). -/
lemma Pcyc_colsum {n : ℕ} (j : Fin n) : ∑ i, Pcyc n i j = 1 := by
  simp only [Pcyc]
  rw [Finset.sum_eq_single (cpred j)]
  · rw [ite_eq_left]
    have := (csucc_eq_iff j (cpred j)).mpr rfl
    rw [Fin.ext_iff] at this
    exact this.symm
  · intro i _ hi; rw [ite_eq_right]; intro h; apply hi
    exact (csucc_eq_iff j i).mp (Fin.ext h.symm)
  · simp

/-- Propagation forward along the cycle until a missing group: the restricted cyclic shift
is a union of paths (tex 10688–10690). Kind: PROVED (helper). -/
lemma cyc_zero_succ {n : ℕ} (J : Finset (Fin n)) (m : Fin n) (hm : m ∉ J)
    (c : Fin n → ZMod 2) (hc : ∀ j, j ∉ J → c j = 0) (h : ∀ i ∈ J, c i = c (csucc i)) :
    c = 0 := by
  have key : ∀ k, ∀ i : Fin n, (i.val + k) % n = m.val → c i = 0 := by
    intro k
    induction k with
    | zero =>
      intro i hi
      rw [Nat.add_zero, Nat.mod_eq_of_lt i.isLt] at hi
      have : i = m := Fin.ext hi
      rw [this]; exact hc m hm
    | succ k ih =>
      intro i hi
      by_cases hiJ : i ∈ J
      · rw [h i hiJ]
        apply ih
        simp only [csucc]
        rw [Nat.mod_add_mod, ← hi]; congr 1; omega
      · exact hc i hiJ
  funext i
  apply key (n - i.val + m.val) i
  have := i.isLt; have := m.isLt
  rw [show i.val + (n - i.val + m.val) = m.val + n by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt m.isLt]

/-- Propagation backward along the cycle until a missing group (tex 10688–10690).
Kind: PROVED (helper). -/
lemma cyc_zero_pred {n : ℕ} (J : Finset (Fin n)) (m : Fin n) (hm : m ∉ J)
    (a : Fin n → ZMod 2) (ha : ∀ j, j ∉ J → a j = 0) (h : ∀ i ∈ J, a i = a (cpred i)) :
    a = 0 := by
  have key : ∀ k, ∀ i : Fin n, (m.val + k) % n = i.val → a i = 0 := by
    intro k
    induction k with
    | zero =>
      intro i hi
      rw [Nat.add_zero, Nat.mod_eq_of_lt m.isLt] at hi
      have : i = m := Fin.ext hi.symm
      rw [this]; exact ha m hm
    | succ k ih =>
      intro i hi
      by_cases hiJ : i ∈ J
      · rw [h i hiJ]
        apply ih
        have hn : 0 < n := by have := i.isLt; omega
        let j0 : Fin n := ⟨(m.val + k) % n, Nat.mod_lt _ hn⟩
        have hj0 : csucc j0 = i := by
          ext; simp only [csucc, j0]; rw [Nat.mod_add_mod, ← hi, Nat.add_assoc]
        have := (csucc_eq_iff i j0).mp hj0
        rw [← this]
      · exact ha i hiJ
  funext i
  apply key (i.val + n - m.val) i
  have := i.isLt; have := m.isLt
  rw [show m.val + (i.val + n - m.val) = i.val + n by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt i.isLt]

/-- On a proper group subset `T_J` and `T_Jᵀ` are injective, `T = I + P` (tex 10688–10690). Kind:
    PROVED (helper). -/
lemma cyc_inj_proper {n : ℕ} (J : Finset (Fin n)) (hJ : J ≠ univ)
    (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (a c : Fin n → ZMod 2) (ha : ∀ j, j ∉ J → a j = 0) (hc : ∀ j, j ∉ J → c j = 0)
    (h1 : ∀ i ∈ J, ((1 + Pcyc n) *ᵥ c) i = 0)
    (h2 : ∀ i ∈ J, ((1 + Pcyc n)ᵀ *ᵥ a) i + (B *ᵥ c) i = 0) : a = 0 ∧ c = 0 := by
  obtain ⟨m, hm⟩ : ∃ m, m ∉ J := by
    by_contra hcon
    exact hJ (Finset.eq_univ_iff_forall.mpr fun x => by
      by_contra hx; exact hcon ⟨x, hx⟩)
  have hc0 : c = 0 := by
    refine cyc_zero_succ J m hm c hc fun i hi => ?_
    have := h1 i hi
    rw [add_mulVec, one_mulVec, Pi.add_apply, Pcyc_mulVec] at this
    exact zmod2_eq_of_add this
  refine ⟨?_, hc0⟩
  refine cyc_zero_pred J m hm a ha fun i hi => ?_
  have := h2 i hi
  rw [hc0, mulVec_zero, Pi.zero_apply, add_zero, transpose_add, transpose_one, add_mulVec,
    one_mulVec, Pi.add_apply, PcycT_mulVec] at this
  exact zmod2_eq_of_add this

/-- On every proper group subset the singular network is nondegenerate: the restricted cyclic
shift is a union of paths, so `det Q_J = det(T_J)^2 = 1` (tex 10688–10691). Kind: PROVED. -/
theorem Qsing_det_proper (b : ℕ) (hb : 0 < b) (J : Finset (Fin b)) (hJ : J ≠ univ) :
    (Qsub (Qsing b hb) J).det = 1 :=
  Qsub_det_eq_one _ _ J fun a c ha hc h1 h2 => cyc_inj_proper J hJ _ a c ha hc h1 h2

/-- Every principal matrix `Q_J` of the varying network has determinant one: `T_J` is unipotent
(tex 10707–10709). Kind: PROVED. -/
theorem Qvar_det (b : ℕ) (hb : 0 < b) (ε : ZMod 2) (J : Finset (Fin b)) :
    (Qsub (Qvar b hb ε) J).det = 1 :=
  Qsub_det_eq_one _ _ J fun a c ha hc h1 h2 => Llow_inj J _ a c ha hc h1 h2

/-! ### The vectors `r` and `c` -/

/-- `r = Σ u_i` is `(1,1,0)` on every group (tex 10693–10694). Kind: PROVED (helper). -/
lemma rvec_apply {n : ℕ} (p : Phys n) : rvec n p = uu3 p.2 := by
  simp only [rvec]
  rw [Finset.sum_eq_single p.1]
  · obtain ⟨j, k⟩ := p
    fin_cases k <;> simp [uvec, uu3]
  · intro i _ hi; simp [uvec, Ne.symm hi]
  · simp

/-- Group coordinates of `r` (tex 10693–10697). Kind: PROVED (helper). -/
lemma gA_rvec {n : ℕ} (i : Fin n) : gA (rvec n) i = 0 := by
  simp only [gA, rvec_apply]; decide
/-- Group coordinates of `r` (tex 10693–10697). Kind: PROVED (helper). -/
lemma gB_rvec {n : ℕ} : gB (rvec n) = 0 := funext fun i => by
  simp only [gB, rvec_apply, Pi.zero_apply]; decide
/-- Group coordinates of `r` (tex 10693–10697). Kind: PROVED (helper). -/
lemma gC_rvec {n : ℕ} : gC (rvec n) = fun _ => 1 := funext fun i => by
  simp only [gC, rvec_apply]; decide

/-- The extra column `c` is dual to `u_1`: it pairs to zero with every `e_j` and `v_j`, to
`δ_{j1}` with `u_j`, and is supported on the first group (tex 10677–10679). Kind: PROVED. -/
theorem cvec_spec (b : ℕ) (hb : 0 < b) :
    (∀ j, cvec b hb ⬝ᵥ grp j = 0) ∧ (∀ j, cvec b hb ⬝ᵥ uvec j = if j = ⟨0, hb⟩ then 1 else 0) ∧
    (∀ j, cvec b hb ⬝ᵥ vvec j = 0) ∧ (∀ p, cvec b hb p ≠ 0 → p.1 = ⟨0, hb⟩) := by
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun p hp => ?_⟩
  · rw [dotProduct_comm, grp_dot, cvec, gA_vvec]
  · rw [dotProduct_comm, uvec_dot, cvec, gB_vvec]
  · rw [dotProduct_comm, vvec_dot, cvec, gC_vvec]
  · simp only [cvec, vvec] at hp
    split_ifs at hp with h
    · exact h.1
    · exact absurd rfl hp

/-- The anchor columns pair to zero with `r` (tex 10696–10697). Kind: PROVED. -/
theorem grp_rvec {b : ℕ} (i : Fin b) : grp i ⬝ᵥ rvec b = 0 := by
  rw [grp_dot, gA_rvec]

/-- `cᵀ r = 1` (tex 10697). Kind: PROVED. -/
theorem cvec_rvec (b : ℕ) (hb : 0 < b) : cvec b hb ⬝ᵥ rvec b = 1 := by
  rw [cvec, vvec_dot, gC_rvec]

/-- The singular network matrix is symmetric (tex 10685–10687). Kind: PROVED. -/
theorem Qsing_symm (b : ℕ) (hb : 0 < b) : (Qsing b hb)ᵀ = Qsing b hb :=
  Qmat_transpose _ _ (by rw [transpose_single])

/-- The varying network matrices are symmetric (tex 10704–10706). Kind: PROVED. -/
theorem Qvar_symm (b : ℕ) (hb : 0 < b) (ε : ZMod 2) : (Qvar b hb ε)ᵀ = Qvar b hb ε :=
  Qmat_transpose _ _ (by rw [transpose_smul, transpose_single])

/-! ### The singular network on all groups -/

/-- A matrix unit applied to a column (tex 10686–10687). Kind: PROVED (helper). -/
lemma single_mulVec_apply {n : ℕ} (i₀ j₀ : Fin n) (y : Fin n → ZMod 2) (i : Fin n) :
    (Matrix.single i₀ j₀ (1 : ZMod 2) *ᵥ y) i = if i = i₀ then y j₀ else 0 := by
  rw [single_mulVec, Function.update_apply, one_mul]
  rfl

/-- Row sums of `I + P` vanish (tex 10691–10692). Kind: PROVED (helper). -/
lemma T1_rowsum {n : ℕ} (j : Fin n) : ∑ i, (1 + Pcyc n) j i = 0 := by
  simp only [Matrix.add_apply, Finset.sum_add_distrib, Pcyc_rowsum, one_apply, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  decide

/-- Column sums of `I + P` vanish (tex 10691–10692). Kind: PROVED (helper). -/
lemma T1_colsum {n : ℕ} (j : Fin n) : ∑ i, (1 + Pcyc n) i j = 0 := by
  simp only [Matrix.add_apply, Finset.sum_add_distrib, Pcyc_colsum, one_apply, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  decide

/-- `1ᵀ (I + P)ᵀ = 0` (tex 10691–10692). Kind: PROVED (helper). -/
lemma sum_T1T_mulVec {n : ℕ} (x : Fin n → ZMod 2) : ∑ i, ((1 + Pcyc n)ᵀ *ᵥ x) i = 0 := by
  simp only [mulVec, dotProduct, transpose_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, T1_rowsum, zero_mul, Finset.sum_const_zero]

/-- `1ᵀ (I + P) = 0` (tex 10691–10692). Kind: PROVED (helper). -/
lemma sum_T1_mulVec {n : ℕ} (y : Fin n → ZMod 2) : ∑ i, ((1 + Pcyc n) *ᵥ y) i = 0 := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, T1_colsum, zero_mul, Finset.sum_const_zero]

/-- A function invariant under the cyclic successor is constant (tex 10691–10692). Kind: PROVED
    (helper). -/
lemma const_of_succ {n : ℕ} (hn : 0 < n) (f : Fin n → ZMod 2) (h : ∀ i, f i = f (csucc i)) :
    ∀ i, f i = f ⟨0, hn⟩ := by
  have key : ∀ k : ℕ, f ⟨k % n, Nat.mod_lt _ hn⟩ = f ⟨0, hn⟩ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← ih, h ⟨k % n, Nat.mod_lt _ hn⟩]
      congr 1; ext; simp [csucc, Nat.mod_add_mod]
  intro i
  have := key i.val
  rwa [show (⟨i.val % n, Nat.mod_lt _ hn⟩ : Fin n) = i from Fin.ext (Nat.mod_eq_of_lt i.isLt)]
    at this

/-- Arithmetic in `F_2` used to recover a vector from its group coordinates (tex 10664–10666).
    Kind: PROVED (helper). -/
lemma zmod2_aux2 {a b c t : ZMod 2} (h1 : a + b + c = 0) (h2 : a + b = 0) (h3 : b + c = t) :
    a = t ∧ b = t ∧ c = 0 := by
  revert a b c t; decide

/-- Kernel of the singular network in group coordinates: `ker T = ker Tᵀ = span 1` and the
diagonal entry of `B` kills the lower component (tex 10691–10694). Kind: PROVED (helper). -/
lemma sing_core {n : ℕ} (hn : 0 < n) (z : Phys n → ZMod 2) (h1 : ∀ i, gA z i = 0)
    (h2 : ∀ i, ((1 + Pcyc n) *ᵥ gB z) i = 0)
    (h3 : ∀ i, ((1 + Pcyc n)ᵀ *ᵥ gC z) i + (Matrix.single ⟨0, hn⟩ ⟨0, hn⟩ 1 *ᵥ gB z) i = 0) :
    ∃ t : ZMod 2, z = t • rvec n := by
  have hBc : ∀ i, gB z i = gB z ⟨0, hn⟩ := const_of_succ hn _ fun i => by
    have := h2 i
    rw [add_mulVec, one_mulVec, Pi.add_apply, Pcyc_mulVec] at this
    exact zmod2_eq_of_add this
  have hB0 : gB z ⟨0, hn⟩ = 0 := by
    have hs : ∑ i, (((1 + Pcyc n)ᵀ *ᵥ gC z) i +
        (Matrix.single ⟨0, hn⟩ ⟨0, hn⟩ 1 *ᵥ gB z) i) = 0 :=
      Finset.sum_eq_zero fun i _ => h3 i
    rw [Finset.sum_add_distrib, sum_T1T_mulVec, zero_add] at hs
    simpa only [single_mulVec_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hs
  have hB : gB z = 0 := funext fun i => (hBc i).trans hB0
  have hCc : ∀ i, gC z i = gC z ⟨0, hn⟩ := const_of_succ hn _ fun i => by
    have := h3 (csucc i)
    rw [hB, mulVec_zero, Pi.zero_apply, add_zero, transpose_add, transpose_one, add_mulVec,
      one_mulVec, Pi.add_apply, PcycT_mulVec, ← (csucc_eq_iff _ _).mp rfl] at this
    exact (zmod2_eq_of_add this).symm
  refine ⟨gC z ⟨0, hn⟩, ?_⟩
  generalize gC z ⟨0, hn⟩ = t at hCc ⊢
  funext ⟨i, k⟩
  have e1 := h1 i
  have e2 := congrFun hB i
  have e3 := hCc i
  simp only [gA, gB, gC, Pi.zero_apply] at e1 e2 e3
  obtain ⟨e0, e1', e2'⟩ := zmod2_aux2 e1 e2 e3
  simp only [Pi.smul_apply, smul_eq_mul, rvec_apply]
  fin_cases k
  · simp [uu3, e0]
  · simp [uu3, e1']
  · simp [uu3, e2']

/-- `ker Q` of the singular network on all groups is contained in the line of `r` (tex
    10691–10694). Kind: PROVED (helper). -/
lemma sing_ker {n : ℕ} (hn : 0 < n) (z : Phys n → ZMod 2) (hz : Qsing n hn *ᵥ z = 0) :
    ∃ t : ZMod 2, z = t • rvec n := by
  refine sing_core hn z (fun i => ?_) (fun i => ?_) (fun i => ?_)
  · rw [← gA_Qmat (1 + Pcyc n) (Matrix.single ⟨0, hn⟩ ⟨0, hn⟩ 1)]
    change gA (Qsing n hn *ᵥ z) i = 0
    rw [hz]; simp [gA]
  · rw [← gB_Qmat _ (Matrix.single ⟨0, hn⟩ ⟨0, hn⟩ 1)]
    change gB (Qsing n hn *ᵥ z) i = 0
    rw [hz]; simp [gB]
  · rw [← gC_Qmat]
    change gC (Qsing n hn *ᵥ z) i = 0
    rw [hz]; simp [gC]

/-- A matrix with one row replaced, applied to a column (tex 10694–10696). Kind: PROVED (helper). -/
lemma updateRow_mulVec_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι (ZMod 2))
    (p₀ : ι) (w v : ι → ZMod 2) (p : ι) :
    (A.updateRow p₀ w *ᵥ v) p = if p = p₀ then w ⬝ᵥ v else (A *ᵥ v) p := by
  by_cases h : p = p₀
  · subst h; simp [mulVec]
  · simp [mulVec, h]

/-- The principal cofactor of the singular network at the first coordinate is one, so
`adj Q ≠ 0` (tex 10694–10696). Kind: PROVED (helper). -/
lemma Qsing_adj_diag {n : ℕ} (hn : 0 < n) :
    (Qsing n hn).adjugate (⟨0, hn⟩, 0) (⟨0, hn⟩, 0) = 1 := by
  rw [adjugate_apply]
  have hne : ((Qsing n hn).updateRow (⟨0, hn⟩, 0) (Pi.single (⟨0, hn⟩, 0) 1)).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hv
    have hv0 : v (⟨0, hn⟩, 0) = 0 := by
      have := congrFun hAv (⟨0, hn⟩, 0)
      rw [updateRow_mulVec_apply, ite_eq_left rfl] at this
      simpa [dotProduct, Pi.single_apply] using this
    have hQv : ∀ p, p ≠ (⟨0, hn⟩, 0) → (Qsing n hn *ᵥ v) p = 0 := fun p hp => by
      have := congrFun hAv p
      rwa [updateRow_mulVec_apply, ite_eq_right hp] at this
    have hrow : ∀ i : Fin n, i ≠ ⟨0, hn⟩ → ∀ k, (Qsing n hn *ᵥ v) (i, k) = 0 :=
      fun i hi k => hQv _ (fun h => hi (congrArg Prod.fst h))
    have hA' : ∀ i, i ≠ ⟨0, hn⟩ → gA v i = 0 := fun i hi => by
      rw [← gA_Qmat (1 + Pcyc n) (Matrix.single ⟨0, hn⟩ ⟨0, hn⟩ 1)]
      change gA (Qsing n hn *ᵥ v) i = 0
      simp [gA, hrow i hi]
    have hX' : ∀ i, i ≠ ⟨0, hn⟩ → ((1 + Pcyc n) *ᵥ gB v) i = 0 := fun i hi => by
      rw [← gB_Qmat _ (Matrix.single ⟨0, hn⟩ ⟨0, hn⟩ 1)]
      change gB (Qsing n hn *ᵥ v) i = 0
      simp [gB, hrow i hi]
    have h01 : (⟨0, hn⟩, (1 : Fin 3)) ≠ ((⟨0, hn⟩, 0) : Phys n) := by simp
    have h02 : (⟨0, hn⟩, (2 : Fin 3)) ≠ ((⟨0, hn⟩, 0) : Phys n) := by simp
    have hY : ∀ i, ((1 + Pcyc n)ᵀ *ᵥ gC v) i +
        (Matrix.single ⟨0, hn⟩ ⟨0, hn⟩ 1 *ᵥ gB v) i = 0 := by
      intro i
      rw [← gC_Qmat]
      change gC (Qsing n hn *ᵥ v) i = 0
      by_cases hi : i = ⟨0, hn⟩
      · subst hi
        simp only [gC]
        rw [hQv _ h01, hQv _ h02, add_zero]
      · simp [gC, hrow i hi]
    have hX0 : ((1 + Pcyc n) *ᵥ gB v) ⟨0, hn⟩ = 0 := by
      have hs := sum_T1_mulVec (gB v)
      rwa [Finset.sum_eq_single ⟨0, hn⟩ (fun i _ hi => hX' i hi) (by simp)] at hs
    have hA0 : gA v ⟨0, hn⟩ = 0 := by
      have h2 := hQv _ h02
      rw [Qsing, Qmat_mulVec_apply, hX0, hY ⟨0, hn⟩] at h2
      simpa [vv3, uu3] using h2
    have hX : ∀ i, ((1 + Pcyc n) *ᵥ gB v) i = 0 := fun i => by
      by_cases hi : i = ⟨0, hn⟩
      · rw [hi]; exact hX0
      · exact hX' i hi
    have hA : ∀ i, gA v i = 0 := fun i => by
      by_cases hi : i = ⟨0, hn⟩
      · rw [hi]; exact hA0
      · exact hA' i hi
    obtain ⟨t, ht⟩ := sing_core hn v hA hX hY
    have ht0 : t = 0 := by
      have := congrFun ht (⟨0, hn⟩, 0)
      rw [hv0, Pi.smul_apply, rvec_apply] at this
      simpa [uu3] using this.symm
    rw [ht, ht0, zero_smul]
  generalize ((Qsing n hn).updateRow (⟨0, hn⟩, 0) (Pi.single (⟨0, hn⟩, 0) 1)).det = d at hne
  revert d; decide

/-- On all groups the singular network has kernel the line of `r = Σ u_i`, and
`adj(Q) = r rᵀ` (tex 10691–10696; for `b = 1`, `T = 0`, tex 10702). Kind: PROVED. -/
theorem Qsing_adjugate (b : ℕ) (hb : 0 < b) :
    (Qsing b hb).adjugate = vecMulVec (rvec b) (rvec b) := by
  have hr0 : rvec b (⟨0, hb⟩, 0) = 1 := by rw [rvec_apply]; rfl
  have hQr : Qsing b hb *ᵥ rvec b = 0 := by
    funext ⟨i, k⟩
    rw [Qsing, Qmat_mulVec_apply, gA_rvec, gB_rvec, gC_rvec, mulVec_zero, mulVec_zero,
      transpose_add, transpose_one, add_mulVec, one_mulVec]
    simp only [Pi.add_apply, PcycT_mulVec, Pi.zero_apply, mul_zero, add_zero, zero_add]
    rw [show (1 : ZMod 2) + 1 = 0 from rfl, mul_zero]
  have hdet : (Qsing b hb).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨rvec b, fun h => by simp [h] at hr0, hQr⟩
  have hcol : ∀ q, ∃ t : ZMod 2, (fun p => (Qsing b hb).adjugate p q) = t • rvec b := by
    intro q
    apply sing_ker hb
    funext p
    have := congrFun (congrFun (mul_adjugate (Qsing b hb)) p) q
    rw [hdet, zero_smul] at this
    simpa [mul_apply, mulVec, dotProduct] using this
  choose t ht using hcol
  have hsym : ∀ p q, (Qsing b hb).adjugate p q = (Qsing b hb).adjugate q p := by
    intro p q
    have := congrFun (congrFun (adjugate_transpose (Qsing b hb)) q) p
    rw [Qsing_symm] at this
    simpa [transpose_apply] using this
  have hval : ∀ p q, (Qsing b hb).adjugate p q = t q * rvec b p := fun p q => by
    have := congrFun (ht q) p
    simpa using this
  have ht0 : t (⟨0, hb⟩, 0) = 1 := by
    have := hval (⟨0, hb⟩, 0) (⟨0, hb⟩, 0)
    rw [Qsing_adj_diag, hr0, mul_one] at this
    exact this.symm
  have htq : ∀ q, t q = rvec b q := fun q => by
    have h1 := hval (⟨0, hb⟩, 0) q
    rw [hr0, mul_one, hsym, hval, ht0, one_mul] at h1
    exact h1.symm
  ext p q
  rw [hval, htq, vecMulVec_apply, mul_comm]

/-! ### The varying network: change of the inverse -/

/-- Entry of `u = (1,1,0)`. Kind: PROVED (helper). -/
lemma uu3_0 : uu3 0 = 1 := rfl
/-- Entry of `u = (1,1,0)`. Kind: PROVED (helper). -/
lemma uu3_1 : uu3 1 = 1 := rfl
/-- Entry of `u = (1,1,0)`. Kind: PROVED (helper). -/
lemma uu3_2 : uu3 2 = 0 := rfl
/-- Entry of `v = (0,1,1)`. Kind: PROVED (helper). -/
lemma vv3_0 : vv3 0 = 0 := rfl
/-- Entry of `v = (0,1,1)`. Kind: PROVED (helper). -/
lemma vv3_1 : vv3 1 = 1 := rfl
/-- Entry of `v = (0,1,1)`. Kind: PROVED (helper). -/
lemma vv3_2 : vv3 2 = 1 := rfl

/-- Indicator that the whole initial path `0, …, j` of groups is active. -/
def bJ {n : ℕ} (J : Finset (Fin n)) (j : Fin n) : ZMod 2 :=
  if ∀ m : Fin n, m.val ≤ j.val → m ∈ J then 1 else 0
/-- The constant `u`-coordinate of the solution below: `ε` when all groups are active. -/
def aJ {n : ℕ} (ε : ZMod 2) (J : Finset (Fin n)) : ZMod 2 := if J = univ then ε else 0
/-- Explicit solution `w` of `Q_J w = c` for the varying network. -/
def wv {n : ℕ} (ε : ZMod 2) (J : Finset (Fin n)) : Phys n → ZMod 2 :=
  fun q => if q.1 ∈ J then aJ ε J * uu3 q.2 + bJ J q.1 * vv3 q.2 else 0

/-- The path indicator vanishes off `J` (tex 10709–10713). Kind: PROVED (helper). -/
lemma bJ_mem {n : ℕ} (J : Finset (Fin n)) (j : Fin n) (h : bJ J j ≠ 0) : j ∈ J := by
  unfold bJ at h
  split_ifs at h with h'
  · exact h' j le_rfl
  · exact absurd rfl h

/-- The path indicator vanishes off `J` (tex 10709–10713). Kind: PROVED (helper). -/
lemma bJ_of_not_mem {n : ℕ} (J : Finset (Fin n)) (j : Fin n) (h : j ∉ J) : bJ J j = 0 := by
  by_contra h'; exact h (bJ_mem J j h')

/-- The constant `aJ` vanishes when some group is inactive (tex 10709–10713). Kind: PROVED
    (helper). -/
lemma aJ_of_not_mem {n : ℕ} (ε : ZMod 2) (J : Finset (Fin n)) (j : Fin n) (h : j ∉ J) :
    aJ ε J = 0 := by
  unfold aJ; rw [ite_eq_right]; rintro rfl; exact h (Finset.mem_univ j)

/-- Group coordinates of the explicit solution `w` (tex 10709–10713). Kind: PROVED (helper). -/
lemma gA_wv {n : ℕ} (ε : ZMod 2) (J : Finset (Fin n)) : gA (wv ε J) = 0 := funext fun j => by
  by_cases hj : j ∈ J
  · simp only [gA, wv, hj, ↓reduceIte, uu3_0, uu3_1, uu3_2, vv3_0, vv3_1, vv3_2, Pi.zero_apply]
    grind
  · simp [gA, wv, hj]

/-- Group coordinates of the explicit solution `w`: `T_J⁻¹ δ_1` is the path indicator (tex
    10709–10713). Kind: PROVED (helper). -/
lemma gB_wv {n : ℕ} (ε : ZMod 2) (J : Finset (Fin n)) : gB (wv ε J) = bJ J := funext fun j => by
  by_cases hj : j ∈ J
  · simp only [gB, wv, hj, ↓reduceIte, uu3_0, uu3_1, vv3_0, vv3_1]
    grind
  · simp [gB, wv, hj, bJ_of_not_mem J j hj]

/-- Group coordinates of the explicit solution `w` (tex 10709–10713). Kind: PROVED (helper). -/
lemma gC_wv {n : ℕ} (ε : ZMod 2) (J : Finset (Fin n)) : gC (wv ε J) = fun _ => aJ ε J :=
  funext fun j => by
  by_cases hj : j ∈ J
  · simp only [gC, wv, hj, ↓reduceIte, uu3_1, uu3_2, vv3_1, vv3_2]
    grind
  · simp [gC, wv, hj, aJ_of_not_mem ε J j hj]

/-- `T_J` applied to the path indicator gives `δ_1`, `T = I + L` (tex 10707–10713). Kind: PROVED
    (helper). -/
lemma T_bJ {n : ℕ} (hn : 0 < n) (J : Finset (Fin n)) (i : Fin n) (hi : i ∈ J) :
    ((1 + Llow n) *ᵥ bJ J) i = if i = ⟨0, hn⟩ then 1 else 0 := by
  rw [add_mulVec, one_mulVec, Pi.add_apply, Llow_mulVec]
  by_cases h0 : 0 < i.val
  · have hne : i ≠ ⟨0, hn⟩ := fun h => by rw [h] at h0; exact absurd h0 (lt_irrefl 0)
    simp only [h0, ↓reduceDIte, hne, ↓reduceIte]
    have key : (∀ m : Fin n, m.val ≤ i.val → m ∈ J) ↔
        (∀ m : Fin n, m.val ≤ i.val - 1 → m ∈ J) := by
      constructor
      · intro h m hm; exact h m (by omega)
      · intro h m hm
        by_cases hmi : m.val = i.val
        · rw [Fin.ext hmi]; exact hi
        · exact h m (by omega)
    have : bJ J i = bJ J ⟨i.val - 1, by omega⟩ := by
      simp only [bJ, key]
    rw [this]; grind
  · have heq : i = ⟨0, hn⟩ := Fin.ext (by simp only; omega)
    simp only [h0, ↓reduceDIte, add_zero]
    rw [ite_eq_left heq]
    unfold bJ
    rw [ite_eq_left]
    intro m hm
    exact (Fin.ext (by omega) : m = i) ▸ hi

/-- The path indicator at the last group is one exactly when all groups are active (tex
    10711–10713). Kind: PROVED (helper). -/
lemma bJ_last {n : ℕ} (hn : 0 < n) (J : Finset (Fin n)) :
    bJ J ⟨n - 1, by omega⟩ = if J = univ then 1 else 0 := by
  by_cases hJ : J = univ
  · subst hJ; simp [bJ]
  · rw [ite_eq_right hJ]
    unfold bJ
    rw [ite_eq_right]
    intro h; apply hJ; rw [Finset.eq_univ_iff_forall]; intro m
    exact h m (by have := m.isLt; show m.val ≤ n - 1; omega)

/-- `T_Jᵀ a + B_ε b = 0` for the explicit coordinates (tex 10709–10713). Kind: PROVED (helper). -/
lemma TT_aJ_B {n : ℕ} (hn : 0 < n) (ε : ZMod 2) (J : Finset (Fin n)) (i : Fin n) :
    ((1 + Llow n)ᵀ *ᵥ (fun _ => aJ ε J)) i +
      ((ε • Matrix.single ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ (1 : ZMod 2)) *ᵥ bJ J) i = 0 := by
  rw [transpose_add, transpose_one, add_mulVec, one_mulVec, Pi.add_apply, LlowT_mulVec,
    smul_mulVec, Pi.smul_apply, single_mulVec_apply, bJ_last hn, smul_eq_mul]
  have hlast : i = ⟨n - 1, by omega⟩ ↔ ¬ (i.val + 1 < n) := by
    rw [Fin.ext_iff]; have := i.isLt; simp only; omega
  unfold aJ
  by_cases hJ : J = univ
  · by_cases hi : i.val + 1 < n
    · have hne : ¬ i = ⟨n - 1, by omega⟩ := fun h => (hlast.mp h) hi
      simp only [hJ, hi, ↓reduceDIte, hne, ↓reduceIte, mul_zero, add_zero]
      grind
    · have heq : i = ⟨n - 1, by omega⟩ := hlast.mpr hi
      simp only [hJ, heq, ↓reduceIte, mul_one]
      grind
  · simp only [hJ, ↓reduceIte]
    split_ifs <;> simp

/-- The explicit column `w` solves `Q_J w = c` on the active groups (tex 10709–10713). Kind:
    PROVED (helper). -/
lemma Qvar_wv {n : ℕ} (hn : 0 < n) (ε : ZMod 2) (J : Finset (Fin n)) (i : Fin n) (hi : i ∈ J)
    (k : Fin 3) : (Qvar n hn ε *ᵥ wv ε J) (i, k) = cvec n hn (i, k) := by
  rw [Qvar, Qmat_mulVec_apply, gA_wv, gB_wv, gC_wv, T_bJ hn J i hi, TT_aJ_B hn ε J i]
  by_cases h0 : i = ⟨0, hn⟩
  · subst h0; fin_cases k <;> simp [cvec, vvec, uu3, vv3]
  · fin_cases k <;> simp [cvec, vvec, uu3, vv3, h0]

/-- `Q` fixes every column constant on each group, i.e. every combination of the `e_i` (tex
    10670–10671). Kind: PROVED (helper). -/
lemma Qmat_mulVec_const {n : ℕ} (T B : Matrix (Fin n) (Fin n) (ZMod 2)) (β : Fin n → ZMod 2) :
    Qmat T B *ᵥ (fun q => β q.1) = fun q => β q.1 := by
  have hA : gA (fun q : Phys n => β q.1) = β := funext fun i => by simp only [gA]; grind
  have hB : gB (fun q : Phys n => β q.1) = 0 := funext fun i => by
    simp only [gB, Pi.zero_apply]; grind
  have hC : gC (fun q : Phys n => β q.1) = 0 := funext fun i => by
    simp only [gC, Pi.zero_apply]; grind
  funext ⟨i, k⟩
  rw [Qmat_mulVec_apply, hA, hB, hC]; simp

/-- The bilinear form of `adj Q_J = Q_J⁻¹` of the varying network on anchor and extra
columns, computed from the explicit solution `w` (tex 10709–10714). Kind: PROVED (helper). -/
lemma Qvar_form (b : ℕ) (hb : 0 < b) (ε : ZMod 2) (J : Finset (Fin b))
    (α α' : Fin b → ZMod 2) (γ γ' : ZMod 2) :
    restr J (∑ i, α i • grp i + γ • cvec b hb) ⬝ᵥ
        ((Qsub (Qvar b hb ε) J).adjugate *ᵥ restr J (∑ i, α' i • grp i + γ' • cvec b hb)) =
      (∑ j, if j ∈ J then α j * α' j else 0) +
        (if (⟨0, hb⟩ : Fin b) ∈ J then γ * γ' * aJ ε J else 0) := by
  have hsum : ∀ (β : Fin b → ZMod 2) (q : Phys b), (∑ i, β i • grp i) q = β q.1 := by
    intro β q
    rw [Finset.sum_apply, Finset.sum_eq_single q.1]
    · simp [grp]
    · intro i _ hi; simp [grp, Ne.symm hi]
    · simp
  have hc : ∀ q : Phys b, cvec b hb q = if q.1 = ⟨0, hb⟩ then vv3 q.2 else 0 := by
    intro ⟨j, k⟩
    by_cases h : j = ⟨0, hb⟩ <;> fin_cases k <;> simp [cvec, vvec, vv3, h]
  have hx : ∀ (β : Fin b → ZMod 2) (g : ZMod 2) (q : Phys b),
      (∑ i, β i • grp i + g • cvec b hb) q =
        β q.1 + g * (if q.1 = ⟨0, hb⟩ then vv3 q.2 else 0) := by
    intro β g q; rw [Pi.add_apply, hsum, Pi.smul_apply, smul_eq_mul, hc]
  let f : Phys b → ZMod 2 := fun q => if q.1 ∈ J then α' q.1 else 0
  let zz : Phys b → ZMod 2 := f + γ' • wv ε J
  have hzz_supp : ∀ q : Phys b, q.1 ∉ J → zz q = 0 := fun q hq => by
    simp [zz, f, hq, wv]
  have hsolve : Qsub (Qvar b hb ε) J *ᵥ restr J zz =
      restr J (∑ i, α' i • grp i + γ' • cvec b hb) := by
    rw [Qsub_mulVec_restr _ _ _ hzz_supp]
    funext ⟨⟨i, k⟩, hi⟩
    simp only [restr]
    have hf : Qvar b hb ε *ᵥ f = f := Qmat_mulVec_const _ _ (fun j => if j ∈ J then α' j else 0)
    rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf,
      Qvar_wv hb ε J i hi k, hx]
    simp only [f, hi, ↓reduceIte, hc]
  have hadj : (Qsub (Qvar b hb ε) J).adjugate *ᵥ
      restr J (∑ i, α' i • grp i + γ' • cvec b hb) = restr J zz := by
    rw [← hsolve, mulVec_mulVec, adjugate_mul, Qvar_det, one_smul, one_mulVec]
  rw [hadj, restr_dot _ _ _ hzz_supp, dot_eq_sum]
  have hterm : ∀ j : Fin b,
      ((∑ i, α i • grp i + γ • cvec b hb) (j, 0) * zz (j, 0) +
        (∑ i, α i • grp i + γ • cvec b hb) (j, 1) * zz (j, 1) +
        (∑ i, α i • grp i + γ • cvec b hb) (j, 2) * zz (j, 2)) =
      (if j ∈ J then α j * α' j else 0) +
        (if j = ⟨0, hb⟩ then (if (⟨0, hb⟩ : Fin b) ∈ J then γ * γ' * aJ ε J else 0) else 0) := by
    intro j
    rw [hx, hx, hx]
    simp only [zz, f, wv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hjJ : j ∈ J <;> by_cases hj0 : j = ⟨0, hb⟩
    · subst hj0
      simp only [hjJ, ↓reduceIte, uu3_0, uu3_1, uu3_2, vv3_0, vv3_1, vv3_2]
      grind
    · simp only [hjJ, hj0, ↓reduceIte, uu3_0, uu3_1, uu3_2, vv3_0, vv3_1, vv3_2]
      grind
    · subst hj0
      simp only [hjJ, ↓reduceIte, vv3_0, vv3_1, vv3_2]
      grind
    · simp only [hjJ, hj0, ↓reduceIte]
      grind
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- The change of the inverse of the varying network between `ε = 1` and `ε = 0`, on anchor
columns and the extra column `c`: zero unless every group is active, where it is `γ γ'`
(the entry `((T_J^{-1})_{b1})^2`; adjugate equals inverse since `det Q_J = 1`)
(tex 10709–10714). Kind: PROVED. -/
theorem Qvar_change (b : ℕ) (hb : 0 < b) (J : Finset (Fin b)) (α α' : Fin b → ZMod 2)
    (γ γ' : ZMod 2) :
    restr J (∑ i, α i • grp i + γ • cvec b hb) ⬝ᵥ
        ((Qsub (Qvar b hb 1) J).adjugate *ᵥ restr J (∑ i, α' i • grp i + γ' • cvec b hb)) +
      restr J (∑ i, α i • grp i + γ • cvec b hb) ⬝ᵥ
        ((Qsub (Qvar b hb 0) J).adjugate *ᵥ restr J (∑ i, α' i • grp i + γ' • cvec b hb)) =
      if J = univ then γ * γ' else 0 := by
  rw [Qvar_form, Qvar_form]
  by_cases hJ : J = univ
  · subst hJ
    simp only [aJ, ↓reduceIte, Finset.mem_univ, mul_one, mul_zero, add_zero]
    grind
  · simp only [aJ, hJ, ↓reduceIte, mul_zero, ite_self, add_zero]
    grind

end ZInQ.Manuscript.RC.Symbols
