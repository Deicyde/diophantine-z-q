import ZInQKernel.Contrib.OneProof.RC.Symbols.Core
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

/-- The prescribed symmetric matrix: bilinear matrix `I_b` on the `e_i` and `H(T,B)` on the
`u_i, v_i` (tex 10664–10669). (Helper: give the definition.) -/
noncomputable def Qmat {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) :
    Matrix (Phys b) (Phys b) (ZMod 2) := sorry

theorem Qmat_transpose {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) (hB : Bᵀ = B) :
    (Qmat T B)ᵀ = Qmat T B := sorry
theorem Qmat_mulVec_grp {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) (i : Fin b) :
    Qmat T B *ᵥ grp i = grp i := sorry
theorem Qmat_form {b : ℕ} (T B : Matrix (Fin b) (Fin b) (ZMod 2)) (i j : Fin b) :
    grp i ⬝ᵥ (Qmat T B *ᵥ grp j) = (if i = j then 1 else 0) ∧
    grp i ⬝ᵥ (Qmat T B *ᵥ uvec j) = 0 ∧ grp i ⬝ᵥ (Qmat T B *ᵥ vvec j) = 0 ∧
    uvec i ⬝ᵥ (Qmat T B *ᵥ uvec j) = 0 ∧ uvec i ⬝ᵥ (Qmat T B *ᵥ vvec j) = T i j ∧
    vvec i ⬝ᵥ (Qmat T B *ᵥ vvec j) = B i j := sorry

/-- Principal submatrix on the active groups `J`. -/
def Qsub {b : ℕ} (Q : Matrix (Phys b) (Phys b) (ZMod 2)) (J : Finset (Fin b)) :
    Matrix {p : Phys b // p.1 ∈ J} {p : Phys b // p.1 ∈ J} (ZMod 2) :=
  Q.submatrix Subtype.val Subtype.val
/-- Restriction of a column to the active groups. -/
def restr {b : ℕ} (J : Finset (Fin b)) (x : Phys b → ZMod 2) : {p : Phys b // p.1 ∈ J} → ZMod 2 :=
  fun p => x p.1

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
/-- The extra column `c`, dual to `u_1`, supported on the first group (tex 10678). -/
def cvec (b : ℕ) (hb : 0 < b) : Phys b → ZMod 2 := sorry

theorem cvec_spec (b : ℕ) (hb : 0 < b) :
    (∀ j, cvec b hb ⬝ᵥ grp j = 0) ∧ (∀ j, cvec b hb ⬝ᵥ uvec j = if j = ⟨0, hb⟩ then 1 else 0) ∧
    (∀ j, cvec b hb ⬝ᵥ vvec j = 0) ∧ (∀ p, cvec b hb p ≠ 0 → p.1 = ⟨0, hb⟩) := sorry
theorem grp_rvec {b : ℕ} (i : Fin b) : grp i ⬝ᵥ rvec b = 0 := sorry
theorem cvec_rvec (b : ℕ) (hb : 0 < b) : cvec b hb ⬝ᵥ rvec b = 1 := sorry

theorem Qsing_symm (b : ℕ) (hb : 0 < b) : (Qsing b hb)ᵀ = Qsing b hb := sorry
theorem Qsing_det_proper (b : ℕ) (hb : 0 < b) (J : Finset (Fin b)) (hJ : J ≠ univ) :
    (Qsub (Qsing b hb) J).det = 1 := sorry
theorem Qsing_adjugate (b : ℕ) (hb : 0 < b) :
    (Qsing b hb).adjugate = vecMulVec (rvec b) (rvec b) := sorry

theorem Qvar_symm (b : ℕ) (hb : 0 < b) (ε : ZMod 2) : (Qvar b hb ε)ᵀ = Qvar b hb ε := sorry
theorem Qvar_det (b : ℕ) (hb : 0 < b) (ε : ZMod 2) (J : Finset (Fin b)) :
    (Qsub (Qvar b hb ε) J).det = 1 := sorry
theorem Qvar_change (b : ℕ) (hb : 0 < b) (J : Finset (Fin b)) (α α' : Fin b → ZMod 2)
    (γ γ' : ZMod 2) :
    restr J (∑ i, α i • grp i + γ • cvec b hb) ⬝ᵥ
        ((Qsub (Qvar b hb 1) J).adjugate *ᵥ restr J (∑ i, α' i • grp i + γ' • cvec b hb)) +
      restr J (∑ i, α i • grp i + γ • cvec b hb) ⬝ᵥ
        ((Qsub (Qvar b hb 0) J).adjugate *ᵥ restr J (∑ i, α' i • grp i + γ' • cvec b hb)) =
      if J = univ then γ * γ' else 0 := sorry
end ZInQ.Manuscript.RC.Symbols
