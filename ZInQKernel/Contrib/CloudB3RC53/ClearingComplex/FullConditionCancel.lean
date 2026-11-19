import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.SelmerLink
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.DualQuasiIso

/-!
# The full-condition model: the new singular blocks in degrees one and two

Manuscript `diophantine_zq.tex`, the actual support comparisons (tex 3479–3498), the triangle (5.6)
(tex 5234–5238) and the proof of Lemma `ex:limits-fixed-field-budget` (tex 5394–5454).

Replacing the unramified condition by the full condition at a new place adds the singular
quotient `[Φ_q − q]` **in degrees one and two** (tex 3479–3481: "the singular quotient `[Φ−q]` in
degrees one and two"; tex 5320–5322: `Q_{r_i,w} = [ℤ₂² --(Φ_{r_i}−r_i)--> ℤ₂²]` "in degrees one and
two"). Changing the condition `U_ur → U_full` in `Cone(G ⊕ U → L)[−1]` puts the quotient in the same
degrees as `U_full / U_ur`; it is not shifted. The graded model of (5.6) is `C_old ⊕ ⊕_q Q_q`
with an upper triangular differential (tex 5398–5403); the block containing the local quotients is
`(P Q; T B)` with `B₀ = A = diag(A_q)`, `T₀ = 0` (tex 5420–5424), and it is the differential **out
of degree one**.

* `FullPreComplex S`: `C⁰ = E₀`, `C¹ = D¹ ⊕ N`, `C² = D² ⊕ N`, `C³ = B₃` (`D¹ = B₁ ⊕ H₁ ⊕ E₁`,
  `D² = B₂ ⊕ H₂ ⊕ E₂` as in `BlockComplex`; `N` the new singular summands, possibly empty), with
  differentials `d⁰ = (c⁰; Y)`, `d¹ = (P Q; T B)`, `d² = (U V)`;
* `FullPreComplex.cancel`: for `B` invertible, the remaining block complex `d⁰ = c⁰`,
  `d¹ = P − Q B⁻¹ T` (the surviving Schur differential, tex 5424–5425), `d² = U`: the adjacent
  differentials are literally unchanged (tex 5440–5454: in the new coordinates `(X, B⁻¹TX + Y) =
  (X, 0)` and `(U, UQB⁻¹ + V) = (U, 0)`); PROVED (`d² = 0` both times);
* `FullPreComplex.incl`, `incl_quasiIso`: the inclusion `D → C` (`x ↦ (x, −B⁻¹Tx)` in degree one,
  `y ↦ (y, 0)` in degree two) is a quasi-isomorphism (PROVED: it is degreewise split injective with
  cokernel the disk `N --B--> N` in degrees one and two, which is acyclic).

All statements are PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (GAcyclic acyclic_toCC_iff quasiIso_of_acyclic
  quasiIso_τ₁ idGHom toCC_idGHom)

/-- **The full-condition pre-cancellation complex** (tex 5398–5424): the old block complex with
the new singular summands `N` in degrees one and two. -/
structure FullPreComplex (S : Type) [CommRing S] where
  m0 : ℕ
  m1 : ℕ
  m2 : ℕ
  /-- the index of the new singular summands (empty when `Q = ∅`) -/
  N : Type
  [fN : Fintype N]
  [dN : DecidableEq N]
  c0 : Matrix (Fin m0 ⊕ Unit ⊕ Fin m1) (Fin m0) S
  Y : Matrix N (Fin m0) S
  P : Matrix (Fin m1 ⊕ Unit ⊕ Fin m2) (Fin m0 ⊕ Unit ⊕ Fin m1) S
  Q : Matrix (Fin m1 ⊕ Unit ⊕ Fin m2) N S
  T : Matrix N (Fin m0 ⊕ Unit ⊕ Fin m1) S
  /-- the new singular block, from degree one to degree two -/
  B : Matrix N N S
  U : Matrix (Fin m2) (Fin m1 ⊕ Unit ⊕ Fin m2) S
  V : Matrix (Fin m2) N S
  c1_c0 : fromBlocks P Q T B * fromRows c0 Y = 0
  c2_c1 : fromCols U V * fromBlocks P Q T B = 0

attribute [instance] FullPreComplex.fN FullPreComplex.dN

namespace FullPreComplex

variable {S : Type} [CommRing S] (C : FullPreComplex S)

abbrev D1 : Type := Fin C.m0 ⊕ Unit ⊕ Fin C.m1
abbrev D2 : Type := Fin C.m1 ⊕ Unit ⊕ Fin C.m2

theorem Pc0_QY : C.P * C.c0 + C.Q * C.Y = 0 := by
  have h := C.c1_c0
  rw [fromBlocks_mul_fromRows, ← fromRows_zero] at h
  exact (fromRows_inj h).1

theorem Tc0_BY : C.T * C.c0 + C.B * C.Y = 0 := by
  have h := C.c1_c0
  rw [fromBlocks_mul_fromRows, ← fromRows_zero] at h
  exact (fromRows_inj h).2

theorem UP_VT : C.U * C.P + C.V * C.T = 0 := by
  have h := C.c2_c1
  rw [fromCols_mul_fromBlocks, ← fromCols_zero] at h
  exact (fromCols_inj h).1

theorem UQ_VB : C.U * C.Q + C.V * C.B = 0 := by
  have h := C.c2_c1
  rw [fromCols_mul_fromBlocks, ← fromCols_zero] at h
  exact (fromCols_inj h).2

variable {C}

theorem Y_eq (hB : IsUnit C.B.det) : C.Y = -(C.B⁻¹ * C.T * C.c0) := by
  have h2 : C.B⁻¹ * C.B = 1 := nonsing_inv_mul _ hB
  have h := congrArg (C.B⁻¹ * ·) C.Tc0_BY
  simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc, h2, Matrix.one_mul] at h
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h

theorem V_eq (hB : IsUnit C.B.det) : C.V = -(C.U * C.Q * C.B⁻¹) := by
  have h2 : C.B * C.B⁻¹ = 1 := mul_nonsing_inv _ hB
  have h := congrArg (· * C.B⁻¹) C.UQ_VB
  simp only [Matrix.add_mul, Matrix.zero_mul, Matrix.mul_assoc, h2, Matrix.mul_one] at h
  rw [eq_neg_iff_add_eq_zero, add_comm, Matrix.mul_assoc]
  exact h

variable (C)

/-- **The remaining complex after cancelling `B`** (tex 5424–5425, 5440–5454): `d⁰ = c⁰`,
`d¹ = P − Q B⁻¹ T`, `d² = U`. -/
def cancel (hB : IsUnit C.B.det) : BlockComplex S where
  m0 := C.m0
  m1 := C.m1
  m2 := C.m2
  d0 := C.c0
  d1 := C.P - C.Q * C.B⁻¹ * C.T
  d2 := C.U
  d1_d0 := by
    have h : (C.P - C.Q * C.B⁻¹ * C.T) * C.c0 = C.P * C.c0 + C.Q * (-(C.B⁻¹ * C.T * C.c0)) := by
      rw [Matrix.sub_mul, Matrix.mul_neg, sub_eq_add_neg]
      simp only [Matrix.mul_assoc]
    rw [h, ← Y_eq hB]
    exact C.Pc0_QY
  d2_d1 := by
    have h : C.U * (C.P - C.Q * C.B⁻¹ * C.T) = C.U * C.P + (-(C.U * C.Q * C.B⁻¹)) * C.T := by
      rw [Matrix.mul_sub, Matrix.neg_mul, sub_eq_add_neg]
      simp only [Matrix.mul_assoc]
    rw [h, ← V_eq hB]
    exact C.UP_VT

/-! ### The pre-cancellation complex and the disk as `GCx` -/

/-- The basis index of `C^n`. -/
def idx : ℤ → Type
  | 0 => Fin C.m0
  | 1 => (Fin C.m0 ⊕ Unit ⊕ Fin C.m1) ⊕ C.N
  | 2 => (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) ⊕ C.N
  | 3 => Fin C.m2
  | _ => Empty

/-- The differentials of `C`. -/
def ddL : (i : ℤ) → (C.idx i → S) →ₗ[S] (C.idx (i + 1) → S)
  | 0 => (fromRows C.c0 C.Y).mulVecLin
  | 1 => (fromBlocks C.P C.Q C.T C.B).mulVecLin
  | 2 => (fromCols C.U C.V).mulVecLin
  | _ => 0

theorem ddL_ddL (i : ℤ) (x : C.idx i → S) : C.ddL (i + 1) (C.ddL i x) = 0 := by
  match i with
  | 0 =>
    have h : ∀ y : Fin C.m0 → S,
        (fromBlocks C.P C.Q C.T C.B).mulVec ((fromRows C.c0 C.Y).mulVec y) = 0 := fun y => by
      rw [Matrix.mulVec_mulVec, C.c1_c0, Matrix.zero_mulVec]
    exact h x
  | 1 =>
    have h : ∀ y : (Fin C.m0 ⊕ Unit ⊕ Fin C.m1) ⊕ C.N → S,
        (fromCols C.U C.V).mulVec ((fromBlocks C.P C.Q C.T C.B).mulVec y) = 0 := fun y => by
      rw [Matrix.mulVec_mulVec, C.c2_c1, Matrix.zero_mulVec]
    exact h x
  | 2 => rfl
  | Int.ofNat (n + 3) => rfl
  | Int.negSucc n =>
    change C.ddL (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- **The full-condition pre-cancellation complex as a `GCx`.** -/
def toGCx : GCx S where
  X n := ModuleCat.of S (C.idx n → S)
  d i j h := by subst h; exact C.ddL i
  d_d i j k hij hjk x := by
    subst hij hjk
    exact C.ddL_ddL i x

/-- The basis index of the disk `N --B--> N` in degrees one and two. -/
def kidx : ℤ → Type
  | 1 => C.N
  | 2 => C.N
  | _ => Empty

theorem isEmpty_kidx (j : ℤ) (h1 : j ≠ 1) (h2 : j ≠ 2) : IsEmpty (C.kidx j) := by
  match j with
  | 1 => exact absurd rfl h1
  | 2 => exact absurd rfl h2
  | 0 => exact (inferInstance : IsEmpty Empty)
  | Int.ofNat (n + 3) => exact (inferInstance : IsEmpty Empty)
  | Int.negSucc n => exact (inferInstance : IsEmpty Empty)

/-- The differential of the disk. -/
def kdL : (i : ℤ) → (C.kidx i → S) →ₗ[S] (C.kidx (i + 1) → S)
  | 1 => C.B.mulVecLin
  | _ => 0

theorem kdL_kdL (i : ℤ) (x : C.kidx i → S) : C.kdL (i + 1) (C.kdL i x) = 0 := by
  match i with
  | 1 => rfl
  | 0 => exact map_zero _
  | Int.ofNat (n + 2) => exact map_zero _
  | Int.negSucc n => exact map_zero _

/-- **The singular disk `N --B--> N`** (degrees one and two). -/
def disk : GCx S where
  X n := ModuleCat.of S (C.kidx n → S)
  d i j h := by subst h; exact C.kdL i
  d_d i j k hij hjk x := by
    subst hij hjk
    exact C.kdL_kdL i x

/-- **The disk is acyclic** when `B` is invertible. -/
theorem disk_acyclic (hB : IsUnit C.B.det) : GAcyclic C.disk := by
  intro i j k hij hjk x hx
  subst hij hjk
  match i with
  | 0 =>
    -- `x ∈ N` in degree one with `B x = 0`
    have key : ∀ y : C.N → S, C.B.mulVec y = 0 → y = 0 := fun y hy => by
      have h2 : C.B⁻¹ * C.B = 1 := nonsing_inv_mul _ hB
      calc y = (C.B⁻¹ * C.B).mulVec y := by rw [h2, Matrix.one_mulVec]
        _ = 0 := by rw [← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero]
    refine ⟨0, ?_⟩
    rw [map_zero]
    exact (key x hx).symm
  | 1 =>
    have key : ∀ y : C.N → S, C.B.mulVec (C.B⁻¹.mulVec y) = y := fun y => by
      rw [Matrix.mulVec_mulVec, mul_nonsing_inv _ hB, Matrix.one_mulVec]
    exact ⟨C.B⁻¹.mulVec x, key x⟩
  | Int.ofNat (n + 2) =>
    have := C.isEmpty_kidx (n + 3) (by omega) (by omega)
    exact ⟨0, Subsingleton.elim (α := C.kidx (n + 3) → S) _ _⟩
  | Int.negSucc 0 =>
    have := C.isEmpty_kidx (Int.negSucc 0 + 1) (by omega) (by omega)
    exact ⟨0, Subsingleton.elim (α := C.kidx (Int.negSucc 0 + 1) → S) _ _⟩
  | Int.negSucc (n + 1) =>
    have := C.isEmpty_kidx (Int.negSucc (n + 1) + 1) (by omega) (by omega)
    exact ⟨0, Subsingleton.elim (α := C.kidx (Int.negSucc (n + 1) + 1) → S) _ _⟩

/-! ### The inclusion of the remaining complex and the projection to the disk -/

variable {C}

/-- The components of the inclusion `D → C`. -/
def inc (hB : IsUnit C.B.det) : (i : ℤ) → ((C.cancel hB).idx i → S) →ₗ[S] (C.idx i → S)
  | 0 => LinearMap.id
  | 1 => (fromRows (1 : Matrix C.D1 C.D1 S) (-(C.B⁻¹ * C.T))).mulVecLin
  | 2 => (fromRows (1 : Matrix C.D2 C.D2 S) (0 : Matrix C.N C.D2 S)).mulVecLin
  | 3 => LinearMap.id
  | _ => 0

theorem inc_comm (hB : IsUnit C.B.det) (i : ℤ) (x : (C.cancel hB).idx i → S) :
    inc hB (i + 1) ((C.cancel hB).ddL i x) = C.ddL i (inc hB i x) := by
  match i with
  | 0 =>
    have hM : fromRows (1 : Matrix C.D1 C.D1 S) (-(C.B⁻¹ * C.T)) * C.c0 = fromRows C.c0 C.Y := by
      rw [fromRows_mul, Matrix.one_mul, Y_eq hB, Matrix.neg_mul]
    have h : ∀ y : Fin C.m0 → S,
        (fromRows (1 : Matrix C.D1 C.D1 S) (-(C.B⁻¹ * C.T))).mulVec (C.c0.mulVec y) =
          (fromRows C.c0 C.Y).mulVec y := fun y => by
      rw [Matrix.mulVec_mulVec, hM]
    exact h x
  | 1 =>
    have h1 : C.B * C.B⁻¹ = 1 := mul_nonsing_inv _ hB
    have hM : fromRows (1 : Matrix C.D2 C.D2 S) (0 : Matrix C.N C.D2 S) *
          (C.P - C.Q * C.B⁻¹ * C.T) =
        fromBlocks C.P C.Q C.T C.B * fromRows (1 : Matrix C.D1 C.D1 S) (-(C.B⁻¹ * C.T)) := by
      rw [fromRows_mul, fromBlocks_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one,
        Matrix.mul_one, Matrix.mul_neg, Matrix.mul_neg, ← Matrix.mul_assoc C.B C.B⁻¹ C.T, h1,
        Matrix.one_mul, add_neg_cancel, ← sub_eq_add_neg, Matrix.mul_assoc C.Q]
    have h : ∀ y : C.D1 → S,
        (fromRows (1 : Matrix C.D2 C.D2 S) (0 : Matrix C.N C.D2 S)).mulVec
          ((C.P - C.Q * C.B⁻¹ * C.T).mulVec y) =
        (fromBlocks C.P C.Q C.T C.B).mulVec
          ((fromRows (1 : Matrix C.D1 C.D1 S) (-(C.B⁻¹ * C.T))).mulVec y) := fun y => by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
    exact h x
  | 2 =>
    have hM : fromCols C.U C.V * fromRows (1 : Matrix C.D2 C.D2 S) (0 : Matrix C.N C.D2 S) =
        C.U := by
      rw [fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
    have h : ∀ y : C.D2 → S, C.U.mulVec y =
        (fromCols C.U C.V).mulVec
          ((fromRows (1 : Matrix C.D2 C.D2 S) (0 : Matrix C.N C.D2 S)).mulVec y) := fun y => by
      rw [Matrix.mulVec_mulVec, hM]
    exact h x
  | Int.ofNat (n + 3) => rfl
  | Int.negSucc n =>
    change inc hB (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- **The inclusion `D → C` of the remaining complex** (a chain map). -/
def incl (hB : IsUnit C.B.det) : GHom (C.cancel hB).toGCx C.toGCx where
  f i j h := by subst h; exact inc hB i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact inc_comm hB i x

/-- The components of the projection `C → disk`. -/
def proj (_hB : IsUnit C.B.det) : (i : ℤ) → (C.idx i → S) →ₗ[S] (C.kidx i → S)
  | 1 => (fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S)).mulVecLin
  | 2 => (fromCols (0 : Matrix C.N C.D2 S) (1 : Matrix C.N C.N S)).mulVecLin
  | _ => 0

theorem proj_comm (hB : IsUnit C.B.det) (i : ℤ) (x : C.idx i → S) :
    proj hB (i + 1) (C.ddL i x) = C.kdL i (proj hB i x) := by
  match i with
  | 0 =>
    have hM : fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S) * fromRows C.c0 C.Y = 0 := by
      rw [fromCols_mul_fromRows, Matrix.one_mul, Y_eq hB, Matrix.mul_assoc, add_neg_cancel]
    have h : ∀ y : Fin C.m0 → S,
        (fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S)).mulVec ((fromRows C.c0 C.Y).mulVec y) =
          0 := fun y => by
      rw [Matrix.mulVec_mulVec, hM, Matrix.zero_mulVec]
    exact h x
  | 1 =>
    have h1 : C.B * C.B⁻¹ = 1 := mul_nonsing_inv _ hB
    have hM : fromCols (0 : Matrix C.N C.D2 S) (1 : Matrix C.N C.N S) *
          fromBlocks C.P C.Q C.T C.B = C.B * fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S) := by
      rw [fromCols_mul_fromBlocks, mul_fromCols, Matrix.zero_mul, Matrix.zero_mul, zero_add,
        zero_add, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc, h1,
        Matrix.one_mul]
    have h : ∀ y : C.D1 ⊕ C.N → S,
        (fromCols (0 : Matrix C.N C.D2 S) (1 : Matrix C.N C.N S)).mulVec
          ((fromBlocks C.P C.Q C.T C.B).mulVec y) =
        C.B.mulVec ((fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S)).mulVec y) := fun y => by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
    exact h x
  | 2 => rfl
  | Int.ofNat (n + 3) => rfl
  | Int.negSucc n =>
    change proj hB (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- **The projection `C → disk`** (a chain map). -/
def projH (hB : IsUnit C.B.det) : GHom C.toGCx C.disk where
  f i j h := by subst h; exact proj hB i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact proj_comm hB i x

/-! ### The short exact sequence `0 → D → C → disk → 0` -/

open SelmerDuality in
/-- The short complex `D → C → disk`. -/
def cancelSES (hB : IsUnit C.B.det) : ShortComplex (CochainComplex (ModuleCat.{0} S) ℤ) :=
  ShortComplex.mk (GHom.toCC (incl hB)) (GHom.toCC (projH hB)) (by
    ext i x
    change proj hB i (inc hB i x) = 0
    match i with
    | 1 =>
      have hM : fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S) *
          fromRows (1 : Matrix C.D1 C.D1 S) (-(C.B⁻¹ * C.T)) = 0 := by
        rw [fromCols_mul_fromRows, Matrix.mul_one, Matrix.one_mul, add_neg_cancel]
      have h : ∀ y : C.D1 → S,
          (fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S)).mulVec
            ((fromRows (1 : Matrix C.D1 C.D1 S) (-(C.B⁻¹ * C.T))).mulVec y) = 0 := fun y => by
        rw [Matrix.mulVec_mulVec, hM, Matrix.zero_mulVec]
      exact h x
    | 2 =>
      have hM : fromCols (0 : Matrix C.N C.D2 S) (1 : Matrix C.N C.N S) *
          fromRows (1 : Matrix C.D2 C.D2 S) (0 : Matrix C.N C.D2 S) = 0 := by
        rw [fromCols_mul_fromRows, Matrix.zero_mul, Matrix.one_mul, add_zero]
      have h : ∀ y : C.D2 → S,
          (fromCols (0 : Matrix C.N C.D2 S) (1 : Matrix C.N C.N S)).mulVec
            ((fromRows (1 : Matrix C.D2 C.D2 S) (0 : Matrix C.N C.D2 S)).mulVec y) = 0 :=
        fun y => by rw [Matrix.mulVec_mulVec, hM, Matrix.zero_mulVec]
      exact h x
    | 0 => rfl
    | 3 => rfl
    | Int.ofNat (n + 4) => rfl
    | Int.negSucc n => rfl)

/-! ### Degreewise exactness -/

theorem comp_inl_fromRows_mulVec {m₁ m₂ n : Type} [Fintype n] (A₁ : Matrix m₁ n S)
    (A₂ : Matrix m₂ n S) (v : n → S) : (fromRows A₁ A₂).mulVec v ∘ Sum.inl = A₁.mulVec v := by
  rw [fromRows_mulVec, Sum.elim_comp_inl]

theorem exact_fromCols_one {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix n m S) (c : m ⊕ n → S)
    (hc : (fromCols M (1 : Matrix n n S)).mulVec c = 0) :
    (fromRows (1 : Matrix m m S) (-M)).mulVec (c ∘ Sum.inl) = c := by
  rw [fromCols_mulVec, Matrix.one_mulVec] at hc
  have h' : c ∘ Sum.inr = -(M.mulVec (c ∘ Sum.inl)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hc
  rw [fromRows_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, ← h']
  exact Sum.elim_comp_inl_inr c

theorem inj_fromRows_one {m n : Type} [Fintype m] [DecidableEq m] (M : Matrix n m S) (a b : m → S)
    (h : (fromRows (1 : Matrix m m S) M).mulVec a = (fromRows (1 : Matrix m m S) M).mulVec b) :
    a = b := by
  have h' := congrArg (· ∘ Sum.inl) h
  rwa [comp_inl_fromRows_mulVec, comp_inl_fromRows_mulVec, Matrix.one_mulVec,
    Matrix.one_mulVec] at h'

theorem surj_fromCols_one {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (M : Matrix n m S)
    (y : n → S) : (fromCols M (1 : Matrix n n S)).mulVec (Sum.elim 0 y) = y := by
  rw [fromCols_mulVec_sumElim, Matrix.mulVec_zero, Matrix.one_mulVec, zero_add]

open SelmerDuality in
theorem cancelSES_shortExact (hB : IsUnit C.B.det) : (cancelSES hB).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro c hc
    change proj hB i c = 0 at hc
    change ∃ a, inc hB i a = c
    match i with
    | 0 => exact ⟨c, rfl⟩
    | 1 => exact ⟨c ∘ Sum.inl, exact_fromCols_one (C.B⁻¹ * C.T) c hc⟩
    | 2 =>
      refine ⟨c ∘ Sum.inl, ?_⟩
      have h := exact_fromCols_one (0 : Matrix C.N C.D2 S) c hc
      rwa [neg_zero] at h
    | 3 => exact ⟨c, rfl⟩
    | Int.ofNat (n + 4) => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩
    | Int.negSucc n => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩
  · rw [ModuleCat.mono_iff_injective]
    intro a b h
    change inc hB i a = inc hB i b at h
    match i with
    | 0 => exact h
    | 1 => exact inj_fromRows_one (m := C.D1) (-(C.B⁻¹ * C.T)) a b h
    | 2 => exact inj_fromRows_one (m := C.D2) (0 : Matrix C.N C.D2 S) a b h
    | 3 => exact h
    | Int.ofNat (n + 4) => exact Subsingleton.elim (α := Empty → S) _ _
    | Int.negSucc n => exact Subsingleton.elim (α := Empty → S) _ _
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    change ∃ c, proj hB i c = y
    match i with
    | 1 => exact ⟨Sum.elim 0 y, surj_fromCols_one (C.B⁻¹ * C.T) y⟩
    | 2 => exact ⟨Sum.elim 0 y, surj_fromCols_one (0 : Matrix C.N C.D2 S) y⟩
    | 0 => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩
    | 3 => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩
    | Int.ofNat (n + 4) => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩
    | Int.negSucc n => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩

/-! ### The comparison sequence `C → C → 0` and the quasi-isomorphism -/

open SelmerDuality in
/-- The short complex `C --id--> C → 0`. -/
def idSES : ShortComplex (CochainComplex (ModuleCat.{0} S) ℤ) :=
  ShortComplex.mk (GHom.toCC (idGHom C.toGCx))
    (GHom.toCC (ClearingComplex.zeroGHom C.toGCx (zeroGCx S))) (by ext i x; rfl)

open SelmerDuality in
theorem idSES_shortExact : (idSES (C := C)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro c _
    exact ⟨c, rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    intro a b h
    exact h
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    exact ⟨0, rfl⟩

open SelmerDuality in
/-- The morphism of sequences `(incl, id, 0)`. -/
def cancelSESHom (hB : IsUnit C.B.det) : cancelSES hB ⟶ idSES (C := C) where
  τ₁ := GHom.toCC (incl hB)
  τ₂ := GHom.toCC (idGHom C.toGCx)
  τ₃ := GHom.toCC (ClearingComplex.zeroGHom C.disk (zeroGCx S))
  comm₁₂ := by ext i x; rfl
  comm₂₃ := by ext i x; rfl

theorem zeroGCx_acyclic : GAcyclic (zeroGCx S) := fun _ _ _ _ _ _ _ => ⟨0, rfl⟩

open SelmerDuality in
/-- **The inclusion of the remaining complex is a quasi-isomorphism** (PROVED): the cokernel is the
acyclic disk `N --B--> N` in degrees one and two (tex 5424–5425, 5440–5454). -/
theorem incl_quasiIso (hB : IsUnit C.B.det) : QuasiIso (GHom.toCC (incl hB)) := by
  have h₂ : QuasiIso (cancelSESHom hB).τ₂ := by
    change QuasiIso (GHom.toCC (idGHom C.toGCx))
    rw [toCC_idGHom]
    infer_instance
  have h₃ : QuasiIso (cancelSESHom hB).τ₃ :=
    quasiIso_of_acyclic _ ((acyclic_toCC_iff _).2 (C.disk_acyclic hB))
      ((acyclic_toCC_iff _).2 zeroGCx_acyclic)
  exact quasiIso_τ₁ (cancelSESHom hB) (cancelSES_shortExact hB) idSES_shortExact h₂ h₃

end FullPreComplex

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
