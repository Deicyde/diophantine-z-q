import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.SelmerLink
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.DualQuasiIso

/-!
# The new-local cancellation as a quasi-isomorphism of complexes

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:limits-fixed-field-budget`, tex L5394–5454.
The support-change triangle (5.6) gives a finite free model whose graded module is
`C_old ⊕ ⊕_q Q_q` (tex 5398–5403); the block containing the local quotients has
`B₀ = A = diag(A_q)`, `T₀ = 0` in a differential `(P Q; T B)` (tex 5420–5424); "over `𝒪[G]`, cancel
`B`. The surviving Schur differential `P − QB⁻¹T` augments to `P₀`" (tex 5424–5425); the adjacent
differential is literally unchanged (tex 5440–5454).

The new local quotients sit in the two top degrees of the four-term complex: for an unramified new
place the local quotient `L_q / U_q` (lane SelmerDuality's `UnramifiedNewPlace`: `L_q` in degrees
`0, 1, 2`, `U_q` in degrees `0, 1`) lives in degrees `1, 2`, hence in degrees `2, 3` of the Selmer
complex `C^n = G^n ⊕ U^n ⊕ L^{n−1}`.

* `PreComplex S`: the pre-cancellation complex `C⁰ = E₀`, `C¹ = D¹`, `C² = D² ⊕ N`, `C³ = B₃ ⊕ N'`
  (`N, N'` the new local summands, both indexed by `N`), with differentials `c⁰`, `(X; Y)` and
  `(P Q; T B)`;
* `PreComplex.cancel`: for `B` invertible, the remaining block complex `d⁰ = c⁰`, `d¹ = X`,
  `d² = P − Q B⁻¹ T` (PROVED: `d² = 0`);
* `PreComplex.incl`: the chain map `D → C`, `x ↦ (x, −B⁻¹ T x)` in degree two, `y ↦ (y, 0)` in
  degree three, and `incl_quasiIso`: it is a quasi-isomorphism (PROVED: it is degreewise split
  injective with cokernel the disk `N --B--> N`, which is acyclic; lane SelmerDuality's
  `quasiIso_τ₁`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (GAcyclic acyclic_toCC_iff quasiIso_of_acyclic
  quasiIso_τ₁ idGHom toCC_idGHom)

/-- **The pre-cancellation complex** (tex 5398–5425): old summands in block form and the new local
summands `N` in degrees two and three, with differential `(P Q; T B)` from `D² ⊕ N` to `B₃ ⊕ N`. -/
structure PreComplex (S : Type) [CommRing S] where
  m0 : ℕ
  m1 : ℕ
  m2 : ℕ
  /-- the index of the new local summands -/
  N : Type
  [fN : Fintype N]
  [dN : DecidableEq N]
  c0 : Matrix (Fin m0 ⊕ Unit ⊕ Fin m1) (Fin m0) S
  X : Matrix (Fin m1 ⊕ Unit ⊕ Fin m2) (Fin m0 ⊕ Unit ⊕ Fin m1) S
  Y : Matrix N (Fin m0 ⊕ Unit ⊕ Fin m1) S
  P : Matrix (Fin m2) (Fin m1 ⊕ Unit ⊕ Fin m2) S
  Q : Matrix (Fin m2) N S
  T : Matrix N (Fin m1 ⊕ Unit ⊕ Fin m2) S
  /-- the new local block -/
  B : Matrix N N S
  c1_c0 : fromRows X Y * c0 = 0
  c2_c1 : fromBlocks P Q T B * fromRows X Y = 0

attribute [instance] PreComplex.fN PreComplex.dN

namespace PreComplex

variable {S : Type} [CommRing S] (C : PreComplex S)

theorem X_c0 : C.X * C.c0 = 0 := by
  have h := C.c1_c0
  rw [fromRows_mul, ← fromRows_zero] at h
  exact (fromRows_inj h).1

theorem PX_QY : C.P * C.X + C.Q * C.Y = 0 := by
  have h := C.c2_c1
  rw [fromBlocks_mul_fromRows, ← fromRows_zero] at h
  exact (fromRows_inj h).1

theorem TX_BY : C.T * C.X + C.B * C.Y = 0 := by
  have h := C.c2_c1
  rw [fromBlocks_mul_fromRows, ← fromRows_zero] at h
  exact (fromRows_inj h).2

variable {C}

theorem Y_eq (hB : IsUnit C.B.det) : C.Y = -(C.B⁻¹ * C.T * C.X) := by
  have h2 : C.B⁻¹ * C.B = 1 := nonsing_inv_mul _ hB
  have h := congrArg (C.B⁻¹ * ·) C.TX_BY
  simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc, h2, Matrix.one_mul] at h
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h

variable (C)

/-- **The remaining complex after cancelling `B`** (tex 5424–5425, 5440–5454): `d⁰ = c⁰`, `d¹ = X`
(the adjacent differential is unchanged), `d² = P − Q B⁻¹ T`. -/
def cancel (hB : IsUnit C.B.det) : BlockComplex S where
  m0 := C.m0
  m1 := C.m1
  m2 := C.m2
  d0 := C.c0
  d1 := C.X
  d2 := C.P - C.Q * C.B⁻¹ * C.T
  d1_d0 := C.X_c0
  d2_d1 := by
    have h : (C.P - C.Q * C.B⁻¹ * C.T) * C.X = C.P * C.X + C.Q * (-(C.B⁻¹ * C.T * C.X)) := by
      rw [Matrix.sub_mul, Matrix.mul_neg, sub_eq_add_neg]
      simp only [Matrix.mul_assoc]
    rw [h, ← Y_eq hB]
    exact C.PX_QY

/-! ### The pre-cancellation complex and the disk as `GCx` -/

/-- The basis index of `C^n`. -/
def idx : ℤ → Type
  | 0 => Fin C.m0
  | 1 => Fin C.m0 ⊕ Unit ⊕ Fin C.m1
  | 2 => (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) ⊕ C.N
  | 3 => Fin C.m2 ⊕ C.N
  | _ => Empty

/-- The differentials of `C`. -/
def ddL : (i : ℤ) → (C.idx i → S) →ₗ[S] (C.idx (i + 1) → S)
  | 0 => C.c0.mulVecLin
  | 1 => (fromRows C.X C.Y).mulVecLin
  | 2 => (fromBlocks C.P C.Q C.T C.B).mulVecLin
  | _ => 0

theorem ddL_ddL (i : ℤ) (x : C.idx i → S) : C.ddL (i + 1) (C.ddL i x) = 0 := by
  match i with
  | 0 =>
    have h : ∀ y : Fin C.m0 → S, (fromRows C.X C.Y).mulVec (C.c0.mulVec y) = 0 := fun y => by
      rw [Matrix.mulVec_mulVec, C.c1_c0, Matrix.zero_mulVec]
    exact h x
  | 1 =>
    have h : ∀ y : Fin C.m0 ⊕ Unit ⊕ Fin C.m1 → S,
        (fromBlocks C.P C.Q C.T C.B).mulVec ((fromRows C.X C.Y).mulVec y) = 0 := fun y => by
      rw [Matrix.mulVec_mulVec, C.c2_c1, Matrix.zero_mulVec]
    exact h x
  | 2 => rfl
  | Int.ofNat (n + 3) => rfl
  | Int.negSucc n =>
    change C.ddL (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- **The pre-cancellation complex as a `GCx`.** -/
def toGCx : GCx S where
  X n := ModuleCat.of S (C.idx n → S)
  d i j h := by subst h; exact C.ddL i
  d_d i j k hij hjk x := by
    subst hij hjk
    exact C.ddL_ddL i x

/-- The basis index of the disk `N --B--> N` in degrees two and three. -/
def kidx : ℤ → Type
  | 2 => C.N
  | 3 => C.N
  | _ => Empty

theorem isEmpty_kidx (j : ℤ) (h2 : j ≠ 2) (h3 : j ≠ 3) : IsEmpty (C.kidx j) := by
  match j with
  | 2 => exact absurd rfl h2
  | 3 => exact absurd rfl h3
  | 0 => exact (inferInstance : IsEmpty Empty)
  | 1 => exact (inferInstance : IsEmpty Empty)
  | Int.ofNat (n + 4) => exact (inferInstance : IsEmpty Empty)
  | Int.negSucc n => exact (inferInstance : IsEmpty Empty)

/-- The differential of the disk. -/
def kdL : (i : ℤ) → (C.kidx i → S) →ₗ[S] (C.kidx (i + 1) → S)
  | 2 => C.B.mulVecLin
  | _ => 0

theorem kdL_kdL (i : ℤ) (x : C.kidx i → S) : C.kdL (i + 1) (C.kdL i x) = 0 := by
  match i with
  | 2 => rfl
  | 0 => exact map_zero _
  | 1 => exact map_zero _
  | Int.ofNat (n + 3) => exact map_zero _
  | Int.negSucc n => exact map_zero _

/-- **The disk `N --B--> N`** (degrees two and three). -/
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
  | 1 =>
    -- `x ∈ N` in degree two with `B x = 0`
    have key : ∀ y : C.N → S, C.B.mulVec y = 0 → y = 0 := fun y hy => by
      have h2 : C.B⁻¹ * C.B = 1 := nonsing_inv_mul _ hB
      calc y = (C.B⁻¹ * C.B).mulVec y := by rw [h2, Matrix.one_mulVec]
        _ = 0 := by rw [← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero]
    refine ⟨0, ?_⟩
    rw [map_zero]
    exact (key x hx).symm
  | 2 =>
    have key : ∀ y : C.N → S, C.B.mulVec (C.B⁻¹.mulVec y) = y := fun y => by
      rw [Matrix.mulVec_mulVec, mul_nonsing_inv _ hB, Matrix.one_mulVec]
    exact ⟨C.B⁻¹.mulVec x, key x⟩
  | 0 =>
    have := C.isEmpty_kidx 1 (by omega) (by omega)
    exact ⟨0, Subsingleton.elim (α := C.kidx 1 → S) _ _⟩
  | Int.ofNat (n + 3) =>
    have := C.isEmpty_kidx (n + 4) (by omega) (by omega)
    exact ⟨0, Subsingleton.elim (α := C.kidx (n + 4) → S) _ _⟩
  | Int.negSucc n =>
    have := C.isEmpty_kidx (Int.negSucc n + 1) (by omega) (by omega)
    exact ⟨0, Subsingleton.elim (α := C.kidx (Int.negSucc n + 1) → S) _ _⟩

/-! ### The inclusion of the remaining complex and the projection to the disk -/

variable {C}

/-- The components of the inclusion `D → C`. -/
def inc (hB : IsUnit C.B.det) : (i : ℤ) → ((C.cancel hB).idx i → S) →ₗ[S] (C.idx i → S)
  | 0 => LinearMap.id
  | 1 => LinearMap.id
  | 2 => (fromRows (1 : Matrix (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)
      (-(C.B⁻¹ * C.T))).mulVecLin
  | 3 => (fromRows (1 : Matrix (Fin C.m2) (Fin C.m2) S) (0 : Matrix C.N (Fin C.m2) S)).mulVecLin
  | _ => 0

theorem inc_comm (hB : IsUnit C.B.det) (i : ℤ) (x : (C.cancel hB).idx i → S) :
    inc hB (i + 1) ((C.cancel hB).ddL i x) = C.ddL i (inc hB i x) := by
  match i with
  | 0 => rfl
  | 1 =>
    have hM : fromRows (1 : Matrix (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)
        (-(C.B⁻¹ * C.T)) * C.X = fromRows C.X C.Y := by
      rw [fromRows_mul, Matrix.one_mul, Y_eq hB, Matrix.neg_mul]
    have h : ∀ y : Fin C.m0 ⊕ Unit ⊕ Fin C.m1 → S,
        (fromRows (1 : Matrix (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)
          (-(C.B⁻¹ * C.T))).mulVec (C.X.mulVec y) = (fromRows C.X C.Y).mulVec y := fun y => by
      rw [Matrix.mulVec_mulVec, hM]
    exact h x
  | 2 =>
    have h1 : C.B * C.B⁻¹ = 1 := mul_nonsing_inv _ hB
    have hM : fromRows (1 : Matrix (Fin C.m2) (Fin C.m2) S) (0 : Matrix C.N (Fin C.m2) S) *
          (C.P - C.Q * C.B⁻¹ * C.T) =
        fromBlocks C.P C.Q C.T C.B *
          fromRows (1 : Matrix (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)
            (-(C.B⁻¹ * C.T)) := by
      rw [fromRows_mul, fromBlocks_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one,
        Matrix.mul_one, Matrix.mul_neg, Matrix.mul_neg, ← Matrix.mul_assoc C.B C.B⁻¹ C.T, h1,
        Matrix.one_mul, add_neg_cancel, ← sub_eq_add_neg, Matrix.mul_assoc C.Q]
    have h : ∀ y : Fin C.m1 ⊕ Unit ⊕ Fin C.m2 → S,
        (fromRows (1 : Matrix (Fin C.m2) (Fin C.m2) S) (0 : Matrix C.N (Fin C.m2) S)).mulVec
          ((C.P - C.Q * C.B⁻¹ * C.T).mulVec y) =
        (fromBlocks C.P C.Q C.T C.B).mulVec
          ((fromRows (1 : Matrix (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)
            (-(C.B⁻¹ * C.T))).mulVec y) := fun y => by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
    exact h x
  | 3 => rfl
  | Int.ofNat (n + 4) => rfl
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
  | 2 => (fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S)).mulVecLin
  | 3 => (fromCols (0 : Matrix C.N (Fin C.m2) S) (1 : Matrix C.N C.N S)).mulVecLin
  | _ => 0

theorem proj_comm (hB : IsUnit C.B.det) (i : ℤ) (x : C.idx i → S) :
    proj hB (i + 1) (C.ddL i x) = C.kdL i (proj hB i x) := by
  match i with
  | 0 => rfl
  | 1 =>
    have hM : fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S) * fromRows C.X C.Y = 0 := by
      rw [fromCols_mul_fromRows, Matrix.one_mul, Y_eq hB, Matrix.mul_assoc, add_neg_cancel]
    have h : ∀ y : Fin C.m0 ⊕ Unit ⊕ Fin C.m1 → S,
        (fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S)).mulVec ((fromRows C.X C.Y).mulVec y) =
          0 := fun y => by
      rw [Matrix.mulVec_mulVec, hM, Matrix.zero_mulVec]
    exact h x
  | 2 =>
    have h1 : C.B * C.B⁻¹ = 1 := mul_nonsing_inv _ hB
    have hM : fromCols (0 : Matrix C.N (Fin C.m2) S) (1 : Matrix C.N C.N S) *
          fromBlocks C.P C.Q C.T C.B = C.B * fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S) := by
      rw [fromCols_mul_fromBlocks, mul_fromCols, Matrix.zero_mul, Matrix.zero_mul, zero_add,
        zero_add, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc, h1,
        Matrix.one_mul]
    have h : ∀ y : (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) ⊕ C.N → S,
        (fromCols (0 : Matrix C.N (Fin C.m2) S) (1 : Matrix C.N C.N S)).mulVec
          ((fromBlocks C.P C.Q C.T C.B).mulVec y) =
        C.B.mulVec ((fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S)).mulVec y) := fun y => by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
    exact h x
  | 3 => rfl
  | Int.ofNat (n + 4) => rfl
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
    | 2 =>
      have hM : fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S) *
          fromRows (1 : Matrix (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)
            (-(C.B⁻¹ * C.T)) = 0 := by
        rw [fromCols_mul_fromRows, Matrix.mul_one, Matrix.one_mul, add_neg_cancel]
      have h : ∀ y : Fin C.m1 ⊕ Unit ⊕ Fin C.m2 → S,
          (fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S)).mulVec
            ((fromRows (1 : Matrix (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)
              (-(C.B⁻¹ * C.T))).mulVec y) = 0 := fun y => by
        rw [Matrix.mulVec_mulVec, hM, Matrix.zero_mulVec]
      exact h x
    | 3 =>
      have hM : fromCols (0 : Matrix C.N (Fin C.m2) S) (1 : Matrix C.N C.N S) *
          fromRows (1 : Matrix (Fin C.m2) (Fin C.m2) S) (0 : Matrix C.N (Fin C.m2) S) = 0 := by
        rw [fromCols_mul_fromRows, Matrix.zero_mul, Matrix.one_mul, add_zero]
      have h : ∀ y : Fin C.m2 → S,
          (fromCols (0 : Matrix C.N (Fin C.m2) S) (1 : Matrix C.N C.N S)).mulVec
            ((fromRows (1 : Matrix (Fin C.m2) (Fin C.m2) S)
              (0 : Matrix C.N (Fin C.m2) S)).mulVec y) = 0 := fun y => by
        rw [Matrix.mulVec_mulVec, hM, Matrix.zero_mulVec]
      exact h x
    | 0 => rfl
    | 1 => rfl
    | Int.ofNat (n + 4) => rfl
    | Int.negSucc n => rfl)

/-! ### Degreewise exactness -/

theorem comp_inl_fromRows_mulVec {m₁ m₂ n : Type} [Fintype n] (A₁ : Matrix m₁ n S)
    (A₂ : Matrix m₂ n S) (v : n → S) : (fromRows A₁ A₂).mulVec v ∘ Sum.inl = A₁.mulVec v := by
  rw [fromRows_mulVec, Sum.elim_comp_inl]

theorem exact₂ (c : (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) ⊕ C.N → S)
    (hc : (fromCols (C.B⁻¹ * C.T) (1 : Matrix C.N C.N S)).mulVec c = 0) :
    (fromRows (1 : Matrix (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)
      (-(C.B⁻¹ * C.T))).mulVec (c ∘ Sum.inl) = c := by
  rw [fromCols_mulVec, Matrix.one_mulVec] at hc
  have h' : c ∘ Sum.inr = -((C.B⁻¹ * C.T).mulVec (c ∘ Sum.inl)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hc
  rw [fromRows_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, ← h']
  exact Sum.elim_comp_inl_inr c

theorem exact₃ (c : Fin C.m2 ⊕ C.N → S)
    (hc : (fromCols (0 : Matrix C.N (Fin C.m2) S) (1 : Matrix C.N C.N S)).mulVec c = 0) :
    (fromRows (1 : Matrix (Fin C.m2) (Fin C.m2) S) (0 : Matrix C.N (Fin C.m2) S)).mulVec
      (c ∘ Sum.inl) = c := by
  rw [fromCols_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec, zero_add] at hc
  rw [fromRows_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec, ← hc]
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
    | 1 => exact ⟨c, rfl⟩
    | 2 => exact ⟨c ∘ Sum.inl, exact₂ c hc⟩
    | 3 => exact ⟨c ∘ Sum.inl, exact₃ c hc⟩
    | Int.ofNat (n + 4) => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩
    | Int.negSucc n => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩
  · rw [ModuleCat.mono_iff_injective]
    intro a b h
    change inc hB i a = inc hB i b at h
    match i with
    | 0 => exact h
    | 1 => exact h
    | 2 => exact inj_fromRows_one (m := Fin C.m1 ⊕ Unit ⊕ Fin C.m2) (-(C.B⁻¹ * C.T)) a b h
    | 3 => exact inj_fromRows_one (m := Fin C.m2) (0 : Matrix C.N (Fin C.m2) S) a b h
    | Int.ofNat (n + 4) => exact Subsingleton.elim (α := Empty → S) _ _
    | Int.negSucc n => exact Subsingleton.elim (α := Empty → S) _ _
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    change ∃ c, proj hB i c = y
    match i with
    | 2 => exact ⟨Sum.elim 0 y, surj_fromCols_one (C.B⁻¹ * C.T) y⟩
    | 3 => exact ⟨Sum.elim 0 y, surj_fromCols_one (0 : Matrix C.N (Fin C.m2) S) y⟩
    | 0 => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩
    | 1 => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩
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
acyclic disk `N --B--> N` (tex 5424–5425, 5440–5454). -/
theorem incl_quasiIso (hB : IsUnit C.B.det) : QuasiIso (GHom.toCC (incl hB)) := by
  have h₂ : QuasiIso (cancelSESHom hB).τ₂ := by
    change QuasiIso (GHom.toCC (idGHom C.toGCx))
    rw [toCC_idGHom]
    infer_instance
  have h₃ : QuasiIso (cancelSESHom hB).τ₃ :=
    quasiIso_of_acyclic _ ((acyclic_toCC_iff _).2 (C.disk_acyclic hB))
      ((acyclic_toCC_iff _).2 zeroGCx_acyclic)
  exact quasiIso_τ₁ (cancelSESHom hB) (cancelSES_shortExact hB) idSES_shortExact h₂ h₃

end PreComplex

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
