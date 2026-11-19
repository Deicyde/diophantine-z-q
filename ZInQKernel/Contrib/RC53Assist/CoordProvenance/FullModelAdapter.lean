import ZInQKernel.Contrib.CloudB3RC53.CoordLink.E1aG
import ZInQKernel.Contrib.CloudB3RC53.Torsion.ConeCoord

/-!
# The full-condition model in the legacy coordinate shape

A singular disk in degrees one and two contributes the inverse determinant.
After localization its four-term model can be put in the legacy shape by
adjoining an inverse disk in degrees two and three.  The class and functional
are transported through the same remaining complex; no scalar rescaling is
inserted.  The retained original coordinate is thereby preserved.

The finite coefficient and local Frobenius data of the two identification
records are not interchangeable.  The inverse-disk construction below is a
localized graded model adapter, not an integral identification record.

The locators are the full-condition triangle, TeX 3479–3481 and 5398–5403,
and ex:limits-fixed-field-clearing, TeX 5509–5516 and 5586–5617.
The preliminary full-condition definitions and proofs are reproduced from
the existing mathematical development so this single file is self-contained.
No new printed proposition is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53






























noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (GAcyclic acyclic_toCC_iff quasiIso_of_acyclic
  quasiIso_τ₁ idGHom toCC_idGHom)



structure FullPreComplex (S : Type) [CommRing S] where
  m0 : ℕ
  m1 : ℕ
  m2 : ℕ
  
  N : Type
  [fN : Fintype N]
  [dN : DecidableEq N]
  c0 : Matrix (Fin m0 ⊕ Unit ⊕ Fin m1) (Fin m0) S
  Y : Matrix N (Fin m0) S
  P : Matrix (Fin m1 ⊕ Unit ⊕ Fin m2) (Fin m0 ⊕ Unit ⊕ Fin m1) S
  Q : Matrix (Fin m1 ⊕ Unit ⊕ Fin m2) N S
  T : Matrix N (Fin m0 ⊕ Unit ⊕ Fin m1) S
  
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



abbrev cancel (hB : IsUnit C.B.det) : BlockComplex S where
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




def idx : ℤ → Type
  | 0 => Fin C.m0
  | 1 => (Fin C.m0 ⊕ Unit ⊕ Fin C.m1) ⊕ C.N
  | 2 => (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) ⊕ C.N
  | 3 => Fin C.m2
  | _ => Empty


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


def toGCx : GCx S where
  X n := ModuleCat.of S (C.idx n → S)
  d i j h := by subst h; exact C.ddL i
  d_d i j k hij hjk x := by
    subst hij hjk
    exact C.ddL_ddL i x


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


def kdL : (i : ℤ) → (C.kidx i → S) →ₗ[S] (C.kidx (i + 1) → S)
  | 1 => C.B.mulVecLin
  | _ => 0

theorem kdL_kdL (i : ℤ) (x : C.kidx i → S) : C.kdL (i + 1) (C.kdL i x) = 0 := by
  match i with
  | 1 => rfl
  | 0 => exact map_zero _
  | Int.ofNat (n + 2) => exact map_zero _
  | Int.negSucc n => exact map_zero _


def disk : GCx S where
  X n := ModuleCat.of S (C.kidx n → S)
  d i j h := by subst h; exact C.kdL i
  d_d i j k hij hjk x := by
    subst hij hjk
    exact C.kdL_kdL i x


theorem disk_acyclic (hB : IsUnit C.B.det) : GAcyclic C.disk := by
  intro i j k hij hjk x hx
  subst hij hjk
  match i with
  | 0 =>
    
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



variable {C}


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


def incl (hB : IsUnit C.B.det) : GHom (C.cancel hB).toGCx C.toGCx where
  f i j h := by subst h; exact inc hB i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact inc_comm hB i x


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


def projH (hB : IsUnit C.B.det) : GHom C.toGCx C.disk where
  f i j h := by subst h; exact proj hB i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact proj_comm hB i x



open SelmerDuality in

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



open SelmerDuality in

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

def cancelSESHom (hB : IsUnit C.B.det) : cancelSES hB ⟶ idSES (C := C) where
  τ₁ := GHom.toCC (incl hB)
  τ₂ := GHom.toCC (idGHom C.toGCx)
  τ₃ := GHom.toCC (ClearingComplex.zeroGHom C.disk (zeroGCx S))
  comm₁₂ := by ext i x; rfl
  comm₂₃ := by ext i x; rfl

theorem zeroGCx_acyclic : GAcyclic (zeroGCx S) := fun _ _ _ _ _ _ _ => ⟨0, rfl⟩

open SelmerDuality in


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

end ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport
noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

namespace FullPreComplex

variable {S S' : Type} [CommRing S] [CommRing S']


def map (C : FullPreComplex S) (f : S →+* S') : FullPreComplex S' where
  m0 := C.m0
  m1 := C.m1
  m2 := C.m2
  N := C.N
  c0 := C.c0.map f
  Y := C.Y.map f
  P := C.P.map f
  Q := C.Q.map f
  T := C.T.map f
  B := C.B.map f
  U := C.U.map f
  V := C.V.map f
  c1_c0 := by
    rw [← fromRows_map, ← fromBlocks_map, ← Matrix.map_mul, C.c1_c0,
      Matrix.map_zero _ (map_zero f)]
  c2_c1 := by
    rw [← fromCols_map, ← fromBlocks_map, ← Matrix.map_mul, C.c2_c1,
      Matrix.map_zero _ (map_zero f)]

theorem map_Y_zero (C : FullPreComplex S) (f : S →+* S') (h : C.Y = 0) : (C.map f).Y = 0 := by
  change C.Y.map f = 0
  rw [h, Matrix.map_zero _ (map_zero f)]

theorem map_T_zero (C : FullPreComplex S) (f : S →+* S') (h : C.T = 0) : (C.map f).T = 0 := by
  change C.T.map f = 0
  rw [h, Matrix.map_zero _ (map_zero f)]

variable (C : FullPreComplex S)



def old (hY : C.Y = 0) (hT : C.T = 0) : BlockComplex S where
  m0 := C.m0
  m1 := C.m1
  m2 := C.m2
  d0 := C.c0
  d1 := C.P
  d2 := C.U
  d1_d0 := by
    have h := C.Pc0_QY
    rwa [hY, Matrix.mul_zero, add_zero] at h
  d2_d1 := by
    have h := C.UP_VT
    rwa [hT, Matrix.mul_zero, add_zero] at h

end FullPreComplex
end ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport























noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.CoordLink (eEp)

namespace FullPreComplex

variable {R : Type} [CommRing R] (C : FullPreComplex R)


def toFour : FourCx R (Fin C.m0) (C.D1 ⊕ C.N) (C.D2 ⊕ C.N) (Fin C.m2) where
  d0 := fromRows C.c0 C.Y
  d1 := fromBlocks C.P C.Q C.T C.B
  d2 := fromCols C.U C.V
  d10 := C.c1_c0
  d21 := C.c2_c1

variable {C} (hB : IsUnit C.B.det)

include hB in

theorem hz_full {z : C.D1 ⊕ C.N → R} (hz : C.toFour.d1 *ᵥ z = 0) :
    (C.cancel hB).d1 *ᵥ (z ∘ Sum.inl) = 0 := by
  have h1 : C.P *ᵥ (z ∘ Sum.inl) + C.Q *ᵥ (z ∘ Sum.inr) = 0 := by
    have h := congrArg (· ∘ Sum.inl) hz
    simp only [toFour] at h
    rw [← Sum.elim_comp_inl_inr z, fromBlocks_mulVec] at h
    simpa using h
  have h2 : C.T *ᵥ (z ∘ Sum.inl) + C.B *ᵥ (z ∘ Sum.inr) = 0 := by
    have h := congrArg (· ∘ Sum.inr) hz
    simp only [toFour] at h
    rw [← Sum.elim_comp_inl_inr z, fromBlocks_mulVec] at h
    simpa using h
  have hN : z ∘ Sum.inr = -((C.B⁻¹ * C.T) *ᵥ (z ∘ Sum.inl)) := by
    have e : C.B *ᵥ (z ∘ Sum.inr) = -(C.T *ᵥ (z ∘ Sum.inl)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2
    have e2 := congrArg (C.B⁻¹ *ᵥ ·) e
    simp only [mulVec_mulVec, nonsing_inv_mul _ hB, one_mulVec, mulVec_neg] at e2
    exact e2
  change (C.P - C.Q * C.B⁻¹ * C.T) *ᵥ (z ∘ Sum.inl) = 0
  rw [hN, mulVec_neg, mulVec_mulVec, ← sub_eq_add_neg] at h1
  rw [sub_mulVec, Matrix.mul_assoc]
  exact h1

include hB in

theorem hlam_full {lam : C.D2 ⊕ C.N → R} (hlam : lam ᵥ* C.toFour.d1 = 0) :
    (lam ∘ Sum.inl) ᵥ* (C.cancel hB).d1 = 0 := by
  have hsplit : lam ᵥ* fromBlocks C.P C.Q C.T C.B =
      Sum.elim ((lam ∘ Sum.inl) ᵥ* C.P + (lam ∘ Sum.inr) ᵥ* C.T)
        ((lam ∘ Sum.inl) ᵥ* C.Q + (lam ∘ Sum.inr) ᵥ* C.B) := by
    rw [← Sum.elim_comp_inl_inr lam, vecMul_fromBlocks]
  have h : lam ᵥ* fromBlocks C.P C.Q C.T C.B = 0 := hlam
  rw [hsplit] at h
  have h1 : (lam ∘ Sum.inl) ᵥ* C.P + (lam ∘ Sum.inr) ᵥ* C.T = 0 := by
    have := congrArg (· ∘ Sum.inl) h
    simpa using this
  have h2 : (lam ∘ Sum.inl) ᵥ* C.Q + (lam ∘ Sum.inr) ᵥ* C.B = 0 := by
    have := congrArg (· ∘ Sum.inr) h
    simpa using this
  have hN : lam ∘ Sum.inr = -((lam ∘ Sum.inl) ᵥ* (C.Q * C.B⁻¹)) := by
    have e : (lam ∘ Sum.inr) ᵥ* C.B = -((lam ∘ Sum.inl) ᵥ* C.Q) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2
    have e2 := congrArg (· ᵥ* C.B⁻¹) e
    simp only [vecMul_vecMul, mul_nonsing_inv _ hB, vecMul_one, neg_vecMul] at e2
    exact e2
  change (lam ∘ Sum.inl) ᵥ* (C.P - C.Q * C.B⁻¹ * C.T) = 0
  rw [hN, neg_vecMul, vecMul_vecMul, ← sub_eq_add_neg] at h1
  rw [vecMul_sub]
  exact h1

end FullPreComplex



section Relabel

variable (m0 m1 m2 : ℕ) (N : Type)


def eOf : ((Fin m0 ⊕ Unit ⊕ Fin m1) ⊕ N) ⊕ (Fin m2 ⊕ Unit) ≃
    ((Fin m0 ⊕ Unit ⊕ Fin m1) ⊕ (Fin m2 ⊕ Unit)) ⊕ N where
  toFun
    | .inl (.inl c) => .inl (.inl c)
    | .inl (.inr n) => .inr n
    | .inr b => .inl (.inr b)
  invFun
    | .inl (.inl c) => .inl (.inl c)
    | .inl (.inr b) => .inr b
    | .inr n => .inl (.inr n)
  left_inv := by rintro ((c | n) | b) <;> rfl
  right_inv := by rintro ((c | b) | n) <;> rfl



def σFull : (Fin m0 ⊕ Unit) ⊕ ((Fin m1 ⊕ Unit ⊕ Fin m2) ⊕ N) ≃
    ((Fin m0 ⊕ Unit ⊕ Fin m1) ⊕ N) ⊕ (Fin m2 ⊕ Unit) :=
  (eEp m0 m1 m2 N).trans (((σBlock m0 m1 m2).sumCongr (Equiv.refl N)).trans
    (eOf m0 m1 m2 N).symm)

end Relabel



section Cancel

variable {K : Type} [Field K] {C : FullPreComplex K} (hB : IsUnit C.B.det)
  (z : C.D1 ⊕ C.N → K) (lam : C.D2 ⊕ C.N → K) (hz : C.toFour.d1 *ᵥ z = 0)
  (hlam : lam ᵥ* C.toFour.d1 = 0)


def Xf : BasedCx K (((Fin C.m0 ⊕ Unit) ⊕ C.D2) ⊕ C.N) ((C.D1 ⊕ (Fin C.m2 ⊕ Unit)) ⊕ C.N) :=
  (C.toFour.aug z lam hz hlam).toBased.reindex (eEp C.m0 C.m1 C.m2 C.N)
    (eOf C.m0 C.m1 C.m2 C.N)

theorem Xf_degO (n : C.N) : (Xf z lam hz hlam).degO (Sum.inr n) = 1 := rfl
theorem Xf_degE (n : C.N) : (Xf z lam hz hlam).degE (Sum.inr n) = 1 + 1 := rfl

theorem Xf_blk : (Xf z lam hz hlam).dEO.toBlocks₂₂ = C.B := by
  ext n m; rfl

variable {z lam hz hlam}

include hB in
theorem Xf_hA : IsUnit ((Xf z lam hz hlam).dEO.toBlocks₂₂).det := by
  rw [Xf_blk]; exact hB



theorem schurO_Xf :
    schurO (Xf z lam hz hlam) 1 (Xf_degO z lam hz hlam) (Xf_degE z lam hz hlam) (Xf_hA hB) =
      ((C.cancel hB).toFour.aug (z ∘ Sum.inl) (lam ∘ Sum.inl)
        (FullPreComplex.hz_full hB hz) (FullPreComplex.hlam_full hB hlam)).toBased := by
  apply BasedCx.ext'
  · funext x; rcases x with (a | a) | d <;> rfl
  · funext x; rcases x with c | (b | u) <;> rfl
  · ext i j
    rcases i with c | (b | u) <;> rcases j with (a | a) | d <;> rfl
  · change (Xf z lam hz hlam).dEO.toBlocks₁₁ - (Xf z lam hz hlam).dEO.toBlocks₁₂ *
        ((Xf z lam hz hlam).dEO.toBlocks₂₂)⁻¹ * (Xf z lam hz hlam).dEO.toBlocks₂₁ = _
    rw [Xf_blk]
    ext i j
    rcases i with (a | a) | d <;> rcases j with c | (b | u)
    all_goals first
      | rfl
      | (simp [Xf, BasedCx.reindex, FourCx.toBased_dEO, FourCx.aug, eEp, eOf, mul_apply,
          toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, FullPreComplex.toFour])




theorem kmCoord_fullCancel :
    kmCoord C.toFour z lam hz hlam (σFull C.m0 C.m1 C.m2 C.N) =
      (C.B.det)⁻¹ * kmCoord (C.cancel hB).toFour (z ∘ Sum.inl) (lam ∘ Sum.inl)
        (FullPreComplex.hz_full hB hz) (FullPreComplex.hlam_full hB hlam)
        (σBlock C.m0 C.m1 C.m2) := by
  unfold kmCoord
  have t0 : torsion (Xf z lam hz hlam) ((σBlock C.m0 C.m1 C.m2).sumCongr (Equiv.refl _)) =
      torsion (C.toFour.aug z lam hz hlam).toBased (σFull C.m0 C.m1 C.m2 C.N) := by
    have := torsion_reindex' (C.toFour.aug z lam hz hlam).toBased
      (σFull C.m0 C.m1 C.m2 C.N) (eEp C.m0 C.m1 C.m2 C.N) (eOf C.m0 C.m1 C.m2 C.N)
    rw [σFull, transport_eq] at this
    exact this
  have t1 := torsion_cancelO (Xf z lam hz hlam) 1 (Xf_degO z lam hz hlam)
    (Xf_degE z lam hz hlam) odd_one (Xf_hA hB) (σBlock C.m0 C.m1 C.m2)
  rw [← t0, t1, schurO_Xf hB, Xf_blk, mul_comm, mul_neg]

end Cancel

end ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport
namespace ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport
open Matrix
open ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup aug sgnChar)
variable {b : ℕ}


theorem isUnit_B_full {Qn ιn : Type} [Fintype Qn] [DecidableEq Qn] [Fintype ιn] [DecidableEq ιn]
    (A : Qn → Matrix ιn ιn Lam) (dq : Qn → ℕ) (hd : ∀ q, dq q ≤ 4) (v : Qn → Lamˣ) (w : Qn → Lam)
    (hdet : ∀ q, (A q).det = (PowerSeries.X : Lam) ^ dq q * (v q : Lam) + 2 * w q)
    (C : FullPreComplex (MonoidAlgebra Lam (SignGroup b))) (eN : C.N ≃ ιn × Qn)
    (hB0 : (C.B.submatrix eN.symm eN.symm).map aug = Matrix.blockDiagonal A) :
    IsUnit (C.map (φO b)).B.det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  refine Determinant.matrix_isUnit_of_isUnit_aug Determinant.isUnit_one_add_two_mul_OO
    Determinant.signGroup_mul_self _ ?_
  change IsUnit ((C.B.map (φO b)).map aug).det
  have h0 := (Determinant.newLocal_family_pole_genuine A dq hd v w hdet
    (C.B.submatrix eN.symm eN.symm) hB0 (sgnChar 0) 0).1
  have e : ((C.B.submatrix eN.symm eN.symm).map (Determinant.signEval (sgnChar 0))).map
      (algebraMap Lam OO) = ((C.B.map (φO b)).map aug).submatrix eN.symm eN.symm := by
    refine Matrix.ext fun i j => ?_
    change algebraMap Lam OO (Determinant.signEval (sgnChar 0) (C.B _ _)) = aug (φO b (C.B _ _))
    rw [Determinant.signEval_sgnChar_zero, aug_φO]
  rw [e, Matrix.det_submatrix_equiv_self] at h0
  exact h0




structure FullCore (Qn : Type) [Fintype Qn] [DecidableEq Qn] (b : ℕ) (dK hK cE tK : ℕ) where
  
  ιn : Type
  [fι : Fintype ιn]
  [dι : DecidableEq ιn]
  
  A : Qn → Matrix ιn ιn Lam
  dq : Qn → ℕ
  hd : ∀ q, dq q ≤ 4
  v : Qn → Lamˣ
  w : Qn → Lam
  hdet : ∀ q, (A q).det = (PowerSeries.X : Lam) ^ dq q * (v q : Lam) + 2 * w q
  
  C : FullPreComplex (MonoidAlgebra Lam (SignGroup b))
  eN : C.N ≃ ιn × Qn
  hB0 : (C.B.submatrix eN.symm eN.symm).map aug = Matrix.blockDiagonal A
  hT0 : C.T.map (augR b) = 0
  hY0 : C.Y.map (augR b) = 0
  s : (i : ℕ) → Fin (((C.map (augR b)).old hY0 hT0).mi i) → ℤ_[2]
  s_ne : ∀ i j, s i j ≠ 0
  central_full :
    ((C.map (augR b)).old hY0 hT0).d0.map PowerSeries.constantCoeff =
        (smithForm C.m0 C.m1 C.m2 (s 0) (s 1) (s 2)).d0 ∧
      ((C.map (augR b)).old hY0 hT0).d1.map PowerSeries.constantCoeff =
        (smithForm C.m0 C.m1 C.m2 (s 0) (s 1) (s 2)).d1 ∧
      ((C.map (augR b)).old hY0 hT0).d2.map PowerSeries.constantCoeff =
        (smithForm C.m0 C.m1 C.m2 (s 0) (s 1) (s 2)).d2
  budget : BudgetInputsAt (((C.map (φO b)).cancel (isUnit_B_full A dq hd v w hdet C eN hB0)).toSmithBlocks
    (O := OO) ((C.map (augR b)).old hY0 hT0).Ai s s_ne (central_of_full _ s central_full))
    fr₀ dK hK cE tK

namespace FullCore

attribute [instance] fι dι

variable {Qn : Type} [Fintype Qn] [DecidableEq Qn] {dK hK cE tK : ℕ}
  (M : FullCore Qn b dK hK cE tK)

theorem isUnit_B : IsUnit (M.C.map (φO b)).B.det :=
  isUnit_B_full M.A M.dq M.hd M.v M.w M.hdet M.C M.eN M.hB0


def D : BlockComplex (MonoidAlgebra OO (SignGroup b)) :=
  (M.C.map (φO b)).cancel M.isUnit_B


abbrev oldC : BlockComplex Lam := (M.C.map (augR b)).old M.hY0 M.hT0


abbrev Bsub : Matrix (M.ιn × Qn) (M.ιn × Qn)
    (MonoidAlgebra Lam (SignGroup b)) :=
  M.C.B.submatrix M.eN.symm M.eN.symm

theorem d1_map_aug : M.D.d1.map (augS b) = (M.C.P.map (augR b)).map (algebraMap Lam OO) := by
  change (M.C.P.map (φO b) - M.C.Q.map (φO b) * (M.C.B.map (φO b))⁻¹ *
    M.C.T.map (φO b)).map (augS b) = _
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, map_φO_aug, map_φO_aug M.C.T,
    M.hT0, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, sub_zero]

theorem aug_eq (i : ℕ) :
    (M.D.Ai i).map aug = (M.oldC.Ai i).map (algebraMap Lam OO) := by
  match i with
  | 0 => exact Matrix.ext fun j k => aug_φO (M.C.c0 (Sum.inl j) k)
  | 1 =>
    exact Matrix.ext fun j k =>
      congrArg (fun N : Matrix _ _ OO => N (Sum.inl j) (Sum.inr (Sum.inr k))) M.d1_map_aug
  | 2 => exact Matrix.ext fun j k => aug_φO (M.C.U j (Sum.inr (Sum.inr k)))
  | _ + 3 => exact Matrix.ext fun j => j.elim0



theorem poles1 : IsNewLocalSchur (b := b) fun x => M.D.d1.map (Determinant.signEval (sgnChar x)) := by
  refine ⟨Qn, M.ιn, inferInstance, inferInstance, inferInstance, inferInstance, M.A,
    M.dq, M.hd, M.v, M.w, M.hdet, M.Bsub, M.hB0, Fin M.D.m1 ⊕ Unit ⊕ Fin M.D.m2,
    Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1, inferInstance, inferInstance, M.C.P,
    M.C.Q.submatrix id M.eN.symm, M.C.T.submatrix M.eN.symm id, 1, 1, fun x => ?_⟩
  set f := (Determinant.signEval (O := OO) (sgnChar x)).toRingHom
  have hB : IsUnit (M.C.B.map (φO b)).det := M.isUnit_B
  have h1 : M.D.d1.map (Determinant.signEval (sgnChar x)) =
      (M.C.P.map (φO b) - M.C.Q.map (φO b) * (M.C.B.map (φO b))⁻¹ *
        M.C.T.map (φO b)).map f := rfl
  set Px := (M.C.P.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  set Qx := (M.C.Q.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  set Bx := (M.C.B.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  set Tx := (M.C.T.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  have hL : M.D.d1.map (Determinant.signEval (sgnChar x)) = Px - Qx * Bx⁻¹ * Tx := by
    rw [h1, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul,
      map_inv_of_isUnit f _ hB]
    change (M.C.P.map (φO b)).map (Determinant.signEval (sgnChar x)) -
        (M.C.Q.map (φO b)).map (Determinant.signEval (sgnChar x)) *
          ((M.C.B.map (φO b)).map (Determinant.signEval (sgnChar x)))⁻¹ *
          (M.C.T.map (φO b)).map (Determinant.signEval (sgnChar x)) = _
    rw [map_φO_signEval, map_φO_signEval, map_φO_signEval, map_φO_signEval]
  have hR : (1 : Matrix (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) Lam).map
        (algebraMap Lam OO) *
      (Px - (Qx.submatrix id M.eN.symm) * (Bx.submatrix M.eN.symm M.eN.symm)⁻¹ *
        (Tx.submatrix M.eN.symm id)) *
      (1 : Matrix (Fin M.C.m0 ⊕ Unit ⊕ Fin M.C.m1) (Fin M.C.m0 ⊕ Unit ⊕ Fin M.C.m1) Lam).map
        (algebraMap Lam OO) = Px - Qx * Bx⁻¹ * Tx := by
    rw [Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
  exact hL.trans hR.symm



def toIdentification : Identification b dK hK cE tK where
  D := M.D
  A0 := M.oldC.Ai
  s := M.s
  s_ne := M.s_ne
  central := central_of_full _ M.s M.central_full
  aug_eq := M.aug_eq
  poles0 := Identification2.isNewLocalSchur_lam M.C.c0
  poles1 := M.poles1
  poles2 := Identification2.isNewLocalSchur_lam M.C.U
  budget := budgetInputs_of_at M.budget

end FullCore
end ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter

open Matrix CategoryTheory
open ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport
open ZInQ.Contrib.CloudB3RC53.CoordLink
open ZInQ.Contrib.CloudB3RC53.Torsion

variable {K : Type} [Field K]

/-- The localized legacy shape uses the inverse disk, not the same
Frobenius disk shifted to different degrees.  The remaining complex is unchanged. -/
abbrev inverseDiskLegacy (C : FullPreComplex K) (hB : IsUnit C.B.det) : PreComplex K where
  m0 := C.m0
  m1 := C.m1
  m2 := C.m2
  N := C.N
  c0 := C.c0
  X := (C.cancel hB).d1
  Y := 0
  P := C.U
  Q := 0
  T := 0
  B := C.B⁻¹
  c1_c0 := by
    rw [fromRows_mul, Matrix.zero_mul, (C.cancel hB).d1_d0, fromRows_zero]
  c2_c1 := by
    rw [fromBlocks_mul_fromRows]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]
    rw [(C.cancel hB).d2_d1, fromRows_zero]

/-- The localized inverse disk is invertible. -/
theorem inverseDiskLegacy_unit (C : FullPreComplex K) (hB : IsUnit C.B.det) :
    IsUnit (inverseDiskLegacy C hB).B.det := by
  change IsUnit (C.B⁻¹).det
  rw [det_nonsing_inv]
  exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul (show Ring.inverse C.B.det * C.B.det ≠ 0 from
    by rw [Ring.inverse_mul_cancel _ hB]; exact one_ne_zero))

/-- Both graded shapes have exactly the same remaining differentials. -/
theorem inverseDiskLegacy_cancel (C : FullPreComplex K) (hB : IsUnit C.B.det) :
    ((inverseDiskLegacy C hB).cancel (inverseDiskLegacy_unit C hB)).toFour = (C.cancel hB).toFour := by
  refine FourCx.ext' (C := ((inverseDiskLegacy C hB).cancel (inverseDiskLegacy_unit C hB)).toFour)
    (C' := (C.cancel hB).toFour) rfl rfl ?_
  simp [PreComplex.cancel, inverseDiskLegacy, FullPreComplex.cancel, BlockComplex.toFour]

/-- The source-to-target chain map transports the same actual class through
the full-condition Schur projection. -/
def fullToLegacy (C : FullPreComplex K) (hB : IsUnit C.B.det) :
    FourMap C.toFour (PreComplex'.toFour (inverseDiskLegacy C hB)) where
  f0 := 1
  f1 := fromCols 1 0
  f2 := fromBlocks 1 (-(C.Q * C.B⁻¹)) 0 0
  f3 := fromRows 1 0
  c0 := by
    change C.c0 * 1 = fromCols 1 0 * fromRows C.c0 C.Y
    rw [fromCols_mul_fromRows]
    simp
  c1 := by
    change fromRows (C.P - C.Q * C.B⁻¹ * C.T) 0 * fromCols 1 0 =
      fromBlocks 1 (-(C.Q * C.B⁻¹)) 0 0 * fromBlocks C.P C.Q C.T C.B
    rw [fromRows_mul_fromCols, fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, Matrix.neg_mul, Matrix.mul_assoc]
    rw [nonsing_inv_mul _ hB, Matrix.mul_one, sub_eq_add_neg, add_neg_cancel]
  c2 := by
    change fromBlocks C.U 0 0 C.B⁻¹ * fromBlocks 1 (-(C.Q * C.B⁻¹)) 0 0 =
      fromRows 1 0 * fromCols C.U C.V
    rw [fromBlocks_multiply, fromRows_mul_fromCols]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      Matrix.mul_neg, neg_zero]
    rw [C.V_eq hB, Matrix.mul_assoc]

/-- The full-condition cycle is transported by the original degree-one
projection, with no independent class selected. -/
theorem fullToLegacy_class (C : FullPreComplex K) (hB : IsUnit C.B.det) (z : C.D1 ⊕ C.N → K) :
    (fullToLegacy C hB).f1 *ᵥ z = z ∘ Sum.inl := by
  change fromCols 1 0 *ᵥ z = z ∘ Sum.inl
  rw [fromCols_mulVec]
  simp

/-- The full-condition functional restricts to the same paired functional
in the remaining complex; its inverse-disk extension is zero. -/
def legacyFunctional (C : FullPreComplex K) (lam : C.D2 ⊕ C.N → K) : C.D2 ⊕ C.N → K :=
  Sum.elim (lam ∘ Sum.inl) 0

/-- The actual closed functional satisfies the pullback along the constructed
Schur projection, not an arbitrary scalar normalization. -/
theorem fullToLegacy_functional (C : FullPreComplex K) (hB : IsUnit C.B.det)
    (lam : C.D2 ⊕ C.N → K) (hlam : lam ᵥ* C.toFour.d1 = 0) :
    legacyFunctional C lam ᵥ* (fullToLegacy C hB).f2 = lam := by
  have h0 : (lam ∘ Sum.inl) ᵥ* C.Q + (lam ∘ Sum.inr) ᵥ* C.B = 0 := by
    have h := congrArg (· ∘ Sum.inr) hlam
    change (lam ᵥ* fromBlocks C.P C.Q C.T C.B) ∘ Sum.inr =
      (0 : C.D1 ⊕ C.N → K) ∘ Sum.inr at h
    rw [← Sum.elim_comp_inl_inr lam, vecMul_fromBlocks] at h
    exact h
  have hN : lam ∘ Sum.inr = -((lam ∘ Sum.inl) ᵥ* (C.Q * C.B⁻¹)) := by
    have h := congrArg (· ᵥ* C.B⁻¹) h0
    rw [add_vecMul, vecMul_vecMul, vecMul_vecMul, mul_nonsing_inv _ hB, vecMul_one, zero_vecMul] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h
  change Sum.elim (lam ∘ Sum.inl) 0 ᵥ* fromBlocks 1 (-(C.Q * C.B⁻¹)) 0 0 = lam
  rw [vecMul_fromBlocks]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, vecMul_one, vecMul_zero, add_zero, vecMul_neg]
  rw [← hN]
  exact Sum.elim_comp_inl_inr lam

/-- The same functional is closed on the inverse-disk legacy model. -/
theorem legacyFunctional_closed (C : FullPreComplex K) (hB : IsUnit C.B.det)
    (lam : C.D2 ⊕ C.N → K) (hlam : lam ᵥ* C.toFour.d1 = 0) :
    legacyFunctional C lam ᵥ* (PreComplex'.toFour (inverseDiskLegacy C hB)).d1 = 0 := by
  change Sum.elim (lam ∘ Sum.inl) 0 ᵥ* fromRows (C.cancel hB).d1 0 = 0
  funext j
  have h := FullPreComplex.hlam_full hB hlam
  change (Sum.elim (lam ∘ Sum.inl) 0 ᵥ* fromRows (C.cancel hB).d1 0) j = 0
  simp only [vecMul, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    fromRows_apply_inl, fromRows_apply_inr, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  simpa only [vecMul, dotProduct, Fintype.sum_sum_type, FullPreComplex.cancel, Pi.zero_apply] using congrFun h j

/-- The same cycle is closed on the inverse-disk legacy model. -/
theorem legacy_cycle_closed (C : FullPreComplex K) (hB : IsUnit C.B.det)
    (z : C.D1 ⊕ C.N → K) (hz : C.toFour.d1 *ᵥ z = 0) :
    (PreComplex'.toFour (inverseDiskLegacy C hB)).d1 *ᵥ (z ∘ Sum.inl) = 0 := by
  change fromRows (C.cancel hB).d1 0 *ᵥ (z ∘ Sum.inl) = 0
  rw [fromRows_mulVec, zero_mulVec, FullPreComplex.hz_full hB hz]
  funext i
  cases i <;> rfl

/-- The original retained coordinate is preserved by the inverse-disk adapter.
The local disk is inverted to compensate its changed degree, while the actual
class and functional are transported unchanged through the remaining complex. -/
theorem full_coordinate_eq_inverseDiskLegacy (C : FullPreComplex K) (hB : IsUnit C.B.det)
    (z : C.D1 ⊕ C.N → K) (lam : C.D2 ⊕ C.N → K)
    (hz : C.toFour.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.toFour.d1 = 0) :
    kmCoord C.toFour z lam hz hlam (σFull C.m0 C.m1 C.m2 C.N) =
      kmCoord (PreComplex'.toFour (inverseDiskLegacy C hB)) (z ∘ Sum.inl)
        (legacyFunctional C lam) (legacy_cycle_closed C hB z hz) (legacyFunctional_closed C hB lam hlam)
        (σPre C.m0 C.m1 C.m2 C.N) := by
  rw [kmCoord_fullCancel hB,
    kmCoord_preCancel (inverseDiskLegacy_unit C hB)]
  change C.B.det⁻¹ * kmCoord (C.cancel hB).toFour (z ∘ Sum.inl) (lam ∘ Sum.inl) _ _
      (σBlock C.m0 C.m1 C.m2) = (C.B⁻¹).det *
      kmCoord ((inverseDiskLegacy C hB).cancel (inverseDiskLegacy_unit C hB)).toFour
        (z ∘ Sum.inl) (transportFun (inverseDiskLegacy C hB) (legacyFunctional C lam)) _ _
        (σBlock C.m0 C.m1 C.m2)
  rw [det_nonsing_inv,
    show Ring.inverse C.B.det = C.B.det⁻¹ from eq_inv_of_mul_eq_one_left (Ring.inverse_mul_cancel _ hB)]
  have hfun : transportFun (inverseDiskLegacy C hB) (legacyFunctional C lam) = lam ∘ Sum.inl := by
    simp [transportFun, inverseDiskLegacy, legacyFunctional]
  congr 1
  exact (kmCoord_congr (inverseDiskLegacy_cancel C hB) rfl hfun _ _ _ _ _).symm

/-- A degree shift without inverting the disk cannot preserve the retained
factor unless the determinant squares to one.  The inverse-disk adapter is
not an integral identification record with the same local blocks. -/
theorem same_disk_factor_obstruction (d c : K) (hd : d ≠ 0) (hc : c ≠ 0) (h : d ^ 2 ≠ 1) :
    d⁻¹ * c ≠ d * c := by
  intro he
  have hf : d⁻¹ = d := mul_right_cancel₀ hc he
  have h1 := congrArg (d * ·) hf
  rw [mul_inv_cancel₀ hd] at h1
  exact h (by rw [pow_two]; exact h1.symm)

section IntegralLift

variable {R S : Type} [CommRing R] [CommRing S]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A coefficient-compatible integral lift of the inverse disk forces the
original disk to be invertible already in the integral coefficient ring. -/
theorem inverse_matrix_lift_forces_integral_unit (f : R →+* S) (hf : Function.Injective f)
    (D E : Matrix ι ι R) (hD : IsUnit (D.map f).det) (hE : E.map f = (D.map f)⁻¹) :
    IsUnit D.det := by
  have hmul : D * E = 1 := by
    ext i j
    apply hf
    have hm : (D * E).map f = 1 := by
      rw [Matrix.map_mul, hE, mul_nonsing_inv _ hD]
    have he := congrFun (congrFun hm i) j
    have h1 : (1 : Matrix ι ι R).map f = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    have h1e := congrFun (congrFun h1 i) j
    exact he.trans h1e.symm
  have hdet : D.det * E.det = 1 := by rw [← det_mul, hmul, det_one]
  exact ⟨⟨D.det, E.det, hdet, (mul_comm _ _).trans hdet⟩, rfl⟩

/-- Hence the localized inverse-disk adapter cannot be promoted to an
integral model with the same local blocks when the original determinant is a
nonunit of the integral coefficient ring. -/
theorem no_integral_inverse_disk_lift (f : R →+* S) (hf : Function.Injective f)
    (D : Matrix ι ι R) (hD : IsUnit (D.map f).det) (hnot : ¬ IsUnit D.det) :
    ¬ ∃ E : Matrix ι ι R, E.map f = (D.map f)⁻¹ := by
  rintro ⟨E, hE⟩
  exact hnot (inverse_matrix_lift_forces_integral_unit f hf D E hD hE)

end IntegralLift

end ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter
