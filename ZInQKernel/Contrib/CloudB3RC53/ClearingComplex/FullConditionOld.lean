import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionCancel

/-!
# The old part of the full-condition model and the model of the triangle (5.6)

Manuscript `diophantine_zq.tex`, the triangle (5.6) (tex 5234–5238:
`C_old → (C_b)₀ → ⊕_q Q_q → C_old[1]`) and its graded model (tex 5398–5403: `C_old ⊕ ⊕_q Q_q`
with an upper triangular differential, the local quotients `Q_q` in degrees one and two,
tex 3479–3481, 5320–5322).

For a `FullPreComplex` with `Y = T = 0` (upper triangular over the old part):

* `FullPreComplex.map`: coefficient change along a ring map;
* `FullPreComplex.old`: the old part, the block complex `d⁰ = c⁰`, `d¹ = P`, `d² = U`;
* `FullPreComplex.oldIncl`: its inclusion (`x ↦ (x, 0)` in degrees one and two), a chain map;
* `FullPreComplex.oldProj`: the projection onto the singular summands, the complex
  `N --B--> N` in degrees one and two (the model of `⊕_q Q_q`), a chain map;
* `FullPreComplex.oldSES_shortExact`: `0 → C_old → C → (N --B--> N) → 0` is short exact. No
  invertibility of `B` is assumed: for the genuine mod-two representation `B` vanishes at an odd
  good prime and the old inclusion is not a quasi-isomorphism; the sequence still is the model of
  (5.6).

All statements are PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

namespace FullPreComplex

variable {S S' : Type} [CommRing S] [CommRing S']

/-- **Coefficient change** of a full-condition pre-cancellation complex along a ring map. -/
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

/-- **The old part** of an upper triangular full-condition complex (`Y = T = 0`): `d⁰ = c⁰`,
`d¹ = P`, `d² = U`. -/
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

variable {C}

/-- The components of the inclusion of the old part. -/
def oinc (hY : C.Y = 0) (hT : C.T = 0) : (i : ℤ) → ((C.old hY hT).idx i → S) →ₗ[S] (C.idx i → S)
  | 0 => LinearMap.id
  | 1 => (fromRows (1 : Matrix C.D1 C.D1 S) (0 : Matrix C.N C.D1 S)).mulVecLin
  | 2 => (fromRows (1 : Matrix C.D2 C.D2 S) (0 : Matrix C.N C.D2 S)).mulVecLin
  | 3 => LinearMap.id
  | _ => 0

theorem oinc_comm (hY : C.Y = 0) (hT : C.T = 0) (i : ℤ) (x : (C.old hY hT).idx i → S) :
    oinc hY hT (i + 1) ((C.old hY hT).ddL i x) = C.ddL i (oinc hY hT i x) := by
  match i with
  | 0 =>
    have hM : fromRows (1 : Matrix C.D1 C.D1 S) (0 : Matrix C.N C.D1 S) * C.c0 =
        fromRows C.c0 C.Y := by
      rw [fromRows_mul, Matrix.one_mul, Matrix.zero_mul, hY]
    have h : ∀ y : Fin C.m0 → S,
        (fromRows (1 : Matrix C.D1 C.D1 S) (0 : Matrix C.N C.D1 S)).mulVec (C.c0.mulVec y) =
          (fromRows C.c0 C.Y).mulVec y := fun y => by
      rw [Matrix.mulVec_mulVec, hM]
    exact h x
  | 1 =>
    have hM : fromRows (1 : Matrix C.D2 C.D2 S) (0 : Matrix C.N C.D2 S) * C.P =
        fromBlocks C.P C.Q C.T C.B * fromRows (1 : Matrix C.D1 C.D1 S) (0 : Matrix C.N C.D1 S) := by
      rw [fromRows_mul, fromBlocks_mul_fromRows, hT, Matrix.one_mul, Matrix.zero_mul,
        Matrix.mul_one, Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero]
    have h : ∀ y : C.D1 → S,
        (fromRows (1 : Matrix C.D2 C.D2 S) (0 : Matrix C.N C.D2 S)).mulVec (C.P.mulVec y) =
        (fromBlocks C.P C.Q C.T C.B).mulVec
          ((fromRows (1 : Matrix C.D1 C.D1 S) (0 : Matrix C.N C.D1 S)).mulVec y) := fun y => by
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
    change oinc hY hT (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- **The inclusion of the old part** (a chain map; the first map of (5.6)). -/
def oldIncl (hY : C.Y = 0) (hT : C.T = 0) : GHom (C.old hY hT).toGCx C.toGCx where
  f i j h := by subst h; exact oinc hY hT i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact oinc_comm hY hT i x

/-- The components of the projection onto the singular summands. -/
def oproj (_hY : C.Y = 0) (_hT : C.T = 0) : (i : ℤ) → (C.idx i → S) →ₗ[S] (C.kidx i → S)
  | 1 => (fromCols (0 : Matrix C.N C.D1 S) (1 : Matrix C.N C.N S)).mulVecLin
  | 2 => (fromCols (0 : Matrix C.N C.D2 S) (1 : Matrix C.N C.N S)).mulVecLin
  | _ => 0

theorem oproj_comm (hY : C.Y = 0) (hT : C.T = 0) (i : ℤ) (x : C.idx i → S) :
    oproj hY hT (i + 1) (C.ddL i x) = C.kdL i (oproj hY hT i x) := by
  match i with
  | 0 =>
    have hM : fromCols (0 : Matrix C.N C.D1 S) (1 : Matrix C.N C.N S) * fromRows C.c0 C.Y = 0 := by
      rw [fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, zero_add, hY]
    have h : ∀ y : Fin C.m0 → S,
        (fromCols (0 : Matrix C.N C.D1 S) (1 : Matrix C.N C.N S)).mulVec
          ((fromRows C.c0 C.Y).mulVec y) = 0 := fun y => by
      rw [Matrix.mulVec_mulVec, hM, Matrix.zero_mulVec]
    exact h x
  | 1 =>
    have hM : fromCols (0 : Matrix C.N C.D2 S) (1 : Matrix C.N C.N S) *
          fromBlocks C.P C.Q C.T C.B =
        C.B * fromCols (0 : Matrix C.N C.D1 S) (1 : Matrix C.N C.N S) := by
      rw [fromCols_mul_fromBlocks, mul_fromCols, Matrix.zero_mul, Matrix.zero_mul, zero_add,
        zero_add, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, hT]
    have h : ∀ y : C.D1 ⊕ C.N → S,
        (fromCols (0 : Matrix C.N C.D2 S) (1 : Matrix C.N C.N S)).mulVec
          ((fromBlocks C.P C.Q C.T C.B).mulVec y) =
        C.B.mulVec ((fromCols (0 : Matrix C.N C.D1 S) (1 : Matrix C.N C.N S)).mulVec y) :=
      fun y => by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
    exact h x
  | 2 => rfl
  | Int.ofNat (n + 3) => rfl
  | Int.negSucc n =>
    change oproj hY hT (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- **The projection onto the singular summands** `C → (N --B--> N)` (a chain map; the second map
of (5.6)). -/
def oldProj (hY : C.Y = 0) (hT : C.T = 0) : GHom C.toGCx C.disk where
  f i j h := by subst h; exact oproj hY hT i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact oproj_comm hY hT i x

open SelmerDuality in
/-- **The model of the triangle (5.6)**: `C_old → C → (N --B--> N)`. -/
def oldSES (hY : C.Y = 0) (hT : C.T = 0) : ShortComplex (CochainComplex (ModuleCat.{0} S) ℤ) :=
  ShortComplex.mk (GHom.toCC (oldIncl hY hT)) (GHom.toCC (oldProj hY hT)) (by
    ext i x
    change oproj hY hT i (oinc hY hT i x) = 0
    match i with
    | 1 =>
      have hM : fromCols (0 : Matrix C.N C.D1 S) (1 : Matrix C.N C.N S) *
          fromRows (1 : Matrix C.D1 C.D1 S) (0 : Matrix C.N C.D1 S) = 0 := by
        rw [fromCols_mul_fromRows, Matrix.zero_mul, Matrix.one_mul, add_zero]
      have h : ∀ y : C.D1 → S,
          (fromCols (0 : Matrix C.N C.D1 S) (1 : Matrix C.N C.N S)).mulVec
            ((fromRows (1 : Matrix C.D1 C.D1 S) (0 : Matrix C.N C.D1 S)).mulVec y) = 0 :=
        fun y => by rw [Matrix.mulVec_mulVec, hM, Matrix.zero_mulVec]
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

open SelmerDuality in
/-- **`0 → C_old → C → (N --B--> N) → 0` is short exact** (no invertibility of `B`). PROVED. -/
theorem oldSES_shortExact (hY : C.Y = 0) (hT : C.T = 0) : (oldSES hY hT).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro c hc
    change oproj hY hT i c = 0 at hc
    change ∃ a, oinc hY hT i a = c
    match i with
    | 0 => exact ⟨c, rfl⟩
    | 1 =>
      refine ⟨c ∘ Sum.inl, ?_⟩
      have h := exact_fromCols_one (0 : Matrix C.N C.D1 S) c hc
      rwa [neg_zero] at h
    | 2 =>
      refine ⟨c ∘ Sum.inl, ?_⟩
      have h := exact_fromCols_one (0 : Matrix C.N C.D2 S) c hc
      rwa [neg_zero] at h
    | 3 => exact ⟨c, rfl⟩
    | Int.ofNat (n + 4) => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩
    | Int.negSucc n => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩
  · rw [ModuleCat.mono_iff_injective]
    intro a b h
    change oinc hY hT i a = oinc hY hT i b at h
    match i with
    | 0 => exact h
    | 1 => exact inj_fromRows_one (m := C.D1) (0 : Matrix C.N C.D1 S) a b h
    | 2 => exact inj_fromRows_one (m := C.D2) (0 : Matrix C.N C.D2 S) a b h
    | 3 => exact h
    | Int.ofNat (n + 4) => exact Subsingleton.elim (α := Empty → S) _ _
    | Int.negSucc n => exact Subsingleton.elim (α := Empty → S) _ _
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    change ∃ c, oproj hY hT i c = y
    match i with
    | 1 => exact ⟨Sum.elim 0 y, surj_fromCols_one (0 : Matrix C.N C.D1 S) y⟩
    | 2 => exact ⟨Sum.elim 0 y, surj_fromCols_one (0 : Matrix C.N C.D2 S) y⟩
    | 0 => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩
    | 3 => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩
    | Int.ofNat (n + 4) => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩
    | Int.negSucc n => exact ⟨0, Subsingleton.elim (α := Empty → S) _ _⟩

end FullPreComplex

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
