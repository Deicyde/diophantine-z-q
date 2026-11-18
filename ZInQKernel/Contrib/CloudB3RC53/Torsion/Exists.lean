import ZInQKernel.Contrib.CloudB3RC53.Torsion.KnudsenMumford

/-!
# Torsion, part 6: exact complexes over a field are contractible

* `exists_inner_inverse`: over a field every matrix `A` has an inner inverse `G` (`A G A = A`).
* `BasedCx.IsExact`: `ker d = im d` on the even and on the odd part (as `d` is homogeneous this is
  exactness in every degree); `BasedCx.isExact_of_contraction` (the easy converse).
* `exists_contraction` (**an exact bounded complex of finite free modules over a field has a chain
  contraction**): with inner inverses `A⁺, B⁺` of `A = d|_{ev}`, `B = d|_{od}`, the maps
  `s = A⁺(1 − B⁺B)`, `t = B⁺(1 − A⁺A)` satisfy `dh + hd = 1` (exactness gives
  `BB⁺ = 1` on `ker A` and `AA⁺ = 1` on `ker B`); the degree `−1` component of `(s, t)` is then a
  graded contraction, because `d` is homogeneous of degree `+1` and `1` of degree `0`
  (`mul_trunc`, `trunc_mul`).
* `torsion_eq_tau_of_isExact`, `isUnit_torsion_of_isExact`: the torsion of an exact complex needs no
  contraction argument: `torsion C σ` equals `τ(C, h, σ)` for every contraction `h`, and is a unit.
* `FourCx.IsExact`, `FourCx.isExact_toBased`: degreewise exactness of `C⁰ → C¹ → C² → C³`
  (`d⁰` injective, `ker d¹ = im d⁰`, `ker d² = im d¹`, `d²` surjective) gives `IsExact`.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.Torsion

open Matrix

section InnerInverse

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- **Inner inverses over a field**: `A G A = A`. -/
theorem exists_inner_inverse (A : Matrix m n K) : ∃ G : Matrix n m K, A * G * A = A := by
  set f := toLin' A
  set p := f.rangeRestrict
  set i := (LinearMap.range f).subtype
  obtain ⟨r, hr⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict f)
  obtain ⟨l, hl⟩ := i.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  refine ⟨LinearMap.toMatrix' (r ∘ₗ l), toLin'.injective ?_⟩
  rw [toLin'_mul, toLin'_mul, toLin'_toMatrix']
  have h1 : ∀ y, l (i y) = y := fun y => LinearMap.congr_fun hl y
  have h2 : ∀ y, p (r y) = y := fun y => LinearMap.congr_fun hr y
  have h3 : ∀ x, f x = i (p x) := fun _ => rfl
  refine LinearMap.ext fun x => ?_
  change f (r (l (f x))) = f x
  rw [h3 (r _), h2, h3 x, h1]

end InnerInverse

variable {R : Type*} [CommRing R]
variable {κe κo : Type*} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]

/-! ### Exactness -/

/-- **Exactness** of a based complex: `ker d ⊆ im d` on the even and on the odd part (the
reverse inclusions are `d² = 0`). -/
def BasedCx.IsExact (C : BasedCx R κe κo) : Prop :=
  (∀ x : κe → R, C.dOE *ᵥ x = 0 → ∃ y, C.dEO *ᵥ y = x) ∧
    (∀ y : κo → R, C.dEO *ᵥ y = 0 → ∃ x, C.dOE *ᵥ x = y)

/-- A contractible complex is exact. -/
theorem BasedCx.isExact_of_contraction (C : BasedCx R κe κo) (h : Contraction C) : C.IsExact := by
  constructor
  · intro x hx
    refine ⟨h.hOE *ᵥ x, ?_⟩
    have := congrArg (· *ᵥ x) h.htpy_E
    simp only [Matrix.add_mulVec, ← mulVec_mulVec, hx, mulVec_zero, add_zero, one_mulVec] at this
    exact this
  · intro y hy
    refine ⟨h.hEO *ᵥ y, ?_⟩
    have := congrArg (· *ᵥ y) h.htpy_O
    simp only [Matrix.add_mulVec, ← mulVec_mulVec, hy, mulVec_zero, add_zero, one_mulVec] at this
    exact this

/-! ### Truncation to a homogeneous component -/

section Trunc

variable {l m n p : Type*} [Fintype n]

/-- The component of degree `a` of a matrix between graded bases. -/
def trunc (Y : Matrix m n R) (bm : m → ℤ) (bn : n → ℤ) (a : ℤ) : Matrix m n R :=
  of fun i j => if bm i = bn j + a then Y i j else 0

omit [Fintype n] in
theorem hasDeg_trunc (Y : Matrix m n R) (bm : m → ℤ) (bn : n → ℤ) (a : ℤ) :
    HasDeg (trunc Y bm bn a) bm bn a := by
  intro i j h
  by_contra hne
  exact h (by simp [trunc, hne])

/-- A homogeneous left factor commutes with truncation. -/
theorem mul_trunc {X : Matrix l n R} {bl : l → ℤ} {bn : n → ℤ} {c : ℤ} (hX : HasDeg X bl bn c)
    (Y : Matrix n p R) (bp : p → ℤ) (a : ℤ) :
    X * trunc Y bn bp a = trunc (X * Y) bl bp (a + c) := by
  ext i j
  simp only [trunc, mul_apply, of_apply]
  split_ifs with hij
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : X i k = 0
    · simp [hk]
    · have := hX i k hk
      simp only [show bn k = bp j + a from by omega, ↓reduceIte]
  · refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : X i k = 0
    · simp [hk]
    · have := hX i k hk
      simp only [show ¬ (bn k = bp j + a) from by omega, ↓reduceIte, mul_zero]

/-- A homogeneous right factor commutes with truncation. -/
theorem trunc_mul {X : Matrix n p R} {bn : n → ℤ} {bp : p → ℤ} {c : ℤ} (hX : HasDeg X bn bp c)
    (Y : Matrix l n R) (bl : l → ℤ) (a : ℤ) :
    trunc Y bl bn a * X = trunc (Y * X) bl bp (a + c) := by
  ext i j
  simp only [trunc, mul_apply, of_apply]
  split_ifs with hij
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : X k j = 0
    · simp [hk]
    · have := hX k j hk
      simp only [show bl i = bn k + a from by omega, ↓reduceIte]
  · refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : X k j = 0
    · simp [hk]
    · have := hX k j hk
      simp only [show ¬ (bl i = bn k + a) from by omega, ↓reduceIte, zero_mul]

omit [Fintype n] in
theorem trunc_add (Y Z : Matrix m n R) (bm : m → ℤ) (bn : n → ℤ) (a : ℤ) :
    trunc (Y + Z) bm bn a = trunc Y bm bn a + trunc Z bm bn a := by
  ext i j; simp only [trunc, of_apply, Matrix.add_apply]; split_ifs <;> simp

omit [Fintype n] in
theorem trunc_one [DecidableEq m] (b : m → ℤ) : trunc (1 : Matrix m m R) b b 0 = 1 := by
  ext i j
  simp only [trunc, of_apply, add_zero]
  split_ifs with h
  · rfl
  · rw [one_apply_ne (by rintro rfl; exact h rfl)]

end Trunc

/-! ### Exact complexes over a field are contractible -/

section Field

variable {K : Type*} [Field K]

/-- The graded contraction obtained by truncating an ungraded one. -/
def Contraction.ofUngraded (C : BasedCx K κe κo) (s : Matrix κe κo K) (t : Matrix κo κe K)
    (hE : C.dEO * t + s * C.dOE = 1) (hO : C.dOE * s + t * C.dEO = 1) : Contraction C where
  hOE := trunc t C.degO C.degE (-1)
  hEO := trunc s C.degE C.degO (-1)
  deg_hOE := hasDeg_trunc _ _ _ _
  deg_hEO := hasDeg_trunc _ _ _ _
  htpy_E := by
    rw [mul_trunc C.deg_dEO, trunc_mul C.deg_dOE, ← trunc_add,
      show (-1 : ℤ) + 1 = 0 by norm_num, hE, trunc_one]
  htpy_O := by
    rw [mul_trunc C.deg_dOE, trunc_mul C.deg_dEO, ← trunc_add,
      show (-1 : ℤ) + 1 = 0 by norm_num, hO, trunc_one]

/-- `X Y = Y` when every column of `Y` lies in `{v | X v = v}`, tested on vectors. -/
private theorem mul_eq_of_mulVec {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n]
    (X : Matrix m m K) (Y : Matrix m n K) (h : ∀ v, X *ᵥ (Y *ᵥ v) = Y *ᵥ v) : X * Y = Y := by
  apply toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [toLin'_mul]
  exact h v

/-- **An exact bounded complex of finite free modules over a field has a chain contraction.** -/
theorem exists_contraction (C : BasedCx K κe κo) (hC : C.IsExact) : Nonempty (Contraction C) := by
  obtain ⟨Ap, hA⟩ := exists_inner_inverse C.dOE
  obtain ⟨Bp, hB⟩ := exists_inner_inverse C.dEO
  -- `B B⁺ (1 − A⁺A) = 1 − A⁺A` and `A A⁺ (1 − B⁺B) = 1 − B⁺B`
  have hBB : C.dEO * Bp * (1 - Ap * C.dOE) = 1 - Ap * C.dOE := by
    apply mul_eq_of_mulVec
    intro v
    obtain ⟨y, hy⟩ := hC.1 ((1 - Ap * C.dOE) *ᵥ v) (by
      rw [mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hA, sub_self,
        zero_mulVec])
    rw [← hy, mulVec_mulVec, hB]
  have hAA : C.dOE * Ap * (1 - Bp * C.dEO) = 1 - Bp * C.dEO := by
    apply mul_eq_of_mulVec
    intro v
    obtain ⟨x, hx⟩ := hC.2 ((1 - Bp * C.dEO) *ᵥ v) (by
      rw [mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hB, sub_self,
        zero_mulVec])
    rw [← hx, mulVec_mulVec, hA]
  refine ⟨Contraction.ofUngraded C (Ap * (1 - Bp * C.dEO)) (Bp * (1 - Ap * C.dOE)) ?_ ?_⟩
  · calc C.dEO * (Bp * (1 - Ap * C.dOE)) + Ap * (1 - Bp * C.dEO) * C.dOE
        = (1 - Ap * C.dOE) + (Ap * C.dOE - Ap * Bp * (C.dEO * C.dOE)) := by
          rw [← Matrix.mul_assoc, hBB]; simp only [Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [C.dd_E, Matrix.mul_zero, sub_zero, sub_add_cancel]
  · calc C.dOE * (Ap * (1 - Bp * C.dEO)) + Bp * (1 - Ap * C.dOE) * C.dEO
        = (1 - Bp * C.dEO) + (Bp * C.dEO - Bp * Ap * (C.dOE * C.dEO)) := by
          rw [← Matrix.mul_assoc, hAA]; simp only [Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [C.dd_O, Matrix.mul_zero, sub_zero, sub_add_cancel]

/-- **The torsion of an exact complex** (no contraction argument): it is `τ(C, h, σ)` for every
contraction `h`, and one exists. -/
theorem torsion_eq_tau_of_isExact (C : BasedCx K κe κo) (hC : C.IsExact) (σ : κe ≃ κo) :
    ∃ h : Contraction C, torsion C σ = tau C h σ :=
  let h := (exists_contraction C hC).some
  ⟨h, (tau_eq_torsion C h σ).symm⟩

theorem isUnit_torsion_of_isExact (C : BasedCx K κe κo) (hC : C.IsExact) (σ : κe ≃ κo) :
    IsUnit (torsion C σ) := by
  obtain ⟨h, e⟩ := torsion_eq_tau_of_isExact C hC σ
  rw [e]; exact isUnit_tau C h σ

end Field

/-! ### Degreewise exactness of four-term complexes -/

section Four

variable {ι0 ι1 ι2 ι3 : Type*} [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]

/-- **Exactness of `C⁰ → C¹ → C² → C³`** in every degree. -/
def FourCx.IsExact (C : FourCx R ι0 ι1 ι2 ι3) : Prop :=
  (∀ x, C.d0 *ᵥ x = 0 → x = 0) ∧ (∀ y, C.d1 *ᵥ y = 0 → ∃ x, C.d0 *ᵥ x = y) ∧
    (∀ y, C.d2 *ᵥ y = 0 → ∃ x, C.d1 *ᵥ x = y) ∧ (∀ y, ∃ x, C.d2 *ᵥ x = y)

omit [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
theorem FourCx.isExact_toBased (C : FourCx R ι0 ι1 ι2 ι3) (hC : C.IsExact) :
    C.toBased.IsExact := by
  obtain ⟨h0, h1, h2, h3⟩ := hC
  constructor
  · intro v hv
    rw [FourCx.toBased_dOE, fromBlocks_mulVec] at hv
    have e0 : C.d0 *ᵥ (v ∘ Sum.inl) = 0 := by
      have := congrFun hv; funext i; simpa using this (Sum.inl i)
    have e2 : C.d2 *ᵥ (v ∘ Sum.inr) = 0 := by
      have := congrFun hv; funext i; simpa using this (Sum.inr i)
    obtain ⟨y, hy⟩ := h2 _ e2
    refine ⟨Sum.elim y 0, ?_⟩
    rw [FourCx.toBased_dEO, fromBlocks_mulVec]
    funext i; rcases i with i | i
    · simpa using (congrFun (h0 _ e0) i).symm
    · simpa using congrFun hy i
  · intro w hw
    rw [FourCx.toBased_dEO, fromBlocks_mulVec] at hw
    have e1 : C.d1 *ᵥ (w ∘ Sum.inl) = 0 := by
      have := congrFun hw; funext i; simpa using this (Sum.inr i)
    obtain ⟨x, hx⟩ := h1 _ e1
    obtain ⟨x', hx'⟩ := h3 (w ∘ Sum.inr)
    refine ⟨Sum.elim x x', ?_⟩
    rw [FourCx.toBased_dOE, fromBlocks_mulVec]
    funext i; rcases i with i | i
    · simpa using congrFun hx i
    · simpa using congrFun hx' i

/-- **The torsion of an exact four-term complex over a field** needs no contraction argument. -/
theorem FourCx.isUnit_torsion {K : Type*} [Field K] (C : FourCx K ι0 ι1 ι2 ι3) (hC : C.IsExact)
    (σ : ι0 ⊕ ι2 ≃ ι1 ⊕ ι3) : IsUnit (torsion C.toBased σ) :=
  isUnit_torsion_of_isExact _ (C.isExact_toBased hC) σ

end Four

end ZInQ.Contrib.CloudB3RC53.Torsion
