import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.Ideal.Span

/-!
# The pole calculus "modulo `2^M`" of §9 (Lane RC7)

Manuscript `diophantine_zq.tex` (11/5 version; identical in Version 19), §9:

* tex 5220–5223 and 5428–5436, 5469–5483 (`ex:limits-fixed-field-budget`, display (5.8)): the inverse
  of the new local block at a sign character, `B_x⁻¹ = C ∑_{j<M} (-2F)^j (mod 2^M)`, has no Laurent
  terms below `-4M` modulo `2^M`, uniformly in the number of blocks; the surviving Schur differential
  `P_x - Q_x B_x⁻¹ T_x` has the same bound since `P_x, Q_x, T_x` are power-series matrices;
* tex 5630–5634 (`ex:limits-fixed-field-clearing`, display (5.9)): a polynomial of degree `4m` with
  constant integral coefficients in entries with pole at most `4M` modulo `2^M` has pole at most
  `16 m M` modulo `2^M`; "sums cannot increase this bound".

### The interface

The manuscript works in `𝒪 = (ℤ₂[[t]]_{(2)})^`, where `t` is invertible, and measures poles of an
element "modulo `2^M`" by its image in `(ℤ/2^M)((t))`.  Everything in the pole calculus only uses:
a ring map `Λ → O` and an element `tΛ ∈ Λ` (the variable `t`) whose image is invertible in `O`.
`PoleData` records exactly this.  `poleLE N` is the `Λ`-submodule `t^{-N} Λ` ("pole at most `N`"),
and `poleModLE M N = t^{-N} Λ + 2^M O` ("pole at most `N` modulo `2^M`").  For the genuine `𝒪`
(file `OModel`), membership in `poleModLE M N` implies that the image in `(ℤ/2^M)((t))` has no
coefficient below `-N`, which is the manuscript's formulation.

Everything in this file is PROVED.
-/

namespace ZInQ.Manuscript.RC.Determinant

open Matrix

/-- The data of a pole filtration: a ring map `Λ → O` and an element `tΛ : Λ` whose image in `O`
is invertible, with chosen inverse `tinv`.  For the manuscript `Λ = ℤ₂[[t]]`, `tΛ = t`,
`O = 𝒪 = (Λ_{(2)})^` (tex 2747–2748). -/
structure PoleData (Λ O : Type*) [CommRing Λ] [CommRing O] [Algebra Λ O] where
  /-- the variable `t ∈ Λ` -/
  tΛ : Λ
  /-- the inverse of `t` in `O` -/
  tinv : O
  mul_tinv : algebraMap Λ O tΛ * tinv = 1

namespace PoleData

variable {Λ O : Type*} [CommRing Λ] [CommRing O] [Algebra Λ O] (D : PoleData Λ O)

/-- `poleLE N = t^{-N} Λ ⊆ O`: elements with Laurent order at least `-N` ("pole at most `N`"). -/
def poleLE (N : ℕ) : Submodule Λ O :=
  LinearMap.range ((LinearMap.mulLeft Λ (D.tinv ^ N)).comp (Algebra.linearMap Λ O))

/-- `poleModLE M N = t^{-N} Λ + 2^M O`: "pole at most `N` modulo `2^M`" (tex 5221, 5501, 5518). -/
def poleModLE (M N : ℕ) : Submodule Λ O :=
  D.poleLE N ⊔ (Ideal.span {(2 : O) ^ M}).restrictScalars Λ

theorem mem_poleLE {N : ℕ} {y : O} : y ∈ D.poleLE N ↔ ∃ a : Λ, D.tinv ^ N * algebraMap Λ O a = y := by
  simp [poleLE]

theorem algebraMap_mem_poleLE (a : Λ) : algebraMap Λ O a ∈ D.poleLE 0 :=
  D.mem_poleLE.2 ⟨a, by simp⟩

theorem one_mem_poleLE : (1 : O) ∈ D.poleLE 0 := by
  simpa using D.algebraMap_mem_poleLE 1

theorem zero_mem_poleLE (N : ℕ) : (0 : O) ∈ D.poleLE N := Submodule.zero_mem _

theorem tinv_pow_mem_poleLE (N : ℕ) : D.tinv ^ N ∈ D.poleLE N :=
  D.mem_poleLE.2 ⟨1, by simp⟩

theorem poleLE_mono {N N' : ℕ} (h : N ≤ N') : D.poleLE N ≤ D.poleLE N' := by
  intro y hy
  obtain ⟨a, rfl⟩ := D.mem_poleLE.1 hy
  refine D.mem_poleLE.2 ⟨D.tΛ ^ (N' - N) * a, ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have ht : D.tinv * algebraMap Λ O D.tΛ = 1 := by rw [mul_comm]; exact D.mul_tinv
  simp only [Nat.add_sub_cancel_left, map_mul, map_pow, pow_add]
  calc D.tinv ^ N * D.tinv ^ k * ((algebraMap Λ O D.tΛ) ^ k * algebraMap Λ O a)
      = D.tinv ^ N * (D.tinv * algebraMap Λ O D.tΛ) ^ k * algebraMap Λ O a := by ring
    _ = D.tinv ^ N * algebraMap Λ O a := by rw [ht, one_pow, mul_one]

theorem mul_mem_poleLE {N₁ N₂ : ℕ} {x y : O} (hx : x ∈ D.poleLE N₁) (hy : y ∈ D.poleLE N₂) :
    x * y ∈ D.poleLE (N₁ + N₂) := by
  obtain ⟨a, rfl⟩ := D.mem_poleLE.1 hx
  obtain ⟨b, rfl⟩ := D.mem_poleLE.1 hy
  exact D.mem_poleLE.2 ⟨a * b, by rw [map_mul, pow_add]; ring⟩

theorem algebraMap_mul_mem_poleLE {N : ℕ} (a : Λ) {y : O} (hy : y ∈ D.poleLE N) :
    algebraMap Λ O a * y ∈ D.poleLE N := by
  rw [← Algebra.smul_def]; exact Submodule.smul_mem _ a hy

theorem mem_poleModLE {M N : ℕ} {y : O} :
    y ∈ D.poleModLE M N ↔ ∃ a : Λ, y - D.tinv ^ N * algebraMap Λ O a ∈ Ideal.span {(2 : O) ^ M} := by
  constructor
  · intro hy
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a, rfl⟩ := D.mem_poleLE.1 hp
    exact ⟨a, by simpa using hq⟩
  · rintro ⟨a, ha⟩
    refine Submodule.mem_sup.2 ⟨D.tinv ^ N * algebraMap Λ O a, D.mem_poleLE.2 ⟨a, rfl⟩,
      y - D.tinv ^ N * algebraMap Λ O a, ha, by ring⟩

theorem poleLE_le_poleModLE (M N : ℕ) : D.poleLE N ≤ D.poleModLE M N := le_sup_left

theorem span_le_poleModLE (M N : ℕ) :
    (Ideal.span {(2 : O) ^ M}).restrictScalars Λ ≤ D.poleModLE M N := le_sup_right

theorem two_pow_mul_mem_poleModLE (M N : ℕ) (z : O) : (2 : O) ^ M * z ∈ D.poleModLE M N :=
  D.span_le_poleModLE M N (Ideal.mul_mem_right z _ (Ideal.subset_span rfl))

theorem poleModLE_mono {M N N' : ℕ} (h : N ≤ N') : D.poleModLE M N ≤ D.poleModLE M N' :=
  sup_le_sup_right (D.poleLE_mono h) _

theorem mul_mem_poleModLE {M N₁ N₂ : ℕ} {x y : O} (hx : x ∈ D.poleModLE M N₁)
    (hy : y ∈ D.poleModLE M N₂) : x * y ∈ D.poleModLE M (N₁ + N₂) := by
  obtain ⟨a, ha⟩ := D.mem_poleModLE.1 hx
  obtain ⟨b, hb⟩ := D.mem_poleModLE.1 hy
  refine D.mem_poleModLE.2 ⟨a * b, ?_⟩
  have : x * y - D.tinv ^ (N₁ + N₂) * algebraMap Λ O (a * b) =
      (x - D.tinv ^ N₁ * algebraMap Λ O a) * y +
        D.tinv ^ N₁ * algebraMap Λ O a * (y - D.tinv ^ N₂ * algebraMap Λ O b) := by
    rw [map_mul, pow_add]; ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)

theorem algebraMap_mul_mem_poleModLE {M N : ℕ} (a : Λ) {y : O} (hy : y ∈ D.poleModLE M N) :
    algebraMap Λ O a * y ∈ D.poleModLE M N := by
  rw [← Algebra.smul_def]; exact Submodule.smul_mem _ a hy

theorem prod_mem_poleModLE {ι : Type*} (s : Finset ι) {M : ℕ} (N : ι → ℕ) (f : ι → O)
    (hf : ∀ i ∈ s, f i ∈ D.poleModLE M (N i)) : (∏ i ∈ s, f i) ∈ D.poleModLE M (∑ i ∈ s, N i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using D.poleLE_le_poleModLE M 0 D.one_mem_poleLE
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact D.mul_mem_poleModLE (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem pow_mem_poleModLE {M N : ℕ} {x : O} (hx : x ∈ D.poleModLE M N) (k : ℕ) :
    x ^ k ∈ D.poleModLE M (k * N) := by
  induction k with
  | zero => simpa using D.poleLE_le_poleModLE M 0 D.one_mem_poleLE
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact D.mul_mem_poleModLE ih hx

/-! ### Matrices with entries of bounded pole -/

section Matrices

variable {l m n : Type*} [Fintype m]

theorem matMul_mem_poleLE {N₁ N₂ : ℕ} (A : Matrix l m O) (B : Matrix m n O)
    (hA : ∀ i j, A i j ∈ D.poleLE N₁) (hB : ∀ i j, B i j ∈ D.poleLE N₂) :
    ∀ i j, (A * B) i j ∈ D.poleLE (N₁ + N₂) := fun i j =>
  Submodule.sum_mem _ fun k _ => D.mul_mem_poleLE (hA i k) (hB k j)

theorem matMul_mem_poleModLE {M N₁ N₂ : ℕ} (A : Matrix l m O) (B : Matrix m n O)
    (hA : ∀ i j, A i j ∈ D.poleModLE M N₁) (hB : ∀ i j, B i j ∈ D.poleModLE M N₂) :
    ∀ i j, (A * B) i j ∈ D.poleModLE M (N₁ + N₂) := fun i j =>
  Submodule.sum_mem _ fun k _ => D.mul_mem_poleModLE (hA i k) (hB k j)

theorem one_mem_poleLE_entries [DecidableEq n] : ∀ i j, (1 : Matrix n n O) i j ∈ D.poleLE 0 := by
  intro i j
  by_cases h : i = j
  · subst h; simpa using D.one_mem_poleLE
  · simp [Matrix.one_apply_ne h]

theorem matPow_mem_poleLE [Fintype n] [DecidableEq n] {N : ℕ} (F : Matrix n n O)
    (hF : ∀ i j, F i j ∈ D.poleLE N) (k : ℕ) : ∀ i j, (F ^ k) i j ∈ D.poleLE (k * N) := by
  induction k with
  | zero => simpa using D.one_mem_poleLE_entries
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact D.matMul_mem_poleLE _ _ ih hF

/-- **Tex 5630–5633 (PROVED).**  The determinant is a polynomial of degree `card n` with constant
integral coefficients in the entries; if every entry has pole at most `N` modulo `2^M`, the
determinant has pole at most `card n · N` modulo `2^M` ("a product of entries has pole at most the
sum, and sums cannot increase this bound"). -/
theorem det_mem_poleModLE [Fintype n] [DecidableEq n] {M N : ℕ} (A : Matrix n n O)
    (hA : ∀ i j, A i j ∈ D.poleModLE M N) : A.det ∈ D.poleModLE M (Fintype.card n * N) := by
  rw [Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hprod : (∏ i, A (σ i) i) ∈ D.poleModLE M (Fintype.card n * N) := by
    have := D.prod_mem_poleModLE Finset.univ (fun _ => N) (fun i => A (σ i) i)
      (fun i _ => hA (σ i) i)
    simpa [Finset.sum_const, Finset.card_univ, smul_eq_mul] using this
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simpa [h] using hprod
  · rw [h, Units.neg_smul, one_smul]; exact Submodule.neg_mem _ hprod

/-- **Tex 5428–5436 and 5469–5477, display (5.8) (PROVED).**  Let `B` be invertible and suppose
`B C = 1 + 2F` where every entry of `C` and of `F` has pole at most `N` (in the manuscript `N = 4`:
"both `C` and `F` having no Laurent terms below degree `-4`").  Then
`B⁻¹ = C ∑_{j=0}^{M-1} (-2F)^j  (mod 2^M)`, and every entry of `B⁻¹` has pole at most `N·M`
modulo `2^M` (the `j`-th summand has pole at most `N(j+1)`).  The bound counts the largest pole of an
entry, not the number of summands or of blocks: it is independent of the size of `B`. -/
theorem inv_neumann [Fintype n] [DecidableEq n] (B C F : Matrix n n O) (hB : IsUnit B.det)
    (hBC : B * C = 1 + (2 : O) • F) (M : ℕ) :
    B⁻¹ = C * ∑ j ∈ Finset.range M, (-((2 : O) • F)) ^ j + (2 : O) ^ M • (B⁻¹ * (-F) ^ M) := by
  set X : Matrix n n O := -((2 : O) • F) with hX
  have hgeom : (1 - X) * ∑ j ∈ Finset.range M, X ^ j = 1 - X ^ M := mul_neg_geom_sum X M
  have h1X : 1 - X = B * C := by rw [hBC, hX, sub_neg_eq_add]
  have hXM : X ^ M = (2 : O) ^ M • (-F) ^ M := by
    rw [hX, ← smul_neg, smul_pow]
  have hBinv : B⁻¹ * B = 1 := nonsing_inv_mul B hB
  calc B⁻¹ = B⁻¹ * ((1 - X) * ∑ j ∈ Finset.range M, X ^ j + X ^ M) := by
        rw [hgeom, sub_add_cancel, Matrix.mul_one]
    _ = C * ∑ j ∈ Finset.range M, X ^ j + B⁻¹ * X ^ M := by
        rw [Matrix.mul_add, h1X, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBinv, Matrix.one_mul]
    _ = _ := by rw [hXM, Matrix.mul_smul]

/-- **Tex 5434–5436, 5476–5478 (PROVED).**  The pole bound of (5.8): under the hypotheses of
`inv_neumann`, with the entries of `C` and `F` of pole at most `N`, every entry of `B⁻¹` has pole at
most `N * M` modulo `2^M`.  For the manuscript's `N = 4` this is the bound `4M`. -/
theorem inv_entry_mem_poleModLE [Fintype n] [DecidableEq n] (B C F : Matrix n n O) (hB : IsUnit B.det)
    (hBC : B * C = 1 + (2 : O) • F) {N : ℕ} (hC : ∀ i j, C i j ∈ D.poleLE N)
    (hF : ∀ i j, F i j ∈ D.poleLE N) (M : ℕ) : ∀ i j, B⁻¹ i j ∈ D.poleModLE M (N * M) := by
  intro i j
  rw [inv_neumann B C F hB hBC M, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine Submodule.add_mem _ ?_ (D.two_pow_mul_mem_poleModLE M _ _)
  refine D.poleLE_le_poleModLE M _ ?_
  rw [Matrix.mul_sum, Matrix.sum_apply]
  refine Submodule.sum_mem _ fun k hk => ?_
  have hk' : k + 1 ≤ M := Finset.mem_range.1 hk
  have hX : ∀ i j, (-((2 : O) • F)) i j ∈ D.poleLE N := by
    intro i j
    have : (-((2 : O) • F)) i j = algebraMap Λ O (-2) * F i j := by
      simp [map_neg, map_ofNat]
    rw [this]; exact D.algebraMap_mul_mem_poleLE _ (hF i j)
  have := D.matMul_mem_poleLE C _ hC (D.matPow_mem_poleLE _ hX k) i j
  exact D.poleLE_mono (by nlinarith) this

/-- **Tex 5479–5481 (PROVED).**  The surviving Schur differential `P_x - Q_x B_x⁻¹ T_x` has the same
pole bound as `B_x⁻¹`, since `P_x, Q_x, T_x` are power-series matrices (entries in the image of
`Λ`, i.e. pole at most `0`). -/
theorem schur_entry_mem_poleModLE {l' : Type*} [Fintype n] [DecidableEq n] (P : Matrix l' l O) (Q : Matrix l' n O)
    (T : Matrix n l O) (B : Matrix n n O) {M L : ℕ} (hP : ∀ i j, P i j ∈ D.poleLE 0)
    (hQ : ∀ i j, Q i j ∈ D.poleLE 0) (hT : ∀ i j, T i j ∈ D.poleLE 0)
    (hBinv : ∀ i j, B⁻¹ i j ∈ D.poleModLE M L) [Fintype l] :
    ∀ i j, (P - Q * B⁻¹ * T) i j ∈ D.poleModLE M L := by
  intro i j
  rw [Matrix.sub_apply]
  refine Submodule.sub_mem _ (D.poleModLE_mono (Nat.zero_le L)
    (D.poleLE_le_poleModLE M 0 (hP i j))) ?_
  have hQ' : ∀ i j, Q i j ∈ D.poleModLE M 0 := fun i j => D.poleLE_le_poleModLE M 0 (hQ i j)
  have hT' : ∀ i j, T i j ∈ D.poleModLE M 0 := fun i j => D.poleLE_le_poleModLE M 0 (hT i j)
  have h1 := D.matMul_mem_poleModLE Q B⁻¹ hQ' hBinv
  have h2 := D.matMul_mem_poleModLE (Q * B⁻¹) T h1 hT' i j
  simpa using h2

/-- **Tex 5526–5527, 5631–5632 (PROVED).**  The constant basis changes of the Smith decomposition
(matrices over `Λ`, in particular constant `ℤ₂` matrices) preserve the entrywise pole bound modulo
`2^M`: if every entry of `d` has pole at most `L` modulo `2^M`, so has every entry of `U d V`.
Submatrices (such as the blocks `A_i`) inherit the bound entrywise. -/
theorem basisChange_entry_mem_poleModLE {l' k : Type*} [Fintype k] {M L : ℕ}
    (U : Matrix l' m Λ) (d : Matrix m k O) (V : Matrix k n Λ)
    (hd : ∀ i j, d i j ∈ D.poleModLE M L) :
    ∀ i j, (U.map (algebraMap Λ O) * d * V.map (algebraMap Λ O)) i j ∈ D.poleModLE M L := by
  have hU : ∀ i j, U.map (algebraMap Λ O) i j ∈ D.poleModLE M 0 := fun i j =>
    D.poleLE_le_poleModLE M 0 (D.algebraMap_mem_poleLE (U i j))
  have hV : ∀ i j, V.map (algebraMap Λ O) i j ∈ D.poleModLE M 0 := fun i j =>
    D.poleLE_le_poleModLE M 0 (D.algebraMap_mem_poleLE (V i j))
  intro i j
  have h1 := D.matMul_mem_poleModLE _ _ hU hd
  have h2 := D.matMul_mem_poleModLE _ _ h1 hV i j
  simpa using h2

end Matrices

end PoleData

end ZInQ.Manuscript.RC.Determinant
