import Mathlib

/-!
# Lane RC16 (job `det`): the class-functional coordinate of a square two-term complex

Formalizes the linear algebra behind the terminal step of the proof of (5.5):

* tex 3877-3892 (`ex:arith-coordinate`): the class-functional coordinate `u` is the coordinate of
  `[z] ⊗ [λ]` in the determinant line `𝒟 = det⁻¹ C ≃ H¹(C) ⊗ H²(C)^*`, written in the retained integral
  determinant basis;
* tex 4958-4964: "At terminal outer dimension one a maximal boundary minor `Δ` is nonzero. [...]
  Determinant-one Schur operations in a square two-term rank-one-kernel complex give `u = ±αβ/Δ`, where
  `α` is an integral surviving cycle coordinate and `β` has valuation at least `-a`.
  Consequently `v₂u_j ≥ -a-b`";
* tex 4972-4973: "Bounded matrix size alone would not prove it: `[2^j]` is a counterexample to that
  inference."

Everything here is over an arbitrary field `K`, for the square complex `[K^{n+1} --D--> K^{n+1}]` in
degrees one and two with the standard (integral) bases `e_i` of `C¹` and `f_k` of `C²`.

Main results (all `PROVED`):
* `classFunctionalCoordWith`: the coordinate computed through a complement `(w, y)`;
* `classFunctionalCoordWith_indep`: independence of the complement (well-definedness);
* `classFunctionalCoord_cramer`: the Cramer formula `u · Δ = ± z_{j₀} λ_{k₀}` for every maximal minor
  `Δ = M_{k₀ j₀}`, for every complement with nonzero denominator; `den_stdComplement` and
  `exists_complement_iff_exists_minor_ne_zero`: the coordinate is defined iff some maximal minor is
  nonzero;
* `classFunctionalCoord_valuation`, `classFunctionalCoord_valuation_bound`: `v u + v Δ = v α + v β` and
  `v u ≥ -a-b`;
* `twoPow_counterexample`: the `[2^j]` remark;
* `exists_minor_ne_zero_of_ker_eq_span`: nullity one forces a nonzero maximal minor.
-/

namespace ZInQ.Manuscript.RC.Uniform

open Matrix

variable {K : Type*} [Field K]

/-! ### Determinants of listed columns -/

/-- The square matrix whose COLUMNS are `v 0, v 1, …, v (m-1)` (column `j` is `v j`). -/
def colsMat {m : ℕ} (v : Fin m → Fin m → K) : Matrix (Fin m) (Fin m) K :=
  Matrix.of fun i j => v j i

/-- `det[v 0 | v 1 | ⋯ | v (m-1)]`: the determinant of the matrix whose columns are the listed
vectors. -/
def detCols {m : ℕ} (v : Fin m → Fin m → K) : K :=
  (colsMat v).det

/-- The column list `z, w 0, …, w (n-1)` (`z` first, then `w`). -/
def colsZW {n : ℕ} (z : Fin (n + 1) → K) (w : Fin n → Fin (n + 1) → K) :
    Fin (n + 1) → Fin (n + 1) → K :=
  @Fin.cons n (fun _ => Fin (n + 1) → K) z w

/-- The column list `D w 0, …, D w (n-1), y` (`D w` first, then `y`). -/
def colsDWY {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (w : Fin n → Fin (n + 1) → K)
    (y : Fin (n + 1) → K) : Fin (n + 1) → Fin (n + 1) → K :=
  @Fin.snoc n (fun _ => Fin (n + 1) → K) (fun i => D *ᵥ w i) y

/-- **The class-functional coordinate computed through a complement** (tex 3882-3892,
`ex:arith-coordinate`; `PROVED` facts about it below).

For the square two-term complex `C = [C¹ = K^{n+1} --D--> C² = K^{n+1}]` (degrees one and two), a cycle
`z ∈ H¹ = ker D` and a functional `λ` on `C²` killing the boundaries `B² = im D` (so `[λ] ∈ H²(C)^*`),
the manuscript's coordinate `u` is the coordinate of `[z] ⊗ [λ]` in the determinant line
`𝒟 = det⁻¹ C ≃ H¹(C) ⊗ H²(C)^*`, written in the retained integral basis
`(e_1 ∧ ⋯ ∧ e_{n+1}) ⊗ (f_1 ∧ ⋯ ∧ f_{n+1})^*`.

The isomorphism `det C¹ ⊗ (det C²)^* ≃ H¹ ⊗ (H²)^*` comes from the two short exact sequences
`0 → H¹ → C¹ → B² → 0` and `0 → B² → C² → H² → 0`. To compute it one chooses a complement: vectors
`w_1, …, w_n ∈ C¹` (whose images `D w_i` form a basis of `B²`) and `y ∈ C²` (whose class spans `H²`).
Then `z ∧ w_1 ∧ ⋯ ∧ w_n ↦ z ⊗ (D w_1 ∧ ⋯ ∧ D w_n)` and
`D w_1 ∧ ⋯ ∧ D w_n ∧ y ↦ (D w_1 ∧ ⋯ ∧ D w_n) ⊗ [y]`, so that, since `[λ] = λ(y) · [y]^*`,
`[z] ⊗ [λ] = det[z | w] · λ(y) / det[D w | y] · (e_1 ∧ ⋯ ∧ e_{n+1}) ⊗ (f_1 ∧ ⋯ ∧ f_{n+1})^*`.
Here `det[c_1 | ⋯ | c_{n+1}]` is the determinant of the matrix with the listed COLUMNS. Hence
`u = det[z | w] · λ(y) / det[D w_1 | ⋯ | D w_n | y]`.
The complement is admissible when the denominator is nonzero; `classFunctionalCoordWith_indep` proves
that the value does not depend on the admissible complement, and
`exists_complement_iff_exists_minor_ne_zero` that an admissible complement exists iff some maximal
minor of `D` is nonzero.

DEPARTURE: the manuscript works with integral models over `𝒪_j` and its fraction field; here the
statement is over an arbitrary field `K` (the generic fibre), which is where the coordinate lives. -/
def classFunctionalCoordWith {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (z lam : Fin (n + 1) → K) (w : Fin n → Fin (n + 1) → K) (y : Fin (n + 1) → K) : K :=
  detCols (colsZW z w) * (lam ⬝ᵥ y) / detCols (colsDWY D w y)

/-! ### Helper identities -/

/-- Replacing the first column. -/
theorem colsMat_colsZW {n : ℕ} (x : Fin (n + 1) → K) (w : Fin n → Fin (n + 1) → K) :
    colsMat (colsZW x w) = (colsMat (colsZW 0 w)).updateCol 0 x := by
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [colsMat, colsZW]
  · simp [colsMat, colsZW]

/-- `det[s • x | w] = s · det[x | w]`. -/
theorem detCols_colsZW_smul {n : ℕ} (s : K) (x : Fin (n + 1) → K) (w : Fin n → Fin (n + 1) → K) :
    detCols (colsZW (s • x) w) = s * detCols (colsZW x w) := by
  simp only [detCols]
  rw [colsMat_colsZW, colsMat_colsZW x w, det_updateCol_smul]

/-- `det[0 | w] = 0`. -/
theorem detCols_colsZW_zero {n : ℕ} (w : Fin n → Fin (n + 1) → K) :
    detCols (colsZW (0 : Fin (n + 1) → K) w) = 0 := by
  simpa using detCols_colsZW_smul (0 : K) (0 : Fin (n + 1) → K) w

/-- Moving the last column `y` to the front: `det[D w | y] = (-1)^n · det[y | D w]`. -/
theorem detCols_colsDWY_eq {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (w : Fin n → Fin (n + 1) → K) (y : Fin (n + 1) → K) :
    detCols (colsDWY D w y) = (-1) ^ n * detCols (colsZW y fun i => D *ᵥ w i) := by
  have h : colsMat (colsDWY D w y) =
      (colsMat (colsZW y fun i => D *ᵥ w i)).submatrix id (finRotate (n + 1)) := by
    ext i j
    simp only [colsMat, colsDWY, colsZW, of_apply, submatrix_apply, id]
    rw [Fin.snoc_eq_cons_rotate]
  simp only [detCols]
  rw [h, det_permute', sign_finRotate]
  simp

/-- The classical identity `det[y | D w] = det[adj(D) y | w]`, valid for every square matrix `D`, all
`w` and all `y` (no hypothesis). Proof: `[y | D w] = (D W).updateCol 0 y` for `W = [0 | w]`, then
Cramer's rule and `adj(D W) = adj(W) adj(D)`. -/
theorem detCols_colsZW_mulVec {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (w : Fin n → Fin (n + 1) → K) (y : Fin (n + 1) → K) :
    detCols (colsZW y fun i => D *ᵥ w i) = detCols (colsZW (D.adjugate *ᵥ y) w) := by
  set W := colsMat (colsZW (0 : Fin (n + 1) → K) w) with hW
  have h1 : colsMat (colsZW y fun i => D *ᵥ w i) = (D * W).updateCol 0 y := by
    ext i j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [colsMat, colsZW]
    · simp [colsMat, colsZW, hW, mul_apply, mulVec, dotProduct]
  simp only [detCols]
  rw [h1, colsMat_colsZW, ← hW, ← cramer_apply, ← cramer_apply, cramer_eq_adjugate_mulVec,
    cramer_eq_adjugate_mulVec, adjugate_mul_distrib, ← mulVec_mulVec]

/-- Columns of `adj D` are parallel to a kernel vector `z`:
`adj(D)_{a b} z_c = adj(D)_{c b} z_a` whenever `D z = 0`. -/
theorem adjugate_mul_kernel_comm {m : Type*} [Fintype m] [DecidableEq m]
    (D : Matrix m m K) (z : m → K) (hz : D *ᵥ z = 0) (a b c : m) :
    D.adjugate a b * z c = D.adjugate c b * z a := by
  by_cases hac : a = c
  · subst hac; rfl
  have hadj : ∀ x, D.adjugate x b = (D.updateCol x (Pi.single b 1)).det := by
    intro x
    rw [← cramer_apply, cramer_eq_adjugate_mulVec, mulVec_single_one]
    rfl
  set N := D.updateCol a (Pi.single b 1) with hN
  have hDN : D *ᵥ z - N *ᵥ z = z a • ((fun i => D i a) - Pi.single b 1) := by
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hN, mulVec, dotProduct, updateCol_apply]
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
    · simp; ring
    · intro k _ hk; simp [hk]
    · simp
  have hNz : N *ᵥ z = z a • (Pi.single b 1 - fun i => D i a) := by
    rw [hz, zero_sub] at hDN
    rw [← neg_neg (N *ᵥ z), hDN, ← smul_neg, neg_sub]
  have key : (N.adjugate *ᵥ (N *ᵥ z)) c = (N.det • z) c := by
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  rw [hNz, mulVec_smul, mulVec_sub, ← cramer_eq_adjugate_mulVec,
    ← cramer_eq_adjugate_mulVec] at key
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, cramer_apply] at key
  have h1 : (N.updateCol c (Pi.single b 1)).det = 0 := by
    apply det_zero_of_column_eq hac
    intro k
    simp [hN, hac]
  have h2 : (N.updateCol c (fun i => D i a)).det = -(D.updateCol c (Pi.single b 1)).det := by
    have hm : N.updateCol c (fun i => D i a) =
        (D.updateCol c (Pi.single b 1)).submatrix id (Equiv.swap a c) := by
      ext i j
      simp only [hN, updateCol_apply, submatrix_apply, id]
      by_cases hja : j = a
      · subst hja
        rw [Equiv.swap_apply_left]
        simp [hac]
      · by_cases hjc : j = c
        · subst hjc
          rw [Equiv.swap_apply_right]
          simp [hac]
        · rw [Equiv.swap_apply_of_ne_of_ne hja hjc]
          simp [hja, hjc]
    rw [hm, det_permute', Equiv.Perm.sign_swap hac]
    simp
  rw [h1, h2] at key
  rw [hadj a, hadj c]
  linear_combination -key

/-- Rows of `adj D` are parallel to a functional `λ` killing the image:
`adj(D)_{a b} λ_d = adj(D)_{a d} λ_b` whenever `λ D = 0`. -/
theorem adjugate_mul_cokernel_comm {m : Type*} [Fintype m] [DecidableEq m]
    (D : Matrix m m K) (lam : m → K) (hlam : lam ᵥ* D = 0) (a b d : m) :
    D.adjugate a b * lam d = D.adjugate a d * lam b := by
  have h := adjugate_mul_kernel_comm Dᵀ lam (by rw [mulVec_transpose]; exact hlam) b a d
  rwa [← adjugate_transpose, transpose_apply, transpose_apply] at h

/-- Rank-one shape of `adj D`: `adj(D)_{a b} z_c λ_d = adj(D)_{c d} z_a λ_b`. -/
theorem adjugate_rankOne {m : Type*} [Fintype m] [DecidableEq m]
    (D : Matrix m m K) (z lam : m → K) (hz : D *ᵥ z = 0) (hlam : lam ᵥ* D = 0) (a b c d : m) :
    D.adjugate a b * (z c * lam d) = D.adjugate c d * (z a * lam b) := by
  have h1 := adjugate_mul_kernel_comm D z hz a b c
  have h2 := adjugate_mul_cokernel_comm D lam hlam c b d
  linear_combination lam d * h1 + z a * h2

/-- `(z_c λ_d) · adj(D) y = (adj(D)_{c d} λ(y)) · z`. -/
theorem smul_adjugate_mulVec {m : Type*} [Fintype m] [DecidableEq m]
    (D : Matrix m m K) (z lam : m → K) (hz : D *ᵥ z = 0) (hlam : lam ᵥ* D = 0) (c d : m)
    (y : m → K) :
    (z c * lam d) • (D.adjugate *ᵥ y) = (D.adjugate c d * (lam ⬝ᵥ y)) • z := by
  ext a
  simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := adjugate_rankOne D z lam hz hlam a b c d
  linear_combination y b * this

/-- **The key identity** (`PROVED`): for `D z = 0`, `λ D = 0`, every complement `(w, y)` and every pair
`(c, d)`: `det[D w | y] · z_c λ_d = (-1)^n · adj(D)_{c d} · det[z | w] · λ(y)`.
No nondegeneracy is assumed. -/
theorem den_mul_eq {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (z lam : Fin (n + 1) → K)
    (hz : D *ᵥ z = 0) (hlam : lam ᵥ* D = 0) (w : Fin n → Fin (n + 1) → K) (y : Fin (n + 1) → K)
    (c d : Fin (n + 1)) :
    detCols (colsDWY D w y) * (z c * lam d) =
      (-1) ^ n * (D.adjugate c d * (detCols (colsZW z w) * (lam ⬝ᵥ y))) := by
  rw [detCols_colsDWY_eq, detCols_colsZW_mulVec]
  have h := congrArg (fun x => detCols (colsZW x w)) (smul_adjugate_mulVec D z lam hz hlam c d y)
  simp only [detCols_colsZW_smul] at h
  linear_combination (-1 : K) ^ n * h

/-! ### Main theorems -/

/-- **Well-definedness of the determinant-line coordinate** (tex 3882-3892, `PROVED`).
If `D z = 0` (`z` is a cycle) and `λ D = 0` (`λ` kills the boundaries), then any two complements
`(w, y)`, `(w', y')` with nonzero denominators `det[D w | y]`, `det[D w' | y']` give the same value of
`u = det[z | w] · λ(y) / det[D w | y]`: the coordinate of `[z] ⊗ [λ]` in
`det⁻¹ C ≃ H¹ ⊗ (H²)^*` does not depend on the splitting used to compute it. -/
theorem classFunctionalCoordWith_indep {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (z lam : Fin (n + 1) → K) (hz : D *ᵥ z = 0) (hlam : lam ᵥ* D = 0)
    (w w' : Fin n → Fin (n + 1) → K) (y y' : Fin (n + 1) → K)
    (hden : detCols (colsDWY D w y) ≠ 0) (hden' : detCols (colsDWY D w' y') ≠ 0) :
    classFunctionalCoordWith D z lam w y = classFunctionalCoordWith D z lam w' y' := by
  unfold classFunctionalCoordWith
  rw [div_eq_div_iff hden hden']
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [detCols_colsZW_zero]
  rcases eq_or_ne lam 0 with rfl | hl0
  · simp
  obtain ⟨c, hc⟩ := Function.ne_iff.mp hz0
  obtain ⟨d, hd⟩ := Function.ne_iff.mp hl0
  have hX : z c * lam d ≠ 0 := mul_ne_zero hc hd
  have e1 := den_mul_eq D z lam hz hlam w y c d
  have e2 := den_mul_eq D z lam hz hlam w' y' c d
  apply mul_right_cancel₀ hX
  linear_combination (detCols (colsZW z w) * (lam ⬝ᵥ y)) * e2 -
    (detCols (colsZW z w') * (lam ⬝ᵥ y')) * e1

/-- The general Cramer identity behind `classFunctionalCoord_cramer`, without assuming `Δ ≠ 0`:
`u · Δ_{k₀ j₀} = (-1)^(n + j₀ + k₀) · z_{j₀} · λ_{k₀}` for every complement with nonzero
denominator. -/
theorem classFunctionalCoord_mul_minor {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (z lam : Fin (n + 1) → K) (hz : D *ᵥ z = 0) (hlam : lam ᵥ* D = 0) (k0 j0 : Fin (n + 1))
    (w : Fin n → Fin (n + 1) → K) (y : Fin (n + 1) → K) (hden : detCols (colsDWY D w y) ≠ 0) :
    classFunctionalCoordWith D z lam w y * (D.submatrix k0.succAbove j0.succAbove).det =
      (-1) ^ (n + (j0 : ℕ) + (k0 : ℕ)) * (z j0 * lam k0) := by
  have e := den_mul_eq D z lam hz hlam w y j0 k0
  rw [adjugate_fin_succ_eq_det_submatrix] at e
  set Δ := (D.submatrix k0.succAbove j0.succAbove).det
  set den := detCols (colsDWY D w y)
  set num := detCols (colsZW z w) * (lam ⬝ᵥ y)
  have hs : ∀ m : ℕ, (-1 : K) ^ m * (-1) ^ m = 1 := fun m => by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  unfold classFunctionalCoordWith
  change num / den * Δ = _
  rw [div_mul_eq_mul_div, div_eq_iff hden]
  have hsplit : (-1 : K) ^ (n + (j0 : ℕ) + (k0 : ℕ)) = (-1) ^ n * (-1) ^ ((k0 : ℕ) + (j0 : ℕ)) := by
    rw [← pow_add]; congr 1; ring
  rw [hsplit]
  have h1 := hs n
  have h2 := hs ((k0 : ℕ) + (j0 : ℕ))
  linear_combination (-((-1 : K) ^ n * (-1) ^ ((k0 : ℕ) + (j0 : ℕ)))) * e - num * Δ * h1 -
    num * Δ * (-1 : K) ^ n * (-1 : K) ^ n * h2

/-! ### The standard complement of a maximal minor -/

/-- The standard complement attached to the column `j₀`: `w_i = e_{j₀.succAbove i}` (all standard basis
vectors of `C¹` except `e_{j₀}`). -/
def stdW {n : ℕ} (j0 : Fin (n + 1)) : Fin n → Fin (n + 1) → K :=
  fun i => Pi.single (j0.succAbove i) 1

/-- The standard complement attached to the row `k₀`: `y = f_{k₀}`. -/
def stdY {n : ℕ} (k0 : Fin (n + 1)) : Fin (n + 1) → K :=
  Pi.single k0 1

/-- Laplace expansion along the last column: `det[D e_{j₀.succAbove 0} | ⋯ | x] =
∑_k (-1)^(k+n) x_k M_{k j₀}`, with `M_{k j₀}` the maximal minor deleting row `k` and column `j₀`. -/
theorem detCols_colsDWY_stdW {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (j0 : Fin (n + 1))
    (x : Fin (n + 1) → K) :
    detCols (colsDWY D (stdW j0) x) =
      ∑ k : Fin (n + 1), (-1) ^ ((k : ℕ) + n) * x k * (D.submatrix k.succAbove j0.succAbove).det := by
  unfold detCols
  rw [det_succ_column _ (Fin.last n)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsub : (colsMat (colsDWY D (stdW j0) x)).submatrix k.succAbove (Fin.last n).succAbove =
      D.submatrix k.succAbove j0.succAbove := by
    ext r c
    simp [colsMat, colsDWY, stdW, Fin.succAbove_last]
  rw [hsub]
  simp [colsMat, colsDWY]

/-- **The standard complement's denominator** (`PROVED`): for `w = (e_i)_{i ≠ j₀}` (indexed by
`j₀.succAbove`) and `y = f_{k₀}`, `det[D w | y] = (-1)^(k₀ + n) · Δ` with
`Δ = det (D.submatrix k₀.succAbove j₀.succAbove)` the maximal minor deleting row `k₀` and column `j₀`. -/
theorem den_stdComplement {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (k0 j0 : Fin (n + 1)) :
    detCols (colsDWY D (stdW j0) (stdY k0)) =
      (-1) ^ ((k0 : ℕ) + n) * (D.submatrix k0.succAbove j0.succAbove).det := by
  rw [detCols_colsDWY_stdW, Fintype.sum_eq_single k0]
  · simp [stdY]
  · intro k hk
    simp [stdY, hk]

/-- The standard complement of `(k₀, j₀)` is admissible exactly when `Δ_{k₀ j₀} ≠ 0`. -/
theorem den_stdComplement_ne_zero_iff {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (k0 j0 : Fin (n + 1)) :
    detCols (colsDWY D (stdW j0) (stdY k0)) ≠ 0 ↔ (D.submatrix k0.succAbove j0.succAbove).det ≠ 0 := by
  rw [den_stdComplement]
  constructor
  · intro h h0; exact h (by rw [h0, mul_zero])
  · intro h; exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h

/-- **The coordinate is defined iff some maximal minor is nonzero** (`PROVED`): an admissible complement
(nonzero denominator `det[D w | y]`) exists iff some maximal minor `Δ_{k₀ j₀}` of `D` is nonzero.
(`→`: `det[D w | y] = ± det[adj(D) y | w]`, so `adj D ≠ 0`; `←`: the standard complement.) -/
theorem exists_complement_iff_exists_minor_ne_zero {n : ℕ}
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    (∃ (w : Fin n → Fin (n + 1) → K) (y : Fin (n + 1) → K), detCols (colsDWY D w y) ≠ 0) ↔
      ∃ k0 j0 : Fin (n + 1), (D.submatrix k0.succAbove j0.succAbove).det ≠ 0 := by
  constructor
  · rintro ⟨w, y, h⟩
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    apply h
    have hadj : D.adjugate = 0 := by
      ext i j
      rw [adjugate_fin_succ_eq_det_submatrix, hall j i]
      simp
    rw [detCols_colsDWY_eq, detCols_colsZW_mulVec, hadj, zero_mulVec, detCols_colsZW_zero, mul_zero]
  · rintro ⟨k0, j0, h⟩
    exact ⟨stdW j0, stdY k0, (den_stdComplement_ne_zero_iff D k0 j0).mpr h⟩

/-- **The Cramer formula `u = ±αβ/Δ`** (tex 4958-4964, `PROVED`): `u = ± z_{j₀} λ(f_{k₀}) / M_{k₀ j₀}`
for every nonzero maximal minor `M_{k₀ j₀}`, and the coordinate does not depend on the complement.

For `D z = 0` and `λ D = 0`, for EVERY maximal minor `Δ = det (D.submatrix k₀.succAbove j₀.succAbove)`
(delete row `k₀` and column `j₀`) with `Δ ≠ 0` and EVERY admissible complement `(w, y)`:
`u · Δ = s · (z_{j₀} · λ_{k₀})` and `u = s · z_{j₀} λ_{k₀} / Δ`, with the explicit sign
`s = (-1)^(n + j₀ + k₀) ∈ {1, -1}` (see `neg_one_pow_eq_or`); moreover the standard complement
`w = (e_i)_{i ≠ j₀}`, `y = f_{k₀}` is admissible, so the coordinate is defined.
Here `α = z_{j₀}` is the surviving cycle coordinate and `β = λ_{k₀} = λ(f_{k₀})`.

DEPARTURE: the manuscript reaches `u = ±αβ/Δ` by "determinant-one Schur operations"; here the formula
is proved directly from the adjugate identities `det[y | D w] = det[adj(D) y | w]` and
`adj(D)_{ab} z_c λ_d = adj(D)_{cd} z_a λ_b` (rank-one shape of `adj D` on a complex with `D z = 0`,
`λ D = 0`), which give the same Cramer formula for every complement at once. -/
theorem classFunctionalCoord_cramer {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (z lam : Fin (n + 1) → K) (hz : D *ᵥ z = 0) (hlam : lam ᵥ* D = 0) (k0 j0 : Fin (n + 1))
    (hΔ : (D.submatrix k0.succAbove j0.succAbove).det ≠ 0)
    (w : Fin n → Fin (n + 1) → K) (y : Fin (n + 1) → K) (hden : detCols (colsDWY D w y) ≠ 0) :
    classFunctionalCoordWith D z lam w y * (D.submatrix k0.succAbove j0.succAbove).det =
        (-1) ^ (n + (j0 : ℕ) + (k0 : ℕ)) * (z j0 * lam k0) ∧
      classFunctionalCoordWith D z lam w y =
        (-1) ^ (n + (j0 : ℕ) + (k0 : ℕ)) * (z j0 * lam k0) /
          (D.submatrix k0.succAbove j0.succAbove).det ∧
      detCols (colsDWY D (stdW j0) (stdY k0)) ≠ 0 := by
  have h := classFunctionalCoord_mul_minor D z lam hz hlam k0 j0 w y hden
  refine ⟨h, ?_, (den_stdComplement_ne_zero_iff D k0 j0).mpr hΔ⟩
  rw [eq_div_iff hΔ]
  exact h

/-- The coordinate computed through the standard complement of a nonzero maximal minor. -/
theorem classFunctionalCoord_stdComplement {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (z lam : Fin (n + 1) → K) (hz : D *ᵥ z = 0) (hlam : lam ᵥ* D = 0) (k0 j0 : Fin (n + 1))
    (hΔ : (D.submatrix k0.succAbove j0.succAbove).det ≠ 0) :
    classFunctionalCoordWith D z lam (stdW j0) (stdY k0) =
      (-1) ^ (n + (j0 : ℕ) + (k0 : ℕ)) * (z j0 * lam k0) /
        (D.submatrix k0.succAbove j0.succAbove).det :=
  (classFunctionalCoord_cramer D z lam hz hlam k0 j0 hΔ (stdW j0) (stdY k0)
    ((den_stdComplement_ne_zero_iff D k0 j0).mpr hΔ)).2.1

/-- The Cramer sign `(-1)^(n + j₀ + k₀)` is `1` or `-1`. -/
theorem cramerSign_eq_or (n j0 k0 : ℕ) :
    (-1 : K) ^ (n + j0 + k0) = 1 ∨ (-1 : K) ^ (n + j0 + k0) = -1 :=
  neg_one_pow_eq_or K _

/-! ### Valuations -/

/-- **Valuation form of the Cramer formula** (tex 4962-4964, `PROVED`): for any additive valuation
`v : K → WithTop ℤ`, `v u + v Δ = v (z_{j₀}) + v (λ_{k₀})`, for every maximal minor `Δ` and every
admissible complement (the sign `±1` has valuation `0`; both sides are `⊤` when `Δ = 0`). -/
theorem classFunctionalCoord_valuation {n : ℕ} (v : AddValuation K (WithTop ℤ))
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (z lam : Fin (n + 1) → K) (hz : D *ᵥ z = 0)
    (hlam : lam ᵥ* D = 0) (k0 j0 : Fin (n + 1)) (w : Fin n → Fin (n + 1) → K)
    (y : Fin (n + 1) → K) (hden : detCols (colsDWY D w y) ≠ 0) :
    v (classFunctionalCoordWith D z lam w y) + v (D.submatrix k0.succAbove j0.succAbove).det =
      v (z j0) + v (lam k0) := by
  have h := classFunctionalCoord_mul_minor D z lam hz hlam k0 j0 w y hden
  rw [← AddValuation.map_mul, h, AddValuation.map_mul, AddValuation.map_mul]
  have hs : v ((-1 : K) ^ (n + (j0 : ℕ) + (k0 : ℕ))) = 0 := by
    rw [AddValuation.map_pow, AddValuation.map_neg, AddValuation.map_one, smul_zero]
  rw [hs, zero_add]

/-- **The lower bound `v u ≥ -a-b`** (tex 4962-4964, "Consequently `v₂u_j ≥ -a-b`", `PROVED`):
if `α = z_{j₀}` is integral (`v α ≥ 0`), `β = λ_{k₀}` has `v β ≥ -a`, and the maximal minor `Δ` has
finite valuation `v Δ = b`, then `v u ≥ -a-b`, for every admissible complement. -/
theorem classFunctionalCoord_valuation_bound {n : ℕ} (v : AddValuation K (WithTop ℤ))
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (z lam : Fin (n + 1) → K) (hz : D *ᵥ z = 0)
    (hlam : lam ᵥ* D = 0) (k0 j0 : Fin (n + 1)) (w : Fin n → Fin (n + 1) → K)
    (y : Fin (n + 1) → K) (hden : detCols (colsDWY D w y) ≠ 0) (a b : ℤ)
    (hα : 0 ≤ v (z j0)) (hβ : ((-a : ℤ) : WithTop ℤ) ≤ v (lam k0))
    (hb : v (D.submatrix k0.succAbove j0.succAbove).det = (b : WithTop ℤ)) :
    ((-a - b : ℤ) : WithTop ℤ) ≤ v (classFunctionalCoordWith D z lam w y) := by
  have key := classFunctionalCoord_valuation v D z lam hz hlam k0 j0 w y hden
  rw [hb] at key
  have h3 : ((-a : ℤ) : WithTop ℤ) ≤ v (classFunctionalCoordWith D z lam w y) + (b : WithTop ℤ) := by
    rw [key]
    calc ((-a : ℤ) : WithTop ℤ) = 0 + ((-a : ℤ) : WithTop ℤ) := (zero_add _).symm
      _ ≤ v (z j0) + v (lam k0) := add_le_add hα hβ
  generalize v (classFunctionalCoordWith D z lam w y) = t at h3 ⊢
  induction t using WithTop.recTopCoe with
  | top => exact le_top
  | coe m =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h3
    exact WithTop.coe_le_coe.mpr (by omega)

/-! ### The `[2^j]` remark -/

/-- The 2-adic additive valuation `v₂ : ℚ → WithTop ℤ` (Mathlib's `Padic.addValuation` restricted
along `ℚ → ℚ_[2]`). -/
noncomputable def vTwo : AddValuation ℚ (WithTop ℤ) :=
  (Padic.addValuation (p := 2)).comap (Rat.castHom ℚ_[2])

/-- `v₂ q = padicValRat 2 q` for `q ≠ 0`. -/
theorem vTwo_apply {q : ℚ} (hq : q ≠ 0) : vTwo q = ((padicValRat 2 q : ℤ) : WithTop ℤ) := by
  change Padic.addValuation ((q : ℚ_[2])) = _
  rw [Padic.addValuation.apply (by exact_mod_cast hq), Padic.valuation_ratCast]

/-- The complexes `D_j = [2^j] ⊕ [0] = diag(2^j, 0)` (fixed size `2 × 2`, integral entries). -/
def twoPowComplex (j : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![2 ^ j, 0; 0, 0]

/-- The primitive integral vector `e₂` (used both as the cycle `z = e₂` and the functional `λ = f₂`). -/
def eTwo : Fin 2 → ℚ :=
  Pi.single 1 1

/-- The maximal minor `Δ_{1 1}` of `D_j` (delete the second row and column) is `2^j`. -/
theorem twoPowComplex_minor (j : ℕ) :
    ((twoPowComplex j).submatrix (1 : Fin 2).succAbove (1 : Fin 2).succAbove).det = 2 ^ j := by
  rw [det_unique]
  simp [twoPowComplex]

/-- **The `[2^j]` remark** (tex 4972-4973, "Bounded matrix size alone would not prove it: `[2^j]` is
a counterexample to that inference", `PROVED`).

For `D_j = diag(2^j, 0)` over `ℚ` (all of the same size `2 × 2`, integral entries):
`z = e₂` is a cycle and `λ = f₂` kills the boundaries; the kernel is exactly the line `ℚ e₂`
(rank-one kernel); the standard complement is admissible; for EVERY admissible complement the
class-functional coordinate is `u_j = -2^{-j}`; its 2-adic valuation is `-j`; hence NO lower bound
for `v₂ u_j` holds uniformly in `j`, although the matrix size is fixed. (Consistently with
`classFunctionalCoord_valuation_bound`: here `α = β = 1`, `a = 0`, and the minor `Δ_j = 2^j` has
valuation `b = j`, unbounded; the bound `-a-b = -j` is attained.) -/
theorem twoPow_counterexample :
    (∀ j : ℕ, twoPowComplex j *ᵥ eTwo = 0 ∧ eTwo ᵥ* twoPowComplex j = 0) ∧
    (∀ j : ℕ, ∀ x : Fin 2 → ℚ, twoPowComplex j *ᵥ x = 0 ↔ ∃ t : ℚ, x = t • eTwo) ∧
    (∀ j : ℕ, detCols (colsDWY (twoPowComplex j) (stdW 1) (stdY 1)) ≠ 0) ∧
    (∀ j : ℕ, ∀ (w : Fin 1 → Fin 2 → ℚ) (y : Fin 2 → ℚ),
        detCols (colsDWY (twoPowComplex j) w y) ≠ 0 →
        classFunctionalCoordWith (twoPowComplex j) eTwo eTwo w y = -((2 : ℚ) ^ j)⁻¹) ∧
    (∀ j : ℕ, vTwo (-((2 : ℚ) ^ j)⁻¹) = ((-(j : ℤ) : ℤ) : WithTop ℤ)) ∧
    ¬ ∃ C : ℤ, ∀ j : ℕ, ∀ (w : Fin 1 → Fin 2 → ℚ) (y : Fin 2 → ℚ),
        detCols (colsDWY (twoPowComplex j) w y) ≠ 0 →
        (C : WithTop ℤ) ≤ vTwo (classFunctionalCoordWith (twoPowComplex j) eTwo eTwo w y) := by
  have hcx : ∀ j : ℕ, twoPowComplex j *ᵥ eTwo = 0 ∧ eTwo ᵥ* twoPowComplex j = 0 := by
    intro j
    constructor
    · ext i; fin_cases i <;> simp [twoPowComplex, eTwo, mulVec, dotProduct, Fin.sum_univ_two]
    · ext i; fin_cases i <;> simp [twoPowComplex, eTwo, vecMul, dotProduct, Fin.sum_univ_two]
  have hden : ∀ j : ℕ, detCols (colsDWY (twoPowComplex j) (stdW 1) (stdY 1)) ≠ 0 := by
    intro j
    rw [den_stdComplement_ne_zero_iff, twoPowComplex_minor]
    exact pow_ne_zero _ two_ne_zero
  have hu : ∀ j : ℕ, ∀ (w : Fin 1 → Fin 2 → ℚ) (y : Fin 2 → ℚ),
      detCols (colsDWY (twoPowComplex j) w y) ≠ 0 →
      classFunctionalCoordWith (twoPowComplex j) eTwo eTwo w y = -((2 : ℚ) ^ j)⁻¹ := by
    intro j w y hwy
    have h := classFunctionalCoord_mul_minor (twoPowComplex j) eTwo eTwo (hcx j).1 (hcx j).2 1 1 w y
      hwy
    rw [twoPowComplex_minor] at h
    have h2 : (2 : ℚ) ^ j ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [eq_neg_iff_add_eq_zero, ← mul_right_inj' h2, mul_add, mul_inv_cancel₀ h2, mul_zero,
      mul_comm, h]
    norm_num [eTwo]
  have hv : ∀ j : ℕ, vTwo (-((2 : ℚ) ^ j)⁻¹) = ((-(j : ℤ) : ℤ) : WithTop ℤ) := by
    intro j
    rw [vTwo_apply (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ two_ne_zero)))]
    congr 1
    rw [padicValRat.neg, padicValRat.inv, padicValRat.pow]
    have : padicValRat 2 (2 : ℚ) = 1 := by
      have := padicValRat.self (p := 2) one_lt_two
      exact_mod_cast this
    rw [this, mul_one]
  refine ⟨hcx, ?_, hden, hu, hv, ?_⟩
  · intro j x
    constructor
    · intro h
      have h0 := congrFun h 0
      simp [twoPowComplex, mulVec, dotProduct, Fin.sum_univ_two] at h0
      refine ⟨x 1, ?_⟩
      ext i; fin_cases i <;> simp [eTwo, h0]
    · rintro ⟨t, rfl⟩
      rw [mulVec_smul, (hcx j).1, smul_zero]
  · rintro ⟨C, hC⟩
    set j := (1 - C).toNat with hj
    have h := hC j (stdW 1) (stdY 1) (hden j)
    rw [hu j _ _ (hden j), hv j, WithTop.coe_le_coe] at h
    have : (1 - C) ≤ (j : ℤ) := Int.self_le_toNat (1 - C)
    omega

/-- The hypotheses of `classFunctionalCoord_cramer` are satisfiable (non-vacuity), e.g. by
`D = diag(2^j, 0)`, `z = λ = e₂`, the minor `(k₀, j₀) = (1, 1)` and its standard complement. -/
example (j : ℕ) :
    twoPowComplex j *ᵥ eTwo = 0 ∧ eTwo ᵥ* twoPowComplex j = 0 ∧
      ((twoPowComplex j).submatrix (1 : Fin 2).succAbove (1 : Fin 2).succAbove).det ≠ 0 ∧
      detCols (colsDWY (twoPowComplex j) (stdW 1) (stdY 1)) ≠ 0 :=
  ⟨(twoPow_counterexample.1 j).1, (twoPow_counterexample.1 j).2,
    by rw [twoPowComplex_minor]; exact pow_ne_zero _ two_ne_zero, twoPow_counterexample.2.2.1 j⟩

/-- The hypotheses of `classFunctionalCoord_valuation_bound` are satisfiable (non-vacuity): for
`D_j = diag(2^j, 0)`, `v = v₂`, `a = 0`, `b = j`. -/
example (j : ℕ) :
    0 ≤ vTwo (eTwo 1) ∧ ((-(0 : ℤ) : ℤ) : WithTop ℤ) ≤ vTwo (eTwo 1) ∧
      vTwo ((twoPowComplex j).submatrix (1 : Fin 2).succAbove (1 : Fin 2).succAbove).det =
        ((j : ℤ) : WithTop ℤ) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [eTwo]
  · simp [eTwo]
  · rw [twoPowComplex_minor, vTwo_apply (pow_ne_zero _ two_ne_zero), padicValRat.pow]
    have : padicValRat 2 (2 : ℚ) = 1 := by
      have := padicValRat.self (p := 2) one_lt_two
      exact_mod_cast this
    rw [this, mul_one]

/-! ### Nullity one forces a nonzero maximal minor -/

/-- **Nullity one forces a nonzero maximal minor** (`PROVED`; supports tex 4958 "At terminal outer
dimension one a maximal boundary minor `Δ` is nonzero"). If the kernel of the square matrix `D` over
a field is exactly the line `K z`, then for any `j₀` with `z_{j₀} ≠ 0` some maximal minor
`Δ_{k₀ j₀}` is nonzero; in particular `adj D ≠ 0` and, by
`exists_complement_iff_exists_minor_ne_zero`, the class-functional coordinate is defined.
Proof: the columns `≠ j₀` are independent (a relation among them is a kernel vector vanishing at
`j₀`); if every `Δ_{k j₀}` vanished, every `x` would be a combination of these `n` columns, so `n`
vectors would span `K^{n+1}`. -/
theorem exists_minor_ne_zero_of_ker_eq_span {n : ℕ} (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (z : Fin (n + 1) → K) (hker : ∀ x, D *ᵥ x = 0 ↔ ∃ t : K, x = t • z)
    (j0 : Fin (n + 1)) (hj0 : z j0 ≠ 0) :
    ∃ k0 : Fin (n + 1), (D.submatrix k0.succAbove j0.succAbove).det ≠ 0 := by
  set D' : Matrix (Fin (n + 1)) (Fin n) K := D.submatrix id j0.succAbove with hD'
  have hinj : ∀ c : Fin n → K, D' *ᵥ c = 0 → c = 0 := by
    intro c hc
    have hext : D *ᵥ (Fin.insertNth j0 0 c) = D' *ᵥ c := by
      ext i
      simp only [mulVec, dotProduct, hD', submatrix_apply, id]
      rw [Fin.sum_univ_succAbove _ j0]
      simp
    obtain ⟨t, ht⟩ := (hker _).mp (hext.trans hc)
    have ht0 : t = 0 := by
      have h := congrFun ht j0
      simp only [Fin.insertNth_apply_same, Pi.smul_apply, smul_eq_mul] at h
      rcases mul_eq_zero.mp h.symm with h' | h'
      · exact h'
      · exact absurd h' hj0
    ext i
    have h := congrFun ht (j0.succAbove i)
    simpa [ht0] using h
  by_contra hall
  simp only [not_exists, ne_eq, not_not] at hall
  have hsurj : Function.Surjective D'.mulVecLin := by
    intro x
    have hdet : (colsMat (colsDWY D (stdW j0) x)).det = 0 := by
      have h := detCols_colsDWY_stdW D j0 x
      unfold detCols at h
      rw [h]
      exact Finset.sum_eq_zero fun k _ => by rw [hall k, mul_zero]
    obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr hdet
    have hsplit : colsMat (colsDWY D (stdW j0) x) *ᵥ v =
        D' *ᵥ (fun i => v i.castSucc) + v (Fin.last n) • x := by
      ext r
      simp only [mulVec, dotProduct, colsMat, colsDWY, of_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      rw [Fin.sum_univ_castSucc]
      simp [stdW, hD']
      ring
    rw [hsplit] at hv
    have hlast : v (Fin.last n) ≠ 0 := by
      intro h0
      apply hv0
      rw [h0, zero_smul, add_zero] at hv
      have hc := hinj _ hv
      ext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact h0
      · exact congrFun hc i
    have hu : D' *ᵥ (fun i => v i.castSucc) = -(v (Fin.last n) • x) :=
      eq_neg_of_add_eq_zero_left hv
    refine ⟨(-(v (Fin.last n))⁻¹) • (fun i => v i.castSucc), ?_⟩
    rw [mulVecLin_apply, mulVec_smul, hu, smul_neg, neg_smul, neg_neg, smul_smul,
      inv_mul_cancel₀ hlast, one_smul]
  have hle := LinearMap.finrank_range_le D'.mulVecLin
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at hle
  omega

/-- Nullity one, stated with `finrank`: if `ker D` is one-dimensional then some maximal minor of `D`
is nonzero (`PROVED`). -/
theorem exists_minor_ne_zero_of_finrank_ker_eq_one {n : ℕ}
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (h : Module.finrank K (LinearMap.ker D.mulVecLin) = 1) :
    ∃ k0 j0 : Fin (n + 1), (D.submatrix k0.succAbove j0.succAbove).det ≠ 0 := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h
  have hz0 : (v : Fin (n + 1) → K) ≠ 0 := fun h0 => hv0 (Subtype.ext h0)
  have hker : ∀ x, D *ᵥ x = 0 ↔ ∃ t : K, x = t • (v : Fin (n + 1) → K) := by
    intro x
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := hv ⟨x, by simpa using hx⟩
      exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
    · rintro ⟨t, rfl⟩
      have hvk : D *ᵥ (v : Fin (n + 1) → K) = 0 := by
        have h' := LinearMap.mem_ker.mp v.2
        rwa [mulVecLin_apply] at h'
      rw [mulVec_smul, hvk, smul_zero]
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hz0
  obtain ⟨k0, hk0⟩ := exists_minor_ne_zero_of_ker_eq_span D _ hker j0 hj0
  exact ⟨k0, j0, hk0⟩

end ZInQ.Manuscript.RC.Uniform
