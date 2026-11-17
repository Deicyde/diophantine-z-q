import ZInQKernel.Contrib.OneProof.RC.Determinant.BudgetLength
import ZInQKernel.Contrib.OneProof.RC.Determinant.SmithLength
import ZInQKernel.Contrib.OneProof.RC.Determinant.Clearing

/-!
# The fixed-field budget (5.7) for the determinant clearing (Lane RC7)

Manuscript `diophantine_zq.tex` (11/5; identical in Version 19), Lemma
`ex:limits-fixed-field-budget`, tex 5251–5392.

This file packages the budget (5.7),
`rank_total C_old ≤ 2 d_K + 12`, `m ≤ d_K + 5`, `h₁ ≤ h_K + 2 c_E + 2 t_K`,
into the two hypotheses consumed by the clearing (`Clearing.lean`, `Output.lean`):
`B.mTot ≤ d_K + 5` and `B.hSmith ≤ h_K + 2 c_E + 2 t_K` for the central Smith data `B`.

What is PROVED here, beyond `BudgetLength.lean` and `SmithLength.lean`:
* tex 5340–5342: a matrix over `ℤ₂` whose determinant has valuation at most `c` cannot acquire a
  zero determinant (or change that valuation) under a perturbation divisible by `2^{c+1}`;
* tex 5324–5334: the moving singular differential `Φ - r` has `v₂ det(Φ - r) = v₂(r + 1 - a)` when
  `r` is a unit, so (with the moving-character bound) the two singular complexes have `H¹ = 0` and
  `J_r` of length at most `2 c_E`;
* tex 5375–5383: the torsion length of the cokernels of the central Smith blocks equals the sum of
  the valuations of the Smith entries (`hSmith`): every disk contributes its exponent.

The cohomological inputs — the dimensions (5.7a), the torsion identifications (5.7b), the limiting
triangle (5.7c) and its long exact sequence (5.7d), the moving-character valuation bound, and the
identification of the torsion of `H^*(D_c)` with the cokernels of the central Smith blocks — are
hypotheses, named after the displays they encode (the cohomological counts are the shared top
layer's "RankCounts" area).
-/

namespace ZInQ.Manuscript.RC.Determinant

open Matrix Finset

/-! ### Stability of the determinant valuation (tex 5340–5342) -/

/-- **Tex 5340–5342 (PROVED).**  "A matrix whose determinant has valuation at most `c_E` cannot
acquire a zero determinant in this limit: the property is determined modulo `2^{c_E+1}`."  If
`v₂ det X ≤ c` and `X' ≡ X (mod 2^{c+1})` entrywise, then `det X' ≠ 0` and
`v₂ det X' = v₂ det X`. -/
theorem det_valuation_stable {n : Type*} [Fintype n] [DecidableEq n] (X X' : Matrix n n ℤ_[2])
    (c : ℕ) (hX : X.det ≠ 0) (hc : X.det.valuation ≤ c)
    (hXX' : ∀ i j, (2 : ℤ_[2]) ^ (c + 1) ∣ X' i j - X i j) :
    X'.det ≠ 0 ∧ X'.det.valuation = X.det.valuation := by
  let π := Ideal.Quotient.mk (Ideal.span {(2 : ℤ_[2]) ^ (c + 1)})
  have hmap : X'.map π = X.map π := by
    ext i j
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (hXX' i j))
  have hdet : π X'.det = π X.det := by
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hmap]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hdet)
  set v := X.det.valuation with hv
  have hspec := PadicInt.unitCoeff_spec hX
  set u := PadicInt.unitCoeff hX
  obtain ⟨k, hk⟩ : ∃ k, c + 1 = v + 1 + k := ⟨c - v, by omega⟩
  -- `det X' = 2^v (u + 2 · 2^k w)` with `u + 2(2^k w)` a unit
  have hu' : IsUnit ((u : ℤ_[2]) + 2 * (2 ^ k * w)) := by
    by_contra hnu
    have hmem : (u : ℤ_[2]) + 2 * (2 ^ k * w) ∈ IsLocalRing.maximalIdeal ℤ_[2] := hnu
    have h2mem : 2 * (2 ^ k * w) ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    have : (u : ℤ_[2]) ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
      simpa using Ideal.sub_mem _ hmem h2mem
    exact this u.isUnit
  have hX' : X'.det = (2 : ℤ_[2]) ^ v * ((u : ℤ_[2]) + 2 * (2 ^ k * w)) := by
    have : X'.det = X.det + (2 : ℤ_[2]) ^ (c + 1) * w := by rw [← hw]; ring
    rw [this, hk, hspec]
    simp only [Nat.cast_ofNat]
    ring
  set u' := hu'.unit
  have hX'' : X'.det = (2 : ℤ_[2]) ^ v * (u' : ℤ_[2]) := hX'
  refine ⟨?_, ?_⟩
  · rw [hX'']
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) u'.ne_zero
  · rw [hX'']
    have := valuation_pow_mul_unit (p := 2) v u'
    simpa using this

/-! ### The moving singular complexes (tex 5318–5334) -/

/-- **Tex 5324–5331 (PROVED).**  For the arithmetic Frobenius `Φ` at a place over the moving prime,
with trace `a` and determinant `r` a unit of `ℤ₂`, `det(Φ - r) = r(r + 1 - a) = r det(1 - Φ)`, so
`v₂ det(Φ - r) = v₂(r + 1 - a)`; with the moving-character bound `v₂(r + 1 - a) ≤ c_E` the
determinant is nonzero of valuation at most `c_E`. -/
theorem singular_det_valuation (Φ : Matrix (Fin 2) (Fin 2) ℤ_[2]) (a r : ℤ_[2]) (hr : IsUnit r)
    (htr : Φ.trace = a) (hdet : Φ.det = r) (cE : ℕ) (hne : r + 1 - a ≠ 0)
    (hcE : (r + 1 - a).valuation ≤ cE) :
    (Φ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).det ≠ 0 ∧
      (Φ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).det.valuation ≤ cE := by
  obtain ⟨h1, -⟩ := det_sub_smul_one_fin_two Φ a r htr hdet
  have hr0 : r ≠ 0 := hr.ne_zero
  have hrv : r.valuation = 0 := by
    have := valuation_pow_mul_unit (p := 2) 0 hr.unit
    simpa using this
  rw [h1]
  refine ⟨mul_ne_zero hr0 hne, ?_⟩
  rw [PadicInt.valuation_mul hr0 hne, hrv, zero_add]
  exact hcE

/-- **Tex 5331–5334, 5350–5351 (PROVED).**  The two singular complexes at the places over the moving
prime have degree-two cokernel `J_r` of total length at most `2 c_E`. -/
theorem moving_J_length_le (Φ₁ Φ₂ : Matrix (Fin 2) (Fin 2) ℤ_[2]) (a₁ a₂ r : ℤ_[2]) (hr : IsUnit r)
    (htr₁ : Φ₁.trace = a₁) (hdet₁ : Φ₁.det = r) (htr₂ : Φ₂.trace = a₂) (hdet₂ : Φ₂.det = r)
    (cE : ℕ) (hne₁ : r + 1 - a₁ ≠ 0) (hne₂ : r + 1 - a₂ ≠ 0)
    (hcE₁ : (r + 1 - a₁).valuation ≤ cE) (hcE₂ : (r + 1 - a₂).valuation ≤ cE) :
    Module.length ℤ_[2]
        (((Fin 2 → ℤ_[2]) ⧸ LinearMap.range (Φ₁ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).mulVecLin) ×
        ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range (Φ₂ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).mulVecLin))
      ≤ 2 * cE := by
  obtain ⟨hX, hXc⟩ := singular_det_valuation Φ₁ a₁ r hr htr₁ hdet₁ cE hne₁ hcE₁
  obtain ⟨hY, hYc⟩ := singular_det_valuation Φ₂ a₂ r hr htr₂ hdet₂ cE hne₂ hcE₂
  exact singular_complexes_total_length_le _ _ hX hY cE hXc hYc

/-! ### The Smith entries and the torsion length (tex 5375–5383) -/

namespace SmithBlocks

variable {S O : Type*} [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O)

/-- **Tex 5375–5383 (PROVED).**  The cokernel of the central Smith block `diag(s_i)` has length
`∑_j v₂(s_ij)`, so the total over all blocks is `hSmith`: every disk contributes its exponent. -/
theorem sum_length_coker_eq_hSmith :
    ∑ i ∈ range B.n, Module.length ℤ_[2] ((Fin (B.m i) → ℤ_[2]) ⧸
      LinearMap.range (Matrix.diagonal (B.s i)).mulVecLin) = (B.hSmith : ℕ∞) := by
  rw [hSmith, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdet : (Matrix.diagonal (B.s i)).det ≠ 0 := by
    rw [det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun j _ => B.s_ne i j
  rw [length_quotient_range_eq_valuation_det _ hdet, det_diagonal, Nat.cast_sum]
  have hprod : ∀ (t : Finset (Fin (B.m i))), (∏ j ∈ t, B.s i j).valuation =
      ∑ j ∈ t, (B.s i j).valuation := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj,
        PadicInt.valuation_mul (B.s_ne i j) (Finset.prod_ne_zero_iff.2 fun j _ => B.s_ne i j), ih]
  rw [hprod, Nat.cast_sum]

end SmithBlocks

/-! ### The budget (5.7) in the form consumed by the clearing -/

/-- **Lemma `ex:limits-fixed-field-budget`, the budget (5.7) (tex 5251–5392; PROVED from the
cohomological inputs).**  For the central Smith data `B` of the remaining old complex:
`m = B.mTot ≤ d_K + 5` and `h₁ = B.hSmith ≤ h_K + 2 c_E + 2 t_K`.

Hypotheses and the displays they encode (the cohomological ones are the "RankCounts" inputs):
* `hfg`, `h57a`, `hQ`: the reduction modulo two of the triangle (5.7c), the dimensions
  `(2, d_K, d_K, 2)` of (5.7a), and the contribution of at most eight of the two singular disks
  (tex 5279–5283, 5355–5359; `two_singular_disks_mod_two_le_eight` in `BudgetLength`);
* `hmodel`, `hsmith`: the finite free model of `C_old` has total rank at most the total dimension of
  the cohomology of `D_c ⊗ 𝔽₂` (minimality, tex 5357–5359), and its integral Smith decomposition
  has one free generator in each of degrees one and two and `B.mTot` disks (tex 5375–5381);
* `[Subsingleton H0D]`, `e`, `h57d`: `H⁰(D_c) = 0` and the integral long exact sequence (5.7d)
  (tex 5361–5366);
* `ht₁`, `ht₃`, `hh`: `length H¹(C_K)_tors = t_K` (tex 5288–5292), `length H³(C_K) = t_K` (5.7b),
  `length H²(C_K)_tors = h_K` (tex 5259);
* `hJ`: `J_r = H²(Q_r)` is the product of the cokernels of the two moving singular differentials
  `Φ_k - r` (tex 5318–5334, 5350–5351), with the Frobenius trace/determinant data and the
  moving-character bound `v₂(r + 1 - a_k) ≤ c_E` (Proposition `ex:arith-moving-character`);
* `htors`: the torsion of `H^*(D_c)` is the cokernel of the central Smith blocks (the Smith
  decomposition, tex 5375–5383). -/
theorem budget_57
    {k : Type*} [Field k] {HC HD HQ : Fin 4 → Type*}
    [∀ n, AddCommGroup (HC n)] [∀ n, Module k (HC n)]
    [∀ n, AddCommGroup (HD n)] [∀ n, Module k (HD n)]
    [∀ n, AddCommGroup (HQ n)] [∀ n, Module k (HQ n)]
    [∀ n, FiniteDimensional k (HC n)] [∀ n, FiniteDimensional k (HQ n)]
    (f : ∀ n, HC n →ₗ[k] HD n) (g : ∀ n, HD n →ₗ[k] HQ n) (hfg : ∀ n, Function.Exact (f n) (g n))
    {dK : ℕ} (h57a : ∀ n, Module.finrank k (HC n) = (![2, dK, dK, 2] : Fin 4 → ℕ) n)
    (hQ : ∑ n, Module.finrank k (HQ n) ≤ 8)
    {S O : Type*} [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O)
    {rankTotal : ℕ} (hmodel : rankTotal ≤ ∑ n, Module.finrank k (HD n))
    (hsmith : rankTotal = 2 + 2 * B.mTot)
    {H0D H1C H1D H2C H2D J H3C H3D : Type*}
    [AddCommGroup H0D] [Module ℤ_[2] H0D] [AddCommGroup H1C] [Module ℤ_[2] H1C]
    [AddCommGroup H1D] [Module ℤ_[2] H1D] [AddCommGroup H2C] [Module ℤ_[2] H2C]
    [AddCommGroup H2D] [Module ℤ_[2] H2D] [AddCommGroup J] [Module ℤ_[2] J]
    [AddCommGroup H3C] [Module ℤ_[2] H3C] [AddCommGroup H3D] [Module ℤ_[2] H3D]
    [Subsingleton H0D] (e : H1D ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] H2D) (j : H2D →ₗ[ℤ_[2]] J) (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] H3D)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    {tK hK cE : ℕ} (ht₁ : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK)
    (ht₃ : Module.length ℤ_[2] H3C = tK)
    (hh : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK)
    (Φ₁ Φ₂ : Matrix (Fin 2) (Fin 2) ℤ_[2]) (a₁ a₂ r : ℤ_[2]) (hr : IsUnit r)
    (htr₁ : Φ₁.trace = a₁) (hdet₁ : Φ₁.det = r) (htr₂ : Φ₂.trace = a₂) (hdet₂ : Φ₂.det = r)
    (hne₁ : r + 1 - a₁ ≠ 0) (hne₂ : r + 1 - a₂ ≠ 0)
    (hcE₁ : (r + 1 - a₁).valuation ≤ cE) (hcE₂ : (r + 1 - a₂).valuation ≤ cE)
    (eJ : J ≃ₗ[ℤ_[2]]
      ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range (Φ₁ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).mulVecLin) ×
      ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range (Φ₂ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).mulVecLin))
    (htors : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H0D) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1D) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2D) +
        Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H3D) =
      ∑ i ∈ range B.n, Module.length ℤ_[2] ((Fin (B.m i) → ℤ_[2]) ⧸
        LinearMap.range (Matrix.diagonal (B.s i)).mulVecLin)) :
    B.mTot ≤ dK + 5 ∧ B.hSmith ≤ hK + 2 * cE + 2 * tK := by
  have hJ : Module.length ℤ_[2] J ≤ 2 * (cE : ℕ∞) := by
    rw [eJ.length_eq]
    exact_mod_cast moving_J_length_le Φ₁ Φ₂ a₁ a₂ r hr htr₁ hdet₁ htr₂ hdet₂ cE hne₁ hne₂ hcE₁ hcE₂
  obtain ⟨-, hm, htor⟩ := fixed_field_budget (H0D := H0D) f g hfg h57a hQ hmodel hsmith e i j δ l
    h57d (t := (tK : ℕ∞)) (h := (hK : ℕ∞)) (c := (cE : ℕ∞)) ht₁ ht₃ hh hJ
  refine ⟨hm, ?_⟩
  rw [htors, B.sum_length_coker_eq_hSmith] at htor
  exact_mod_cast htor

end ZInQ.Manuscript.RC.Determinant
