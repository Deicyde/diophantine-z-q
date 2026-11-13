import ZInQKernel.HDecomp.Analytic.Torus

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt4 from
`scratch/bp-analytic/Torus.lean`, §7.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

open scoped Manifold ContDiff Topology
open Set Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace BPAnalytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (Λ : Submodule ℤ E) [DiscreteTopology Λ]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℂ F H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

/-! ## §7. pkg-I1's QM lattice `ι(𝒪)(τ, 1)ᵀ` and its period matrix `Ω(τ)`

The definitions `B`, `oBasis`, `Mi`, `Mj`, `iota`, `latVec`, `Emat`, `F0mat`, `Pinv`, `Omega` are
copied verbatim from `scratch/pkg-I1/I1.lean` (§1, §2, §4). We prove: for `Im τ ≠ 0`,
* `Λ_τ = ι(𝒪)(τ, 1)ᵀ` is a full lattice in `ℂ²`;
* `F'(τ) = F₀(τ)P⁻¹` is invertible and carries `Ω(τ)ℤ² + ℤ²` onto `Λ_τ`;
* hence `det Im Ω(τ) ≠ 0` and `F'(τ)` induces a biholomorphic group isomorphism
  `ℂ² ⧸ Λ_{Ω(τ)} ≃ ℂ² ⧸ Λ_τ`: `Ω(τ)` is a period matrix of the QM torus `A_τ = ℂ² ⧸ Λ_τ`
  (pkg-I1 §4 claimed this from numerical checks; the polarization is not treated here). -/

namespace QM

open Matrix

/-- (pkg-I1) `B = (2,-3)`. -/
abbrev B := QuaternionAlgebra ℚ 2 0 (-3)

/-- (pkg-I1) N5's ordered basis `(1, i, (1+j)/2, (i+ij)/2)` of the maximal order `𝒪`. -/
def oBasis : Fin 4 → B := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨1/2, 0, 1/2, 0⟩, ⟨0, 1/2, 0, 1/2⟩]

/-- (pkg-I1) `ι(i) = [[√2,0],[0,-√2]]`. -/
def Mi : Matrix (Fin 2) (Fin 2) ℝ := !![√2, 0; 0, -√2]
/-- (pkg-I1) `ι(j) = [[0,-3],[1,0]]`. -/
def Mj : Matrix (Fin 2) (Fin 2) ℝ := !![0, -3; 1, 0]

/-- (pkg-I1) The real embedding `ι : B → M₂(ℝ)`. -/
def iota (x : B) : Matrix (Fin 2) (Fin 2) ℝ :=
  (x.re : ℝ) • 1 + (x.imI : ℝ) • Mi + (x.imJ : ℝ) • Mj + (x.imK : ℝ) • (Mi * Mj)

/-- (pkg-I1) `ι(x)·(τ, 1)ᵀ`. -/
def latVec (x : B) (τ : ℂ) : Fin 2 → ℂ := (iota x).map (fun r : ℝ => (r : ℂ)) *ᵥ ![τ, 1]

/-- (pkg-I1) `E(τ)`: columns `ι(1)v_τ`, `ι(i)v_τ`. -/
def Emat (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r c => ![latVec (oBasis 0) τ, latVec (oBasis 1) τ] c r

/-- (pkg-I1) `F₀(τ)`: columns `ι((1+j)/2)v_τ`, `ι((i+ij)/2)v_τ`. -/
def F0mat (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r c => ![latVec (oBasis 2) τ, latVec (oBasis 3) τ] c r

/-- (pkg-I1) `P⁻¹` for `P = [[-1,1],[1,-2]]`. -/
def Pinv : Matrix (Fin 2) (Fin 2) ℂ := !![-2, -1; -1, -1]

/-- (pkg-I1) The period matrix `Ω(τ) = (F₀(τ)P⁻¹)⁻¹E(τ)`. -/
def Omega (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (F0mat τ * Pinv)⁻¹ * Emat τ

theorem latVec0 (τ : ℂ) : latVec (oBasis 0) τ = ![τ, 1] := by
  ext i; fin_cases i <;> simp [latVec, iota, oBasis, Mi, Mj, mulVec, dotProduct, Fin.sum_univ_two]

theorem latVec1 (τ : ℂ) : latVec (oBasis 1) τ = ![√2 * τ, -√2] := by
  ext i; fin_cases i <;> simp [latVec, iota, oBasis, Mi, Mj, mulVec, dotProduct, Fin.sum_univ_two]

theorem latVec2 (τ : ℂ) : latVec (oBasis 2) τ = ![(τ - 3) / 2, (τ + 1) / 2] := by
  ext i; fin_cases i <;>
    simp [latVec, iota, oBasis, Mi, Mj, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem latVec3 (τ : ℂ) : latVec (oBasis 3) τ = ![√2 * (τ - 3) / 2, -(√2 * (τ + 1)) / 2] := by
  ext i; fin_cases i <;>
    simp [latVec, iota, oBasis, Mi, Mj, mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

theorem Emat_eq (τ : ℂ) : Emat τ = !![τ, √2 * τ; 1, -√2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Emat, latVec0, latVec1]

theorem F0mat_eq (τ : ℂ) :
    F0mat τ = !![(τ - 3) / 2, √2 * (τ - 3) / 2; (τ + 1) / 2, -(√2 * (τ + 1)) / 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [F0mat, latVec2, latVec3]

/-- `F'(τ) = F₀(τ)P⁻¹`. -/
def Fp (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := F0mat τ * Pinv

theorem det_Fp (τ : ℂ) : (Fp τ).det = -((√2 : ℂ) * (τ - 3) * (τ + 1)) / 2 := by
  rw [Fp, det_mul, F0mat_eq, Pinv, det_fin_two_of, det_fin_two_of]
  ring

theorem sqrt2_ne_zero : (√2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr two_pos)

theorem det_Fp_ne_zero {τ : ℂ} (hτ : τ.im ≠ 0) : (Fp τ).det ≠ 0 := by
  rw [det_Fp]
  have h3 : τ - 3 ≠ 0 := fun h => hτ (by simpa using congrArg Complex.im h)
  have h1 : τ + 1 ≠ 0 := fun h => hτ (by simpa using congrArg Complex.im h)
  have := sqrt2_ne_zero
  field_simp
  simp [this, h3, h1]

theorem Fp_mul_Omega {τ : ℂ} (hτ : τ.im ≠ 0) : Fp τ * Omega τ = Emat τ := by
  rw [Omega, ← Fp, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit (det_Fp_ne_zero hτ)),
    Matrix.one_mul]

/-- The four generators `ι(b_k)(τ, 1)ᵀ` of `Λ_τ`. -/
def qmVec (τ : ℂ) (k : Fin 4) : Fin 2 → ℂ := latVec (oBasis k) τ

theorem qmVec_linearIndependent {τ : ℂ} (hτ : τ.im ≠ 0) : LinearIndependent ℝ (qmVec τ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have e0 := congrFun hc 0
  have e1 := congrFun hc 1
  simp only [qmVec, Fin.sum_univ_four, latVec0, latVec1, latVec2, latVec3, Finset.sum_apply,
    Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply,
    Complex.real_smul] at e0 e1
  have r0 := congrArg Complex.re e0
  have i0 := congrArg Complex.im e0
  have r1 := congrArg Complex.re e1
  have i1 := congrArg Complex.im e1
  simp at r0 i0 r1 i1
  set x := τ.re
  set y := τ.im
  have hs : √2 ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
  have hA : y * (c 2 - √2 * c 3) = 0 := by linear_combination 2 * i1
  have A : c 2 - √2 * c 3 = 0 := (mul_eq_zero.mp hA).resolve_left hτ
  have hK : y * (c 0 + √2 * c 1 + c 2 / 2 + √2 * c 3 / 2) = 0 := by linear_combination i0
  have K : c 0 + √2 * c 1 + c 2 / 2 + √2 * c 3 / 2 = 0 := (mul_eq_zero.mp hK).resolve_left hτ
  have Bq : c 2 + √2 * c 3 = 0 := by linear_combination (2 / 3 * x) * K - (2 / 3) * r0
  have h3' : √2 * c 3 = 0 := by linear_combination (Bq - A) / 2
  have h3 : c 3 = 0 := (mul_eq_zero.mp h3').resolve_left hs
  have h2 : c 2 = 0 := by linear_combination A + h3'
  have C : c 0 - √2 * c 1 = 0 := by linear_combination r1 - ((x + 1) / 2) * A
  have h1' : √2 * c 1 = 0 := by linear_combination (K - C) / 2 - Bq / 4
  have h1 : c 1 = 0 := (mul_eq_zero.mp h1').resolve_left hs
  have h0 : c 0 = 0 := by linear_combination C + h1'
  intro i; fin_cases i <;> assumption

/-- The ordered `ℝ`-basis `ι(b_k)(τ, 1)ᵀ` of `ℂ²` (for `Im τ ≠ 0`). -/
def qmBasis {τ : ℂ} (hτ : τ.im ≠ 0) : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank' _ (qmVec_linearIndependent hτ) (by
    rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex])

/-- **The QM lattice `Λ_τ = ι(𝒪)(τ, 1)ᵀ`**, the period lattice of N5's QM surface at `τ`. -/
def qmLattice {τ : ℂ} (hτ : τ.im ≠ 0) : Submodule ℤ (Fin 2 → ℂ) :=
  Submodule.span ℤ (Set.range (qmBasis hτ))

instance {τ : ℂ} (hτ : τ.im ≠ 0) : DiscreteTopology (qmLattice hτ) := by
  unfold qmLattice; infer_instance

instance {τ : ℂ} (hτ : τ.im ≠ 0) : IsZLattice ℝ (qmLattice hτ) := by
  unfold qmLattice; infer_instance

theorem qmLattice_eq {τ : ℂ} (hτ : τ.im ≠ 0) :
    qmLattice hτ = Submodule.span ℤ (Set.range (qmVec τ)) := by
  simp [qmLattice, qmBasis]

/-- The QM torus `A_τ = ℂ² ⧸ ι(𝒪)(τ, 1)ᵀ`: a compact connected complex Lie group of dimension 2. -/
abbrev QMTorus {τ : ℂ} (hτ : τ.im ≠ 0) := Torus (qmLattice hτ)

example {τ : ℂ} (hτ : τ.im ≠ 0) : LieAddGroup 𝓘(ℂ, Fin 2 → ℂ) ω (QMTorus hτ) := inferInstance
example {τ : ℂ} (hτ : τ.im ≠ 0) : CompactSpace (QMTorus hτ) := inferInstance

theorem mulVec_col (A M : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2) :
    (A *ᵥ fun i => M i j) = fun i => (A * M) i j := by
  funext i; simp [mulVec, dotProduct, mul_apply]

/-- Images of the period vectors of `Ω(τ)` under `F'(τ)`. -/
theorem Fp_mulVec_periodVec {τ : ℂ} (hτ : τ.im ≠ 0) (k : Fin 2 ⊕ Fin 2) :
    Fp τ *ᵥ periodVec (Omega τ) k =
      match k with
      | Sum.inl 0 => qmVec τ 0
      | Sum.inl 1 => qmVec τ 1
      | Sum.inr 0 => -(2 : ℤ) • qmVec τ 2 - qmVec τ 3
      | Sum.inr 1 => -qmVec τ 2 - qmVec τ 3 := by
  rcases k with j | j
  · rw [periodVec, mulVec_col, Fp_mul_Omega hτ, Emat_eq]
    fin_cases j <;> funext i <;> fin_cases i <;> simp [qmVec, latVec0, latVec1]
  · rw [periodVec, mulVec_single_one]
    fin_cases j <;> funext i <;> fin_cases i <;>
      simp [Fp, F0mat_eq, Pinv, qmVec, latVec2, latVec3] <;> ring

/-- Conversely to `periodVec_linearIndependent`: if the period vectors of `Ω` are `ℝ`-independent,
then `det (Im Ω) ≠ 0`. -/
theorem det_im_ne_zero_of_linearIndependent {g : ℕ} (Ω : Matrix (Fin g) (Fin g) ℂ)
    (h : LinearIndependent ℝ (periodVec Ω)) : (Ω.map Complex.im).det ≠ 0 := by
  intro hdet
  obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hrel := Fintype.linearIndependent_iff.mp h
    (Sum.elim a (fun i => -∑ j, (Ω i j).re * a j)) (by
      funext i
      have hi := congrFun ha i
      simp only [mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hi
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_apply,
        Pi.smul_apply, periodVec, Pi.zero_apply, Pi.single_apply, smul_ite, smul_zero]
      apply Complex.ext
      · simp [Complex.re_sum, mul_comm]
      · simpa [Complex.im_sum, mul_comm] using hi)
  exact ha0 (funext fun j => by simpa using hrel (Sum.inl j))

/-- The images `F'(τ)·(period vectors of Ω(τ))`, explicitly. -/
def imgVec (τ : ℂ) : Fin 2 ⊕ Fin 2 → (Fin 2 → ℂ) :=
  Sum.elim ![qmVec τ 0, qmVec τ 1] ![-(2 : ℤ) • qmVec τ 2 - qmVec τ 3, -qmVec τ 2 - qmVec τ 3]

theorem Fp_mulVec_periodVec' {τ : ℂ} (hτ : τ.im ≠ 0) (k : Fin 2 ⊕ Fin 2) :
    Fp τ *ᵥ periodVec (Omega τ) k = imgVec τ k := by
  rw [Fp_mulVec_periodVec hτ]
  rcases k with j | j <;> fin_cases j <;> rfl

theorem imgVec_linearIndependent {τ : ℂ} (hτ : τ.im ≠ 0) : LinearIndependent ℝ (imgVec τ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set d : Fin 4 → ℝ := ![c (Sum.inl 0), c (Sum.inl 1), -2 * c (Sum.inr 0) - c (Sum.inr 1),
      -c (Sum.inr 0) - c (Sum.inr 1)] with hd
  have hsum : ∑ k, d k • qmVec τ k = ∑ i, c i • imgVec τ i := by
    have e : ∑ k, d k • qmVec τ k = c (Sum.inl 0) • qmVec τ 0 + c (Sum.inl 1) • qmVec τ 1 +
        (-2 * c (Sum.inr 0) - c (Sum.inr 1)) • qmVec τ 2 +
        (-c (Sum.inr 0) - c (Sum.inr 1)) • qmVec τ 3 := by
      simp [Fin.sum_univ_four, d]
    rw [e]
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two, imgVec, Sum.elim_inl, Sum.elim_inr]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
    rw [← Int.cast_smul_eq_zsmul ℝ]
    module
  have key := Fintype.linearIndependent_iff.mp (qmVec_linearIndependent hτ) d (hsum.trans hc)
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  have k3 := key 3
  simp [d] at k0 k1 k2 k3
  rintro (j | j) <;> fin_cases j
  · simpa using k0
  · simpa using k1
  · simp; linarith
  · simp; linarith

theorem span_imgVec {τ : ℂ} :
    Submodule.span ℤ (Set.range (imgVec τ)) = Submodule.span ℤ (Set.range (qmVec τ)) := by
  have hq : ∀ i, qmVec τ i ∈ Submodule.span ℤ (Set.range (qmVec τ)) :=
    fun i => Submodule.subset_span ⟨i, rfl⟩
  have hp : ∀ k, imgVec τ k ∈ Submodule.span ℤ (Set.range (imgVec τ)) :=
    fun k => Submodule.subset_span ⟨k, rfl⟩
  have i0 : imgVec τ (Sum.inr 0) = -(2 : ℤ) • qmVec τ 2 - qmVec τ 3 := rfl
  have i1 : imgVec τ (Sum.inr 1) = -qmVec τ 2 - qmVec τ 3 := rfl
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rcases k with j | j <;> fin_cases j
    · exact hq 0
    · exact hq 1
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (hq 2)) (hq 3)
    · exact Submodule.sub_mem _ (Submodule.neg_mem _ (hq 2)) (hq 3)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe]
    fin_cases k
    · exact hp (Sum.inl 0)
    · exact hp (Sum.inl 1)
    · have h := Submodule.add_mem _ (Submodule.neg_mem _ (hp (Sum.inr 0))) (hp (Sum.inr 1))
      have e : qmVec τ 2 = -imgVec τ (Sum.inr 0) + imgVec τ (Sum.inr 1) := by
        rw [i0, i1]; module
      show qmVec τ 2 ∈ _
      rw [e]; exact h
    · have h := Submodule.sub_mem _ (hp (Sum.inr 0)) (Submodule.smul_mem _ (2 : ℤ) (hp (Sum.inr 1)))
      have e : qmVec τ 3 = imgVec τ (Sum.inr 0) - (2 : ℤ) • imgVec τ (Sum.inr 1) := by
        rw [i0, i1]; module
      show qmVec τ 3 ∈ _
      rw [e]; exact h

/-- `F'(τ)` as a continuous `ℂ`-linear automorphism of `ℂ²`. -/
def FpEquiv {τ : ℂ} (hτ : τ.im ≠ 0) : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLinearEquiv' (Fp τ)
    (Matrix.invertibleOfIsUnitDet _ (Ne.isUnit (det_Fp_ne_zero hτ)))).toContinuousLinearEquiv

theorem FpEquiv_apply {τ : ℂ} (hτ : τ.im ≠ 0) (v : Fin 2 → ℂ) : FpEquiv hτ v = Fp τ *ᵥ v := rfl

/-- **`det Im Ω(τ) ≠ 0`** for `Im τ ≠ 0` (so `Ω(τ)ℤ² + ℤ²` is a full lattice). -/
theorem det_im_Omega_ne_zero {τ : ℂ} (hτ : τ.im ≠ 0) : ((Omega τ).map Complex.im).det ≠ 0 := by
  apply det_im_ne_zero_of_linearIndependent
  apply LinearIndependent.of_comp ((Matrix.toLin' (Fp τ)).restrictScalars ℝ)
  have : ((Matrix.toLin' (Fp τ)).restrictScalars ℝ) ∘ periodVec (Omega τ) = imgVec τ := by
    funext k
    simp only [Function.comp_apply, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
    exact Fp_mulVec_periodVec' hτ k
  rw [this]
  exact imgVec_linearIndependent hτ

/-- **`F'(τ)` carries the Siegel lattice `Ω(τ)ℤ² + ℤ²` onto the QM lattice `ι(𝒪)(τ, 1)ᵀ`.** -/
theorem map_periodLattice_Omega {τ : ℂ} (hτ : τ.im ≠ 0) :
    (periodLattice (Omega τ) (det_im_Omega_ne_zero hτ)).map
      ((FpEquiv hτ).toLinearEquiv.toLinearMap.restrictScalars ℤ) = qmLattice hτ := by
  rw [periodLattice, coe_periodBasis, Submodule.map_span, ← Set.range_comp, qmLattice_eq,
    ← span_imgVec]
  congr 2
  funext k
  exact Fp_mulVec_periodVec' hτ k

/-- **`Ω(τ)` is a period matrix of the QM torus**: `F'(τ)` induces a biholomorphic group
isomorphism `ℂ² ⧸ (Ω(τ)ℤ² + ℤ²) ≃ ℂ² ⧸ ι(𝒪)(τ, 1)ᵀ`. -/
def qmPeriodDiffeo {τ : ℂ} (hτ : τ.im ≠ 0) :
    SiegelTorus (Omega τ) (det_im_Omega_ne_zero hτ) ≃ₘ^ω⟮𝓘(ℂ, Fin 2 → ℂ), 𝓘(ℂ, Fin 2 → ℂ)⟯
      QMTorus hτ :=
  torusDiffeo _ _ (FpEquiv hτ) (map_periodLattice_Omega hτ)

/-- It is additive (a group isomorphism). -/
theorem qmPeriodDiffeo_add {τ : ℂ} (hτ : τ.im ≠ 0) (p q : SiegelTorus (Omega τ)
    (det_im_Omega_ne_zero hτ)) :
    qmPeriodDiffeo hτ (p + q) = qmPeriodDiffeo hτ p + qmPeriodDiffeo hτ q :=
  map_add (torusAddEquiv _ _ (FpEquiv hτ) (map_periodLattice_Omega hτ)) p q

theorem qmPeriodDiffeo_proj {τ : ℂ} (hτ : τ.im ≠ 0) (v : Fin 2 → ℂ) :
    qmPeriodDiffeo hτ (proj _ v) = proj (qmLattice hτ) (Fp τ *ᵥ v) := rfl

theorem sqrt2_sq : (√2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- The compatibility `F' Eᵀ = E F'ᵀ` (the Riemann form is alternating in N5's basis). -/
theorem Fp_mul_Emat_transpose (τ : ℂ) : Fp τ * (Emat τ)ᵀ = Emat τ * (Fp τ)ᵀ := by
  have h2 := sqrt2_sq
  rw [Fp, F0mat_eq, Emat_eq, Pinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> ring_nf <;>
    simp only [h2] <;> ring_nf

/-- **`Ω(τ)` is symmetric** (for `Im τ ≠ 0`). -/
theorem Omega_transpose {τ : ℂ} (hτ : τ.im ≠ 0) : (Omega τ)ᵀ = Omega τ := by
  have hu : IsUnit (Fp τ).det := Ne.isUnit (det_Fp_ne_zero hτ)
  have hut : IsUnit (Fp τ)ᵀ.det := by rwa [det_transpose]
  have key := Fp_mul_Emat_transpose τ
  rw [Omega, ← Fp, transpose_mul, transpose_nonsing_inv]
  calc (Emat τ)ᵀ * ((Fp τ)ᵀ)⁻¹
      = (Fp τ)⁻¹ * (Fp τ * (Emat τ)ᵀ) * ((Fp τ)ᵀ)⁻¹ := by
        rw [← Matrix.mul_assoc (Fp τ)⁻¹, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = (Fp τ)⁻¹ * (Emat τ * (Fp τ)ᵀ) * ((Fp τ)ᵀ)⁻¹ := by rw [key]
    _ = (Fp τ)⁻¹ * Emat τ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hut, Matrix.mul_one]

/-- Hence `θ(·, Ω(τ))` is quasi-periodic for `Ω(τ)ℤ² + ℤ² = F'(τ)⁻¹Λ_τ`: it is a section of a
line bundle on the QM torus (via `qmPeriodDiffeo`). -/
theorem riemannTheta_Omega_add_period {τ : ℂ} (hτ : τ.im ≠ 0) (z : Fin 2 → ℂ) (m n : Fin 2 → ℤ) :
    riemannTheta (Omega τ) (z + (Omega τ *ᵥ intVec m + intVec n)) =
      Complex.exp (-(Real.pi * Complex.I * (intVec m ⬝ᵥ (Omega τ *ᵥ intVec m))) -
          2 * Real.pi * Complex.I * (intVec m ⬝ᵥ z)) * riemannTheta (Omega τ) z :=
  riemannTheta_add_period _ (Omega_transpose hτ) z m n

/-! #### `Ω(τ)` lies in the Siegel space for `Im τ > 0` -/

/-- Partial fractions: `Ω(τ) = A₀ + C/(τ+1) + B/(τ−3)` (found with sympy). -/
def OmegaPF (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (!![-1 + (√2 : ℂ) / 2, 1 - (√2 : ℂ); 1 - (√2 : ℂ), -2 + (√2 : ℂ)] :
      Matrix (Fin 2) (Fin 2) ℂ) +
    (τ + 1)⁻¹ • !![-((√2 : ℂ) + 2) / 2, 1 + (√2 : ℂ); 1 + (√2 : ℂ), -((√2 : ℂ) + 2)] +
    (τ - 3)⁻¹ • !![3 * ((√2 : ℂ) - 2) / 2, -3 * ((√2 : ℂ) - 1); -3 * ((√2 : ℂ) - 1),
      3 * ((√2 : ℂ) - 2)]

theorem Fp_mul_OmegaPF {τ : ℂ} (hτ : τ.im ≠ 0) : Fp τ * OmegaPF τ = Emat τ := by
  have h2 := sqrt2_sq
  have h3 : τ - 3 ≠ 0 := fun h => hτ (by simpa using congrArg Complex.im h)
  have h1 : τ + 1 ≠ 0 := fun h => hτ (by simpa using congrArg Complex.im h)
  rw [Fp, F0mat_eq, Pinv, Emat_eq, OmegaPF]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring_nf <;>
    simp only [h2] <;> ring_nf

theorem Omega_eq_PF {τ : ℂ} (hτ : τ.im ≠ 0) : Omega τ = OmegaPF τ := by
  have hu : IsUnit (Fp τ).det := Ne.isUnit (det_Fp_ne_zero hτ)
  rw [Omega, ← Fp, ← Fp_mul_OmegaPF hτ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]

/-- **`Ω(τ) ∈ 𝔥₂` for `Im τ > 0`.** `Im Ω(τ) = y·(C'/|τ+1|² + B'/|τ−3|²)` with `C'`, `B'` positive
semidefinite of rank one with different kernels. -/
theorem Omega_mem_siegelSpace {τ : ℂ} (hτ : 0 < τ.im) : Omega τ ∈ SiegelSpace 2 := by
  have hτ' : τ.im ≠ 0 := hτ.ne'
  refine ⟨Omega_transpose hτ', ?_⟩
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · show ((Omega τ).map Complex.im)ᴴ = (Omega τ).map Complex.im
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.transpose_map,
      Omega_transpose hτ']
  · intro x hx
    rw [Omega_eq_PF hτ']
    have hs : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hp : 0 < Complex.normSq (τ + 1) :=
      Complex.normSq_pos.mpr fun h => hτ' (by simpa using congrArg Complex.im h)
    have hq : 0 < Complex.normSq (τ - 3) :=
      Complex.normSq_pos.mpr fun h => hτ' (by simpa using congrArg Complex.im h)
    simp [OmegaPF, dotProduct, mulVec, Fin.sum_univ_two, Complex.inv_im, Complex.inv_re]
    set y := τ.im
    set P := Complex.normSq (τ + 1)
    set Q := Complex.normSq (τ - 3)
    set r := √2
    rw [show x 0 * ((-y / P * ((-2 + -r) / 2) + -y / Q * (3 * (r - 2) / 2)) * x 0 +
          (-y / P * (1 + r) + -(-y / Q * (3 * (r - 1)))) * x 1) +
        x 1 * ((-y / P * (1 + r) + -(-y / Q * (3 * (r - 1)))) * x 0 +
          (-y / P * (-2 + -r) + -y / Q * (3 * (r - 2))) * x 1) =
        y / P * ((r + 2) / 2 * (x 0 - r * x 1) ^ 2) + y / Q * (3 * (2 - r) / 2 * (x 0 + r * x 1) ^
            2)
      by linear_combination (x 1 * y * (3 * r * x 1 + 6 * x 0 - 6 * x 1) / (2 * Q) +
        x 1 * y * (-r * x 1 + 2 * x 0 - 2 * x 1) / (2 * P)) * hs]
    have hr0 : 0 < r := Real.sqrt_pos.mpr two_pos
    have hr2 : r < 2 := by nlinarith
    have hA : 0 < y / P * ((r + 2) / 2) := mul_pos (div_pos hτ hp) (by linarith)
    have hB : 0 < y / Q * (3 * (2 - r) / 2) := mul_pos (div_pos hτ hq) (by linarith)
    by_contra hle
    push Not at hle
    have hu : (x 0 - r * x 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 0 - r * x 1), sq_nonneg (x 0 + r * x 1),
        mul_nonneg hA.le (sq_nonneg (x 0 - r * x 1)), mul_nonneg hB.le (sq_nonneg (x 0 + r * x 1))]
    have hw : (x 0 + r * x 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 0 - r * x 1), sq_nonneg (x 0 + r * x 1),
        mul_nonneg hA.le (sq_nonneg (x 0 - r * x 1)), mul_nonneg hB.le (sq_nonneg (x 0 + r * x 1))]
    have hu' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hu
    have hw' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hw
    have hx1 : x 1 = 0 := by
      have : r * x 1 = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hr0.ne'
    have hx0 : x 0 = 0 := by linarith
    exact hx (funext fun i => by fin_cases i <;> simp [hx0, hx1])

end QM

end BPAnalytic
