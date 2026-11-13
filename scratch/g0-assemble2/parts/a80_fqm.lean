/-! ## g0-assemble2: fibre-qm-period (scratch/fibre-qm-period/part_fqm.lean, verbatim; its FQMBase.lean is part 80
(g0-thetapoint) over Leaves.lean, whose `R1fpProps` is qm-pin's full repair and which contains part_pin.lean's
eight declarations) -/

/-! ## §F. fibre-qm-period: `ThetaPt.FibreQMPeriod` for the leaf's own triple, from named Props

Task fibre-qm-period, 2026-11-13. `ThetaPt.FibreQMPeriod` (g0-thetapoint, above, unchanged; in
this file `R1fpProps` is qm-pin's fully repaired clause list) is proved here in two steps.

1. **qm-pin's reduction to the leaf's own triple** (`fibreQMPeriod_of_own`). `FibreQMPeriodAt Y Φ π`
   is the body of `FibreQMPeriod` for one triple (`fibreQMPeriod_iff`, `Iff.rfl`).
   `FibreQMPeriodOwn h` is `FibreQMPeriodAt` for the triple `ownY h, ownΦ h, ownπ h` that
   `Classical.choice` extracts from the leaf bundle `R1R2fp` (through `R1R2fp_Y`). Given qm-pin's
   `Pin.MobiusGlue` (proved by mobius-glue from `CurveRatFactor`, `CurveSurj` and the textbook leaf
   T5), `FibreQMPeriodOwn h` implies `FibreQMPeriod` (`Pin.pointwise_of_witness_mor`).
2. **The own-triple statement from named Props** (`fibreQMPeriodAt_of`): for any triple satisfying
   `R1fpProps` (only its naturality clause is used), from
   * `PkgI1.QMHauptmodul` (existing composite leaf, pkg-I1),
   * `QMComplexUnif` (LEAF candidate: R1(b)(a), Shimura 1967: every QM surface over `ℂ` is
     `ℂ²/ι(𝒪)(τ, 1)ᵀ` compatibly with `ι`, for some `τ ∈ ℍ`, by an analytic uniformization),
   * `QMPeriodValue Y Φ π` (GLUE: the Hauptmodul comparison; the value of `π` at a point is the value
     of `QMHauptmodul`'s `f` at the period `τ` of the point),
   * `QMDenZeroCM3` (LEAF candidate: `Σθ_m⁸ ∘ Ω` vanishes on `ℍ` only at fixed points of `ι(x)`,
     `x² − x + 1 = 0`; Lin–Yang's divisor of `ψ₄` on the QM curve),
   * `UnifTransport` (GLUE: an analytic uniformization of the base change `Q/ℂ` of the fibre object
     gives one of `A(ℂ)_σ` with the same kernel; base change of complex points and rigidity). -/


/-! ## §N. fibre-qm-period: normalization of QM lattices (proved; used for `QMLatticeAlgebra`)

`qmOrbit w = ι(𝒪)w` (the `ℤ`-span of `ι(b_k)w` over N5's basis); `qmLattice τ = qmOrbit (τ, 1)`;
scaling; the unit `1 + i` (reduced norm `−1`) keeps the orbit (`qmOrbit_unit`, coefficients from
`py/unit_coeffs.py`); hence `normalize`: if `w` is not a complex multiple of a real vector, then
`ι(𝒪)w = c·Λ_τ` with `c ≠ 0` and `τ ∈ ℍ`. -/

section FibreQMNormSec

set_option linter.unusedSimpArgs false

open BPAnalytic.QM Matrix

noncomputable section

namespace FibreQMNorm


def qmMatB (x : B) : Matrix (Fin 2) (Fin 2) ℂ := (iota x).map (fun r : ℝ => (r : ℂ))

def qmOrbit (w : Fin 2 → ℂ) : Submodule ℤ (Fin 2 → ℂ) :=
  Submodule.span ℤ (Set.range fun k : Fin 4 => (qmMatB (oBasis k)).mulVec w)

theorem qmLattice_eq_orbit {τ : ℂ} (hτ : τ.im ≠ 0) : qmLattice hτ = qmOrbit ![τ, 1] := by
  rw [qmLattice_eq]; rfl

/-- The four generators, explicitly. -/
theorem gen_eq (a b : ℂ) : (fun k : Fin 4 => (qmMatB (oBasis k)).mulVec ![a, b]) =
    ![![a, b], ![√2 * a, -(√2 * b)], ![(a - 3 * b) / 2, (a + b) / 2],
      ![√2 * (a - 3 * b) / 2, -(√2 * (a + b)) / 2]] := by
  funext k; ext i
  fin_cases k <;> fin_cases i <;>
    simp [qmMatB, iota, oBasis, Mi, Mj, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

def smulMap (c : ℂ) : (Fin 2 → ℂ) →ₗ[ℤ] (Fin 2 → ℂ) :=
  ((c • LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))).restrictScalars ℤ

theorem qmOrbit_smul (c : ℂ) (v : Fin 2 → ℂ) : qmOrbit (c • v) = (qmOrbit v).map (smulMap c) := by
  unfold qmOrbit
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext k
  simp [smulMap, Matrix.mulVec_smul]

theorem sqrt2_sq' : (√2 : ℂ) * √2 = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num

/-- The unit `1 + i` (reduced norm `−1`) does not change the orbit. -/
theorem qmOrbit_unit (τ : ℂ) : qmOrbit ![τ, 1] = qmOrbit ![(1 + √2) * τ, 1 - √2] := by
  have s := sqrt2_sq'
  apply le_antisymm
  · unfold qmOrbit
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [gen_eq, gen_eq]
    set S := Submodule.span ℤ (Set.range ![![((1 + √2) * τ), (1 - √2)], ![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))], ![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2], ![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2]]) with hS
    have m : ∀ j : Fin 4, (![![((1 + √2) * τ), (1 - √2)], ![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))], ![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2], ![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2]] : Fin 4 → Fin 2 → ℂ) j ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩
    fin_cases k
    · have e : (![τ, 1] : Fin 2 → ℂ) = -(![((1 + √2) * τ), (1 - √2)] : Fin 2 → ℂ) + (![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-τ) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-1) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.add_mem (S.neg_mem (m 0)) (m 1))
    · have e : (![√2 * τ, -(√2 * 1)] : Fin 2 → ℂ) = ((![((1 + √2) * τ), (1 - √2)] + ![((1 + √2) * τ), (1 - √2)] : Fin 2 → ℂ) : Fin 2 → ℂ) - (![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (τ) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (1) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.sub_mem (S.add_mem (m 0) (m 0)) (m 1))
    · have e : (![(τ - 3 * 1) / 2, (τ + 1) / 2] : Fin 2 → ℂ) = (![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))] : Fin 2 → ℂ) - (![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2] : Fin 2 → ℂ) - (![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-(τ - 3)/2) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-(τ + 1)/2) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.sub_mem (S.sub_mem (m 1) (m 2)) (m 3))
    · have e : (![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2] : Fin 2 → ℂ) = ((![((1 + √2) * τ), (1 - √2)] + ![((1 + √2) * τ), (1 - √2)] : Fin 2 → ℂ) : Fin 2 → ℂ) - ((![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2] + ![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2] : Fin 2 → ℂ) : Fin 2 → ℂ) - (![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination ((τ + 3)/2) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-(τ - 1)/2) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.sub_mem (S.sub_mem (S.add_mem (m 0) (m 0)) (S.add_mem (m 2) (m 2))) (m 3))
  · unfold qmOrbit
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [gen_eq, gen_eq]
    set S := Submodule.span ℤ (Set.range ![![τ, 1], ![√2 * τ, -(√2 * 1)], ![(τ - 3 * 1) / 2, (τ + 1) / 2], ![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2]]) with hS
    have m : ∀ j : Fin 4, (![![τ, 1], ![√2 * τ, -(√2 * 1)], ![(τ - 3 * 1) / 2, (τ + 1) / 2], ![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2]] : Fin 4 → Fin 2 → ℂ) j ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩
    fin_cases k
    · have e : (![((1 + √2) * τ), (1 - √2)] : Fin 2 → ℂ) = (![τ, 1] : Fin 2 → ℂ) + (![√2 * τ, -(√2 * 1)] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (0) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (0) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.add_mem (m 0) (m 1))
    · have e : (![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))] : Fin 2 → ℂ) = ((![τ, 1] + ![τ, 1] : Fin 2 → ℂ) : Fin 2 → ℂ) + (![√2 * τ, -(√2 * 1)] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (τ) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (1) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.add_mem (S.add_mem (m 0) (m 0)) (m 1))
    · have e : (![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2] : Fin 2 → ℂ) = (![√2 * τ, -(√2 * 1)] : Fin 2 → ℂ) + (![(τ - 3 * 1) / 2, (τ + 1) / 2] : Fin 2 → ℂ) - (![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (0) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (0) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.sub_mem (S.add_mem (m 1) (m 2)) (m 3))
    · have e : (![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2] : Fin 2 → ℂ) = ((![τ, 1] + ![τ, 1] : Fin 2 → ℂ) : Fin 2 → ℂ) - ((![(τ - 3 * 1) / 2, (τ + 1) / 2] + ![(τ - 3 * 1) / 2, (τ + 1) / 2] : Fin 2 → ℂ) : Fin 2 → ℂ) + (![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination ((τ + 3)/2) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-(τ - 1)/2) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.add_mem (S.sub_mem (S.add_mem (m 0) (m 0)) (S.add_mem (m 2) (m 2))) (m 3))


theorem smulMap_comp (a b : ℂ) : smulMap a ∘ₗ smulMap b = smulMap (a * b) := by
  ext v i; simp [smulMap, mul_smul]

theorem one_sub_sqrt2_ne : (1 - (√2 : ℂ)) ≠ 0 := by
  have h : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [show (1 - (√2 : ℂ)) = ((1 - √2 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.ofReal_ne_zero.mpr (by linarith)

/-- **Normalization (proved):** if `w` is not a complex multiple of a real vector, `ι(𝒪)w` is a
nonzero multiple of `Λ_τ` for some `τ ∈ ℍ` (using the unit `1 + i` of reduced norm `−1` when
`Im(w₀/w₁) < 0`). -/
theorem normalize (w : Fin 2 → ℂ) (hw : ¬ ∃ (c : ℂ) (r : Fin 2 → ℝ), w = c • (fun i => (r i : ℂ))) :
    ∃ (τ : ℂ) (hτ : 0 < τ.im) (c : ℂ), c ≠ 0 ∧ qmOrbit w = (qmLattice hτ.ne').map (smulMap c) := by
  have hw2 : w 1 ≠ 0 := by
    intro h0; apply hw; refine ⟨w 0, ![1, 0], ?_⟩; ext i; fin_cases i <;> simp [h0]
  set t := w 0 / w 1 with ht_def
  have hwt : w = w 1 • ![t, 1] := by
    ext i; fin_cases i
    · simp [t]; field_simp
    · simp
  have ht : t.im ≠ 0 := by
    intro h0; apply hw; refine ⟨w 1, ![t.re, 1], ?_⟩
    rw [hwt]; ext i; fin_cases i
    · simp; left; exact Complex.ext (by simp) (by simp [h0])
    · simp
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · set k : ℝ := (1 + √2) / (1 - √2) with hk
    have hk0 : k < 0 := by
      have h1 : (1 : ℝ) < √2 := by
        rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      exact div_neg_of_pos_of_neg (by positivity) (by linarith)
    set τ' : ℂ := (k : ℂ) * t with hτ'_def
    have hτ' : 0 < τ'.im := by
      rw [hτ'_def, Complex.im_ofReal_mul]; exact mul_pos_of_neg_of_neg hk0 hneg
    refine ⟨τ', hτ', w 1 * (1 - √2), mul_ne_zero hw2 one_sub_sqrt2_ne, ?_⟩
    have hv : (![(1 + √2) * t, 1 - √2] : Fin 2 → ℂ) = (1 - √2 : ℂ) • ![τ', 1] := by
      have hs := one_sub_sqrt2_ne
      ext i; fin_cases i
      · simp only [hτ'_def, hk, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.smul_apply,
          smul_eq_mul]
        push_cast
        field_simp
      · simp
    rw [hwt, qmOrbit_smul, qmOrbit_unit, hv, qmOrbit_smul, ← qmLattice_eq_orbit hτ'.ne',
      ← Submodule.map_comp, smulMap_comp]
    simp
  · refine ⟨t, hpos, w 1, hw2, ?_⟩
    rw [hwt, qmOrbit_smul, ← qmLattice_eq_orbit hpos.ne']
    simp

end FibreQMNorm

end

end FibreQMNormSec

noncomputable section

namespace HSyn

open scoped MatrixGroups ModularForm

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

namespace FibreQM

open Complex

/-! ### Step 1: the statement for one triple, and qm-pin's reduction -/

/-- The conclusion of `FibreQMPeriod` for the model `A` over `K` of the fibre over `J(u)`
(verbatim). -/
def QMConcl (u : ℚ) (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K) : Prop :=
  ∃ (σ : K.K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
    (Φu : (Fin 2 → ℂ) → CPts (LeafAdopt.abVarEquiv K.K A) σ), IsUniformization σ Λ Φu ∧
  ∃ (τ : ℂ) (hτ : 0 < τ.im) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ)),
    Λ.map (F.toLinearMap.restrictScalars ℤ) = BPAnalytic.QM.qmLattice hτ.ne' ∧
    PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = ((Jmap u : ℚ) : ℂ)

/-- **`FibreQMPeriod` for one triple `(Y, Φ, π)`** (the body of `ThetaPt.FibreQMPeriod`, unchanged:
`fibreQMPeriod_iff`). -/
def FibreQMPeriodAt (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) :
    Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
      QMConcl u K A

/-- The restatement is the statement (checked by `Iff.rfl`). -/
theorem fibreQMPeriod_iff : ThetaPt.FibreQMPeriod ↔
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R2fpProps Y Φ π → FibreQMPeriodAt Y Φ π :=
  Iff.rfl

/-- The leaf's own `Y₃`: the triple that `Classical.choice` extracts from the bundle `R1R2fp`
(through `R1R2fp_Y`). -/
def ownY (h : R1R2fp) : Over (Spec (CommRingCat.of ℚ)) := (R1R2fp_Y h).choose

/-- The leaf's own moduli bijections. -/
def ownΦ (h : R1R2fp) : PtEquiv (ownY h) := (R1R2fp_Y h).choose_spec.choose

/-- The leaf's own `π : Y₃ → P¹`. -/
def ownπ (h : R1R2fp) : ToP1 (ownY h).left := (R1R2fp_Y h).choose_spec.choose_spec.choose

theorem own_spec (h : R1R2fp) : R1fpProps (ownY h) (ownΦ h) ∧ R1heckeProps (ownY h) (ownΦ h) ∧
    R2fpProps (ownY h) (ownΦ h) (ownπ h) :=
  (R1R2fp_Y h).choose_spec.choose_spec.choose_spec

/-- **`FibreQMPeriod` restated for the leaf's own triple** (qm-pin's option 3 form; with
`Pin.MobiusGlue` it is equivalent to `FibreQMPeriod`: `fibreQMPeriod_of_own` and
`own_of_fibreQMPeriod`). -/
def FibreQMPeriodOwn (h : R1R2fp) : Prop := FibreQMPeriodAt (ownY h) (ownΦ h) (ownπ h)

/-- **qm-pin's reduction (proved).** The own-triple statement implies `FibreQMPeriod` for every
triple satisfying the repaired clause list, given `Pin.MobiusGlue` (mobius-glue proves it from
`CurveRatFactor`, `CurveSurj` and T5) and the CM objects of the bundle. -/
theorem fibreQMPeriod_of_own (h : R1R2fp) (hM : Pin.MobiusGlue) (hOwn : FibreQMPeriodOwn h) :
    ThetaPt.FibreQMPeriod := by
  obtain ⟨h1, -, h2⟩ := own_spec h
  intro Y Φ π h1' h2' u hu K A hFib
  obtain ⟨emb, y, P, hP, hy, hiso⟩ := hFib
  exact Pin.pointwise_of_witness_mor hM (Pin.cm_objects_of_R1R2fp h) h1 h2
    (fun t P => ∀ u : ℚ, u ∉ contactSet → t = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
      ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K) (emb : K.K →+* Qbar),
        (letI : Algebra K.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) →
        QMConcl u K A)
    (fun t y P hP ht u hu hJ K A emb hiso => hOwn u hu K A ⟨emb, y, P, hP, ht.trans hJ, hiso⟩)
    Y Φ π h1' h2' _ y P hP rfl u hu hy K A emb hiso

/-- The converse (trivial): `FibreQMPeriod` implies the own-triple statement. -/
theorem own_of_fibreQMPeriod (h : R1R2fp) (hQM : ThetaPt.FibreQMPeriod) : FibreQMPeriodOwn h :=
  hQM _ _ _ (own_spec h).1 (own_spec h).2.2

/-! ### Step 2: the named Props -/

/-- The clauses of `PkgI1.QMHauptmodul` for one function `f` (verbatim; `PkgI1.QMHauptmodul` is
`∃ f, QMHauptmodulFn f`, `qmHauptmodul_iff`). -/
def QMHauptmodulFn (f : UpperHalfPlane → OnePoint ℂ) : Prop :=
  Continuous f ∧
    (∀ τ : UpperHalfPlane, PkgI1.jDen (PkgI1.Omega τ) ≠ 0 →
      f τ = ((PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) : ℂ) : OnePoint ℂ)) ∧
    (∀ τ τ' : UpperHalfPlane, f τ = f τ' ↔ ∃ g ∈ PkgI1.GammaStar, g • τ = τ') ∧
    Function.Surjective f ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -1 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        f τ = ((0 : ℂ) : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x - x + 1 = 0 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        f τ = (OnePoint.infty : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -6 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        f τ = ((-16/27 : ℂ) : OnePoint ℂ))

theorem qmHauptmodul_iff : PkgI1.QMHauptmodul ↔ ∃ f, QMHauptmodulFn f := Iff.rfl

/-- `𝒪` acting on `ℂ²` through N5's real embedding: `z ↦ ι(a) z` (`ι(a) ∈ M₂(ℝ) ⊆ M₂(ℂ)`); it
preserves `Λ_τ = ι(𝒪)(τ, 1)ᵀ`. (`LeafQM.O` is `ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩ ⊆ B = (2, −3)`, the
order of pkg-I1 and bp-analytic, with the same basis.) -/
def qmMat (a : LeafQM.O) : Matrix (Fin 2) (Fin 2) ℂ :=
  (BPAnalytic.QM.iota (a : LeafQM.B)).map (fun r : ℝ => (r : ℂ))

/-- An analytic uniformization `Φ : ℂ² → Q.A(ℂ)` of a QM surface over `ℂ` is **`ι`-compatible**
if `Φ(ι(a) z) = ι_Q(a)(Φ z)` for all `a ∈ 𝒪`. -/
def IotaCompatible (Q : QML3 ℂ) (Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)) : Prop :=
  ∀ (a : LeafQM.O) (z : Fin 2 → ℂ), Φu ((qmMat a).mulVec z) = Φu z ≫ (Q.q.iota a).hom

/-- **LEAF candidate (R1(b)(a), the complex uniformization of QM surfaces).** Every abelian surface
`Q/ℂ` with QM by `𝒪` (and level-3 structure) has an analytic uniformization
`Φ : ℂ² → Q.A(ℂ)` (`IsUniformization`) whose kernel is exactly the QM lattice
`Λ_τ = ι(𝒪)(τ, 1)ᵀ` for some `τ ∈ ℍ`, compatibly with `ι`.

Sources: Shimura, *Construction of class fields and zeta functions of algebraic curves*,
Ann. of Math. 85 (1967), Main Theorem I and §2 (the QM abelian varieties are the tori
`ℂ²/ι(𝒪)(τ,1)ᵀ`); also Birkenhake–Lange, *Complex abelian varieties*, §9.4, and the analytic
uniformization of `Q.A(ℂ)` with GAGA (the kernel's `UniformizationLeafAll`) (all locators
UNVERIFIED). Why it is a consequence: `H₁(Q.A, ℤ)` is a left `𝒪`-module, locally free of rank one
since `𝒪` is maximal, hence free because indefinite `B` has class number one (Eichler); the analytic
representation of `B ⊗ ℝ = M₂(ℝ)` on `ℂ²` is the standard one up to `GL₂(ℂ)`; so the kernel is
`ι(𝒪)w`, `w = c(τ, 1)ᵀ`, `τ ∉ ℝ`, and if `Im τ < 0` the unit `1 + i ∈ 𝒪` (reduced norm `−1`)
moves it to `ℍ`. Not one printed theorem with this exact normalization: a leaf candidate. -/
def QMComplexUnif : Prop :=
  ∀ Q : QML3 ℂ, ∃ (τ : ℂ) (hτ : 0 < τ.im) (Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice hτ.ne') Φu ∧ IotaCompatible Q Φu

/-- **GLUE (F1, the Hauptmodul comparison, for one triple).** Let `f` satisfy the clauses of
`PkgI1.QMHauptmodul`. For every `ℚ̄`-point `y` of `Y` with object `P`, every embedding
`ι : ℚ̄ → ℂ`, every base change `Q/ℂ` of `P` along `ι`, and every `ι`-compatible uniformization of
`Q.A` with kernel `Λ_τ` (`τ ∈ ℍ`): `f(τ) = ι(π(y))` in `P¹(ℂ)`.

Why true for the genuine triple (model argument, no human review): by R1(b)(b)-(c) (Shimura 1967;
Deligne 1971 §4.15) there is an analytic family `τ ↦ P_τ` over `ℍ` with `P_τ(ℂ) ≅ ℂ²/Λ_τ`
compatibly with `ι`, and `h(τ) = π(P_τ)` is holomorphic `ℍ → P¹(ℂ)`. Two `ι`-compatible tori
`ℂ²/Λ_τ`, `ℂ²/Λ_τ'` give `Aut(𝒪)`-twist-equivalent QM pairs iff `τ' ∈ Γ*τ` (Shimura; `Γ*` is the
positive-norm normalizer, and twists by `Aut 𝒪 = N_B(𝒪)/ℚ^×` are the Atkin–Lehner moves). With
R2fp's fibre clause (GAGA turns the analytic isomorphisms into algebraic ones), `h` is
`Γ*`-invariant with fibres exactly the `Γ*`-orbits. So `h` and `f` both induce bijections
`Γ*\ℍ ≅ P¹(ℂ)` that are holomorphic on the compact Riemann surface `X₆/W`; `h ∘ f⁻¹` is a
biholomorphism of `P¹`, a Möbius map, and it fixes `0, ∞, −16/27` (R2fp's CM clauses at the CM
points, which are the fixed points of `ι(x)`, `x ∈ 𝒪` with `x² = −1`, `x² − x + 1 = 0`, `x² = −6`;
`QMHauptmodul`'s CM clauses), so `h = f`. Finally `Q ≅ P_τ` up to level structure (both are
`ι`-compatibly `ℂ²/Λ_τ`), so `ι(π(y)) = π(Q) = h(τ) = f(τ)` (naturality of `π`,
`ToP1.val_comp`). For other triples it follows from the genuine one by qm-pin's comparison. Inputs
that are not in Mathlib: analytification of `Y₃`, the analytic family (R1(b)(b)-(c)), GAGA, the
compact Riemann surface `X₆/W`. Size: large. -/
def QMPeriodValue (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) :
    Prop :=
  ∀ f : UpperHalfPlane → OnePoint ℂ, QMHauptmodulFn f →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
    ∀ (ιe : Qbar →+* ℂ) (Q : QML3 ℂ), IsBaseChangeOf ιe P Q →
    ∀ (τ : UpperHalfPlane) (Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu →
      IotaCompatible Q Φu →
      f τ = (π.val (K := Qbar) y.left).map ιe

/-- **LEAF candidate (zeros of `ψ₄` on the QM curve).** `Σ_{m even} θ_m(Ω(τ))⁸ = 4ψ₄(Ω(τ))`
vanishes at `τ ∈ ℍ` only at the CM points of discriminant `−3`, the fixed points of `ι(x)` for
`x ∈ 𝒪` with `x² − x + 1 = 0`.

Source: Lin–Yang, *Quaternionic loci in Siegel's modular threefold*, Math. Z. 295 (2020)
(arXiv:1807.00466v1, Example 29 with eqs. (13)-(14)): on the Shimura curve `X = X₆/W ≅ P¹` the
pull-back of `ψ₄` has its zeros only at the elliptic point `P₋₃` (so `j = χ₁₀²/ψ₄⁵`-type functions
have their only pole there), with Igusa's theta expression of `ψ₄` (R4) (locators UNVERIFIED; the
exact divisor statement was not read). Consistent with `QMHauptmodul` (`j_θ` has its only pole at
`P₋₃`) unless `ψ₄` and `χ₁₀` had a common zero on `Ω(ℍ)`. Numerically: `jDen(Ω(i√3)) = 0` with a
zero of order 30 in `τ` (pkg-I1's pole of order 6 of `j_θ`). SPECULATIVE as a reading of the
source. -/
def QMDenZeroCM3 : Prop :=
  ∀ τ : UpperHalfPlane, PkgI1.jDen (PkgI1.Omega τ) = 0 →
    ∃ x : PkgI1.B, PkgI1.InO x ∧ x * x - x + 1 = 0 ∧ ∃ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧ g • τ = τ

/-- **GLUE (base change of complex points).** Let `A` be an abelian variety over a number field
`K`, `emb : K → ℚ̄` with `A_ℚ̄ ≅ P.A` as `ℚ̄`-schemes (`FibreOver`'s isomorphism), `ι : ℚ̄ → ℂ`, and
`Q/ℂ` a base change of `P` along `ι`. Every analytic uniformization of `Q.A(ℂ)` with kernel `Λ`
gives one of `A(ℂ)_σ`, `σ = ι ∘ emb`, with the same kernel `Λ`.

Why true: `A(ℂ)_σ = Hom_K(Spec ℂ, A) = Hom_ℂ(Spec ℂ, A ×_K ℂ)` and `A ×_K ℂ ≅ P.A ×_ℚ̄ ℂ ≅ Q.A` as
`ℂ`-schemes (pullback pasting; `IsBaseChangeOf`'s square). The resulting bijection
`ψ : Q.A(ℂ) → A(ℂ)_σ` comes from an isomorphism of `ℂ`-varieties, so by rigidity (Mumford,
*Abelian Varieties*, §4 Cor. 1) `x ↦ ψ(x)·ψ(1)⁻¹` is a group isomorphism; regular functions on
opens of `A` pull back to regular functions on opens of `Q.A` (translations are morphisms), so
`z ↦ ψ(Φ z)·ψ(1)⁻¹` satisfies every clause of `IsUniformization`, with kernel `Λ`. Size: medium
(scheme bookkeeping: pullbacks of points, `cEvalAt` along morphisms, rigidity, which is not in
Mathlib). -/
def UnifTransport : Prop :=
  ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K) (emb : K.K →+* Qbar) (P : QML3 Qbar),
    (letI : Algebra K.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) →
    ∀ (ιe : Qbar →+* ℂ) (Q : QML3 ℂ), IsBaseChangeOf ιe P Q →
    ∀ (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)),
      IsUniformization (RingHom.id ℂ) Λ Φu →
      ∃ Φa : (Fin 2 → ℂ) → CPts (LeafAdopt.abVarEquiv K.K A) (ιe.comp emb),
        IsUniformization (ιe.comp emb) Λ Φa

/-! ### Step 2b: `QMPeriodValue` from a moduli part and a complex-analysis part -/

/-- `h : ℍ → P¹(ℂ)` is holomorphic at `τ` (as a map to the Riemann sphere): near `τ` it is an
analytic function `g`, or `1/g` with `g` analytic and `g(τ) = 0` (a pole). -/
def IsHolP1At (h : UpperHalfPlane → OnePoint ℂ) (τ : UpperHalfPlane) : Prop :=
  (∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in nhds (τ : ℂ), ∀ hz : 0 < z.im, h ⟨z, hz⟩ = (g z : OnePoint ℂ)) ∨
  (∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧ g τ = 0 ∧
      ∀ᶠ z in nhds (τ : ℂ), ∀ hz : 0 < z.im,
        h ⟨z, hz⟩ = if g z = 0 then OnePoint.infty else (((g z)⁻¹ : ℂ) : OnePoint ℂ))

/-- The fibre and CM clauses of a normalized Hauptmodul of `Γ*`: fibres exactly the `Γ*`-orbits,
values `0, ∞, −16/27` at the fixed points of `ι(x)` for `x ∈ 𝒪` with `x² = −1`, `x² − x + 1 = 0`,
`x² = −6` (as in `PkgI1.QMHauptmodul`). -/
def GammaStarFibresCM (h : UpperHalfPlane → OnePoint ℂ) : Prop :=
  (∀ τ τ' : UpperHalfPlane, h τ = h τ' ↔ ∃ g ∈ PkgI1.GammaStar, g • τ = τ') ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -1 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        h τ = ((0 : ℂ) : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x - x + 1 = 0 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        h τ = (OnePoint.infty : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -6 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        h τ = ((-16/27 : ℂ) : OnePoint ℂ))

/-- The clauses shared by `QMHauptmodul`'s `f` and the period map `h`: continuous, holomorphic into
`P¹(ℂ)`, and `GammaStarFibresCM`. -/
def IsGammaStarHauptmodul (h : UpperHalfPlane → OnePoint ℂ) : Prop :=
  Continuous h ∧ (∀ τ, IsHolP1At h τ) ∧ GammaStarFibresCM h

/-- **GLUE (moduli side of F1: the period map of `Y`, for one triple).** There is a function
`h : ℍ → P¹(ℂ)` with the clauses `IsGammaStarHauptmodul` such that for every `ℚ̄`-point `y` with
object `P`, every `ι : ℚ̄ → ℂ`, every base change `Q/ℂ` of `P` along `ι` and every `ι`-compatible
uniformization of `Q.A` with kernel `Λ_τ`: `h(τ) = ι(π(y))`.

Why true for the genuine triple (model argument): `h(τ) = π(P_τ)` for R1(b)'s analytic family
`τ ↦ P_τ` (Shimura 1967 Main Thm I; Deligne 1971 §4.15; locators UNVERIFIED), holomorphic by
R1(b)(c). The value clause: `Q ≅ P_τ` compatibly with `ι` up to level structure (both are
`ι`-compatibly `ℂ²/Λ_τ`; GAGA), so they have the same `π` (R2fp's fibre clause; naturality of `π`,
`ToP1.val_comp`). Fibres: `ℂ²/Λ_τ ≅ ℂ²/Λ_τ'` up to an `Aut 𝒪`-twist iff `τ' ∈ Γ*τ` (Shimura;
`Aut 𝒪 = N_B(𝒪)/ℚ^×`, and `1 + i` of reduced norm `−1` is absorbed by `ι`-compatibility), with
R2fp's fibre clause. CM values: the fixed point `τ` of `ι(x)`, `x² = −1`, gives `ℂ²/Λ_τ` the
`𝒪`-linear automorphism `z ↦ λz`, `λ² = −1` (`ι(x)v_τ = λv_τ`), so `HasCM4`, and R2fp gives `0`;
likewise for `−3`, `−24`. Composite of R1(b), R2 and GAGA; not in Mathlib (analytification of `Y₃`
and of the universal family, rv-blueprints Q3). Size: large. -/
def QMPeriodMap (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  ∃ h : UpperHalfPlane → OnePoint ℂ, IsGammaStarHauptmodul h ∧
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
    ∀ (ιe : Qbar →+* ℂ) (Q : QML3 ℂ), IsBaseChangeOf ιe P Q →
    ∀ (τ : UpperHalfPlane) (Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu →
      IotaCompatible Q Φu →
      h τ = (π.val (K := Qbar) y.left).map ιe

/-- The clauses of R1(b)(b)-(c) for a map `τ ↦ y_τ` from `ℍ` to the complex points of `Y`: the
object at `y_τ` is `ι`-compatibly `ℂ²/Λ_τ` (an `ι`-compatible uniformization with kernel exactly
`Λ_τ = ι(𝒪)(τ, 1)ᵀ`), and `τ ↦ π(y_τ) ∈ P¹(ℂ)` is continuous and holomorphic. -/
def IsR1bFamily (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y)) : Prop :=
  (∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (yτ τ) = M3.mk P ∧
    ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      IotaCompatible P Φu) ∧
  Continuous (fun τ => π.val (K := ℂ) (yτ τ).left) ∧
  ∀ τ, IsHolP1At (fun τ => π.val (K := ℂ) (yτ τ).left) τ

/-- **LEAF (R1(b), complex uniformization, family form; a concrete replacement for the placeholder
`HSyn.R01b_ComplexUniformization` at the triple `(Y, Φ, π)`).** There is a map `τ ↦ y_τ` from `ℍ`
to `Y(ℂ)` such that the object at `y_τ` is `ℂ²/ι(𝒪)(τ, 1)ᵀ` with its `ι` (`IsR1bFamily`), and
`τ ↦ π(y_τ)` is holomorphic into `P¹(ℂ)`.

Source: Shimura, Ann. of Math. 85 (1967), Main Theorem I (the canonical model `V` of `Γ\ℍ` with a
holomorphic `φ : ℍ → V(ℂ)` whose value at `τ` is the moduli point of `ℂ²/ι(𝒪)(τ, 1)ᵀ`); Deligne,
Sém. Bourbaki 389 (1971), §4.15 (analytic families) (locators UNVERIFIED). Here
`y_τ = φ(τ)` on the component of `Y₃(ℂ)` given by the level structure `η_τ(a) = ι(a)v_τ/3`, and
`π ∘ φ` is holomorphic because `π` is a morphism. For the genuine `Y₃` this is the published
statement composed with `π`; for another triple satisfying the repaired `R1fpProps` it follows by
qm-pin's comparison (`g : Y' → Y` with `Φ' = Φ ∘ g` is bijective on points, hence an isomorphism,
qm-pin §3.3; and `π' = π ∘ g` on `ℚ̄`-points forces equality as morphisms), so its truth does not
depend on which triple `Classical.choice` picks. Rests on bp-qmmoduli §2.2 as `R1R2fpRep`. -/
def R1bFamily (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  ∃ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), IsR1bFamily Y Φ π yτ

/-- **GLUE (the period map is a normalized Hauptmodul and computes `π`).** For a family as in
`R1bFamily`, `h(τ) = π(y_τ)` has the fibre and CM clauses `GammaStarFibresCM`, and for every
`ℚ̄`-point `y` with object `P`, every `ι : ℚ̄ → ℂ`, every base change `Q/ℂ` of `P` and every
`ι`-compatible uniformization of `Q.A` with kernel `Λ_τ`: `h(τ) = ι(π(y))`.

Why true (model argument): (value) `Q` and `P_τ` are both `ι`-compatibly `ℂ²/Λ_τ`, so `Q ≅ P_τ` as
QM pairs (GAGA: the analytic isomorphism is algebraic), and they differ at most in the level
structure, a twist that `π` does not see (R2fp's fibre clause, extended from `ℚ̄`-points to
`ℂ`-points because the fibre relation of `π` is algebraic); with `ToP1.val_comp`,
`ι(π(y)) = π(y_ℂ) = π(y_τ)`. (fibres) `P_τ`, `P_τ'` are `Aut 𝒪`-twist-equivalent iff `τ' ∈ Γ*τ`
(an `ι`-twisted-compatible linear isomorphism `ℂ²/Λ_τ → ℂ²/Λ_τ'` is `ι(u)` up to scalar,
`u ∈ N_B(𝒪)` of positive norm; Shimura). (CM) at the fixed point of `ι(x)`, `ι(x)v_τ = λv_τ` and
`z ↦ λz` is an `𝒪`-linear automorphism of `ℂ²/Λ_τ` with `λ² = −1` (resp. `λ² − λ + 1 = 0`,
`λ² = −6`), so the pair has `HasCM4` (resp. `HasCM3`, `HasCM24`) and R2fp gives the value. Inputs
not in Mathlib: GAGA, the extension of R2fp to `ℂ`-points, Shimura's description of isomorphisms
of QM tori. Size: large. -/
def PeriodMapGlue (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  ∀ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), IsR1bFamily Y Φ π yτ →
    GammaStarFibresCM (fun τ => π.val (K := ℂ) (yτ τ).left) ∧
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
    ∀ (ιe : Qbar →+* ℂ) (Q : QML3 ℂ), IsBaseChangeOf ιe P Q →
    ∀ (τ : UpperHalfPlane) (Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu →
      IotaCompatible Q Φu →
      π.val (K := ℂ) (yτ τ).left = (π.val (K := Qbar) y.left).map ιe

/-- **`QMPeriodMap` from R1(b) in family form and the period-map glue (proved).** -/
theorem qmPeriodMap_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (hR : R1bFamily Y Φ π) (hG : PeriodMapGlue Y Φ π) : QMPeriodMap Y Φ π := by
  obtain ⟨yτ, hfam⟩ := hR
  obtain ⟨hFC, hval⟩ := hG yτ hfam
  exact ⟨fun τ => π.val (K := ℂ) (yτ τ).left, ⟨hfam.2.1, hfam.2.2, hFC⟩, hval⟩

/-- **GLUE (complex analysis: uniqueness of the normalized Hauptmodul of `Γ*`).** A function
`h : ℍ → P¹(ℂ)` with the clauses `IsGammaStarHauptmodul` equals `QMHauptmodul`'s `f`.

Proof sketch (model argument; every step is textbook complex analysis): `Γ*\ℍ` is compact (`B` is
a division algebra; Shimura, *Introduction to the arithmetic theory of automorphic functions*,
Prop. 9.2, UNVERIFIED number). `f` and `h` induce continuous injections `Γ*\ℍ → P¹`; `f`'s is
onto (`QMHauptmodul`), hence a homeomorphism, and `h`'s is open (open mapping theorem) with closed
image, hence onto. So `φ = h ∘ f⁻¹` is a homeomorphism of `P¹`. Away from the finitely many images
of elliptic points and of the zeros of `jDen ∘ Ω`, `f = jNum/jDen ∘ Ω` is holomorphic (theta
series are holomorphic on `𝔥₂`, `Ω` is holomorphic on `ℍ`) and locally injective, so `φ` is
holomorphic there; the finitely many remaining points are removable singularities (`φ` is
continuous). So `φ` is a biholomorphism of `P¹`, a Möbius map, fixing `0, ∞, −16/27` (both satisfy
the CM clauses, and the fixed points exist: `(i+j)² = −1`, `((1+j)/2)² − (1+j)/2 + 1 = 0`,
`(2j+ij)² = −6`), so `φ = id` and `h = f`. Statable over Mathlib as it stands; size: medium-large
(compactness of `Γ*\ℍ`, removable singularities on `P¹`, Möbius rigidity). -/
def HauptmodulUnique : Prop :=
  ∀ f h : UpperHalfPlane → OnePoint ℂ, QMHauptmodulFn f → IsGammaStarHauptmodul h → h = f

/-- **`QMPeriodValue` from the moduli part and the complex-analysis part (proved).** -/
theorem qmPeriodValue_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (hPM : QMPeriodMap Y Φ π) (hHU : HauptmodulUnique) : QMPeriodValue Y Φ π := by
  intro f hf y P hP ιe Q hQ τ Φu hΦu hc
  obtain ⟨h, hh, hval⟩ := hPM
  rw [← hHU f h hf hh]
  exact hval y P hP ιe Q hQ τ Φu hΦu hc

/-! ### Step 2d: `QMComplexUnif` from a textbook leaf, uniformization glue and lattice algebra -/

/-- **TEXTBOOK leaf (analytic uniformization over `ℂ`).** An abelian surface `A/ℂ` has an analytic
uniformization `Φ : ℂ² → A(ℂ)` (`IsUniformization` at `σ = id`). Mumford, *Abelian Varieties*, §1,
with Serre's GAGA (locators UNVERIFIED). In the build: bp-analytic's `UniformizationLeafAll` gives
one for some `g` (`ZInQ.LeafPush2.exists_isUniformization_of_leaf`); `g = dim A = 2` is the
missing identification. -/
def UniformizationExistsC : Prop :=
  ∀ A : PkgI3.AbVar ℂ, A.dim = (2 : WithBot ℕ∞) →
    ∃ (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φu : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)),
      IsUniformization (RingHom.id ℂ) Λ Φu

/-- **GLUE (structure of a uniformization).** For an analytic uniformization `Φ : ℂ² → A(ℂ)` with
kernel `Λ`: `Λ` is a full lattice (discrete, `ℝ`-span `ℂ²`), and endomorphisms lift to `ℂ²`: a ring
homomorphism `ρ : End(A) → End_ℂ(ℂ²)` (the analytic representation) with `Φ(ρ(e) z) = e(Φ z)`;
`ρ(e)` preserves `Λ`. bp-analytic proves the lifting for its form of uniformization
(`ZInQKernel/HDecomp/Analytic/Uniformization.lean`: `IsUniformization.exists_complexLinear_endo`,
`analyticRep_spec`, `analyticRep_mul`, `analyticRep_id`); the lattice clauses come with its leaf
`UniformizationLeafAll`. Missing: the translation from this file's `IsUniformization` back to
bp-analytic's (the converse of `ZInQ.LeafPush2.isUniformization_of_bp`). Size: small-medium. -/
def UnifStructure : Prop :=
  ∀ (A : PkgI3.AbVar ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
    (Φu : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)), IsUniformization (RingHom.id ℂ) Λ Φu →
    ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧
      ∃ ρ : PkgI3.AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ),
        (∀ e z, Φu (ρ e z) = Φu z ≫ e.hom) ∧ (∀ e, ∀ z ∈ Λ, ρ e z ∈ Λ)

/-- **GLUE (lattice algebra; one textbook input, class number one).** Let `Λ ⊆ ℂ²` be a full
lattice stable under a ring homomorphism `ρ : 𝒪 → End_ℂ(ℂ²)`. Then some `ℂ`-linear automorphism
`F` of `ℂ²` intertwines `ρ` with N5's `ι` (`F ρ(a) = ι(a) F`) and carries `Λ` onto
`Λ_τ = ι(𝒪)(τ, 1)ᵀ` for some `τ ∈ ℍ`.

Proof sketch (model argument): `ρ` extends to `B ⊗ ℂ ≅ M₂(ℂ) → M₂(ℂ)` (via `ι ⊗ ℂ`), an
automorphism, inner by Skolem–Noether, so `ρ = g ι g⁻¹`. `g⁻¹Λ` is a left `𝒪`-lattice of rank 4 in
`B ⊗ ℝ`-terms, i.e. a locally free left `𝒪`-ideal; `𝒪` (maximal, in the indefinite algebra of
discriminant 6) has class number one (Eichler's theorem; Vignéras, *Arithmétique des algèbres de
quaternions*, Cor. III.5.7, or Voight, *Quaternion algebras*, Cor. 28.5.17; numbers UNVERIFIED), so
`g⁻¹Λ = ι(𝒪)w`. `w` is not a complex multiple of a real vector (else `ι(𝒪)w` spans a real plane),
so `w = c(τ, 1)ᵀ` with `τ ∉ ℝ`; scaling by `c⁻¹` commutes with `ι`; if `Im τ < 0`, the unit
`u = 1 + i` (reduced norm `−1`) gives `ι(𝒪)v_τ = ι(𝒪)ι(u)v_τ` and `ι(u)v_τ ∝ (τ', 1)ᵀ`,
`τ' = −(1+√2)²τ ∈ ℍ`. Statable and provable over Mathlib (Skolem–Noether is in the kernel,
`TSkolemKW`; class number one can be proved by a Euclidean argument as mobius-glue did for the
normalizer). Size: medium. -/
def QMLatticeAlgebra : Prop :=
  ∀ (Λ : Submodule ℤ (Fin 2 → ℂ)) [DiscreteTopology Λ], IsZLattice ℝ Λ →
    ∀ ρ : LeafQM.O →+* Module.End ℂ (Fin 2 → ℂ), (∀ a, ∀ z ∈ Λ, ρ a z ∈ Λ) →
      ∃ (τ : ℂ) (hτ : 0 < τ.im) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ)),
        Λ.map (F.toLinearMap.restrictScalars ℤ) = BPAnalytic.QM.qmLattice hτ.ne' ∧
        ∀ a z, F (ρ a z) = (qmMat a).mulVec (F z)

/-- **Uniformizations transport along linear automorphisms (proved).** -/
theorem isUniformization_comp {K : Type} [Field K] {A : PkgI3.AbVar K} {σ : K →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φu : (Fin g → ℂ) → CPts A σ}
    (h : IsUniformization σ Λ Φu) (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) :
    IsUniformization σ (Λ.map (F.toLinearMap.restrictScalars ℤ)) (fun z => Φu (F.symm z)) := by
  obtain ⟨hadd, hker, hsurj, hopen, hhol⟩ := h
  let G : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap F.symm.toLinearMap
  have hG : ∀ z, G z = F.symm z := fun z => rfl
  refine ⟨fun z w => ?_, fun z => ?_, fun P => ?_, fun U => ?_, fun U s => ?_⟩
  · simp only [map_add, hadd]
  · change Φu (F.symm z) = 1 ↔ _
    rw [hker, Submodule.mem_map]
    constructor
    · intro hz
      exact ⟨F.symm z, hz, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  · obtain ⟨z, rfl⟩ := hsurj P
    exact ⟨F z, by simp⟩
  · have : cDom (fun z => Φu (F.symm z)) U = G ⁻¹' cDom Φu U := rfl
    rw [this]
    exact (hopen U).preimage G.continuous
  · have hmaps : Set.MapsTo G (cDom (fun z => Φu (F.symm z)) U) (cDom Φu U) := fun z hz => hz
    exact (hhol U s).comp G.differentiableOn hmaps

/-- **`QMComplexUnif` from the textbook uniformization leaf and two glue Props (proved).** -/
theorem qmComplexUnif_of (hE : UniformizationExistsC) (hS : UnifStructure)
    (hL : QMLatticeAlgebra) : QMComplexUnif := by
  intro Q
  obtain ⟨Λ, Φu, hΦ⟩ := hE Q.A Q.surface
  obtain ⟨hd, hlat, ρ, hρ, hpres⟩ := hS Q.A Λ Φu hΦ
  obtain ⟨τ, hτ, F, hF, hFρ⟩ :=
    hL Λ hlat (ρ.comp Q.q.iota) (fun a z hz => hpres (Q.q.iota a) z hz)
  refine ⟨τ, hτ, fun z => Φu (F.symm z), ?_, fun a z => ?_⟩
  · rw [← hF]
    exact isUniformization_comp hΦ F
  · have e1 : F.symm ((qmMat a).mulVec z) = ρ (Q.q.iota a) (F.symm z) := by
      rw [LinearEquiv.symm_apply_eq]
      have := hFρ a (F.symm z)
      simp only [RingHom.comp_apply, LinearEquiv.apply_symm_apply] at this
      exact this.symm
    change Φu (F.symm ((qmMat a).mulVec z)) = Φu (F.symm z) ≫ (Q.q.iota a).hom
    rw [e1, hρ]

/-! ### Step 2e: `QMComplexUnif` from the decomposition's textbook leaves T35, T11a and lattice algebra

`UniformizationExistsT35` and `T11aRiemannEnd` are the kernel's textbook leaves
`ZInQ.LeafPush2.UniformizationExists` (T35) and `ZInQ.LeafPush2.T11a_RiemannEnd` (T11a)
(`ZInQKernel/HDecomp/LeafPush2/T.lean`), copied verbatim over this file's copies of `CPts` and
`IsUniformization` (the same text as the kernel's); both are in leaf-adopt3's `TextbookLeaves`.
With them, `UniformizationExistsC` and `UnifStructure` are proved (`unifStructure_of`,
`uniformizationExistsC_of`), and only `QMLatticeAlgebra` remains. -/

/-- (copied from `ZInQKernel/HDecomp/LeafPush2/T.lean`, `UniformizationExists`, T35) **AN3 for
abelian varieties (textbook leaf; the analytic half of T11/T12).** Every abelian variety over a
field `K` and every `σ : K → ℂ`: `A(ℂ)_σ` has an analytic uniformization by `ℂ^g`, `g = dim A`, with
kernel a full lattice (Mumford, *Abelian varieties*, §1, with GAGA, Serre 1956, for the complex Lie
group structure; UNVERIFIED numbers). -/
def UniformizationExistsT35 : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → CPts A σ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ IsUniformization σ Λ Φ

/-- (copied from `ZInQKernel/HDecomp/LeafPush2/T.lean`, `T11a_RiemannEnd`) **T11(a), Riemann/GAGA
for endomorphisms (textbook leaf).** For an abelian variety over `ℂ` with a uniformization `Φ`
(kernel `Λ`) at `σ = id`, the endomorphisms of `A` are exactly the `ℂ`-linear maps of `ℂ^g`
preserving `Λ`: each such `M` is induced by a unique endomorphism `f` (`Φ(Mz) = f ∘ Φ(z)`), and each
`f` is induced by some `M`. (Mumford §1 and §2, Birkenhake–Lange Prop. 1.2.1 for complex tori;
GAGA, Serre 1956, for "holomorphic ⇒ algebraic"; UNVERIFIED numbers.) -/
def T11aRiemannEnd : Prop :=
  ∀ (A : PkgI3.AbVar ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → IsUniformization (RingHom.id ℂ) Λ Φ →
    (∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z ∈ Λ, M z ∈ Λ) →
      ∃! f : PkgI3.AbVar.End A, ∀ z, Φ (M z) = Φ z ≫ f.hom) ∧
    (∀ f : PkgI3.AbVar.End A, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, Φ (M z) = Φ z ≫ f.hom)

/-- `UniformizationExistsC` from T35 (proved). -/
theorem uniformizationExistsC_of (h : UniformizationExistsT35) : UniformizationExistsC := by
  intro A hA
  obtain ⟨Λ, Φu, -, -, hU⟩ := h ℂ A (RingHom.id ℂ) 2 hA
  exact ⟨Λ, Φu, hU⟩

/-- **Lifts are unique (proved):** two `ℂ`-linear maps with the same image under a uniformization
with discrete kernel are equal (their difference maps `ℂ^g` into the discrete `Λ`; `ℝ` is
connected). -/
theorem lift_unique {K : Type} [Field K] {A : PkgI3.AbVar K} {σ : K →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ] {Φu : (Fin g → ℂ) → CPts A σ}
    (h : IsUniformization σ Λ Φu) {M M' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hMM : ∀ z, Φu (M z) = Φu (M' z)) : M = M' := by
  obtain ⟨hadd, hker, -, -, -⟩ := h
  have hmem : ∀ z, (M - M') z ∈ Λ := by
    intro z
    rw [← hker, LinearMap.sub_apply]
    have e := hadd (M z - M' z) (M' z)
    rw [sub_add_cancel, hMM] at e
    exact mul_right_cancel (e.symm.trans (one_mul (Φu (M' z))).symm)
  refine LinearMap.ext fun z => ?_
  let N := M - M'
  have hc : Continuous (fun t : ℝ => N ((t : ℂ) • z)) :=
    (LinearMap.continuous_of_finiteDimensional N).comp
      (Complex.continuous_ofReal.smul continuous_const)
  let f : ℝ → Λ := fun t => ⟨N ((t : ℂ) • z), hmem _⟩
  have hf : Continuous f := hc.subtype_mk _
  have h01 := PreconnectedSpace.constant inferInstance hf (x := 0) (y := 1)
  have h2 : N (((0 : ℝ) : ℂ) • z) = N (((1 : ℝ) : ℂ) • z) := congrArg Subtype.val h01
  simp only [Complex.ofReal_zero, zero_smul, map_zero, Complex.ofReal_one, one_smul] at h2
  have h3 : M z - M' z = 0 := by
    rw [h2]; rfl
  exact sub_eq_zero.mp h3

/-- **The analytic representation as a ring homomorphism, from T11a (proved).** For a
uniformization with discrete kernel (as T35 provides), T11a's lifts `M_e` of the endomorphisms are
unique (`lift_unique`), hence form a ring homomorphism `ρ`, and they preserve `Λ`. This is
`UnifStructure`'s conclusion for T35's uniformizations (for an arbitrary uniformization the lattice
clauses would follow by comparison with T35's, bp-analytic's `exists_complexLinear`, not reproved
here; the reduction below only needs T35's). -/
theorem unif_ring_hom (hR : T11aRiemannEnd) (A : PkgI3.AbVar ℂ) (hA : A.dim = (2 : WithBot ℕ∞))
    (Λ : Submodule ℤ (Fin 2 → ℂ)) [DiscreteTopology Λ]
    (Φu : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)) (hU : IsUniformization (RingHom.id ℂ) Λ Φu) :
    ∃ ρ : PkgI3.AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ),
      (∀ e z, Φu (ρ e z) = Φu z ≫ e.hom) ∧ (∀ e, ∀ z ∈ Λ, ρ e z ∈ Λ) := by
  have hT := (hR A 2 Λ Φu hA hU).2
  choose ρf hρf using hT
  have hadd := hU.1
  have hker := hU.2.1
  let ρ : PkgI3.AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ) :=
    { toFun := ρf
      map_one' := lift_unique hU fun z => by
        rw [hρf]; exact Category.comp_id _
      map_mul' := fun e f => lift_unique hU fun z => by
        rw [hρf, Module.End.mul_apply, hρf, hρf]
        exact (Category.assoc _ _ _).symm
      map_zero' := lift_unique hU fun z => by
        rw [hρf, LinearMap.zero_apply, (hker 0).2 (zero_mem _)]
        exact MonObj.comp_one _
      map_add' := fun e f => lift_unique hU fun z => by
        rw [hρf, LinearMap.add_apply, hadd, hρf, hρf]
        exact MonObj.comp_mul _ _ _ }
  refine ⟨ρ, hρf, fun e z hz => ?_⟩
  rw [← hker] at hz ⊢
  change Φu (ρf e z) = 1
  rw [hρf, hz]
  exact MonObj.one_comp _

/-- **`QMComplexUnif` from the textbook leaves T35, T11a and `QMLatticeAlgebra` (proved).** -/
theorem qmComplexUnif_of_textbook (hE : UniformizationExistsT35) (hR : T11aRiemannEnd)
    (hL : QMLatticeAlgebra) : QMComplexUnif := by
  intro Q
  obtain ⟨Λ, Φu, hd, hlat, hΦ⟩ := hE ℂ Q.A (RingHom.id ℂ) 2 Q.surface
  obtain ⟨ρ, hρ, hpres⟩ := unif_ring_hom hR Q.A Q.surface Λ Φu hΦ
  obtain ⟨τ, hτ, F, hF, hFρ⟩ :=
    hL Λ hlat (ρ.comp Q.q.iota) (fun a z hz => hpres (Q.q.iota a) z hz)
  refine ⟨τ, hτ, fun z => Φu (F.symm z), ?_, fun a z => ?_⟩
  · rw [← hF]
    exact isUniformization_comp hΦ F
  · have e1 : F.symm ((qmMat a).mulVec z) = ρ (Q.q.iota a) (F.symm z) := by
      rw [LinearEquiv.symm_apply_eq]
      have := hFρ a (F.symm z)
      simp only [RingHom.comp_apply, LinearEquiv.apply_symm_apply] at this
      exact this.symm
    change Φu (F.symm ((qmMat a).mulVec z)) = Φu (F.symm z) ≫ (Q.q.iota a).hom
    rw [e1, hρ]

/-! ### Step 2f: `QMLatticeAlgebra` from its algebraic core (`normalize`, proved) -/

/-- **GLUE (lattice algebra core: Skolem–Noether over `ℂ` and class number one).** A full lattice
`Λ ⊆ ℂ²` stable under a ring homomorphism `ρ : 𝒪 → End_ℂ(ℂ²)` is carried by a `ℂ`-linear
automorphism `G` intertwining `ρ` with N5's `ι` onto `ι(𝒪)w` (`FibreQMNorm.qmOrbit w`) for a vector
`w` that is not a complex multiple of a real vector.

Proof sketch: `ρ ⊗ ℂ : B ⊗ ℂ ≅ M₂(ℂ) → M₂(ℂ)` is inner (Skolem–Noether; in the kernel as
`TSkolemKW`), giving `G` with `Gρ(a)G⁻¹ = ι(a)`; `GΛ` is a left `𝒪`-lattice of rank 4, hence
`ι(𝒪)w` because the maximal order of the indefinite algebra of discriminant 6 has class number one
(Eichler; Vignéras Cor. III.5.7, Voight Cor. 28.5.17; numbers UNVERIFIED); and `w` is not a
complex multiple `c·r` of a real vector `r`, since then `ι(𝒪)w ⊆ c·ℝ²` would not span `ℂ²` over
`ℝ`. Size: medium (class number one is the substantial part). -/
def QMLatticeFree : Prop :=
  ∀ (Λ : Submodule ℤ (Fin 2 → ℂ)) [DiscreteTopology Λ], IsZLattice ℝ Λ →
    ∀ ρ : LeafQM.O →+* Module.End ℂ (Fin 2 → ℂ), (∀ a, ∀ z ∈ Λ, ρ a z ∈ Λ) →
      ∃ (G : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ)) (w : Fin 2 → ℂ),
        (¬ ∃ (c : ℂ) (r : Fin 2 → ℝ), w = c • (fun i => (r i : ℂ))) ∧
        Λ.map (G.toLinearMap.restrictScalars ℤ) = FibreQMNorm.qmOrbit w ∧
        ∀ a z, G (ρ a z) = (qmMat a).mulVec (G z)

/-- **`QMLatticeAlgebra` from `QMLatticeFree` (proved)**, by `FibreQMNorm.normalize` and rescaling
(scalars commute with `ι`). -/
theorem qmLatticeAlgebra_of_free (h : QMLatticeFree) : QMLatticeAlgebra := by
  intro Λ _ hlat ρ hρ
  obtain ⟨G, w, hw, hG, hGρ⟩ := h Λ hlat ρ hρ
  obtain ⟨τ, hτ, c, hc, hcw⟩ := FibreQMNorm.normalize w hw
  refine ⟨τ, hτ, G.trans (LinearEquiv.smulOfNeZero ℂ (Fin 2 → ℂ) c⁻¹ (inv_ne_zero hc)), ?_, ?_⟩
  · have e1 : ((G.trans (LinearEquiv.smulOfNeZero ℂ (Fin 2 → ℂ) c⁻¹ (inv_ne_zero hc))).toLinearMap.restrictScalars ℤ) =
        FibreQMNorm.smulMap c⁻¹ ∘ₗ (G.toLinearMap.restrictScalars ℤ) := by
      ext v i; simp [FibreQMNorm.smulMap]
    rw [e1, Submodule.map_comp, hG, hcw, ← Submodule.map_comp, FibreQMNorm.smulMap_comp,
      inv_mul_cancel₀ hc]
    have e2 : FibreQMNorm.smulMap 1 = LinearMap.id := by
      ext v i; simp [FibreQMNorm.smulMap]
    rw [e2, Submodule.map_id]
  · intro a z
    simp [hGρ, Matrix.mulVec_smul]

/-! ### Step 2g: `QMLatticeFree` from Skolem–Noether over `ℂ` and class number one -/

/-- **Skolem–Noether over `ℂ`, for N5's order (now proved: `qmSkolemNoetherC_proof`).** Every unital ring homomorphism
`ρ : 𝒪 → End_ℂ(ℂ²)` is conjugate to N5's `ι` by a `ℂ`-linear automorphism `G`
(`G ρ(a) = ι(a) G`). Why: `ρ` extends to a `ℂ`-algebra map `B ⊗_ℚ ℂ → M₂(ℂ)`; `B ⊗ ℂ ≅ M₂(ℂ)`
(through `ι`) is simple, so the map is an isomorphism, and automorphisms of `M₂(ℂ)` are inner
(Skolem–Noether; e.g. Voight, *Quaternion algebras*, Cor. 7.7.4, UNVERIFIED number; the kernel's
`TSkolemKW.leafSkolemNoether` is a form of it). -/
def QMSkolemNoetherC : Prop :=
  ∀ ρ : LeafQM.O →+* Module.End ℂ (Fin 2 → ℂ),
    ∃ G : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ), ∀ a z, G (ρ a z) = (qmMat a).mulVec (G z)

/-- **TEXTBOOK (class number one of `𝒪`, lattice form).** Every full lattice `Λ ⊆ ℂ²` stable under
N5's `ι(𝒪)` is `ι(𝒪)w` for a vector `w` that is not a complex multiple of a real vector. Why: `Λ`
is a left `𝒪`-module, torsion-free of rank 4, so `ℚΛ ≅ B` and `Λ` is a left `𝒪`-ideal, principal
because the maximal order of the indefinite algebra of discriminant 6 has class number one
(Eichler's theorem; Vignéras, *Arithmétique des algèbres de quaternions*, Cor. III.5.7; Voight,
Cor. 28.5.17; numbers UNVERIFIED); `w` is not `c·r` with `r` real, else `ι(𝒪)w ⊆ c·ℝ²` would not
span `ℂ²` over `ℝ`. -/
def QMClassNumberOne : Prop :=
  ∀ (Λ : Submodule ℤ (Fin 2 → ℂ)) [DiscreteTopology Λ], IsZLattice ℝ Λ →
    (∀ a : LeafQM.O, ∀ z ∈ Λ, (qmMat a).mulVec z ∈ Λ) →
    ∃ w : Fin 2 → ℂ, (¬ ∃ (c : ℂ) (r : Fin 2 → ℝ), w = c • (fun i => (r i : ℂ))) ∧
      Λ = FibreQMNorm.qmOrbit w

/-- `i ∈ 𝒪`. -/
def oI : LeafQM.O := ⟨⟨0, 1, 0, 0⟩, show LeafQM.InO _ from ⟨![0, 1, 0, 0], by ext <;> simp [LeafQM.ofInt]⟩⟩
/-- `j ∈ 𝒪`. -/
def oJ : LeafQM.O := ⟨⟨0, 0, 1, 0⟩, show LeafQM.InO _ from ⟨![-1, 0, 2, 0], by ext <;> simp [LeafQM.ofInt]⟩⟩

theorem oI_sq : oI * oI = 1 + 1 := by
  apply Subtype.ext; ext <;> simp [oI] <;> norm_num

theorem oJ_sq : oJ * oJ = -(1 + 1 + 1) := by
  apply Subtype.ext; ext <;> simp [oJ] <;> norm_num

theorem oI_oJ : oI * oJ = -(oJ * oI) := by
  apply Subtype.ext; ext <;> simp [oI, oJ]

/-- `2a = 2n₀ + 2n₁ i + n₂(1 + j) + n₃(i + ij)` for `a = ofInt n`. -/
theorem two_mul_eq (a : LeafQM.O) : ∃ n : Fin 4 → ℤ, a + a =
    ((n 0 + n 0 : ℤ) : LeafQM.O) + ((n 1 + n 1 : ℤ) : LeafQM.O) * oI + ((n 2 : ℤ) : LeafQM.O) * (1 + oJ)
      + ((n 3 : ℤ) : LeafQM.O) * (oI + oI * oJ) ∧ (a : LeafQM.B) = LeafQM.ofInt n := by
  obtain ⟨n, hn⟩ := a.2
  refine ⟨n, ?_, hn⟩
  apply Subtype.ext
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_intCast, Subring.coe_one]
  rw [hn]
  ext <;> simp [LeafQM.ofInt, oI, oJ] <;> ring

/-- N5's `ι(i)` over `ℂ`. -/
def Mi' : Matrix (Fin 2) (Fin 2) ℂ := !![(√2 : ℂ), 0; 0, -(√2 : ℂ)]
/-- N5's `ι(j)` over `ℂ`. -/
def Mj' : Matrix (Fin 2) (Fin 2) ℂ := !![0, -3; 1, 0]

theorem two_qmMat (a : LeafQM.O) (n : Fin 4 → ℤ) (hn : (a : LeafQM.B) = LeafQM.ofInt n) :
    qmMat a + qmMat a = ((n 0 + n 0 : ℤ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ((n 1 + n 1 : ℤ) : ℂ) • Mi' + ((n 2 : ℤ) : ℂ) • (1 + Mj') + ((n 3 : ℤ) : ℂ) • (Mi' + Mi' * Mj') := by
  unfold qmMat
  rw [hn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, LeafQM.ofInt, Mi', Mj',
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem s2sq : (√2 : ℂ) * (√2 : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num

theorem s2ne : (√2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr two_pos)

/-- **`QMSkolemNoetherC`, proved.** With `R = ρ(i)`, `S = ρ(j)` (`R² = 2`, `S² = −3`, `RS = −SR`):
an eigenvector `e₁` of `R` for `√2` exists (else `R = −√2`, forcing `S = 0`), `e₂ = S e₁` is one for
`−√2`, and in the basis `(e₁, e₂)` the maps `R`, `S` are N5's `ι(i) = diag(√2, −√2)`,
`ι(j) = [[0, −3], [1, 0]]`; every `a ∈ 𝒪` is `(2n₀ + 2n₁ i + n₂(1+j) + n₃(i+ij))/2`. -/
theorem qmSkolemNoetherC_proof : QMSkolemNoetherC := by
  intro ρ
  set R := ρ oI with hRdef
  set S := ρ oJ with hSdef
  have hRR : ∀ v, R (R v) = v + v := fun v => by
    have := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => T v) (show R * R = 1 + 1 by
      rw [hRdef, ← map_mul, oI_sq, map_add, map_one])
    simpa using this
  have hSS : ∀ v, S (S v) = -(v + v + v) := fun v => by
    have := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => T v) (show S * S = -(1 + 1 + 1) by
      rw [hSdef, ← map_mul, oJ_sq, map_neg, map_add, map_add, map_one])
    simpa using this
  have hRS : ∀ v, R (S v) = -(S (R v)) := fun v => by
    have := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => T v) (show R * S = -(S * R) by
      rw [hRdef, hSdef, ← map_mul, ← map_mul, oI_oJ, map_neg])
    simpa using this
  set s2 : ℂ := (√2 : ℂ) with hs2
  have hs2sq : s2 * s2 = 2 := s2sq
  have hs2ne : s2 ≠ 0 := s2ne
  -- an eigenvector of `R` for `√2`
  obtain ⟨e1, he1, hRe1⟩ : ∃ e1 : Fin 2 → ℂ, e1 ≠ 0 ∧ R e1 = s2 • e1 := by
    by_cases h0 : ∀ v, R v + s2 • v = 0
    · exfalso
      set e : Fin 2 → ℂ := Pi.single 0 1
      have he : e ≠ 0 := by
        intro h; have := congrFun h 0; simp [e] at this
      have hR : ∀ v, R v = -(s2 • v) := fun v => eq_neg_of_add_eq_zero_left (h0 v)
      have h1 : S e = 0 := by
        have := hRS e
        rw [hR, hR, map_neg, map_smul, neg_neg] at this
        have h2 : (s2 + s2) • S e = 0 := by
          rw [add_smul]; linear_combination (norm := module) -this
        rcases smul_eq_zero.mp h2 with h3 | h3
        · exfalso; apply hs2ne; linear_combination h3 / 2
        · exact h3
      have := hSS e
      rw [h1, map_zero] at this
      apply he
      have h4 : (3 : ℂ) • e = 0 := by linear_combination (norm := module) this
      rcases smul_eq_zero.mp h4 with h5 | h5
      · norm_num at h5
      · exact h5
    · push Not at h0
      obtain ⟨v, hv⟩ := h0
      refine ⟨R v + s2 • v, hv, ?_⟩
      rw [map_add, map_smul, hRR]
      linear_combination (norm := module) (-(hs2sq)) • v
  set e2 := S e1 with he2def
  have hRe2 : R e2 = -(s2 • e2) := by
    rw [he2def, hRS, hRe1, map_smul]
  have hSe2 : S e2 = -(e1 + e1 + e1) := hSS e1
  have he2 : e2 ≠ 0 := by
    intro h
    have := hSe2
    rw [h, map_zero] at this
    apply he1
    have h4 : (3 : ℂ) • e1 = 0 := by linear_combination (norm := module) this
    rcases smul_eq_zero.mp h4 with h5 | h5
    · norm_num at h5
    · exact h5
  have hli : LinearIndependent ℂ ![e1, e2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hR' : s • (s2 • e1) + t • (-(s2 • e2)) = 0 := by
      have := congrArg R hst
      rw [map_add, map_smul, map_smul, hRe1, hRe2, map_zero] at this
      exact this
    have hs : (s * s2 * 2) • e1 = 0 := by
      linear_combination (norm := module) s2 • hst + hR'
    have ht : (t * s2 * 2) • e2 = 0 := by
      linear_combination (norm := module) s2 • hst - hR'
    have hs' : s = 0 := by
      rcases smul_eq_zero.mp hs with h | h
      · simpa [hs2ne] using h
      · exact absurd h he1
    have ht' : t = 0 := by
      rcases smul_eq_zero.mp ht with h | h
      · simpa [hs2ne] using h
      · exact absurd h he2
    exact ⟨hs', ht'⟩
  let b : Module.Basis (Fin 2) ℂ (Fin 2 → ℂ) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb0 : b 0 = e1 := by simp [b]
  have hb1 : b 1 = e2 := by simp [b]
  refine ⟨b.equivFun, ?_⟩
  have hG0 : b.equivFun e1 = Pi.single 0 1 := by
    rw [← hb0]; ext j; simp [Module.Basis.equivFun_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  have hG1 : b.equivFun e2 = Pi.single 1 1 := by
    rw [← hb1]; ext j; simp [Module.Basis.equivFun_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  have hGR : ∀ x, b.equivFun (R x) = Mi'.mulVec (b.equivFun x) := by
    have : (b.equivFun.toLinearMap ∘ₗ R) = (Matrix.mulVecLin Mi') ∘ₗ b.equivFun.toLinearMap := by
      refine b.ext fun i => ?_
      fin_cases i
      · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Fin.zero_eta,
          Fin.isValue, hb0, hRe1, map_smul, hG0, Matrix.mulVecLin_apply]
        ext j; fin_cases j <;> simp [Mi', Matrix.mulVec, dotProduct, Fin.sum_univ_two, hs2]
      · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Fin.mk_one,
          Fin.isValue, hb1, hRe2, map_neg, map_smul, hG1, Matrix.mulVecLin_apply]
        ext j; fin_cases j <;> simp [Mi', Matrix.mulVec, dotProduct, Fin.sum_univ_two, hs2]
    intro x
    exact congrArg (fun T => T x) this
  have hGS : ∀ x, b.equivFun (S x) = Mj'.mulVec (b.equivFun x) := by
    have : (b.equivFun.toLinearMap ∘ₗ S) = (Matrix.mulVecLin Mj') ∘ₗ b.equivFun.toLinearMap := by
      refine b.ext fun i => ?_
      fin_cases i
      · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Fin.zero_eta,
          Fin.isValue, hb0, ← he2def, hG1, hG0, Matrix.mulVecLin_apply]
        ext j; fin_cases j <;> simp [Mj', Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Fin.mk_one,
          Fin.isValue, hb1, hSe2, map_neg, map_add, hG0, hG1, Matrix.mulVecLin_apply]
        ext j; fin_cases j <;> simp [Mj', Matrix.mulVec, dotProduct, Fin.sum_univ_two]; norm_num
    intro x
    exact congrArg (fun T => T x) this
  intro a z
  obtain ⟨n, h2a, hn⟩ := two_mul_eq a
  have hρ2 : ρ a z + ρ a z = ((n 0 + n 0 : ℤ) : ℂ) • z + ((n 1 + n 1 : ℤ) : ℂ) • R z +
      ((n 2 : ℤ) : ℂ) • (z + S z) + ((n 3 : ℤ) : ℂ) • (R z + R (S z)) := by
    have := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => T z) (congrArg ρ h2a)
    simp only [map_add, map_mul, map_intCast, map_one, LinearMap.add_apply,
      Module.End.mul_apply, Module.End.intCast_apply, Module.End.one_apply] at this
    rw [← hRdef, ← hSdef] at this
    rw [this]
    simp only [← Int.cast_smul_eq_zsmul ℂ, map_add, smul_add]
  have h2 : (2 : ℂ) • b.equivFun (ρ a z) = (2 : ℂ) • (qmMat a).mulVec (b.equivFun z) := by
    rw [two_smul, two_smul, ← map_add, hρ2, ← Matrix.add_mulVec, two_qmMat a n hn]
    simp only [map_add, map_smul, hGR, hGS, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_mulVec]
  exact smul_right_injective _ two_ne_zero h2

/-- **`QMLatticeFree` from Skolem–Noether over `ℂ` and class number one (proved):** transport the
lattice by the intertwiner `G` (still a full lattice: `ZLattice.comap` along `G⁻¹`). -/
theorem qmLatticeFree_of (hSN : QMSkolemNoetherC) (hCN : QMClassNumberOne) : QMLatticeFree := by
  intro Λ _ hlat ρ hρ
  obtain ⟨G, hG⟩ := hSN ρ
  let Gc : (Fin 2 → ℂ) ≃L[ℝ] (Fin 2 → ℂ) :=
    LinearEquiv.toContinuousLinearEquiv (G.symm.restrictScalars ℝ)
  have hmap : Λ.map (G.toLinearMap.restrictScalars ℤ) = ZLattice.comap ℝ Λ Gc.toLinearMap := by
    ext z
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      ZLattice.comap, Submodule.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change G.symm (G y) ∈ Λ
      simpa using hy
    · intro hz
      exact ⟨G.symm z, hz, by simp⟩
  have : IsZLattice ℝ Λ := hlat
  obtain ⟨w, hw, hΛw⟩ := hCN (ZLattice.comap ℝ Λ Gc.toLinearMap) inferInstance (by
    intro a z hz
    rw [← hmap] at hz ⊢
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨ρ a y, hρ a y hy, by simp [hG]⟩)
  exact ⟨G, w, hw, hmap.trans hΛw, hG⟩

/-! ### Step 2h: `UnifTransport` from the transport of complex points (algebraic geometry) -/

/-- **GLUE (complex points of the base change).** In the situation of `UnifTransport` there is a
group isomorphism `ψ : Q.A(ℂ) ≅ A(ℂ)_σ` (`σ = ι ∘ emb`) compatible with regular functions: for every
open `U` of `A` and `s ∈ Γ(U, 𝒪_A)` there are an open `U'` of `Q.A` and `s' ∈ Γ(U', 𝒪)` with
`ψ(x) ∈ U(ℂ) ↔ x ∈ U'(ℂ)` and `s(ψ x) = s'(x)` there.

Why true: `A(ℂ)_σ = Hom_K(Spec ℂ, A) = Hom_ℂ(Spec ℂ, A ×_K ℂ)`, and `A ×_K ℂ ≅ P.A ×_ℚ̄ ℂ ≅ Q.A`
as `ℂ`-schemes (pullback pasting with `FibreOver`'s isomorphism and `IsBaseChangeOf`'s square).
The bijection `χ : Q.A(ℂ) → A(ℂ)_σ` so obtained comes from an isomorphism of `ℂ`-varieties, so by
rigidity (Mumford, *Abelian Varieties*, §4 Cor. 1, UNVERIFIED number) `ψ(x) = χ(x)·χ(1)⁻¹` is a
group isomorphism. For `U`, `s`: `U'` is the image in `Q.A` of `t⁻¹(U_ℂ)`, `t` the translation by
`χ(1)⁻¹` on `A_ℂ`, and `s' = (s ⊗ 1) ∘ t` transported to `Q.A`. Not in Mathlib: pullbacks of points
over `Over` categories are routine; rigidity is a textbook leaf. Size: medium. -/
def CPtsTransport : Prop :=
  ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K) (emb : K.K →+* Qbar) (P : QML3 Qbar),
    (letI : Algebra K.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) →
    ∀ (ιe : Qbar →+* ℂ) (Q : QML3 ℂ), IsBaseChangeOf ιe P Q →
    ∃ ψ : CPts Q.A (RingHom.id ℂ) ≃* CPts (LeafAdopt.abVarEquiv K.K A) (ιe.comp emb),
      ∀ (U : (LeafAdopt.abVarEquiv K.K A).X.left.Opens)
        (s : Γ((LeafAdopt.abVarEquiv K.K A).X.left, U)),
        ∃ (U' : Q.A.X.left.Opens) (s' : Γ(Q.A.X.left, U')),
          ∀ x : CPts Q.A (RingHom.id ℂ), (⊤ ≤ (ψ x).left ⁻¹ᵁ U ↔ ⊤ ≤ x.left ⁻¹ᵁ U') ∧
            (⊤ ≤ x.left ⁻¹ᵁ U' → cEvalAt (ψ x) U s = cEvalAt x U' s')

/-- **`UnifTransport` from `CPtsTransport` (proved):** `Φ_A = ψ ∘ Φ_Q`. -/
theorem unifTransport_of (hCP : CPtsTransport) : UnifTransport := by
  intro K A emb P hiso ιe Q hQ Λ Φu hU
  obtain ⟨ψ, hψ⟩ := hCP K A emb P hiso ιe Q hQ
  obtain ⟨hadd, hker, hsurj, hopen, hhol⟩ := hU
  have hdom : ∀ (U : (LeafAdopt.abVarEquiv K.K A).X.left.Opens)
      (U' : Q.A.X.left.Opens) (s' : Γ(Q.A.X.left, U')),
      (∀ x : CPts Q.A (RingHom.id ℂ), (⊤ ≤ (ψ x).left ⁻¹ᵁ U ↔ ⊤ ≤ x.left ⁻¹ᵁ U')) →
      cDom (fun z => ψ (Φu z)) U = cDom Φu U' := by
    intro U U' s' h
    ext z
    exact h (Φu z)
  refine ⟨fun z => ψ (Φu z), fun z w => ?_, fun z => ?_, fun x => ?_, fun U => ?_, fun U s => ?_⟩
  · simp only [hadd, map_mul]
  · rw [← hker]
    exact MulEquiv.map_eq_one_iff ψ
  · obtain ⟨y, rfl⟩ := ψ.surjective x
    obtain ⟨z, rfl⟩ := hsurj y
    exact ⟨z, rfl⟩
  · obtain ⟨U', s', h⟩ := hψ U 0
    rw [hdom U U' s' (fun x => (h x).1)]
    exact hopen U'
  · obtain ⟨U', s', h⟩ := hψ U s
    rw [hdom U U' s' (fun x => (h x).1)]
    exact (hhol U' s').congr (fun z hz => (h (Φu z)).2 hz)

/-! ### Step 2c: the proofs -/

/-- An embedding `ℚ̄ → ℂ` over `ℚ`. -/
def qbarToC : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift

/-- **The finite value forces `jDen ≠ 0` (proved)** from `QMDenZeroCM3` and the `−3` clause of
`QMHauptmodul`; then F1's quotient is the value of `f`. -/
theorem jRatio_of_value {f : UpperHalfPlane → OnePoint ℂ} (hf : QMHauptmodulFn f)
    (hD : QMDenZeroCM3) (τ : UpperHalfPlane) (t : ℂ) (ht : f τ = (t : OnePoint ℂ)) :
    PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = t := by
  have hden : PkgI1.jDen (PkgI1.Omega τ) ≠ 0 := by
    intro h0
    obtain ⟨x, hxO, hx, g, hg, hfix⟩ := hD τ h0
    have h3 := hf.2.2.2.2.2.1 x hxO hx g hg τ hfix
    rw [ht] at h3
    exact OnePoint.coe_ne_infty _ h3
  have h2 := hf.2.1 τ hden
  rw [ht] at h2
  exact (OnePoint.coe_injective h2).symm

/-- **`FibreQMPeriod` for one triple from the named Props (proved).** -/
theorem fibreQMPeriodAt_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (h1 : R1fpProps Y Φ) (hH : PkgI1.QMHauptmodul) (hU : QMComplexUnif)
    (hV : QMPeriodValue Y Φ π) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    FibreQMPeriodAt Y Φ π := by
  intro u hu K A hFib
  obtain ⟨emb, y, P, hP, hy, hiso⟩ := hFib
  obtain ⟨f, hf⟩ := hH
  obtain ⟨Q, -, hQ⟩ := h1.2.2.2.1 Qbar ℂ qbarToC y P hP
  obtain ⟨τ, hτ, Φu, hΦu, hc⟩ := hU Q
  obtain ⟨Φa, hΦa⟩ := hT K A emb P hiso (qbarToC : Qbar →+* ℂ) Q hQ _ Φu hΦu
  refine ⟨(qbarToC : Qbar →+* ℂ).comp emb, _, Φa, hΦa, τ, hτ, LinearEquiv.refl ℂ _, ?_, ?_⟩
  · ext v
    simp
  · have hval := hV f hf y P hP (qbarToC : Qbar →+* ℂ) Q hQ ⟨τ, hτ⟩ Φu hΦu hc
    rw [hy, OnePoint.map_some] at hval
    have e : (qbarToC : Qbar →+* ℂ) (algebraMap ℚ Qbar (Jmap u)) = ((Jmap u : ℚ) : ℂ) := by
      rw [RingHom.coe_coe, AlgHom.commutes, eq_ratCast]
    rw [e] at hval
    exact jRatio_of_value hf hD ⟨τ, hτ⟩ _ hval

/-- **`FibreQMPeriod` for the leaf's own triple from the named Props (proved).** -/
theorem fibreQMPeriodOwn_of (h : R1R2fp) (hH : PkgI1.QMHauptmodul) (hU : QMComplexUnif)
    (hV : QMPeriodValue (ownY h) (ownΦ h) (ownπ h)) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    FibreQMPeriodOwn h :=
  fibreQMPeriodAt_of _ _ _ (own_spec h).1 hH hU hV hD hT

/-- **Main result: `FibreQMPeriod` from named Props (proved).** The Hauptmodul comparison is
needed only for the leaf's own triple; `Pin.MobiusGlue` carries it to every triple. -/
theorem fibreQMPeriod_of_named (h : R1R2fp) (hM : Pin.MobiusGlue) (hH : PkgI1.QMHauptmodul)
    (hU : QMComplexUnif) (hV : QMPeriodValue (ownY h) (ownΦ h) (ownπ h)) (hD : QMDenZeroCM3)
    (hT : UnifTransport) : ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_of_own h hM (fibreQMPeriodOwn_of h hH hU hV hD hT)

/-- **Variant without `MobiusGlue` (proved):** with the Hauptmodul comparison for every triple. -/
theorem fibreQMPeriod_of_named_all (hH : PkgI1.QMHauptmodul) (hU : QMComplexUnif)
    (hV : ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R2fpProps Y Φ π → QMPeriodValue Y Φ π)
    (hD : QMDenZeroCM3) (hT : UnifTransport) : ThetaPt.FibreQMPeriod :=
  fun Y Φ π h1 h2 => fibreQMPeriodAt_of Y Φ π h1 hH hU (hV Y Φ π h1 h2) hD hT

/-- The same from the decomposition's bundle form of the leaf (`LeafAdopt.R1R2fpRep`). -/
theorem fibreQMPeriod_of_named_rep (h : LeafAdopt.R1R2fpRep) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hU : QMComplexUnif)
    (hV : QMPeriodValue (ownY (LeafAdopt.R1R2fp_of_rep h)) (ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (ownπ (LeafAdopt.R1R2fp_of_rep h)))
    (hD : QMDenZeroCM3) (hT : UnifTransport) : ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_of_named _ hM hH hU hV hD hT

/-- **Main result, finest form (proved):** `FibreQMPeriod` from `MobiusGlue` (proved by mobius-glue
from two curve facts and T5), the existing leaf `QMHauptmodul`, the leaf candidates
`QMComplexUnif` and `QMDenZeroCM3`, and the glue `QMPeriodMap` (own triple), `HauptmodulUnique`,
`UnifTransport`. -/
theorem fibreQMPeriod_of_parts (h : R1R2fp) (hM : Pin.MobiusGlue) (hH : PkgI1.QMHauptmodul)
    (hU : QMComplexUnif) (hPM : QMPeriodMap (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_of_named h hM hH hU (qmPeriodValue_of _ _ _ hPM hHU) hD hT

/-- **Main result with `QMComplexUnif` split (proved).** -/
theorem fibreQMPeriod_of_parts' (h : R1R2fp) (hM : Pin.MobiusGlue) (hH : PkgI1.QMHauptmodul)
    (hE : UniformizationExistsC) (hS : UnifStructure) (hL : QMLatticeAlgebra)
    (hPM : QMPeriodMap (ownY h) (ownΦ h) (ownπ h)) (hHU : HauptmodulUnique)
    (hD : QMDenZeroCM3) (hT : UnifTransport) : ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_of_parts h hM hH (qmComplexUnif_of hE hS hL) hPM hHU hD hT

/-- **Main result, finest form (proved):** `FibreQMPeriod` from
* `Pin.MobiusGlue` (glue; proved by mobius-glue from `CurveRatFactor`, `CurveSurj` and T5),
* `PkgI1.QMHauptmodul` (existing composite leaf), `UniformizationExistsC` (textbook leaf),
  `R1bFamily` at the leaf's own triple (leaf: R1(b), concrete),
* `UnifStructure`, `QMLatticeAlgebra`, `PeriodMapGlue` (own triple), `HauptmodulUnique`,
  `QMDenZeroCM3`, `UnifTransport` (glue). -/
theorem fibreQMPeriod_of_leaves_glue (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsC)
    (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h))
    (hS : UnifStructure) (hL : QMLatticeAlgebra) (hG : PeriodMapGlue (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_of_parts' h hM hH hE hS hL (qmPeriodMap_of _ _ _ hR hG) hHU hD hT

/-- **Main result, final form (proved):** `FibreQMPeriod` from
* leaves: `PkgI1.QMHauptmodul` (existing composite leaf), the textbook leaves T35
  (`UniformizationExistsT35`) and T11a (`T11aRiemannEnd`), both already in leaf-adopt3's
  `TextbookLeaves`, and R1(b) in family form at the leaf's own triple (`R1bFamily`);
* glue: `Pin.MobiusGlue` (proved by mobius-glue), `QMLatticeAlgebra`, `PeriodMapGlue` (own triple),
  `HauptmodulUnique`, `QMDenZeroCM3`, `UnifTransport`. -/
theorem fibreQMPeriod_of_textbook (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h))
    (hL : QMLatticeAlgebra) (hG : PeriodMapGlue (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_of_parts h hM hH (qmComplexUnif_of_textbook hE hR11 hL)
    (qmPeriodMap_of _ _ _ hR hG) hHU hD hT

/-- **Main result, final form (proved):** as `fibreQMPeriod_of_textbook`, with
`QMLatticeAlgebra` replaced by its algebraic core `QMLatticeFree` (Skolem–Noether and class number
one). -/
theorem fibreQMPeriod_final (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h))
    (hF : QMLatticeFree) (hG : PeriodMapGlue (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_of_textbook h hM hH hE hR11 hR (qmLatticeAlgebra_of_free hF) hG hHU hD hT

/-- **Main result, final form with the lattice algebra split (proved).** Hypotheses:
* leaves: `PkgI1.QMHauptmodul` (existing composite leaf), T35 `UniformizationExistsT35`, T11a
  `T11aRiemannEnd` (both already in leaf-adopt3's `TextbookLeaves`), `QMSkolemNoetherC`,
  `QMClassNumberOne` (textbook), `R1bFamily` at the leaf's own triple (R1(b), concrete);
* glue: `Pin.MobiusGlue` (proved by mobius-glue from two curve facts and T5), `PeriodMapGlue` (own
  triple), `HauptmodulUnique`, `QMDenZeroCM3`, `UnifTransport`. -/
theorem fibreQMPeriod_final' (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hSN : QMSkolemNoetherC) (hCN : QMClassNumberOne)
    (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h)) (hG : PeriodMapGlue (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_final h hM hH hE hR11 hR (qmLatticeFree_of hSN hCN) hG hHU hD hT

/-- **Main result, final form (proved).** As `fibreQMPeriod_final'`, with `UnifTransport` replaced
by `CPtsTransport` (complex points of the base change, as a group isomorphism compatible with
regular functions). -/
theorem fibreQMPeriod_final'' (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hSN : QMSkolemNoetherC) (hCN : QMClassNumberOne)
    (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h)) (hG : PeriodMapGlue (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hCP : CPtsTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_final' h hM hH hE hR11 hSN hCN hR hG hHU hD (unifTransport_of hCP)

/-- **Main result (proved).** `FibreQMPeriod` from
* leaves: `PkgI1.QMHauptmodul` (existing composite leaf), T35 `UniformizationExistsT35` and T11a
  `T11aRiemannEnd` (verbatim copies of the kernel's textbook leaves, in leaf-adopt3's
  `TextbookLeaves`), `QMClassNumberOne` (textbook: Eichler's class number one, lattice form),
  `R1bFamily` at the leaf's own triple (R1(b), concrete);
* glue: `Pin.MobiusGlue` (proved by mobius-glue from two curve facts and T5), `PeriodMapGlue` (own
  triple), `HauptmodulUnique`, `QMDenZeroCM3`, `CPtsTransport`.
(`QMSkolemNoetherC` is proved here, `qmSkolemNoetherC_proof`.) -/
theorem fibreQMPeriod_main (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hCN : QMClassNumberOne)
    (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h)) (hG : PeriodMapGlue (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hCP : CPtsTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_final'' h hM hH hE hR11 qmSkolemNoetherC_proof hCN hR hG hHU hD hCP

/-- **Main result from the decomposition's bundle form of the leaf (`LeafAdopt.R1R2fpRep`,
proved).** -/
theorem fibreQMPeriod_main_rep (h : LeafAdopt.R1R2fpRep) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hCN : QMClassNumberOne)
    (hR : R1bFamily (ownY (LeafAdopt.R1R2fp_of_rep h)) (ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (ownπ (LeafAdopt.R1R2fp_of_rep h)))
    (hG : PeriodMapGlue (ownY (LeafAdopt.R1R2fp_of_rep h)) (ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (ownπ (LeafAdopt.R1R2fp_of_rep h)))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hCP : CPtsTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_main _ hM hH hE hR11 hCN hR hG hHU hD hCP

end FibreQM

end G0Split

end HSyn

end

