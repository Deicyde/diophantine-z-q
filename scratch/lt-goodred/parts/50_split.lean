/-! ## lt-goodred §5: `QMSplitCaseRank`, proved from I3.M1

Suppose `rank End(A) > 4`. Then (all proved below):
* `End⁰(A) ↪ End⁰(A_Ω) ≅ M₂(ℚ(√d))`, a `ℚ`-algebra embedding (`endBC` injective, `ℚ` flat over
  `ℤ`); so `dim_ℚ End⁰(A) ≤ 8`;
* `B →ₐ[ℚ] End⁰(A)` (`quatEmbed`) and `B` is a division algebra, so for `s ∉ θ(B)` the map
  `(b, b') ↦ θ(b) + θ(b')·s` is injective: `dim End⁰(A) ≥ 8` (`eight_le_finrank`);
* hence `End⁰(A) ≅ M₂(ℚ(√d))`, and the preimage `x` of `E₁₂` is a nonzero element with `x² = 0`;
* clearing denominators, `n·x = 1 ⊗ m` with `m ∈ End(A)`, `m ≠ 0`, `m² = 0` (`End(A)` is free,
  I3.M1, so `m ↦ 1 ⊗ m` is injective);
* a nonzero `m` is an isogeny (`EndDivision`), so `m ∘ m = 0` is surjective; but the zero
  endomorphism factors through `Spec k`, a point, so `A` would be a point, against `dim A = 2`
  (`eq_zero_of_mul_self_eq_zero`). -/

section LTSplitSec

set_option linter.style.haveILetI false

noncomputable section

namespace LTGoodRed.QM

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM
open scoped Quaternion TensorProduct

/-! ### A square-zero endomorphism of an `EndDivision` surface is zero -/

/-- **A square-zero endomorphism of a positive-dimensional `EndDivision` abelian variety is zero**
(proved): otherwise it is surjective (an isogeny), so its square, the zero endomorphism, is
surjective; the zero endomorphism factors through `Spec k`, so `A` is a point, of dimension `≤ 0`. -/
theorem eq_zero_of_mul_self_eq_zero {k : Type} [Field k] (A : PkgI3.AbVar k)
    (hdiv : PkgI3.EndDivision A) (hdim : A.dim = 2) (m : PkgI3.AbVar.End A) (hm : m * m = 0) :
    m = 0 := by
  by_contra hm0
  obtain ⟨-, hsurj⟩ := hdiv m hm0
  have hcomp : (m * m).hom = m.hom ≫ m.hom := rfl
  have h1 : m.hom ≫ m.hom = (1 : A.X ⟶ A.X) := by rw [← hcomp, hm]; rfl
  have hs : Surjective (m.hom ≫ m.hom).left := by
    rw [Over.comp_left]; infer_instance
  rw [h1, Hom.one_def, Over.comp_left] at hs
  haveI hsub : Subsingleton A.X.left := by
    constructor
    intro y1 y2
    obtain ⟨x1, rfl⟩ := hs.surj y1
    obtain ⟨x2, rfl⟩ := hs.surj y2
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _
  have hle : A.dim ≤ 0 := topologicalKrullDim_zero_of_discreteTopology A.X.left
  rw [hdim] at hle
  exact absurd hle (by decide)

/-! ### `ℚ ⊗ M` for a free `ℤ`-module `M` -/

section Tensor

variable {M : Type} [Ring M]

theorem intCast_smul_one_tmul (c : ℤ) (m : M) :
    ((c : ℚ)) • ((1 : ℚ) ⊗ₜ[ℤ] m) = (1 : ℚ) ⊗ₜ[ℤ] (c • m) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one,
    show ((c : ℤ) : ℚ) = c • (1 : ℚ) by simp, TensorProduct.smul_tmul]

/-- Every element of `ℚ ⊗ M` has an integer multiple of the form `1 ⊗ m`. -/
theorem exists_smul_eq_tmul (x : ℚ ⊗[ℤ] M) :
    ∃ (n : ℤ) (m : M), n ≠ 0 ∧ (n : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] m := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q m =>
    refine ⟨q.den, q.num • m, by exact_mod_cast q.den_nz, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul,
      show ((q.den : ℤ) : ℚ) * q = ((q.num : ℤ) : ℚ) by
        rw [Int.cast_natCast, mul_comm]; exact Rat.mul_den_eq_num q,
      show ((q.num : ℤ) : ℚ) = q.num • (1 : ℚ) by simp, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨n, m, hn, h⟩ := hx
    obtain ⟨n', m', hn', h'⟩ := hy
    refine ⟨n * n', n' • m + n • m', mul_ne_zero hn hn', ?_⟩
    rw [smul_add, Int.cast_mul, mul_comm, mul_smul, h, mul_comm, mul_smul, h',
      intCast_smul_one_tmul, intCast_smul_one_tmul, TensorProduct.tmul_add]

/-- `m ↦ 1 ⊗ m` is injective for a free `ℤ`-module (flatness). -/
theorem one_tmul_injective [Module.Free ℤ M] :
    Function.Injective (fun m : M => (1 : ℚ) ⊗ₜ[ℤ] m) := by
  have hinj : Function.Injective ((Algebra.linearMap ℤ ℚ).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b h => by simpa using h)
  intro m m' h
  apply (TensorProduct.lid ℤ M).symm.injective
  apply hinj
  simpa [TensorProduct.lid_symm_apply] using h

end Tensor

/-! ### A copy of `B` and an element outside it give dimension `≥ 8` -/

theorem eight_le_finrank {R : Type} [Ring R] [Algebra ℚ R] [FiniteDimensional ℚ R]
    (θ : ℍ[ℚ, 2, -3] →ₐ[ℚ] R) (h4 : 4 < Module.finrank ℚ R) : 8 ≤ Module.finrank ℚ R := by
  haveI : Nontrivial R := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    rw [Module.finrank_zero_of_subsingleton] at h4
    omega
  have hr : Module.finrank ℚ (LinearMap.range θ.toLinearMap) ≤ 4 := by
    calc _ ≤ Module.finrank ℚ ℍ[ℚ, 2, -3] := LinearMap.finrank_range_le _
      _ = 4 := QuaternionAlgebra.finrank_eq_four (R := ℚ) _ _ _
  obtain ⟨s, hs⟩ : ∃ s, s ∉ LinearMap.range θ.toLinearMap := by
    by_contra h
    push_neg at h
    have htop : LinearMap.range θ.toLinearMap = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [htop, finrank_top] at hr
    omega
  have hunit : ∀ b : ℍ[ℚ, 2, -3], b ≠ 0 → ∃ c, θ c * θ b = 1 := by
    intro b hb
    obtain ⟨u, rfl⟩ := quatB6_isUnit b hb
    exact ⟨↑u⁻¹, by rw [← map_mul, Units.inv_mul, map_one]⟩
  let Lm : (ℍ[ℚ, 2, -3] × ℍ[ℚ, 2, -3]) →ₗ[ℚ] R :=
    θ.toLinearMap.comp (LinearMap.fst ℚ _ _) +
      ((LinearMap.mulRight ℚ s).comp θ.toLinearMap).comp (LinearMap.snd ℚ _ _)
  have hLm : ∀ b b', Lm (b, b') = θ b + θ b' * s := fun _ _ => rfl
  have hinj : Function.Injective Lm := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨b, b'⟩ h
    rw [hLm] at h
    by_cases hb' : b' = 0
    · subst hb'
      rw [map_zero, zero_mul, add_zero] at h
      by_cases hb : b = 0
      · rw [hb]; rfl
      · obtain ⟨c, hc⟩ := hunit b hb
        rw [h, mul_zero] at hc
        exact absurd hc zero_ne_one
    · exfalso
      obtain ⟨c, hc⟩ := hunit b' hb'
      apply hs
      refine ⟨-(c * b), ?_⟩
      show θ (-(c * b)) = s
      have : s = θ c * (θ b' * s) := by rw [← _root_.mul_assoc, hc, _root_.one_mul]
      rw [this, eq_neg_of_add_eq_zero_right h, map_neg, map_mul, mul_neg]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod, QuaternionAlgebra.finrank_eq_four (R := ℚ) 2 0 (-3)] at this

/-! ### The proof -/

/-- **`QMSplitCaseRank`, proved** from I3.M1 (`PkgI3.HomFreeFinite`). -/
theorem qmSplitCaseRank (hM1 : PkgI3.HomFreeFinite) : QMSplitCaseRank := by
  intro k _ _ A Ω _ _ _ φ _ hdim hdiv d _ he
  obtain ⟨e⟩ := he
  obtain ⟨hfreeM, hfinM, -, -⟩ := hM1 k A A
  obtain ⟨hfreeN, hfinN, -, -⟩ := hM1 Ω (A.baseChange Ω) (A.baseChange Ω)
  by_contra hlt
  push_neg at hlt
  -- `F = ℚ(√d)`, `dim_ℚ M₂(F) = 8`
  have hf : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by norm_num) d
  have hF : Module.finrank ℚ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) = 2 := by
    rw [(AdjoinRoot.powerBasis hf).finrank, AdjoinRoot.powerBasis_dim,
      Polynomial.natDegree_X_pow_sub_C]
  haveI : Module.Finite ℚ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) :=
    (AdjoinRoot.powerBasis hf).finite
  haveI : Nontrivial (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    rw [Module.finrank_zero_of_subsingleton] at hF
    omega
  have h8 : Module.finrank ℚ
      (Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) = 8 := by
    rw [Module.finrank_matrix, hF]; rfl
  -- `End⁰(A) ↪ End⁰(A_Ω)`
  let β : PkgI3.AbVar.End A →ₐ[ℤ] PkgI3.AbVar.End (A.baseChange Ω) :=
    (HSyn.LinkedTate.endBC A Ω).toIntAlgHom
  let Φ₀ : PkgI3.AbVar.End0 A →ₐ[ℚ] PkgI3.AbVar.End0 (A.baseChange Ω) :=
    Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) β
  haveI : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  have hΦ₀ : Function.Injective Φ₀ := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ) β.toLinearMap
      (HSyn.LinkedTate.endBC_injective A Ω)
    have heq : ⇑Φ₀ = ⇑(β.toLinearMap.lTensor ℚ) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul q m => simp [Φ₀, Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    rw [heq]; exact h
  let Φ := e.toAlgHom.comp Φ₀
  have hΦ : Function.Injective Φ := e.injective.comp hΦ₀
  -- dimensions
  have hrank : Module.finrank ℚ (PkgI3.AbVar.End0 A) = Module.finrank ℤ (PkgI3.AbVar.End A) :=
    finrank_end0 hM1 A
  obtain ⟨θ⟩ := quatEmbed A φ
  have hge : 8 ≤ Module.finrank ℚ (PkgI3.AbVar.End0 A) :=
    eight_le_finrank θ (by rw [hrank]; exact hlt)
  have hle : Module.finrank ℚ (PkgI3.AbVar.End0 A) ≤ 8 := by
    rw [← h8]; exact LinearMap.finrank_le_finrank_of_injective (f := Φ.toLinearMap) hΦ
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := Φ.toLinearMap)
      (by rw [h8]; omega)).mp hΦ
  -- the preimage of `E₁₂`
  let E : Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) := !![0, 1; 0, 0]
  have hE0 : E ≠ 0 := by
    intro h
    have := congrFun (congrFun h 0) 1
    simp [E] at this
  have hEE : E * E = 0 := by
    simp only [E, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  obtain ⟨x, hx⟩ := hsurj E
  have hx0 : x ≠ 0 := by rintro rfl; exact hE0 (by rw [← hx, map_zero])
  have hxx : x * x = 0 := hΦ (by rw [map_mul, hx, hEE, map_zero])
  -- clearing denominators
  obtain ⟨n, m, hn, hnm⟩ := exists_smul_eq_tmul x
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [TensorProduct.tmul_zero, smul_eq_zero] at hnm
    rcases hnm with h | h
    · exact hn (by exact_mod_cast h)
    · exact hx0 h
  have hmm : m * m = 0 := by
    apply one_tmul_injective (M := PkgI3.AbVar.End A)
    show (1 : ℚ) ⊗ₜ[ℤ] (m * m) = (1 : ℚ) ⊗ₜ[ℤ] (0 : PkgI3.AbVar.End A)
    rw [TensorProduct.tmul_zero, ← _root_.mul_one (1 : ℚ), ← Algebra.TensorProduct.tmul_mul_tmul,
      ← hnm, smul_mul_smul_comm, hxx, smul_zero]
  exact hm0 (eq_zero_of_mul_self_eq_zero A hdiv hdim m hmm)

/-- **`QMEndRank` from the leaves I3.M1 and T27 alone** (proved). -/
theorem qmEndRank_of_leaves (hM1 : PkgI3.HomFreeFinite) (hT27 : PkgI3.QMDichotomyYu) :
    HSyn.LinkedTate.QMEndRank :=
  qmEndRank_of hM1 hT27 (qmSplitCaseRank hM1)

end LTGoodRed.QM

end

end LTSplitSec

#print axioms LTGoodRed.QM.eq_zero_of_mul_self_eq_zero
#print axioms LTGoodRed.QM.eight_le_finrank
#print axioms LTGoodRed.QM.qmSplitCaseRank
#print axioms LTGoodRed.QM.qmEndRank_of_leaves
