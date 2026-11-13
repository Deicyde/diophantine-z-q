import FQMBase

noncomputable section

namespace FQMSN

open Matrix

def qmMat (a : LeafQM.O) : Matrix (Fin 2) (Fin 2) ℂ :=
  (BPAnalytic.QM.iota (a : LeafQM.B)).map (fun r : ℝ => (r : ℂ))

def QMSkolemNoetherC : Prop :=
  ∀ ρ : LeafQM.O →+* Module.End ℂ (Fin 2 → ℂ),
    ∃ G : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ), ∀ a z, G (ρ a z) = (qmMat a).mulVec (G z)

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

def Mi' : Matrix (Fin 2) (Fin 2) ℂ := !![(√2 : ℂ), 0; 0, -(√2 : ℂ)]
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

end FQMSN
#print axioms FQMSN.qmSkolemNoetherC_proof
