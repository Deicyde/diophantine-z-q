import ZInQKernel.Contrib.OneProof.RC.Determinant.Output
import ZInQKernel.Contrib.CloudB3RC53.Nodes

/-!
# (5.9) as the shared top layer's coefficient nodes (Lane RC7)

The shared top layer (namespace `ZInQ.Contrib.CloudB3RC53`, file `Nodes.lean`) records `f, d ∈ 𝒪[G]`,
`G = 𝔽₂^b`, and the corrected coordinates `ũ_x` by coefficients (`CoordData b`), and consumes (5.9)
through `ClearingIdentity`, `PoleBound` and `BaseRegular`.  This file produces exactly those
propositions from `fixed_field_clearing` (`Output.lean`), for the actual elements `f = 2^a Δ⁴` and
`d = η Δ Q` of the group ring `MonoidAlgebra O (Multiplicative 𝔽₂^b)` and the given coordinates
`ũ_x = g_x / 2^{e_x} ∈ Λ[1/2]` (manuscript `diophantine_zq.tex`, tex 5486–5664; App G 10901–10914).

* `sgnChar x : Multiplicative 𝔽₂^b →* ℤˣ` is the sign character `g ↦ (-1)^{⟨x, g⟩}`; its values are
  the shared layer's `sgn x g` (`sgnChar_coe`).
* `clearing_nodes` (PROVED from the inputs of `fixed_field_clearing`): there is `C : CoordData b`
  whose `u` is the given coordinate data, with `ClearingIdentity C`, `PoleBound C (16(d_K+5)M) M`
  for every `M`, and `BaseRegular C c` with `c = a + 4h₁ ≤ c_det = a + 4(h_K + 2c_E + 2t_K)`.
-/

namespace ZInQ.Manuscript.RC.Determinant

open Matrix Finset Filter Topology

/-- Binary addresses `x ∈ 𝔽₂^b` (tex 2179–2271). -/
abbrev Addr (b : ℕ) : Type := Fin b → ZMod 2

/-- The sign group `G = 𝔽₂^b`, written multiplicatively for the group ring. -/
abbrev SignGroup (b : ℕ) : Type := Multiplicative (Addr b)

theorem signGroup_mul_self {b : ℕ} (g : SignGroup b) : g * g = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
  generalize (Multiplicative.toAdd g) i = c
  fin_cases c <;> decide

private theorem sgn_mul_aux (A B : ZMod 2) :
    (if A + B = 0 then (1 : ℤˣ) else -1) = (if A = 0 then 1 else -1) * (if B = 0 then 1 else -1) := by
  fin_cases A <;> fin_cases B <;> decide

/-- The sign character `g ↦ (-1)^{⟨x, g⟩}` of the address `x` (tex 2179–2271, 5666–5667). -/
def sgnChar {b : ℕ} (x : Addr b) : SignGroup b →* ℤˣ where
  toFun g := if (∑ i, x i * (Multiplicative.toAdd g) i) = 0 then 1 else -1
  map_one' := by simp
  map_mul' g h := by
    simp only [toAdd_mul, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact sgn_mul_aux _ _

/-- The values of `sgnChar` are the shared layer's signs `sgn x g`. -/
theorem sgnChar_coe {b : ℕ} (x : Addr b) (g : Addr b) :
    ((sgnChar x (Multiplicative.ofAdd g) : ℤˣ) : ℤ) = ZInQ.Contrib.CloudB3RC53.sgn x g := by
  simp only [sgnChar, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, ZInQ.Contrib.CloudB3RC53.sgn]
  split_ifs <;> simp

theorem sgnChar_zero {b : ℕ} : sgnChar (0 : Addr b) = 1 := by
  ext g; simp [sgnChar]

section Bridge

variable {O : Type*} [CommRing O] [Algebra Lam O]

omit [Algebra Lam O] in
/-- The sign evaluation of an element of the group ring, written as the finite sum over the group. -/
theorem signEval_eq_sum {b : ℕ} (χ : SignGroup b →* ℤˣ) (s : MonoidAlgebra O (SignGroup b)) :
    signEval χ s = ∑ g : SignGroup b, s.coeff g * (((χ g : ℤˣ) : ℤ) : O) := by
  rw [signEval, MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by intro; simp)]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp [smul_eq_mul]

omit [Algebra Lam O] in
theorem signEval_sgnChar_zero {b : ℕ} (s : MonoidAlgebra O (SignGroup b)) :
    signEval (sgnChar (0 : Addr b)) s = aug s := by
  rw [signEval_eq_sum, aug, MonoidAlgebra.lift_apply,
    Finsupp.sum_fintype _ _ (by intro; simp)]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp [sgnChar_zero, smul_eq_mul]

variable {D : PoleData Lam O} (LC : LaurentCoeffData D)

/-- The group-basis coefficient data of an element `s ∈ O[G]`: `F g i = [tⁱ] s_g`. -/
noncomputable def coeffData {b : ℕ} (s : MonoidAlgebra O (SignGroup b)) : Addr b → ℤ → ℤ_[2] :=
  fun g i => LC.coeffZ (s.coeff (Multiplicative.ofAdd g)) i

/-- The shared layer's coefficientwise sign evaluation of `coeffData s` is the coefficient of the
sign evaluation: `[tⁱ](s_x) = Σ_g (-1)^{⟨x,g⟩} [tⁱ] s_g` (tex 5666–5667). -/
theorem signEval_coeffData {b : ℕ} (s : MonoidAlgebra O (SignGroup b)) (x : Addr b) (i : ℤ) :
    ZInQ.Contrib.CloudB3RC53.signEval (coeffData LC s) x i =
      LC.coeffZ (signEval (sgnChar x) s) i := by
  rw [signEval_eq_sum, LC.coeffZ_sum, ZInQ.Contrib.CloudB3RC53.signEval]
  rw [← (Equiv.sum_comp Multiplicative.ofAdd _)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_comm (s.coeff _), LC.coeffZ_intCast_mul, sgnChar_coe]
  rfl

/-- The `2`-adic norm of a coefficient divisible by `2^M` is at most `2^{-M}`. -/
theorem norm_le_of_two_pow_dvd {z : ℤ_[2]} {M : ℕ} (h : (2 : ℤ_[2]) ^ M ∣ z) :
    ‖z‖ ≤ (2 : ℝ) ^ (-(M : ℤ)) := by
  have := (PadicInt.norm_le_pow_iff_mem_span_pow z M).2 (Ideal.mem_span_singleton.2 (by
    simpa using h))
  simpa using this

/-- Decay of the coefficients of an element of `O` at `-∞`, as a limit. -/
theorem tendsto_coeffZ_atBot (y : O) : Tendsto (LC.coeffZ y) atBot (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨L, hL⟩ := LC.decay y M
  rw [Filter.eventually_atBot]
  refine ⟨-(L : ℤ) - 1, fun i hi => ?_⟩
  rw [dist_zero_right]
  have h1 := norm_le_of_two_pow_dvd (hL i (by omega))
  have h2 : (2 : ℝ) ^ (-(M : ℤ)) = (1 / 2 : ℝ) ^ M := by
    rw [_root_.zpow_neg, zpow_natCast, one_div, inv_pow]
  linarith

include LC in
/-- **(5.9) as the shared top layer's nodes (PROVED from the inputs of `fixed_field_clearing`).**
For the binary family over `𝔽₂^b`, with the inputs of `fixed_field_clearing` at the sign characters
`sgnChar x` and the coordinates `u x j = [tʲ] ũ_x = [tʲ] g_x / 2^{e_x}`, the coefficient data
`C = (coeffData f, coeffData d, u)` of `f = 2^a Δ⁴`, `d = η Δ Q` satisfies `ClearingIdentity C`,
`PoleBound C (16(d_K+5)M) M` for every `M`, and `BaseRegular C c` with
`c = a + 4h₁ ≤ c_det = a + 4(h_K + 2c_E + 2t_K)`. -/
theorem clearing_nodes [IsDomain O] {b : ℕ}
    (B : SmithBlocks (MonoidAlgebra O (SignGroup b)) O) (hn : 2 < B.n)
    (haug : ∀ i, (B.A i).map aug = (B.A0 i).map (algebraMap Lam O))
    (sd : ScalarData B) (κ ε η : MonoidAlgebra O (SignGroup b)) (a : ℕ)
    (u : Addr b → ℕ → ℚ_[2]) (e : Addr b → ℕ) (g : Addr b → Lam)
    (hu : ∀ x j, u x j = ((PowerSeries.coeff j (g x) : ℤ_[2]) : ℚ_[2]) / 2 ^ e x)
    (h2O : (2 : O) ≠ 0)
    (RankOne Acyclic : Addr b → Prop) (hpat : ∀ x, RankOne x ∨ Acyclic x)
    (hrank : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → RankOne x →
      uK (e x) (g x) = evK (sgnChar x) η * evK (sgnChar x) κ * sd.αK (evK (sgnChar x)) *
        (((2 : FractionRing O) ^ a)⁻¹ * sd.βK (evK (sgnChar x))) * cleanT (evK (sgnChar x)) B ε)
    (hacyc : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → Acyclic x →
      sd.αK (evK (sgnChar x)) = 0 ∧ uK (e x) (g x) = (0 : FractionRing O))
    (hpole : ∀ x M i, ∀ j k, ((B.A i).map (signEval (sgnChar x))) j k ∈ D.poleModLE M (4 * M))
    (dK hK cE tK : ℕ) (hm : B.mTot ≤ dK + 5) (hh : B.hSmith ≤ hK + 2 * cE + 2 * tK) :
    ∃ C : ZInQ.Contrib.CloudB3RC53.CoordData b, C.u = u ∧
      ZInQ.Contrib.CloudB3RC53.ClearingIdentity C ∧
      (∀ M : ℕ, ZInQ.Contrib.CloudB3RC53.PoleBound C (16 * (dK + 5) * M) M) ∧
      ZInQ.Contrib.CloudB3RC53.BaseRegular C (a + 4 * B.hSmith) ∧
      a + 4 * B.hSmith ≤ a + 4 * (hK + 2 * cE + 2 * tK) := by
  obtain ⟨hid, hneg, hne, hval, hle, hpl⟩ := fixed_field_clearing D LC sgnChar B hn haug sd κ ε η a
    e g h2O RankOne Acyclic hpat hrank hacyc hpole dK hK cE tK hm hh
  refine ⟨⟨coeffData LC (clearF B a), coeffData LC (sd.dd κ ε η), u⟩, rfl, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩,
    hle⟩
  · intro gg
    exact tendsto_coeffZ_atBot LC _
  · refine ⟨Finset.univ.sup e, fun x j => ?_⟩
    show ‖u x j‖ ≤ _
    rw [hu x j, norm_div, norm_pow]
    have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
      have := Padic.norm_p (p := 2); simpa using this
    rw [h2, inv_pow, div_inv_eq_mul]
    have hc : ‖((PowerSeries.coeff j (g x) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 := PadicInt.norm_le_one _
    have hex : e x ≤ Finset.univ.sup e := Finset.le_sup (Finset.mem_univ x)
    have hpow : (2 : ℝ) ^ e x ≤ 2 ^ Finset.univ.sup e := pow_le_pow_right₀ (by norm_num) hex
    have hpos : (0 : ℝ) ≤ 2 ^ e x := by positivity
    nlinarith [norm_nonneg ((PowerSeries.coeff j (g x) : ℤ_[2]) : ℚ_[2])]
  · intro x n
    show HasSum (fun j : ℕ => ((ZInQ.Contrib.CloudB3RC53.signEval (coeffData LC (clearF B a)) x
      (n - j) : ℤ_[2]) : ℚ_[2]) * u x j)
      ((ZInQ.Contrib.CloudB3RC53.signEval (coeffData LC (sd.dd κ ε η)) x n : ℤ_[2]) : ℚ_[2])
    simp only [signEval_coeffData]
    convert hid x n using 2 with k
    rw [hu x k]
  · intro M x i hi
    rw [signEval_coeffData]
    exact hpl M x i hi
  · intro i hi
    rw [signEval_coeffData, signEval_sgnChar_zero]
    exact hneg i hi
  · rw [signEval_coeffData, signEval_sgnChar_zero]
    exact hne
  · rw [signEval_coeffData, signEval_sgnChar_zero]
    exact hval

end Bridge

end ZInQ.Manuscript.RC.Determinant
