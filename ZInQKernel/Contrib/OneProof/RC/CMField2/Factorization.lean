import ZInQKernel.Contrib.OneProof.RC.X0Model2.ChartReparam
import ZInQKernel.Contrib.OneProof.RC.X0Model2.JOrbit
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_card_primCosetReps_eq_dedekindPsi
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Topology.Algebra.Module.Cardinality

/-! Specialization of the modular polynomial, including at repeated j-values.
Provenance (c). First use transcendental parameters, then continuity. -/

noncomputable section

open Polynomial UpperHalfPlane ModularCurve Matrix
open scoped MatrixGroups

namespace ZInQ.Manuscript.RC.CMField2

/-- The parameter of the triangular lattice with basis (aτ+b,d). -/
def cosetParameter (t : ℕ × ℕ × ℕ) (τ : ℍ) : ℍ :=
  ofComplex (((t.1 : ℂ) * (τ : ℂ) + (t.2.1 : ℂ)) / (t.2.2 : ℂ))

theorem coe_cosetParameter {N a b d : ℕ} (hN : N ≠ 0)
    (ht : (a, b, d) ∈ primCosetReps N) (τ : ℍ) :
    (cosetParameter (a, b, d) τ : ℂ) = ((a : ℂ) * (τ : ℂ) + (b : ℂ)) / (d : ℂ) := by
  obtain ⟨h, _, _⟩ := (mem_primCosetReps hN).mp ht
  have ha : 0 < a := Nat.pos_of_ne_zero fun ha => hN (h.symm.trans (by simp [ha]))
  have hd : 0 < d := Nat.pos_of_ne_zero fun hd => hN (h.symm.trans (by simp [hd]))
  have hpos : 0 < (((a : ℂ) * (τ : ℂ) + (b : ℂ)) / (d : ℂ)).im := by
    rw [show (d : ℂ) = ((d : ℝ) : ℂ) by norm_cast]
    simpa [Complex.div_ofReal_im, Complex.mul_im] using
      div_pos (mul_pos (show (0 : ℝ) < a by exact_mod_cast ha) τ.im_pos)
        (show (0 : ℝ) < d by exact_mod_cast hd)
  exact congrArg (fun z : ℍ => (z : ℂ)) (ofComplex_apply_of_im_pos hpos)

private theorem coe_slDenom_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    (γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ) ≠ 0 := by
  exact UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ

/-- For a transcendental parameter, the triangular representatives give distinct
j-values. A modular transformation identifying two translates would otherwise
give a nonzero quadratic equation over ℚ for the parameter. -/
theorem injOn_coset_j_of_transcendental (N : ℕ) [NeZero N] {τ : ℍ}
    (hτ : Transcendental ℚ (τ : ℂ)) :
    Set.InjOn (fun t => X0Model.analyticJ (cosetParameter t τ))
      (primCosetReps N : Set (ℕ × ℕ × ℕ)) := by
  rintro ⟨a, b, d⟩ ht ⟨a', b', d'⟩ ht' he
  have hN := NeZero.ne N
  have ⟨had, hbd, _⟩ := (mem_primCosetReps hN).mp ht
  have ⟨had', hbd', _⟩ := (mem_primCosetReps hN).mp ht'
  have ha : a ≠ 0 := by rintro rfl; simp_all
  have hd : d ≠ 0 := by rintro rfl; simp_all
  have ha' : a' ≠ 0 := by rintro rfl; simp_all
  have hd' : d' ≠ 0 := by rintro rfl; simp_all
  obtain ⟨γ, hγ⟩ := (X0Model2.analyticJ_eq_iff _ _).mp he
  let p := γ 0 0
  let q := γ 0 1
  let c := γ 1 0
  let e := γ 1 1
  have hdet : p * e - q * c = 1 := by
    have h := γ.property
    rwa [Matrix.det_fin_two] at h
  have heq := congrArg (fun z : ℍ => (z : ℂ)) hγ
  rw [X0Model2.coe_sl_smul, X0Model2.slMoebius, div_eq_iff (coe_slDenom_ne_zero _ _),
    coe_cosetParameter hN ht, coe_cosetParameter hN ht'] at heq
  change (p : ℂ) * (((a : ℂ) * (τ : ℂ) + b) / d) + (q : ℂ) =
    (((a' : ℂ) * (τ : ℂ) + b') / d') *
      ((c : ℂ) * (((a : ℂ) * (τ : ℂ) + b) / d) + (e : ℂ)) at heq
  let k₂ : ℤ := (a' : ℤ) * c * a
  let k₁ : ℤ := (a' : ℤ) * (c * b + e * d) + (b' : ℤ) * c * a - (d' : ℤ) * p * a
  let k₀ : ℤ := (b' : ℤ) * (c * b + e * d) - (d' : ℤ) * (p * b + q * d)
  let P : ℚ[X] := C (k₂ : ℚ) * X ^ 2 + C (k₁ : ℚ) * X + C (k₀ : ℚ)
  have hzero : aeval (τ : ℂ) P = 0 := by
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
    have hdC' : (d' : ℂ) ≠ 0 := by exact_mod_cast hd'
    field_simp [hdC, hdC'] at heq
    simp [P, k₂, k₁, k₀]
    linear_combination -heq
  have hP : P = 0 := transcendental_iff.mp hτ P hzero
  have hk₂ : k₂ = 0 := by
    have h := congrArg (fun p : ℚ[X] => p.coeff 2) hP
    change P.coeff 2 = (0 : ℚ[X]).coeff 2 at h
    simp only [P, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at h
    norm_num at h
    exact_mod_cast h
  have hk₁ : k₁ = 0 := by
    have h := congrArg (fun p : ℚ[X] => p.coeff 1) hP
    change P.coeff 1 = (0 : ℚ[X]).coeff 1 at h
    simp only [P, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at h
    norm_num at h
    exact_mod_cast h
  have hk₀ : k₀ = 0 := by
    have h := congrArg (fun p : ℚ[X] => p.coeff 0) hP
    exact_mod_cast (show (k₀ : ℚ) = 0 by simpa [P, coeff_add, coeff_C_mul, coeff_X_pow] using h)
  have hc : c = 0 := by
    have haZ : (a : ℤ) ≠ 0 := by exact_mod_cast ha
    have haZ' : (a' : ℤ) ≠ 0 := by exact_mod_cast ha'
    exact ((mul_eq_zero.mp ((mul_eq_zero.mp hk₂).resolve_right haZ)).resolve_left haZ')
  have hpe : p * e = 1 := by simpa [hc] using hdet
  have hp0 : p ≠ 0 := by intro hh; simp [hh] at hpe
  have huni : p = 1 ∨ p = -1 := Int.isUnit_iff.mp (isUnit_iff_dvd_one.mpr ⟨e, hpe.symm⟩)
  have hep : e = p := by rcases huni with h | h <;> rw [h] at hpe ⊢ <;> omega
  have hcross : (a' : ℤ) * (d : ℤ) = (d' : ℤ) * (a : ℤ) := by
    apply mul_left_cancel₀ hp0
    have hh : (a' : ℤ) * (p * d) - (d' : ℤ) * p * a = 0 := by
      simpa [k₁, hc, hep] using hk₁
    linear_combination hh
  have hA : a = a' := by
    have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN
    have hD : (a : ℤ) * (d : ℤ) = N := by exact_mod_cast had
    have hD' : (a' : ℤ) * (d' : ℤ) = N := by exact_mod_cast had'
    have hq : (N : ℤ) * (a : ℤ)^2 = (N : ℤ) * (a' : ℤ)^2 := by
      calc
        (N : ℤ) * (a : ℤ)^2 = ((a' : ℤ) * (d' : ℤ)) * (a : ℤ)^2 := by rw [hD']
        _ = ((d' : ℤ) * (a : ℤ)) * (a : ℤ) * (a' : ℤ) := by ring
        _ = ((a : ℤ) * (d : ℤ)) * (a' : ℤ)^2 := by rw [← hcross]; ring
        _ = (N : ℤ) * (a' : ℤ)^2 := by rw [hD]
    have hz := mul_left_cancel₀ hN' hq
    exact_mod_cast (show (a : ℤ) = (a' : ℤ) by
      rcases le_or_gt (a : ℤ) a' with h | h
      · by_contra hn
        have h' := lt_of_le_of_ne h hn
        nlinarith [mul_pos (sub_pos.mpr h') (show 0 < (a : ℤ) + (a' : ℤ) by positivity)]
      · nlinarith [mul_pos (sub_pos.mpr h) (show 0 < (a : ℤ) + (a' : ℤ) by positivity)])
  subst a'
  have hD : d' = d := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) (had'.trans had.symm)
  subst d'
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd
  have hdiff : p * ((b' : ℤ) - b) = q * d := by
    have hh : (b' : ℤ) * (p * d) - (d : ℤ) * (p * b + q * d) = 0 := by
      simpa [k₀, hc, hep] using hk₀
    apply mul_right_cancel₀ hdZ
    linear_combination hh
  have hB : b = b' := by
    have h₁ : (d : ℤ) ∣ (b' : ℤ) - b := by
      refine ⟨p * q, ?_⟩
      have hp₂ : p * p = 1 := by simpa [hep] using hpe
      calc
        (b' : ℤ) - b = p * (p * ((b' : ℤ) - b)) := by rw [← mul_assoc, hp₂, one_mul]
        _ = (d : ℤ) * (p * q) := by rw [hdiff]; ring
    have h₂ : (b' : ℤ) - b = 0 := by
      by_contra hn
      have hh := Int.natAbs_le_of_dvd_ne_zero h₁ hn
      omega
    omega
  simp [hB]

/-- The specialization has one factor for each primitive coset, including
multiplicities when several values coincide. -/
theorem modularPolynomial_eq_coset_product (N : ℕ) [NeZero N]
    (P : ModularPolynomialData N) (τ : ℍ) :
    P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) (X0Model.analyticJ τ)) =
      ∏ t ∈ primCosetReps N, (X - C (X0Model.analyticJ (cosetParameter t τ))) := by
  classical
  have hgen (τ : ℍ) (hτ : Transcendental ℚ (τ : ℂ)) :
      P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) (X0Model.analyticJ τ)) =
        ∏ t ∈ primCosetReps N, (X - C (X0Model.analyticJ (cosetParameter t τ))) := by
    let p := P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) (X0Model.analyticJ τ))
    have hmon : p.Monic := P.monic.map _
    let f := fun t => X0Model.analyticJ (cosetParameter t τ)
    have hprod : (∏ t ∈ primCosetReps N, (X - C (f t))).Monic :=
      monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
    have hdiv : (∏ t ∈ primCosetReps N, (X - C (f t))) ∣ p := by
      apply Finset.prod_dvd_of_coprime
      · intro i hi j hj hij
        exact isCoprime_X_sub_C_of_isUnit_sub
          (sub_ne_zero.mpr (fun h => hij (injOn_coset_j_of_transcendental N hτ hi hj h))).isUnit
      · intro t ht
        apply dvd_iff_isRoot.mpr
        rcases t with ⟨a,b,d⟩
        exact ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero N P ht τ _
          (coe_cosetParameter (NeZero.ne N) ht τ)
    have hdeg : p.natDegree ≤ (∏ t ∈ primCosetReps N, (X - C (f t))).natDegree := by
      rw [natDegree_finsetProd_X_sub_C_eq_card, card_primCosetReps_eq_dedekindPsi N (NeZero.ne N)]
      exact ((P.monic.natDegree_map _).trans P.natDegree_eq).le
    simpa [p, f, hmon.leadingCoeff] using
      eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hprod hdiv hdeg
  have hcont : Continuous X0Model.analyticJ := by
    rw [← continuousOn_univ]
    have h := X0Model.analyticOn_j.continuousOn.comp
      (UpperHalfPlane.continuous_coe.continuousOn (s := Set.univ)) (fun x _ => x.im_pos)
    simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply] using h
  have hparam (t : ℕ × ℕ × ℕ) (ht : t ∈ primCosetReps N) : Continuous (cosetParameter t) := by
    rcases t with ⟨a,b,d⟩
    apply UpperHalfPlane.isOpenEmbedding_coe.isInducing.continuous_iff.mpr
    have h := fun x : ℍ => coe_cosetParameter (NeZero.ne N) ht x
    change Continuous (fun x : ℍ => (cosetParameter (a,b,d) x : ℂ))
    simp_rw [h]
    exact ((continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const).div_const _
  have hdense : Dense {τ : ℍ | Transcendental ℚ (τ : ℂ)} := by
    exact ((Algebraic.countable ℚ ℂ).dense_compl ℂ).preimage
      UpperHalfPlane.isOpenEmbedding_coe.isOpenMap
  apply Polynomial.funext
  intro y
  let lhs := fun τ : ℍ =>
    (P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) (X0Model.analyticJ τ))).eval y
  let rhs := fun τ : ℍ =>
    (∏ t ∈ primCosetReps N, (X - C (X0Model.analyticJ (cosetParameter t τ))) : ℂ[X]).eval y
  have hl : Continuous lhs := by
    simp only [lhs, eval_map, eval₂_eq_sum]
    exact continuous_finsetSum _ fun i _ => ((P.Φ.coeff i).continuous_eval₂ _ |>.comp hcont).mul
      continuous_const
  have hr : Continuous rhs := by
    simp only [rhs, eval_prod, eval_sub, eval_X, eval_C]
    exact continuous_finsetProd _ fun t ht => continuous_const.sub (hcont.comp (hparam t ht))
  have hclosed : IsClosed {τ | lhs τ = rhs τ} := isClosed_eq hl hr
  have hs : {τ : ℍ | Transcendental ℚ (τ : ℂ)} ⊆ {τ | lhs τ = rhs τ} :=
    fun z hz => congrArg (eval y) (hgen z hz)
  exact closure_minimal hs hclosed (hdense τ)

/-- Every root is one of the primitive coset values, even in special fibers. -/
theorem exists_coset_of_modularPolynomial_root (N : ℕ) [NeZero N]
    (P : ModularPolynomialData N) (τ : ℍ) (j : ℂ)
    (hj : (P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) (X0Model.analyticJ τ))).IsRoot j) :
    ∃ t ∈ primCosetReps N, X0Model.analyticJ (cosetParameter t τ) = j := by
  rw [modularPolynomial_eq_coset_product, IsRoot, eval_prod, Finset.prod_eq_zero_iff] at hj
  obtain ⟨t, ht, he⟩ := hj
  exact ⟨t, ht, (sub_eq_zero.mp (by simpa only [eval_sub, eval_X, eval_C] using he)).symm⟩


end ZInQ.Manuscript.RC.CMField2
