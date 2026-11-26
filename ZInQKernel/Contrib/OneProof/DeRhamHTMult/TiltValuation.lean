import ZInQKernel.Contrib.G9.KerTheta

/-! # `[ε] − 1` is not in `(ξ²)` for a generator `ε` of `ℤ_p(1)` in the tilt

Let `ε ∈ 𝓞_ℂ_p♭` with `ε♯ = 1` and `ε^{(1)} ≠ 1` (so `ε = (1, ζ_p, ζ_{p²}, …)`). Then
`[ε] − 1 ∈ W(𝓞_ℂ_p♭)` is not divisible by `ξ²` (`teich_sub_one_not_mem_span_xi_sq`).

Proof: write `ε = ε₁^p` and `[ε] − 1 = ([ε₁] − 1) η` with `η = Σ_{j<p} [ε₁]^j`. Here
`θ([ε₁] − 1) = ζ_p − 1 ≠ 0` and `θ(η) = Σ ζ_p^j = 0`. The image `η₀ = Σ ε₁^j` of `η` in the tilt
satisfies `η₀^p = (ε − 1)^{p−1}`, and `|(ε − 1)♯| = |ζ_{p²} − 1|^{p²}` (compare
`(ε − 1)^{(2)}` with `ζ_{p²} − 1` modulo `p`), while `|ζ_{p²} − 1|^{p(p−1)} = |p|` (the cyclotomic
polynomial at `1`). Hence `|η₀♯| = |p|`, which excludes `η ∈ (ξ²)` (that would give
`η₀ = (p♭)² c`). So `η = ξ w` with `θ(w) ≠ 0`, and `[ε] − 1 ∈ (ξ²)` would force `θ(w)(ζ_p − 1) = 0`.
-/

set_option autoImplicit false

namespace DeRhamHTMult

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.BdrKer.Cp Ideal

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

theorem norm_one_sub_pow_le {x : ℂ_[p]} (hx : ‖x‖ ≤ 1) (k : ℕ) : ‖1 - x ^ k‖ ≤ ‖1 - x‖ := by
  have h : 1 - x ^ k = (1 - x) * ∑ i ∈ Finset.range k, x ^ i := by
    linear_combination geom_sum_mul x k
  have hs : ‖∑ i ∈ Finset.range k, x ^ i‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  rw [h, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hs

theorem norm_eq_one_of_pow {x : ℂ_[p]} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1) : ‖x‖ = 1 := by
  have h := congrArg norm hx
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h

/-- `|ζ − 1|^{p(p−1)} = |p|` for a primitive `p²`-th root of unity `ζ ∈ ℂ_p`. -/
theorem norm_sub_one_pow {ζ : ℂ_[p]} (hζ : IsPrimitiveRoot ζ (p ^ 2)) :
    ‖ζ - 1‖ ^ (p * (p - 1)) = (p : ℝ)⁻¹ := by
  have hp0 : p ^ 2 ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hprod := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ
  have hev := congrArg (Polynomial.eval 1) hprod
  rw [show p ^ 2 = p ^ (1 + 1) by norm_num, Polynomial.eval_one_cyclotomic_prime_pow,
    ← show p ^ 2 = p ^ (1 + 1) by norm_num, Polynomial.eval_prod] at hev
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
  have hn := congrArg norm hev
  rw [norm_prod, PkgI4.Cp.norm_p] at hn
  have hconst : ∀ μ ∈ primitiveRoots (p ^ 2) ℂ_[p], ‖1 - μ‖ = ‖ζ - 1‖ := by
    intro μ hμ
    have hμp : IsPrimitiveRoot μ (p ^ 2) :=
      (mem_primitiveRoots (Nat.pos_of_ne_zero hp0)).mp hμ
    have hμ1 : ‖μ‖ = 1 := norm_eq_one_of_pow p hp0 hμp.pow_eq_one
    have hζ1 : ‖ζ‖ = 1 := norm_eq_one_of_pow p hp0 hζ.pow_eq_one
    obtain ⟨i, -, hi⟩ := hμp.eq_pow_of_pow_eq_one hζ.pow_eq_one
    obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hμp.pow_eq_one
    rw [norm_sub_rev ζ 1]
    apply le_antisymm
    · rw [← hj]; exact norm_one_sub_pow_le p hζ1.le j
    · rw [← hi]; exact norm_one_sub_pow_le p hμ1.le i
  rw [Finset.prod_congr rfl hconst, Finset.prod_const, hζ.card_primitiveRoots,
    Nat.totient_prime_pow hp.out two_pos, show p ^ (2 - 1) = p by norm_num] at hn
  exact hn.symm

theorem inv_p_lt_norm_sub_one {ζ : ℂ_[p]} (hζ : IsPrimitiveRoot ζ (p ^ 2)) :
    (p : ℝ)⁻¹ < ‖ζ - 1‖ := by
  by_contra hle
  push Not at hle
  have h2 : 2 ≤ p * (p - 1) := by
    have := hp.out.two_le
    nlinarith [Nat.sub_add_cancel (show 1 ≤ p by omega)]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have := norm_sub_one_pow p hζ
  have h3 : ‖ζ - 1‖ ^ (p * (p - 1)) ≤ (p : ℝ)⁻¹ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) hle _).trans (pow_le_pow_of_le_one hpos.le hpinv.le h2)
  rw [this] at h3
  nlinarith

variable {p}

/-- `ε^{(2)}` is a primitive `p²`-th root of unity. -/
theorem isPrimitiveRoot_root_two {ε : PreTilt 𝓞_ℂ_[p] p} (h1 : PreTilt.untilt ε = 1)
    (h2 : root ε 1 ≠ 1) : IsPrimitiveRoot (root ε 2) (p ^ 2) := by
  rw [IsPrimitiveRoot.iff_orderOf]
  apply orderOf_eq_prime_pow
  · rw [pow_one, root_succ_pow]; exact h2
  · rw [root_pow]; exact h1

theorem isPrimitiveRoot_root_one {ε : PreTilt 𝓞_ℂ_[p] p} (h1 : PreTilt.untilt ε = 1)
    (h2 : root ε 1 ≠ 1) : IsPrimitiveRoot (root ε 1) p := by
  rw [IsPrimitiveRoot.iff_orderOf]
  apply orderOf_eq_prime
  · have := root_pow ε 1
    rw [pow_one] at this
    rw [this, h1]
  · exact h2

/-- `|(ε − 1)♯| = |ζ_{p²} − 1|^{p²}`. -/
theorem norm_untilt_sub_one {ε : PreTilt 𝓞_ℂ_[p] p} (h1 : PreTilt.untilt ε = 1)
    (h2 : root ε 1 ≠ 1) :
    ‖((PreTilt.untilt (ε - 1) : 𝓞_ℂ_[p]) : ℂ_[p])‖ =
      ‖((root ε 2 : 𝓞_ℂ_[p]) : ℂ_[p]) - 1‖ ^ (p ^ 2) := by
  set z : ℂ_[p] := ((root ε 2 : 𝓞_ℂ_[p]) : ℂ_[p]) with hz
  set w : ℂ_[p] := ((root (ε - 1) 2 : 𝓞_ℂ_[p]) : ℂ_[p]) with hw
  have hζ : IsPrimitiveRoot z (p ^ 2) :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mpr (isPrimitiveRoot_root_two h1 h2)
  have hmod : root (ε - 1) 2 - (root ε 2 - 1) ∈ span {(p : 𝓞_ℂ_[p])} := by
    rw [← Ideal.Quotient.eq, mk_root, map_sub, map_sub (Ideal.Quotient.mk _), mk_root, map_one,
      map_one]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmod
  have hd : ‖w - (z - 1)‖ ≤ (p : ℝ)⁻¹ := by
    have := congrArg (fun x : 𝓞_ℂ_[p] => ‖(x : ℂ_[p])‖) hc
    push_cast at this
    rw [← this, norm_mul, PkgI4.Cp.norm_p, mul_comm]
    exact mul_le_of_le_one_right (by positivity) (norm_le_one p c)
  have hr : ‖w‖ = ‖z - 1‖ := by
    have hlt : ‖w - (z - 1)‖ < ‖z - 1‖ :=
      hd.trans_lt (inv_p_lt_norm_sub_one p hζ)
    have e : w = (z - 1) + (w - (z - 1)) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]
  rw [← root_pow (ε - 1) 2]
  push_cast
  rw [norm_pow, hr]

/-- The `p`-th root `ε₁ = ε^{1/p}` in the tilt. -/
abbrev epsOne (ε : PreTilt 𝓞_ℂ_[p] p) : PreTilt 𝓞_ℂ_[p] p :=
  (frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε

theorem epsOne_pow (ε : PreTilt 𝓞_ℂ_[p] p) : epsOne ε ^ p = ε :=
  frobeniusEquiv_symm_pow_p (PreTilt 𝓞_ℂ_[p] p) p ε

theorem untilt_epsOne (ε : PreTilt 𝓞_ℂ_[p] p) : PreTilt.untilt (epsOne ε) = root ε 1 := rfl

theorem ne_one_of_root {ε : PreTilt 𝓞_ℂ_[p] p} (h2 : root ε 1 ≠ 1) : ε ≠ 1 := by
  rintro rfl
  apply h2
  simp [root]

/-- `η₀^p = (ε − 1)^{p−1}` for `η₀ = Σ_{j<p} ε₁^j`. -/
theorem eta0_pow {ε : PreTilt 𝓞_ℂ_[p] p} (h2 : root ε 1 ≠ 1) :
    (∑ j ∈ Finset.range p, epsOne ε ^ j) ^ p = (ε - 1) ^ (p - 1) := by
  have hne : ε - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_root h2)
  have e1 : (∑ j ∈ Finset.range p, epsOne ε ^ j) * (epsOne ε - 1) = ε - 1 := by
    rw [geom_sum_mul, epsOne_pow]
  have e2 : (epsOne ε - 1) ^ p = ε - 1 := by
    rw [sub_pow_char, epsOne_pow, one_pow]
  have e3 : (∑ j ∈ Finset.range p, epsOne ε ^ j) ^ p * (ε - 1) = (ε - 1) ^ (p - 1) * (ε - 1) := by
    rw [← e2, ← mul_pow, e1, e2, ← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le]
  exact mul_right_cancel₀ hne e3

theorem norm_untilt_eta0 {ε : PreTilt 𝓞_ℂ_[p] p} (h1 : PreTilt.untilt ε = 1)
    (h2 : root ε 1 ≠ 1) :
    ‖((PreTilt.untilt (∑ j ∈ Finset.range p, epsOne ε ^ j) : 𝓞_ℂ_[p]) : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have hζ : IsPrimitiveRoot ((root ε 2 : 𝓞_ℂ_[p]) : ℂ_[p]) (p ^ 2) :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mpr (isPrimitiveRoot_root_two h1 h2)
  have h := congrArg (fun z => ‖((PreTilt.untilt z : 𝓞_ℂ_[p]) : ℂ_[p])‖) (eta0_pow h2)
  simp only [map_pow] at h
  push_cast at h
  rw [norm_pow, norm_pow, norm_untilt_sub_one h1 h2, ← pow_mul,
    show p ^ 2 * (p - 1) = p * (p - 1) * p by ring, pow_mul, norm_sub_one_pow p hζ] at h
  have hp0 : p ≠ 0 := hp.out.ne_zero
  rwa [pow_left_inj₀ (norm_nonneg _) (by positivity) hp0] at h

theorem constantCoeff_xi : WittVector.constantCoeff (xi p) = -(pFlat p) := by
  rw [xi, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
  simp

theorem coeff_zero_xi : (xi p).coeff 0 = -(pFlat p) := by
  rw [← WittVector.constantCoeff_apply, constantCoeff_xi]

/-- `η = Σ_{j<p} [ε₁]^j ∉ (ξ²)`. -/
theorem eta_not_mem {ε : PreTilt 𝓞_ℂ_[p] p} (h1 : PreTilt.untilt ε = 1) (h2 : root ε 1 ≠ 1) :
    ∑ j ∈ Finset.range p, WittVector.teichmuller p (epsOne ε) ^ j ∉ span {xi p ^ 2} := by
  intro hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have h0 := congrArg WittVector.constantCoeff hc
  simp only [map_mul, map_pow, map_sum, WittVector.constantCoeff_apply,
    WittVector.teichmuller_coeff_zero, coeff_zero_xi, neg_sq] at h0
  have h3 := congrArg (fun z => ‖((PreTilt.untilt z : 𝓞_ℂ_[p]) : ℂ_[p])‖) h0
  simp only [map_mul, map_pow] at h3
  rw [norm_untilt_eta0 h1 h2] at h3
  push_cast at h3
  rw [norm_mul, norm_pow, untilt_pFlat] at h3
  have hc1 := norm_le_one p (PreTilt.untilt (c.coeff 0))
  push_cast at h3
  rw [PkgI4.Cp.norm_p] at h3
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hpinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  nlinarith [norm_nonneg ((PreTilt.untilt (c.coeff 0) : 𝓞_ℂ_[p]) : ℂ_[p])]

/-- **`[ε] − 1 ∉ (ξ²)`** in `W(𝓞_ℂ_p♭)`, for `ε♯ = 1`, `ε^{(1)} ≠ 1`. -/
theorem teich_sub_one_not_mem_span_xi_sq {ε : PreTilt 𝓞_ℂ_[p] p} (h1 : PreTilt.untilt ε = 1)
    (h2 : root ε 1 ≠ 1) : WittVector.teichmuller p ε - 1 ∉ span {xi p ^ 2} := by
  set t₁ := WittVector.teichmuller p (epsOne ε)
  set η := ∑ j ∈ Finset.range p, t₁ ^ j
  have hfac : WittVector.teichmuller p ε - 1 = η * (t₁ - 1) := by
    rw [geom_sum_mul, ← map_pow, epsOne_pow]
  have hθt : WittVector.fontaineTheta 𝓞_ℂ_[p] p t₁ = root ε 1 := by
    rw [WittVector.fontaineTheta_teichmuller, untilt_epsOne]
  have hθη : WittVector.fontaineTheta 𝓞_ℂ_[p] p η = 0 := by
    simp only [η, map_sum, map_pow, hθt]
    exact (isPrimitiveRoot_root_one h1 h2).geom_sum_eq_zero hp.out.one_lt
  have hη : η ∈ span {xi p} := by
    rw [← ker_fontaineTheta_Cp]; exact hθη
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hη
  have hθw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w ≠ 0 := by
    intro h0
    have : w ∈ span {xi p} := by rw [← ker_fontaineTheta_Cp]; exact h0
    obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.mp this
    apply eta_not_mem h1 h2
    exact Ideal.mem_span_singleton'.mpr ⟨w', by
      show w' * xi p ^ 2 = η
      rw [← hw, ← hw']; ring⟩
  intro hmem
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem
  have e : xi p * (w * (t₁ - 1)) = xi p * (d * xi p) := by
    rw [← mul_assoc, mul_comm (xi p) w, hw, ← hfac, ← hd]; ring
  have e2 := mul_left_cancel₀ (xi_ne_zero p) e
  have e3 := congrArg (WittVector.fontaineTheta 𝓞_ℂ_[p] p) e2
  rw [map_mul, map_mul, map_sub, map_one, hθt] at e3
  have hxi0 : WittVector.fontaineTheta 𝓞_ℂ_[p] p (xi p) = 0 := by
    have : xi p ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := by
      rw [ker_fontaineTheta_Cp]; exact Ideal.mem_span_singleton_self _
    exact this
  rw [hxi0, mul_zero] at e3
  exact mul_ne_zero hθw (sub_ne_zero.mpr h2) e3

/-- **A uniformizer criterion in `B_dR^+`.** If `t ≠ 0` reduces modulo `(ker θ)²` to `y + y² r`
with `y ∈ ker θ ∖ (ker θ)²`, then `t` is irreducible (a uniformizer of the DVR `B_dR^+`). -/
theorem irreducible_of_evalTwo (t : BDeRhamPlus 𝓞_ℂ_[p] p) (ht : t ≠ 0)
    (y r : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)))
    (hy : y ∈ RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p))
    (hy2 : y ∉ RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p) ^ 2)
    (heval : AdicCompletion.evalₐ (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)) 2 t =
      Ideal.Quotient.mk _ (y + y ^ 2 * r)) : Irreducible t := by
  haveI := isDiscreteValuationRing_BDeRhamPlus p
  let φ : BDeRhamPlus 𝓞_ℂ_[p] p →+* Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)) ⧸
      RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p) ^ 2 :=
    (AdicCompletion.evalₐ (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)) 2).toRingHom
  have hφ : φ t = Ideal.Quotient.mk _ (y + y ^ 2 * r) := heval
  have hϖ : Irreducible (BdrKer.ofPlus 𝓞_ℂ_[p] p (xi' p)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr (maximalIdeal_BDeRhamPlus p)
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hϖ
  have hxi : xi' p ∈ RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p) := by
    rw [ker_fontaineThetaInvertP_Cp]; exact Ideal.mem_span_singleton_self _
  have hevxi : φ (BdrKer.ofPlus 𝓞_ℂ_[p] p (xi' p)) =
      Ideal.Quotient.mk _ (xi' p) :=
    AdicCompletion.evalₐ_of (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)) 2 _
  have hsq : Ideal.Quotient.mk (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p) ^ 2) (xi' p) ^ 2 =
      0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hxi 2
  have hy2r : y ^ 2 * r ∈ RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p) ^ 2 :=
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hy 2)
  rcases n with _ | _ | n
  · -- `t` a unit: its image is a unit with square `0`
    exfalso
    rw [pow_zero, mul_one] at hv
    have hu : IsUnit (φ t) := by
      rw [hv]; exact (v.isUnit).map φ
    have hz : (φ t) ^ 2 = 0 := by
      rw [hφ, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      have : (y + y ^ 2 * r) ^ 2 = y ^ 2 * (1 + y * r) ^ 2 := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hy 2)
    have h01 := isUnit_zero_iff.mp (hz ▸ hu.pow 2)
    have h1 : (1 : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) ∈
        RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p) ^ 2 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_one, ← h01]
    exact (ker_fontaineThetaInvertP_isMaximal p).ne_top
      ((Ideal.eq_top_iff_one _).mpr (Ideal.pow_le_self two_ne_zero h1))
  · rw [zero_add, pow_one] at hv
    rw [hv]
    exact (irreducible_units_mul v).mpr hϖ
  · exfalso
    have h0 : φ t = 0 := by
      rw [hv, map_mul, map_pow, hevxi, pow_eq_zero_of_le (by omega) hsq, mul_zero]
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem] at h0
    apply hy2
    have := Ideal.sub_mem _ h0 hy2r
    rwa [add_sub_cancel_right] at this

end

end DeRhamHTMult
