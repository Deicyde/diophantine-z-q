import ZInQKernel.Contrib.OneProof.WeberField
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Descent

/-! ON THE SPOT (c): the Weber coordinate under a diamond is computed by the
division polynomials of a multiple of the marked point. -/

noncomputable section

namespace BShStandard

open scoped MatrixGroups Pointwise
open UpperHalfPlane T5Glue X1Igusa X1Igusa.Weber WeierstrassCurve LeafModCurves Matrix

private def factor (g : SL(2, ℤ)) (τ : ℍ) : ℂ :=
  (g 1 0 : ℂ) * τ + (g 1 1 : ℂ)

private theorem factor_ne (g : SL(2, ℤ)) (τ : ℍ) : factor g τ ≠ 0 := by
  simpa [factor, UpperHalfPlane.denom, SpecialLinearGroup.mapGL] using
    UpperHalfPlane.denom_ne_zero (SpecialLinearGroup.mapGL ℝ g) τ

private theorem factor_mul (g : SL(2, ℤ)) (τ : ℍ) :
    factor g τ * (↑(g • τ) : ℂ) = (g 0 0 : ℂ) * τ + (g 0 1 : ℂ) := by
  rw [coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq, Int.coe_castRingHom, Complex.ofReal_intCast]
  change factor g τ * (_ / factor g τ) = _
  rw [mul_div_cancel₀ _ (factor_ne g τ)]

private theorem scale_diamond (g : SL(2, ℤ)) (τ : ℍ) :
    IsScale (pp τ) (pp (g • τ)) (factor g τ) := by
  refine ⟨factor_ne g τ, ?_⟩
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hdC : (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) = 1 := by
    exact_mod_cast hd
  ext z
  simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_smul_set, smul_eq_mul, pp]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨_, ⟨m * g 0 0 - n * g 0 1, n * g 1 1 - m * g 1 0, rfl⟩, ?_⟩
    simp only [Int.cast_sub, Int.cast_mul, mul_one, mul_add]
    rw [show factor g τ * (((n : ℂ) * (g 1 1 : ℂ) - (m : ℂ) * (g 1 0 : ℂ)) * (↑(g • τ) : ℂ)) =
      ((n : ℂ) * (g 1 1 : ℂ) - (m : ℂ) * (g 1 0 : ℂ)) *
        (factor g τ * (↑(g • τ) : ℂ)) by ring, factor_mul]
    unfold factor
    linear_combination ((m : ℂ) + (n : ℂ) * τ) * hdC
  · rintro ⟨_, ⟨m, n, rfl⟩, rfl⟩
    refine ⟨m * g 1 1 + n * g 0 1, m * g 1 0 + n * g 0 0, ?_⟩
    simp only [Int.cast_add, Int.cast_mul, mul_one, mul_add]
    rw [show factor g τ * ((n : ℂ) * (↑(g • τ) : ℂ)) =
      (n : ℂ) * (factor g τ * (↑(g • τ) : ℂ)) by ring, factor_mul]
    unfold factor
    ring

/-- The lattice homothety preserves the first coordinate. -/
theorem j_diamond (g : SL(2, ℤ)) (τ : ℍ) :
    jL (pp (g • τ)) = jL (pp τ) :=
  (scale_diamond g τ).jL.symm

private theorem weber_diamond_z {N : ℕ} (g : SL(2, ℤ)) (h : (N : ℤ) ∣ g 1 0)
    (τ : ℍ) :
    weber (pp (g • τ)) (1 / (N : ℂ)) =
      weber (pp τ) ((g 1 1 : ℂ) * (1 / (N : ℂ))) := by
  obtain ⟨m, hm⟩ := h
  by_cases hN : N = 0
  · simpa only [hN, Nat.cast_zero, div_zero, mul_zero] using ((scale_diamond g τ).weber 0).symm
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have he : (g 1 0 : ℂ) = (N : ℂ) * (m : ℂ) := by exact_mod_cast hm
  have he' : factor g τ * (1 / (N : ℂ)) =
      (g 1 1 : ℂ) * (1 / (N : ℂ)) + (m : ℂ) * τ := by
    unfold factor
    rw [he]
    field_simp
    ring
  rw [← (scale_diamond g τ).weber, he', weber_add_mem]
  simpa [pp, zsmul_eq_mul] using (pp τ).lattice.smul_mem m (PeriodPair.ω₂_mem_lattice (pp τ))

/-- The generic Weber coordinate after a diamond is the Weber value at the chosen
integer representative of the residue, even at the exceptional Weber parameters. -/
theorem weber_diamond {N : ℕ} (g : SL(2, ℤ)) (h : (N : ℤ) ∣ g 1 0)
    {d : ℤ} (hd : (g 1 1 : ZMod N) = (d : ZMod N)) (τ : ℍ) :
    weber (pp (g • τ)) (1 / (N : ℂ)) =
      weber (pp τ) ((d : ℂ) * (1 / (N : ℂ))) := by
  rw [weber_diamond_z g h]
  have hdiv : (N : ℤ) ∣ g 1 1 - d := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub, hd, sub_self]
  obtain ⟨m, hm⟩ := hdiv
  by_cases hN : N = 0
  · simp [hN]
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have he : (g 1 1 : ℂ) - (d : ℂ) = (N : ℂ) * (m : ℂ) := by exact_mod_cast hm
  rw [show (g 1 1 : ℂ) * (1 / (N : ℂ)) = (d : ℂ) * (1 / (N : ℂ)) + m by
    field_simp
    linear_combination he, weber_add_mem]
  simpa [pp, zsmul_eq_mul] using (pp τ).lattice.smul_mem m (PeriodPair.ω₁_mem_lattice (pp τ))

/-- Homothety also preserves the two nonvanishing tests for the generic branch. -/
theorem diamond_good (g : SL(2, ℤ)) (τ : ℍ) :
    ((pp (g • τ)).g₂ ≠ 0 ∧ (pp (g • τ)).g₃ ≠ 0) ↔
      ((pp τ).g₂ ≠ 0 ∧ (pp τ).g₃ ≠ 0) := by
  rw [(scale_diamond g τ).g₂, (scale_diamond g τ).g₃]
  simp [factor_ne]

/-- The two polynomial evaluations for multiplication by an integer, at the
normalized Weierstrass point corresponding to the Weber coordinate. -/
theorem diamond_division {N : ℕ} (hN : 2 ≤ N) (g : SL(2, ℤ))
    (hg : (N : ℤ) ∣ g 1 0) {d : ℤ} (hd : (g 1 1 : ZMod N) = (d : ZMod N))
    (τ : ℍ) (h2 : (pp τ).g₂ ≠ 0) (h3 : (pp τ).g₃ ≠ 0) :
    let L := pp τ
    let E := curveG (L.g₂ ^ 3 / L.g₃ ^ 2)
    let x := L.g₂ / L.g₃ * L.weierstrassP (1 / (N : ℂ))
    let x' := L.g₂ / L.g₃ * L.weierstrassP ((d : ℂ) * (1 / (N : ℂ)))
    (E.ΨSq d).eval x ≠ 0 ∧ x' * (E.ΨSq d).eval x = (E.Φ d).eval x := by
  dsimp only
  let L := pp τ
  let E := curveG (L.g₂ ^ 3 / L.g₃ ^ 2)
  let z : ℂ := 1 / (N : ℂ)
  let hΔ := discNeZero_pp τ
  have hz (σ : ℍ) : z ∉ (pp σ).lattice := by
    have hh := div_nat_not_mem σ (a := 1) (N := N) one_pos (by omega)
    simpa [z] using hh
  have hdz : (d : ℂ) * z ∉ L.lattice := by
    obtain ⟨m, hm⟩ := hg
    have hh : (N : ℤ) ∣ g 1 1 - d := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      rw [Int.cast_sub, hd, sub_self]
    obtain ⟨n, hn⟩ := hh
    have hn0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hmC : (g 1 0 : ℂ) = (N : ℂ) * (m : ℂ) := by exact_mod_cast hm
    have hnC : (g 1 1 : ℂ) - (d : ℂ) = (N : ℂ) * (n : ℂ) := by exact_mod_cast hn
    have he : factor g τ * z = (d : ℂ) * z + ((m : ℂ) * τ + (n : ℂ)) := by
      unfold factor z
      rw [hmC]
      field_simp
      linear_combination hnC
    have hl : (m : ℂ) * τ + (n : ℂ) ∈ L.lattice :=
      L.lattice.add_mem
        (by simpa [L, pp, zsmul_eq_mul] using L.lattice.smul_mem m (PeriodPair.ω₂_mem_lattice L))
        (by simpa [L, pp, zsmul_eq_mul] using L.lattice.smul_mem n (PeriodPair.ω₁_mem_lattice L))
    intro h
    have h' := L.lattice.add_mem h hl
    rw [← he, (scale_diamond g τ).mem_iff, inv_mul_cancel_left₀ (factor_ne g τ)] at h'
    exact hz _ h'
  obtain ⟨u, hu₂⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ / L.g₃) two_pos
  have hu : u ≠ 0 := by
    rintro rfl
    exact div_ne_zero h2 h3 (by simpa using hu₂.symm)
  obtain ⟨e, he⟩ := exists_addEquiv_xCoord L.weierstrassCurve E _
    (curveC_smul L h2 h3 u hu₂ hu)
  let toPt : ℂ →+ L.weierstrassCurve.toAffine.Point :=
    { toFun := L.toPoint hΔ
      map_zero' := L.toPoint_zero hΔ
      map_add' := (L.isUniformization_toPoint hΔ).1 }
  have hx (w : ℂ) (hw : w ∉ L.lattice) :
      ∃ x y, ∃ hns : E.toAffine.Nonsingular x y,
        e (toPt w) = Affine.Point.some x y hns ∧
          x = L.g₂ / L.g₃ * L.weierstrassP w := by
    have hn : toPt w ≠ 0 := fun h => hw ((toPoint_eq_zero_iff L hΔ w).mp h)
    have hc := he (toPt w) hn
    have hc' : xCoord (toPt w) = L.weierstrassP w := by
      change xCoord (L.toPoint hΔ w) = _
      rw [L.toPoint_of_notMem hΔ hw]
      rfl
    rw [hc'] at hc
    cases h : e (toPt w) with
    | zero => exact (hn (e.map_eq_zero_iff.mp h)).elim
    | some x y hns =>
      refine ⟨x, y, hns, rfl, ?_⟩
      rw [h] at hc
      change x = u ^ 2 * L.weierstrassP w + 0 at hc
      rw [add_zero, hu₂] at hc
      exact hc
  obtain ⟨x, y, hns, h, hx₀⟩ := hx z (hz τ)
  obtain ⟨x', y', hns', h', hx₁⟩ := hx ((d : ℂ) * z) hdz
  have hmul : d • Affine.Point.some x y hns = Affine.Point.some x' y' hns' := by
    rw [← h, ← h', ← map_zsmul, ← map_zsmul]
    congr 2
    simp [zsmul_eq_mul]
  rw [← hx₀, ← hx₁]
  refine ⟨?_, E.mul_eval_ΨSq_eq_eval_Φ_of_zsmul hns hns' hmul⟩
  rw [ne_eq, eval_ΨSq_eq_zero_iff_zsmul_eq_zero _ hns,
    zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero, hmul]
  exact Affine.Point.some_ne_zero hns'

open Polynomial in
private theorem clears_at {P U : Polynomial (Polynomial ℚ)} {k N : ℕ}
    (h : Clears P U k) (τ : ℍ) (h3 : (pp τ).g₃ ≠ 0) :
    ez N τ U = (jL (pp τ) - 1728) ^ k *
      X1Igusa.Weber.ev2 ((pp τ).g₂ ^ 3 / (pp τ).g₃ ^ 2)
        ((pp τ).g₂ / (pp τ).g₃ * (pp τ).weierstrassP (1 / (N : ℂ))) P := by
  have h₃ : G3f τ ≠ 0 := by simpa [G3f, ofComplex_apply] using h3
  have hD := Dlf_ne (τ : ℂ)
  have hne : ez N τ DJ ≠ 0 := by
    rw [ez_DJ, Jf_sub]; exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 h₃)) hD
  have e1 : 27 * ez N τ (C X) / ez N τ DJ = G2f τ ^ 3 / G3f τ ^ 2 := by
    rw [ez_DJ, Jf_sub, show ez N τ (C X) = Jf τ by simp [ez], Jf_eq]
    field_simp
    ring
  have e2 : 46656 * ez N τ X / ez N τ DJ = G2f τ / G3f τ * Pf N τ := by
    rw [ez_DJ, Jf_sub, show ez N τ X = Wf N τ by simp [ez], Wf]
    field_simp
  rw [h ℂ (ez N τ) hne, e1, e2, ez_DJ]
  simp only [Jf, G2f, G3f, Pf, ofComplex_apply]

open Polynomial in
private theorem eval_phi (a b : ℂ) (d : ℤ) :
    X1Igusa.Weber.ev2 a b (WG.Φ d) = ((curveG a).Φ d).eval b := by
  rw [← WG_map, map_Φ, Polynomial.eval_map]
  rfl

open Polynomial in
/-- At every generic parameter the diamond Weber coordinate is the same rational
function of the source's two coordinates; the denominator is nonzero there. -/
theorem diamond_fraction (d : ℤ) :
    ∃ A B : Polynomial (Polynomial ℚ),
      ∀ {N : ℕ}, 2 ≤ N → ∀ (g : SL(2, ℤ)), (N : ℤ) ∣ g 1 0 →
        (g 1 1 : ZMod N) = (d : ZMod N) → ∀ τ : ℍ,
        (pp τ).g₂ ≠ 0 → (pp τ).g₃ ≠ 0 →
        ez N τ B ≠ 0 ∧
          weber (pp (g • τ)) (1 / (N : ℂ)) = ez N τ A / ez N τ B := by
  obtain ⟨U, k, hk⟩ := exists_clears (WG.Φ d)
  obtain ⟨V, l, hl⟩ := exists_clears (WG.ΨSq d)
  refine ⟨U * DJ ^ (l + 1), C (C 46656) * V * DJ ^ k,
    fun {N} hN g hg hd τ h2 h3 => ?_⟩
  let L := pp τ
  let D := jL L - 1728
  have hD : D = 46656 * L.g₃ ^ 2 / discL L := by
    simpa [D, L, Jf, G3f, Dlf, ofComplex_apply] using (Jf_sub (z := (τ : ℂ)))
  have hdisc : discL L ≠ 0 := by
    simpa [L, Dlf, ofComplex_apply] using Dlf_ne (τ : ℂ)
  have hD₀ : D ≠ 0 := by rw [hD]; exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 h3)) hdisc
  have hDj : ez N τ DJ = D := by
    rw [ez_DJ]
    simp only [D, L, Jf, ofComplex_apply]
  let E := curveG (L.g₂ ^ 3 / L.g₃ ^ 2)
  let x := L.g₂ / L.g₃ * L.weierstrassP (1 / (N : ℂ))
  let x' := L.g₂ / L.g₃ * L.weierstrassP ((d : ℂ) * (1 / (N : ℂ)))
  let S := (E.ΨSq d).eval x
  have hu := clears_at (N := N) hk τ h3
  have hv := clears_at (N := N) hl τ h3
  rw [eval_phi] at hu
  rw [ev2_ΨSq] at hv
  change ez N τ U = D ^ k * (E.Φ d).eval x at hu
  change ez N τ V = D ^ l * S at hv
  obtain ⟨hn, he⟩ := diamond_division hN g hg hd τ h2 h3
  change S ≠ 0 at hn
  change x' * S = (E.Φ d).eval x at he
  have h46 : ez N τ (C (C 46656)) = (46656 : ℂ) := by simp [ez]
  simp only [map_mul, map_pow, hDj, hu, hv, h46]
  have hB : (46656 : ℂ) * (D ^ l * S) * D ^ k ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero _ hD₀) hn)) (pow_ne_zero _ hD₀)
  refine ⟨hB, (eq_div_iff hB).mpr ?_⟩
  have hw : weber (pp (g • τ)) (1 / (N : ℂ)) = D / 46656 * x' := by
    rw [weber_diamond g hg hd, weber, if_neg h3, if_neg h2, hD]
    change L.g₂ * L.g₃ / discL L * _ = _
    dsimp only [x']
    field_simp [h3, hdisc]
    ring
  rw [hw, ← he, pow_succ]
  ring

#print axioms factor_ne
#print axioms factor_mul
#print axioms scale_diamond
#print axioms j_diamond
#print axioms weber_diamond_z
#print axioms weber_diamond
#print axioms diamond_good
#print axioms diamond_division
#print axioms clears_at
#print axioms eval_phi
#print axioms diamond_fraction

end BShStandard
