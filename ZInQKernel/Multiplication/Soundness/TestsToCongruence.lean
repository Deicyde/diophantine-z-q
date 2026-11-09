import ZInQKernel.Multiplication.Local
import ZInQKernel.Multiplication.Certificate
import ZInQKernel.Multiplication.Soundness.CommonGroup

/-!
# From the local tests to the congruence

Blueprint: `multiplication/soundness/tests-to-congruence.md`.

The twelve test values `τ(h, z; c, cn₁, cn₂, cn₃)` (the certificate's `testValues`) are
`ρ([h]P₀)`, `ρ([zᵢ]P₀)`, `σρ([h - c]P₀)`, `σρ([zᵢ - c nᵢ]P₀)`, `Aᵢ - σBᵢ` and `A₁A₂ - A₃`,
where `ρ = invX`, `Aᵢ = Λ([zᵢ]P₀)/Λ([h]P₀)` and `Bᵢ = Λ([zᵢ - c nᵢ]P₀)/Λ([h - c]P₀)`
(`Λ = Lam`). If at a prime `π ∣ p`, `p > 324`, `p ∤ c`, the first eight have valuation at least
`1` and the last four at least `25`, then `p²⁵ ∣ n₁n₂ - n₃` (`tests_to_congruence`). The proof
is `tests_to_congruence_aux`, on the individual quantities (indices `i ∈ Fin 3`).
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

/-- `Λ([m]P₀) = L(z([m]P₀))`. -/
noncomputable def logAt (m : ℤ) : K0 := Lam (m • genP0)

/-- The ratio `Λ([u]P₀) / Λ([h]P₀)`. -/
noncomputable def ratioAt (u h : ℤ) : K0 := logAt u / logAt h

/-- `ρ([m]P₀) = 1/x([m]P₀)` (`0` at `O`). -/
noncomputable def rhoAt (m : ℤ) : K0 := invX (m • genP0)

theorem map_truncLog {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (δ z : R) :
    f (truncLog δ z) = truncLog (f δ) (f z) := by
  simp [truncLog, map_sum, map_mul, map_pow, map_intCast]

@[simp] theorem logAt_zero : logAt 0 = 0 := by
  rw [logAt, zero_zsmul]; exact Lam_zero

section

variable {p : ℕ} [hp : Fact p.Prime]

/-- The image of a nonzero point of `E(K₀)` in `E(K_π)` is nonzero. -/
theorem mapE_ne_zero {π : Zs} (hπ : Prime π) {Q : genCurve.toAffine.Point} (hQ : Q ≠ 0) :
    mapE π hπ Q ≠ 0 := by
  rcases Q with _ | ⟨x, y, hxy⟩
  · exact absurd rfl hQ
  · exact Point.some_ne_zero _

/-- The image in `E(K_π)` of a point of the formal group `E₁` of `E(K₀)` at `π` lies in the
formal group `E₁(K_π)`. -/
theorem mapE_mem_W1_of_mem {π : Zs} (hπ : Prime π) {Q : genCurve.toAffine.Point}
    (hQ : Q ∈ W1 (vP π hπ) (-genD ^ 2)) :
    mapE π hπ Q ∈ W1 (vComp π hπ) (-genDAt π hπ ^ 2) := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact trivial
  · show vComp π hπ (algebraMap K0 _ x) < 0
    rw [vComp_algebraMap]; exact hQ

/-- If `v_π(ρ([m]P₀)) ≥ 1` then `[m]P₀` lies in the formal group `E₁` at `π`. -/
theorem zsmul_genP0_mem_W1_of_rhoAt {π : Zs} (hπ : Prime π) {m : ℤ}
    (hρ : Vge (vP π hπ) 1 (rhoAt m)) : m • genP0 ∈ W1 (vP π hπ) (-genD ^ 2) := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [zero_zsmul]; exact zero_mem_W1 _
  obtain ⟨x, y, h, hQ, hx0, -, -⟩ := log25_z_ne_zero hm
  rw [rhoAt, hQ] at hρ
  rw [hQ]
  show vP π hπ x < 0
  have h1 : Vge (vP π hπ) 1 x⁻¹ := hρ
  obtain ⟨n, hn⟩ := val_eq_coe hx0
  have := (vge_iff_of_eq (val_inv_coe hn)).mp h1
  rw [hn]; exact_mod_cast (by omega : n < 0)

theorem algebraMap_logAt {π : Zs} (hπ : Prime π) (m : ℤ) :
    algebraMap K0 ((primeSpec π hπ).adicCompletion K0) (logAt m) =
      truncLog (genDAt π hπ ^ 2) (zCoord (mapE π hπ (m • genP0))) := by
  unfold logAt Lam
  generalize m • genP0 = Q
  rcases Q with _ | ⟨x, y, h⟩
  · exact (by simp [truncLog] : algebraMap K0 ((primeSpec π hπ).adicCompletion K0)
      (truncLog (genD ^ 2) 0) = truncLog (genDAt π hπ ^ 2) 0)
  · rw [map_truncLog, map_pow]
    show truncLog _ (algebraMap K0 _ (-x / y)) = truncLog _ (-(algebraMap K0 _ x) / algebraMap K0 _ y)
    rw [map_div₀, map_neg]

/-- **Truncated ratios.** If `h ≠ 0` and `ρ([h]P₀)`, `ρ([u]P₀)` have valuation at least `1` at a
prime `π ∣ p`, `p > 324`, then `Λ([u]P₀)/Λ([h]P₀) = (u/h)(1 + δ)` with `v_π(δ) ≥ 28`. -/
theorem ratioAt_eq (hp324 : 324 < p) {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs)) {u h : ℤ}
    (hh : h ≠ 0) (hH : Vge (vP π hπ) 1 (rhoAt h)) (hU : Vge (vP π hπ) 1 (rhoAt u)) :
    ∃ δ : K0, Vge (vP π hπ) 28 δ ∧ ratioAt u h = (u : K0) / (h : K0) * (1 + δ) := by
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, Vge.zero _, by simp [ratioAt]⟩
  have hH1 := mapE_mem_W1_of_mem hπ (zsmul_genP0_mem_W1_of_rhoAt hπ hH)
  have hU1 := mapE_mem_W1_of_mem hπ (zsmul_genP0_mem_W1_of_rhoAt hπ hU)
  have hH0 := mapE_ne_zero hπ (zsmul_genP0_ne_zero hh)
  have hU0 := mapE_ne_zero hπ (zsmul_genP0_ne_zero hu)
  obtain ⟨-, -, εH, hεH, eH⟩ := log25_truncation_error hp324 hπ hπp _ hH1 hH0
  obtain ⟨-, -, εU, hεU, eU⟩ := log25_truncation_error hp324 hπ hπp _ hU1 hU0
  obtain ⟨hl0, hl⟩ := ellLog_ratio (p := p) (by omega) hπ hπp hh hH1 hU1
  replace hεH : Vge (vComp π hπ) 28 εH := by unfold Vge; exact_mod_cast hεH
  replace hεU : Vge (vComp π hπ) 28 εU := by unfold Vge; exact_mod_cast hεU
  have hεH1 : Vge (vComp π hπ) 1 εH := Vge.mono hεH (by norm_num)
  have h1εH : 1 + εH ≠ 0 := Mult.one_add_ne_zero hεH1
  have hcast : ∀ n : ℤ, algebraMap K0 ((primeSpec π hπ).adicCompletion K0) (n : K0) =
      (n : (primeSpec π hπ).adicCompletion K0) := fun n => map_intCast _ n
  have hhK : (h : (primeSpec π hπ).adicCompletion K0) ≠ 0 := Int.cast_ne_zero.mpr hh
  have huK : (u : (primeSpec π hπ).adicCompletion K0) ≠ 0 := Int.cast_ne_zero.mpr hu
  have hγ : (u : K0) / (h : K0) ≠ 0 :=
    div_ne_zero (Int.cast_ne_zero.mpr hu) (Int.cast_ne_zero.mpr hh)
  refine ⟨ratioAt u h / ((u : K0) / (h : K0)) - 1, ?_, by field_simp; ring⟩
  -- the image of `δ` is `(ε_U - ε_H) / (1 + ε_H)`
  have himg : algebraMap K0 ((primeSpec π hπ).adicCompletion K0) (ratioAt u h / ((u : K0) / (h : K0)) - 1) =
      (εU - εH) / (1 + εH) := by
    rw [map_sub, map_div₀, map_div₀, map_one, ratioAt, map_div₀, algebraMap_logAt,
      algebraMap_logAt, eU, eH, hl, hcast, hcast]
    field_simp
    ring
  have hv : Vge (vComp π hπ) 28 ((εU - εH) / (1 + εH)) :=
    (Vge.sub hεU hεH).div_unit (val_one_add hεH1)
  rw [← himg] at hv
  change ((28 : ℤ) : WithTop ℤ) ≤ _ at hv
  rwa [vComp_algebraMap] at hv

/-- If `X = γ (1 + δ)` with `v(δ) ≥ 28` and `v(X) ≥ 0`, then `v(γ) ≥ 0` and `v(X - γ) ≥ 28`. -/
theorem integral_of_rel {v : AddValuation K0 (WithTop ℤ)} {X γ δ : K0} (hδ : Vge v 28 δ)
    (hX : X = γ * (1 + δ)) (h0 : Vge v 0 X) : Vge v 0 γ ∧ Vge v 28 (X - γ) := by
  have h1 : v (1 + δ) = 0 := val_one_add (hδ.mono (by norm_num))
  have hγ : Vge v 0 γ := by
    have : v X = v γ := by rw [hX, v.map_mul, h1, add_zero]
    unfold Vge at h0 ⊢; rwa [← this]
  refine ⟨hγ, ?_⟩
  have : X - γ = γ * δ := by rw [hX]; ring
  rw [this]; simpa using hγ.mul hδ

theorem rel_close {v : AddValuation K0 (WithTop ℤ)} {X γ δ : K0} (hδ : Vge v 28 δ)
    (hX : X = γ * (1 + δ)) (hγ : Vge v 0 γ) : Vge v 28 (X - γ) := by
  have : X - γ = γ * δ := by rw [hX]; ring
  rw [this]; simpa using hγ.mul hδ

theorem vP_intCast_eq_zero (hp2 : p ≠ 2) {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs)) {n : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) : vP π hπ (n : K0) = 0 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  rw [vP_apply hπ (Int.cast_ne_zero.mpr hn0), vp_intCast hp2 hπ hπp hn0,
    padicValInt.eq_zero_of_not_dvd hn]
  rfl

/-- From the individual test quantities to the congruence. -/
theorem tests_to_congruence_aux (hp324 : 324 < p) {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs))
    {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) (n z : Fin 3 → ℤ) {h : ℤ} (hh : h ≠ 0) (hhc : h ≠ c)
    (t₁ : Vge (vP π hπ) 1 (rhoAt h)) (t₂ : ∀ i, Vge (vP π hπ) 1 (rhoAt (z i)))
    (t₅ : Vge (vP π hπ) 1 (star (rhoAt (h - c))))
    (t₆ : ∀ i, Vge (vP π hπ) 1 (star (rhoAt (z i - c * n i))))
    (t₉ : ∀ i, Vge (vP π hπ) 25 (ratioAt (z i) h - star (ratioAt (z i - c * n i) (h - c))))
    (t₁₂ : Vge (vP π hπ) 25 (ratioAt (z 0) h * ratioAt (z 1) h - ratioAt (z 2) h)) :
    (p : ℤ) ^ 25 ∣ n 0 * n 1 - n 2 := by
  have hp2 : p ≠ 2 := by omega
  set v := vP π hπ with hv
  have hσ := prime_star hπ
  have hσp := star_dvd_natCast hπp
  have hhc0 : h - c ≠ 0 := sub_ne_zero.mpr hhc
  have hcv : v (c : K0) = 0 := vP_intCast_eq_zero hp2 hπ hπp hc
  -- the conjugate tests are tests at `σπ`
  have t₅' : Vge (vP (star π) hσ) 1 (rhoAt (h - c)) := by unfold Vge; rw [vP_star]; exact t₅
  have t₆' : ∀ i, Vge (vP (star π) hσ) 1 (rhoAt (z i - c * n i)) := fun i => by
    unfold Vge; rw [vP_star]; exact t₆ i
  -- for each `i`: `v(nᵢ - Aᵢ) ≥ 25`
  have key : ∀ i, Vge v 25 ((n i : K0) - ratioAt (z i) h) := by
    intro i
    have hdiff := t₉ i
    obtain ⟨δ, hδ, hA⟩ := ratioAt_eq hp324 hπ hπp hh t₁ (t₂ i)
    obtain ⟨δ', hδ', hB⟩ := ratioAt_eq hp324 hσ hσp hhc0 t₅' (t₆' i)
    set A := ratioAt (z i) h
    set α : K0 := (z i : K0) / (h : K0)
    set β : K0 := ((z i - c * n i : ℤ) : K0) / ((h - c : ℤ) : K0)
    -- conjugating the second relation
    have hσB : star (ratioAt (z i - c * n i) (h - c)) = β * (1 + star δ') := by
      rw [hB, star_mul', star_add, star_one]
      congr 1
      simp only [β, star_div₀, star_intCast]
    have hδσ : Vge v 28 (star δ') := by
      unfold Vge; rw [hv, ← vP_star]; exact hδ'
    set σB := star (ratioAt (z i - c * n i) (h - c))
    -- integrality of both ratios
    have hboth : Vge v 28 (A - α) ∧ Vge v 28 (σB - β) := by
      by_cases hph : (p : ℤ) ∣ h
      · have hphc : ¬ (p : ℤ) ∣ (h - c) := by
          intro h2; apply hc; have := dvd_sub hph h2; simpa using this
        have hβ : Vge v 0 β := (Mult.vge_intCast _).div_unit (vP_intCast_eq_zero hp2 hπ hπp hphc)
        have hB2 := rel_close hδσ hσB hβ
        have hσB0 : Vge v 0 σB := by
          have := (hB2.mono (by norm_num : (0 : ℤ) ≤ 28)).add hβ; simpa using this
        have hA0 : Vge v 0 A := by
          have := (hdiff.mono (by norm_num : (0 : ℤ) ≤ 25)).add hσB0; simpa using this
        exact ⟨(integral_of_rel hδ hA hA0).2, hB2⟩
      · have hα : Vge v 0 α := (Mult.vge_intCast _).div_unit (vP_intCast_eq_zero hp2 hπ hπp hph)
        have hA2 := rel_close hδ hA hα
        have hA0 : Vge v 0 A := by
          have := (hA2.mono (by norm_num : (0 : ℤ) ≤ 28)).add hα; simpa using this
        have hσB0 : Vge v 0 σB := by
          have := hA0.sub (hdiff.mono (by norm_num : (0 : ℤ) ≤ 25)); simpa using this
        exact ⟨hA2, (integral_of_rel hδσ hσB hσB0).2⟩
    obtain ⟨hA2, hB2⟩ := hboth
    have hAβ : Vge v 25 (A - β) := by
      have := hdiff.add (hB2.mono (by norm_num)); simpa using this
    -- `zᵢ - h Aᵢ = -h (Aᵢ - αᵢ)` and `zᵢ - c nᵢ - (h - c) Aᵢ = -(h - c)(Aᵢ - βᵢ)`
    have hhK : (h : K0) ≠ 0 := Int.cast_ne_zero.mpr hh
    have hhcK : ((h - c : ℤ) : K0) ≠ 0 := Int.cast_ne_zero.mpr hhc0
    have e1 : (z i : K0) - h * A = -(h : K0) * (A - α) := by
      simp only [α]; field_simp; ring
    have e2 : ((z i - c * n i : ℤ) : K0) - ((h - c : ℤ) : K0) * A =
        -((h - c : ℤ) : K0) * (A - β) := by
      simp only [β]; field_simp; ring
    have v1 : Vge v 25 ((z i : K0) - h * A) := by
      rw [e1]; simpa using ((Mult.vge_intCast h).neg.mul hA2).mono (by norm_num)
    have v2 : Vge v 25 (((z i - c * n i : ℤ) : K0) - ((h - c : ℤ) : K0) * A) := by
      rw [e2]; simpa using (Mult.vge_intCast (h - c)).neg.mul hAβ
    have e3 : (c : K0) * ((n i : K0) - A) =
        ((z i : K0) - h * A) - (((z i - c * n i : ℤ) : K0) - ((h - c : ℤ) : K0) * A) := by
      push_cast; ring
    have v3 : Vge v 25 ((c : K0) * ((n i : K0) - A)) := by rw [e3]; exact v1.sub v2
    have hc0 : (c : K0) ≠ 0 := by
      intro h0; rw [h0, v.map_zero] at hcv; exact WithTop.top_ne_coe hcv
    have := v3.div_unit hcv
    rwa [mul_div_cancel_left₀ _ hc0] at this
  -- the product test
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  set A₀ := ratioAt (z 0) h
  set A₁ := ratioAt (z 1) h
  set A₂ := ratioAt (z 2) h
  have hA₀ : Vge v 0 A₀ := by
    have := (Mult.vge_intCast (v := v) (n 0)).sub (k0.mono (by norm_num)); simpa using this
  have ef : ((n 0 * n 1 - n 2 : ℤ) : K0) = ((n 0 : K0) - A₀) * (n 1 : K0) + A₀ * ((n 1 : K0) - A₁) +
      (A₀ * A₁ - A₂) + -((n 2 : K0) - A₂) := by push_cast; ring
  have hf : Vge v 25 ((n 0 * n 1 - n 2 : ℤ) : K0) := by
    rw [ef]
    refine ((Vge.add ?_ ?_).add t₁₂).add k2.neg
    · simpa using k0.mul (Mult.vge_intCast (n 1))
    · simpa using hA₀.mul k1
  -- back to `ℤ`
  rcases eq_or_ne (n 0 * n 1 - n 2) 0 with h0 | h0
  · rw [h0]; exact dvd_zero _
  rw [padicValInt_dvd_iff]
  right
  unfold Vge at hf
  rw [hv, vP_apply hπ (Int.cast_ne_zero.mpr h0), vp_intCast hp2 hπ hπp h0] at hf
  exact_mod_cast WithTop.coe_le_coe.mp hf

/-- **From the local tests to the congruence.** Let `p > 324` be prime, `π ∣ p` a prime of
`ℤ[s]`, `c ∈ ℤ` with `p ∤ c`, `n, z : Fin 3 → ℤ` and `h ≠ 0, c`. If the test values
`τ(h, z; c, cn₁, cn₂, cn₃)` satisfy `v_π(τ_j) ≥ k_j`, then `p²⁵ ∣ n₁n₂ - n₃`. -/
theorem tests_to_congruence (hp324 : 324 < p) {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs))
    {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) (n z : Fin 3 → ℤ) {h : ℤ} (hh : h ≠ 0) (hhc : h ≠ c)
    (hτ : ∀ j : Fin 12, Vge (vP π hπ) (prec j) (testValues h z ![c, c * n 0, c * n 1, c * n 2] j)) :
    (p : ℤ) ^ 25 ∣ n 0 * n 1 - n 2 := by
  refine tests_to_congruence_aux hp324 hπ hπp hc n z hh hhc (hτ 0) (fun i => ?_) (hτ 4)
    (fun i => ?_) (fun i => ?_) (hτ 11)
  · fin_cases i
    exacts [hτ 1, hτ 2, hτ 3]
  · fin_cases i
    exacts [hτ 5, hτ 6, hτ 7]
  · fin_cases i
    exacts [hτ 8, hτ 9, hτ 10]

end

end ZInQ.Mult
