import ZInQKernel.Contrib.OneProof.EichlerBound.Key

/-! eichler-bound, part B5: the primes `2` and `3` (types of optimal embeddings, no bad prime for
embeddings of the same type, and inertness when two types occur). No `sorry`. -/

set_option linter.style.longLine false

noncomputable section

namespace EichlerBound

open LeafQM LeafQM.AV GRCountX6

theorem nrd_sub_coe (z : B) (a : ℚ) : nrd (z - (a : B)) = a ^ 2 - a * trd z + nrd z := by
  simp [nrd, trd]; ring

theorem nrd_sub_star (z : B) : nrd (z - star z) = 4 * nrd z - trd z ^ 2 := by
  simp [nrd, trd]; ring

theorem L6_natAbs {ℓ : ℤ} (hℓ : L6 ℓ) : 2 ≤ ℓ.natAbs := by rcases hℓ with rfl | rfl <;> norm_num

theorem L6_ne {ℓ : ℤ} (hℓ : L6 ℓ) : ℓ ≠ 0 := by rcases hℓ with rfl | rfl <;> norm_num

theorem L6_prime {ℓ : ℤ} (hℓ : L6 ℓ) : Prime ℓ := by
  rcases hℓ with rfl | rfl
  · exact Int.prime_two
  · exact Int.prime_three

theorem PP_epsL_smul {ℓ : ℤ} (hℓ : L6 ℓ) {v : B} (hv : PP ℓ v) : PP ℓ (((epsL ℓ : ℤ) : ℚ) • v) := by
  rcases hℓ with rfl | rfl
  · have : ((epsL 2 : ℤ) : ℚ) = -1 := by simp [epsL]
    rw [this, neg_one_smul]; exact PP_neg (Or.inl rfl) hv
  · have : ((epsL 3 : ℤ) : ℚ) = 1 := by simp [epsL]
    rw [this, one_smul]; exact hv

/-- An integer in `P_ℓ` is divisible by `ℓ`. -/
theorem dvd_of_PP_int {ℓ : ℤ} (hℓ : L6 ℓ) {x : ℤ} (h : PP ℓ ((x : ℚ) : B)) : ℓ ∣ x := by
  rw [PP_iff (intCast_mem x)] at h
  obtain ⟨z, hz, hd⟩ := h
  rw [nrd_coe] at hz
  have : z = x ^ 2 := by exact_mod_cast hz.symm
  rw [this] at hd
  exact (L6_prime hℓ).dvd_of_dvd_pow hd

section Emb

variable {k : Type} [Field k] [NumberField k] {R : Subring k} (Bs : QBasis R)

theorem pp_of_bad {Ψ Φ : OptEmb k R} {ℓ : ℤ} (hℓ : ℓ ≠ 0) (hB : Bad Ψ Φ ℓ) :
    ∀ c ∈ Jo Ψ Φ, PP ℓ c := by
  intro c hc
  have h := hB c hc c hc
  rw [star_mul_self'] at h
  obtain ⟨w, hw⟩ := LO_rat hℓ h
  rw [PP_iff hc.1]
  exact ⟨ℓ * w, by rw [hw]; push_cast; ring, dvd_mul_right _ _⟩

include Bs in
theorem exists_not_LO (hk : Module.finrank ℚ k = 2) (Ψ Φ : OptEmb k R) {ℓ : ℤ} (hℓ : 2 ≤ ℓ.natAbs) :
    ∃ c ∈ Jo Ψ Φ, c ≠ 0 ∧ ¬ LO ℓ c := by
  have hℓ0 : ℓ ≠ 0 := by intro h; rw [h] at hℓ; simp at hℓ
  obtain ⟨c0, hc0, hne⟩ := exists_Jo Bs hk Ψ Φ
  obtain ⟨z0, hz0⟩ := nrd_int hc0.1
  have hex : ∃ m : ℕ, ∃ c ∈ Jo Ψ Φ, c ≠ 0 ∧ ∃ z : ℤ, nrd c = z ∧ z.natAbs = m :=
    ⟨_, c0, hc0, hne, z0, hz0, rfl⟩
  classical
  obtain ⟨c, hc, hcne, z, hz, hzm⟩ := Nat.find_spec hex
  refine ⟨c, hc, hcne, fun hl => ?_⟩
  have hc' := Jo_div hℓ0 hc hl
  have hcne' : ((ℓ : ℚ)⁻¹ • c) ≠ 0 := by
    rw [smul_ne_zero_iff]; exact ⟨by simpa using hℓ0, hcne⟩
  obtain ⟨z', hz'⟩ := nrd_int hc'.1
  have hzz : z = ℓ ^ 2 * z' := by
    rw [nrd_smul, hz] at hz'
    have hℓq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ0
    have : (z : ℚ) = ℓ ^ 2 * z' := by rw [← hz']; field_simp
    exact_mod_cast this
  have hz0' : z ≠ 0 := by
    intro h0; rw [h0] at hz; exact hcne (nrd_eq_zero_iff.mp hz)
  have hz'0 : z' ≠ 0 := by intro h0; rw [h0, mul_zero] at hzz; exact hz0' hzz
  have hlt : z'.natAbs < Nat.find hex := by
    rw [← hzm, hzz, Int.natAbs_mul, Int.natAbs_pow]
    have : 0 < z'.natAbs := Int.natAbs_pos.mpr hz'0
    have : 4 ≤ ℓ.natAbs ^ 2 := by nlinarith
    nlinarith
  exact Nat.find_min hex hlt ⟨_, hc', hcne', z', hz', rfl⟩

/-- The norm of `Φ(ω − a)`. -/
theorem nrd_omega_sub (Φ : OptEmb k R) (a : ℤ) :
    nrd (Φ.1 (Bs.ω - (a : k))) = ((a ^ 2 - Bs.t * a + Bs.n : ℤ) : ℚ) := by
  rw [map_sub, emb_intCast, nrd_sub_coe, trd_omega, nrd_omega]; push_cast; ring

include Bs in
/-- **Ramified `ℓ ∣ 6`**: an element of `R` with norm exactly divisible by `ℓ` rules out a bad `ℓ`. -/
theorem ram_contra (hk : Module.finrank ℚ k = 2) {Ψ Φ : OptEmb k R} {ℓ : ℤ} (hℓ : L6 ℓ)
    (hB : ∀ d ∈ Jo Ψ Φ, PP ℓ d) {a : ℤ} (hN : ℓ ∣ a ^ 2 - Bs.t * a + Bs.n)
    (hN2 : ¬ ℓ ^ 2 ∣ a ^ 2 - Bs.t * a + Bs.n) : False := by
  have hℓ0 := L6_ne hℓ
  have hℓq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ0
  set l : k := Bs.ω - (a : k) with hldef
  have hl : l ∈ R := R.sub_mem Bs.mem (_root_.intCast_mem R a)
  have hΦl : Φ.1 l ∈ LeafQM.O := (optEmb_mem Φ l).2 hl
  have hPP : PP ℓ (Φ.1 l) := by
    rw [PP_iff hΦl]; exact ⟨_, nrd_omega_sub Bs Φ a, hN⟩
  obtain ⟨o, ho, hlo⟩ := PP_eq_pi_mul hℓ hPP
  obtain ⟨q0, hq0⟩ : ∃ q0 : ℚ, q0 = (ℓ : ℚ)⁻¹ := ⟨_, rfl⟩
  set w : k := (q0 : k) * sk Ψ l with hw
  have hstep : ∀ d ∈ Jo Ψ Φ, d * Ψ.1 w ∈ Jo Ψ Φ := by
    intro d hd
    obtain ⟨od, hod, hdo⟩ := PP_eq_pi_mul hℓ (hB d hd)
    have hLO : LO ℓ (d * Ψ.1 (sk Ψ l)) := by
      rw [hd.2 (sk Ψ l), emb_sk' Bs hk Ψ Φ, hlo, hdo, star_mul]
      have e : star o * star (piL ℓ) * (piL ℓ * od) = star o * (star (piL ℓ) * piL ℓ) * od := by
        simp only [mul_assoc]
      rw [e, star_mul_self', nrd_piL hℓ, LO_iff_smul ℓ hℓ0]
      refine ⟨((epsL ℓ : ℤ) : ℚ) • (star o * od), smul_mem_O (LeafQM.O.mul_mem (star_mem ho) hod) _, ?_⟩
      rw [← coe_comm, mul_assoc, coe_mul_eq_smul, smul_smul]; push_cast; ring_nf
    have := Jo_div hℓ0 (Jo_mul_right hd (sk_mem Ψ hl)) hLO
    rw [hw, map_mul, emb_ratCast, ← mul_assoc, ← coe_comm, mul_assoc, coe_mul_eq_smul, hq0]; exact this
  have hiter : ∀ m : ℕ, ∀ c ∈ Jo Ψ Φ, c * Ψ.1 (w ^ m) ∈ Jo Ψ Φ := by
    intro m
    induction m with
    | zero => intro c hc; rw [pow_zero, map_one, mul_one]; exact hc
    | succ m ih =>
      intro c hc
      rw [pow_succ, map_mul, ← mul_assoc]
      exact hstep _ (ih c hc)
  -- the norm of `Ψ w`
  set N : ℤ := a ^ 2 - Bs.t * a + Bs.n with hNdef
  obtain ⟨u, hu⟩ := hN
  have hu' : ¬ ℓ ∣ u := by
    rintro ⟨v, rfl⟩; exact hN2 ⟨v, by rw [hu]; ring⟩
  have hnw : nrd (Ψ.1 w) = (u : ℚ) / ℓ := by
    rw [hw, map_mul, emb_ratCast, coe_mul_eq_smul, nrd_smul, emb_sk, nrd_star, nrd_emb Bs hk Ψ Φ,
      nrd_omega_sub, ← hNdef, hu, hq0]
    push_cast; field_simp
  obtain ⟨c0, hc0, hne⟩ := exists_Jo Bs hk Ψ Φ
  obtain ⟨z0, hz0⟩ := nrd_int hc0.1
  have hz00 : z0 ≠ 0 := by
    intro h0; rw [h0] at hz0; exact hne (nrd_eq_zero_iff.mp (by exact_mod_cast hz0))
  have hpow : ∀ m : ℕ, nrd (Ψ.1 w ^ m) = ((u : ℚ) / ℓ) ^ m := by
    intro m
    induction m with
    | zero => simp [nrd]
    | succ m ih => rw [pow_succ, nrd_mul, ih, hnw, pow_succ]
  have hdvd : ∀ m : ℕ, ℓ ^ m ∣ z0 := by
    intro m
    obtain ⟨y, hy⟩ := nrd_int (hiter m c0 hc0).1
    rw [nrd_mul, map_pow, hz0] at hy
    rw [hpow, div_pow] at hy
    have e : (z0 : ℚ) * u ^ m = ℓ ^ m * y := by
      have hℓm : (ℓ : ℚ) ^ m ≠ 0 := pow_ne_zero _ hℓq
      field_simp at hy; linarith
    have e' : z0 * u ^ m = ℓ ^ m * y := by exact_mod_cast e
    have hcop : IsCoprime (ℓ ^ m) (u ^ m) :=
      ((Irreducible.coprime_iff_not_dvd (L6_prime hℓ).irreducible).mpr hu').pow
    exact hcop.dvd_of_dvd_mul_right ⟨y, by rw [mul_comm] at e'; linarith⟩
  have h1 := hdvd z0.natAbs
  have h2 := Int.natAbs_dvd_natAbs.mpr h1
  rw [Int.natAbs_pow] at h2
  have h3 := Nat.le_of_dvd (Int.natAbs_pos.mpr hz00) h2
  have h4 : 2 ^ z0.natAbs ≤ ℓ.natAbs ^ z0.natAbs := Nat.pow_le_pow_left (L6_natAbs hℓ) _
  have h5 := Nat.lt_two_pow_self (n := z0.natAbs)
  omega

include Bs in
/-- **Unramified `ℓ ∣ 6`**: a bad `ℓ` for two embeddings of the same type forces `ℓ ∣ Δ`. -/
theorem unram_dvd (hk : Module.finrank ℚ k = 2) {Ψ Φ : OptEmb k R} {ℓ : ℤ} (hℓ : L6 ℓ)
    (htype : PP ℓ (Φ.1 Bs.ω - Ψ.1 Bs.ω)) (hB : ∀ d ∈ Jo Ψ Φ, PP ℓ d) :
    ℓ ∣ Bs.t ^ 2 - 4 * Bs.n := by
  have hℓ0 := L6_ne hℓ
  have hℓq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ0
  obtain ⟨c, hc, hcne, hcl⟩ := exists_not_LO Bs hk Ψ Φ (L6_natAbs hℓ)
  obtain ⟨c1, hc1, hcc1⟩ := PP_eq_pi_mul hℓ (hB c hc)
  have hc1P : ¬ PP ℓ c1 := by
    intro h
    obtain ⟨c2, hc2, hcc2⟩ := PP_eq_pi_mul hℓ h
    apply hcl
    rw [hcc1, hcc2, ← mul_assoc, piL_sq hℓ, LO_iff_smul ℓ hℓ0]
    refine ⟨((-epsL ℓ : ℤ) : ℚ) • c2, smul_mem_O hc2 _, ?_⟩
    rw [coe_mul_eq_smul, smul_smul]; push_cast; ring_nf
  set β0 := Ψ.1 Bs.ω
  set β := Φ.1 Bs.ω
  have hβ0 := emb_omega_mem Bs Ψ
  have hβ := emb_omega_mem Bs Φ
  obtain ⟨w0, hw0, hfrob⟩ := frob hℓ hβ
  have hint : c * β0 = β * c := hc.2 Bs.ω
  -- `nrd π · c₁β₀ = (nrd π β̄ + ℓ w₀) c₁`
  have e1 : nrd (piL ℓ) • (c1 * β0) = (nrd (piL ℓ) • star β + (ℓ : ℚ) • w0) * c1 := by
    have : star (piL ℓ) * c * β0 = star (piL ℓ) * β * piL ℓ * c1 := by
      rw [mul_assoc, hint, hcc1]; simp only [mul_assoc]
    rw [hfrob] at this
    rw [← this, hcc1]
    rw [show star (piL ℓ) * (piL ℓ * c1) * β0 = (star (piL ℓ) * piL ℓ) * (c1 * β0) by simp only [mul_assoc],
      star_mul_self', coe_mul_eq_smul]
  rw [nrd_piL hℓ, add_mul, smul_mul_assoc, smul_mul_assoc] at e1
  have e2 : c1 * β0 - star β * c1 = ((epsL ℓ : ℤ) : ℚ) • (w0 * c1) := by
    have h3 : (ℓ : ℚ) • (((epsL ℓ : ℤ) : ℚ) • (c1 * β0 - star β * c1) - w0 * c1) = 0 := by
      push_cast at e1
      simp only [smul_sub, smul_smul]
      rw [mul_comm (ℓ : ℚ), e1]
      abel
    rw [smul_eq_zero] at h3
    rcases h3 with h | h
    · exact absurd h hℓq
    · rw [sub_eq_zero] at h
      rw [← h, smul_smul]
      have : ((epsL ℓ : ℤ) : ℚ) * ((epsL ℓ : ℤ) : ℚ) = 1 := by exact_mod_cast epsL_sq
      rw [this, one_smul]
  have hP1 : PP ℓ (c1 * β0 - star β * c1) := by
    rw [e2]; exact PP_epsL_smul hℓ (PP_mul_right hw0 hc1)
  have hP2 : PP ℓ (star β * c1 - c1 * star β) := PP_comm hℓ (star_mem hβ) hc1
  have hP3 : PP ℓ (c1 * (β0 - star β)) := by
    have := PP_add hℓ hP1 hP2
    rwa [show c1 * β0 - star β * c1 + (star β * c1 - c1 * star β) = c1 * (β0 - star β) by
      rw [mul_sub]; abel] at this
  have hP4 : PP ℓ (β0 - star β) :=
    (PP_prime (L6_prime hℓ) hc1 (LeafQM.O.sub_mem hβ0 (star_mem hβ)) hP3).resolve_left hc1P
  have hP5 : PP ℓ (β - star β) := by
    have := PP_add hℓ htype hP4
    rwa [show β - β0 + (β0 - star β) = β - star β by abel] at this
  rw [PP_iff (LeafQM.O.sub_mem hβ (star_mem hβ))] at hP5
  obtain ⟨z, hz, hd⟩ := hP5
  rw [nrd_sub_star, trd_omega, nrd_omega] at hz
  have : z = 4 * Bs.n - Bs.t ^ 2 := by exact_mod_cast hz.symm
  rw [this] at hd
  have := dvd_neg.mpr hd
  rwa [neg_sub] at this

include Bs in
/-- **No bad prime `ℓ ∈ {2, 3}` for two embeddings of the same type at `ℓ`.** -/
theorem not_bad6 (hk : Module.finrank ℚ k = 2) (hc : Nat.Coprime (conductor R) 6) {Ψ Φ : OptEmb k R}
    {ℓ : ℤ} (hℓ : L6 ℓ) (htype : PP ℓ (Φ.1 Bs.ω - Ψ.1 Bs.ω)) : ¬ Bad Ψ Φ ℓ := by
  intro hB
  have hPP := pp_of_bad (L6_ne hℓ) hB
  have hΔ := unram_dvd Bs hk hℓ htype hPP
  obtain ⟨a, ha1, ha2⟩ := exists_l R hc Bs.mem Bs.notRat Bs.span Bs.quad hℓ hΔ
  exact ram_contra Bs hk hℓ hPP ha1 ha2

/-- **Types**: modulo `P_ℓ`, `Φ(ω)` is `Ψ(ω)` or its conjugate. -/
theorem type_dichotomy {ℓ : ℤ} (hℓ : L6 ℓ) (Ψ Φ : OptEmb k R) :
    PP ℓ (Φ.1 Bs.ω - Ψ.1 Bs.ω) ∨ PP ℓ (Φ.1 Bs.ω - star (Ψ.1 Bs.ω)) := by
  have hβ0 := emb_omega_mem Bs Ψ
  have hβ := emb_omega_mem Bs Φ
  have e : (Φ.1 Bs.ω - Ψ.1 Bs.ω) * (Φ.1 Bs.ω - star (Ψ.1 Bs.ω)) =
      Φ.1 Bs.ω * Ψ.1 Bs.ω - Ψ.1 Bs.ω * Φ.1 Bs.ω := by
    have h1 := emb_omega_sq Bs Φ
    have h2 : Ψ.1 Bs.ω * star (Ψ.1 Bs.ω) = ((Bs.n : ℚ) : B) := by rw [mul_star_self', nrd_omega]
    have h3 : star (Ψ.1 Bs.ω) = ((Bs.t : ℚ) : B) - Ψ.1 Bs.ω := by rw [star_eq_trd_sub, trd_omega]
    have h4 : Φ.1 Bs.ω * ((Bs.t : ℚ) : B) = ((Bs.t : ℚ) : B) * Φ.1 Bs.ω := (coe_comm _ _).symm
    rw [sub_mul, mul_sub, mul_sub, h1, h2, h3, mul_sub, h4]
    abel
  have := PP_comm hℓ hβ hβ0
  rw [← e] at this
  exact PP_prime (L6_prime hℓ) (LeafQM.O.sub_mem hβ hβ0) (LeafQM.O.sub_mem hβ (star_mem hβ0)) this

end Emb

end EichlerBound
