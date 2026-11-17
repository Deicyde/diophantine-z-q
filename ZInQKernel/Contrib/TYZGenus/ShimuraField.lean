import ZInQKernel.Contrib.TYZGenus.ShimuraZn

/-!
# tyz-cm: the CM leaf `CM.CMFieldOfDefinition ringClassFieldD` from the main theorem of CM

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

Main result: `cmFieldOfDefinition_of (hS : ShimuraReciprocityPic) :
CM.CMFieldOfDefinition RingClass.ringClassFieldD` — every Heegner point of discriminant `D` on
`X₀(32) = A` (through x0-32's `X0.phiC`) has coordinates in the ring class field of discriminant
`D`, given the textbook leaf `ShimuraReciprocityPic` (main theorem of complex multiplication in
Gross's form, `ShimuraRecip.lean`). Also `cmFieldTYZ_of_shimura`: the TYZ package leaf
`Package.CMFieldOfDefinitionTYZ`, through ring-class's bridge `cmFieldTYZ_of_ringClassD`.

Proof: the case `J = 𝓞_K` (trivial Picard class) of the leaf, with `ρ` any automorphism of `ℚ̄`
fixing `H_O`; the lattices `⟨1, τ_Q⟩` and `⟨1/32, τ_Q⟩` of every Heegner form of discriminant
`D = disc(O)` are stable under `κ(O)` (`kappa_order`: `κ(O) ⊆ ℤ + ℤ·Aτ_Q`, a parity computation
with the half-integral coordinates of `𝓞_K`), so `κ(O)·L = L` and the leaf gives
`ρ(P_Q) = P_Q`; infinite Galois theory (`ℚ̄^{Gal(ℚ̄/H)} = H`) finishes.
No Heegner condition `(f, 32) = 1` is used.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex

section Coords
variable {m : ℕ} [NeZero m]

/-- **Half-integral coordinates in `𝓞_K`**, `K = ℚ(√−m)`, `m` squarefree: `2 re = a`, `2 im = t`
with `a, t ∈ ℤ` and `a² + m t² ≡ 0 (mod 4)` (`a² + m t² = 4 N(y)`). -/
theorem two_coords (hsq : Squarefree m) (y : 𝓞 (QNeg m)) :
    ∃ a t N : ℤ, 2 * (y : QNeg m).re = a ∧ 2 * (y : QNeg m).im = t ∧ a ^ 2 + m * t ^ 2 = 4 * N := by
  obtain ⟨a, ha⟩ := exists_two_re y
  obtain ⟨b, hb⟩ := exists_two_re (y * sqrtNeg m)
  have hN := normZ_eq_re_im y
  set N := Algebra.norm ℤ y
  set s := (y : QNeg m).im
  have hb' : 2 * (-(m : ℚ) * s) = b := by
    rw [← hb]; simp [coe_sqrtNeg, s]
  have hnt : (m : ℚ) * (2 * s) = -b := by linarith
  have h4 : (a : ℚ) ^ 2 + m * (2 * s) ^ 2 = 4 * N := by
    rw [hN, ← ha]; ring
  have hdiv : (m : ℤ) ∣ b ^ 2 := by
    refine ⟨4 * N - a ^ 2, ?_⟩
    have : (b : ℚ) ^ 2 = m * (4 * N - a ^ 2) := by
      have : (b : ℚ) ^ 2 = (m * (2 * s)) ^ 2 := by rw [hnt]; ring
      rw [this]; linear_combination (m : ℚ) * h4
    exact_mod_cast this
  have hsqZ : Squarefree (m : ℤ) := Int.squarefree_natCast.mpr hsq
  obtain ⟨t, ht⟩ := (hsqZ.dvd_pow_iff_dvd two_ne_zero).1 hdiv
  have hn0 : (m : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hs2 : 2 * s = -t := by
    have : (m : ℚ) * (2 * s) = m * (-t) := by rw [hnt, ht]; push_cast; ring
    exact mul_left_cancel₀ hn0 this
  refine ⟨a, -t, N, ha, by rw [hs2]; push_cast; ring, ?_⟩
  have : (a : ℚ) ^ 2 + m * (-t : ℤ) ^ 2 = 4 * N := by rw [← h4, hs2]; push_cast; ring
  exact_mod_cast this

theorem sq_mod_four (x : ℤ) : x ^ 2 % 4 = 0 ∧ 2 ∣ x ∨ x ^ 2 % 4 = 1 ∧ ¬ 2 ∣ x := by
  rcases Int.emod_two_eq_zero_or_one x with h | h
  · left; obtain ⟨k, rfl⟩ : 2 ∣ x := Int.dvd_of_emod_eq_zero h
    refine ⟨?_, dvd_mul_right 2 k⟩; ring_nf; omega
  · right; obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
    subst hk; refine ⟨by ring_nf; omega, by omega⟩

omit [NeZero m] in
/-- Parity of the half-coordinates: for `m ≡ 3 (mod 4)`, `a ≡ t (mod 2)`. -/
theorem parity_three {a t N : ℤ} (hm : (m : ℤ) % 4 = 3) (h : a ^ 2 + m * t ^ 2 = 4 * N) :
    (2 ∣ a ↔ 2 ∣ t) := by
  have e1 : ((m : ℤ) * t ^ 2) % 4 = (3 * t ^ 2) % 4 := by rw [Int.mul_emod, hm]; omega
  have e2 : (a ^ 2 + (m : ℤ) * t ^ 2) % 4 = 0 := by rw [h]; simp
  rcases sq_mod_four a with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases sq_mod_four t with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
  · exact ⟨fun _ => h2', fun _ => h1'⟩
  · omega
  · omega
  · exact ⟨fun h => absurd h h1', fun h => absurd h h2'⟩

omit [NeZero m] in
/-- For `m ≢ 3 (mod 4)` squarefree, `a` and `t` are even. -/
theorem parity_other {a t N : ℤ} (hsq : Squarefree m) (hm : ¬ (m : ℤ) % 4 = 3)
    (h : a ^ 2 + m * t ^ 2 = 4 * N) : 2 ∣ a ∧ 2 ∣ t := by
  have hm0 : ¬ (m : ℤ) % 4 = 0 := by
    intro h0
    have h4 : (2 : ℕ) * 2 ∣ m := by
      have : (4 : ℤ) ∣ m := Int.dvd_of_emod_eq_zero h0
      exact_mod_cast this
    exact absurd (hsq 2 h4) (by decide)
  have hm12 : (m : ℤ) % 4 = 1 ∨ (m : ℤ) % 4 = 2 := by omega
  have e2 : (a ^ 2 + (m : ℤ) * t ^ 2) % 4 = 0 := by rw [h]; simp
  rcases hm12 with hm1 | hm2
  · have e1 : ((m : ℤ) * t ^ 2) % 4 = (t ^ 2) % 4 := by
      rw [Int.mul_emod, hm1, one_mul, Int.emod_emod_of_dvd _ (by norm_num)]
    rcases sq_mod_four a with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases sq_mod_four t with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
    · exact ⟨h1', h2'⟩
    all_goals omega
  · have e1 : ((m : ℤ) * t ^ 2) % 4 = (2 * t ^ 2) % 4 := by rw [Int.mul_emod, hm2]; omega
    rcases sq_mod_four a with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases sq_mod_four t with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
    · exact ⟨h1', h2'⟩
    all_goals omega

end Coords

section Order
variable {m f : ℕ} [NeZero m] [NeZero f]

theorem heegner_A_ne_zero {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : (Q.A : ℂ) ≠ 0 := by
  exact_mod_cast Q.A_pos.ne'

/-- `s = i√(−D)` satisfies `s² = D`. -/
theorem sqD_sq {D : ℤ} (hD : D < 0) : (I * (Real.sqrt (-(D : ℝ)) : ℂ)) ^ 2 = D := by
  have h0 : (0 : ℝ) ≤ -(D : ℝ) := by
    have : (D : ℝ) < 0 := by exact_mod_cast hD
    linarith
  rw [mul_pow, I_sq, ← Complex.ofReal_pow, Real.sq_sqrt h0]
  push_cast; ring

/-- `Aτ_Q² + Bτ_Q + C = 0`. -/
theorem heegner_tau_quad {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) :
    (Q.A : ℂ) * Q.tau ^ 2 + Q.B * Q.tau + Q.C = 0 := by
  have hA := heegner_A_ne_zero Q
  have hs := sqD_sq Q.D_neg
  have hdisc : ((Q.B : ℂ)) ^ 2 - 4 * Q.A * Q.C = D := by exact_mod_cast Q.disc
  simp only [HeegnerForm.tau, cmPoint]
  field_simp
  linear_combination hs - hdisc

/-- `Aτ_Q = (−B + i√(−D))/2`. -/
theorem heegner_A_mul_tau {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) :
    (Q.A : ℂ) * Q.tau = (-(Q.B : ℂ) + I * (Real.sqrt (-(D : ℝ)) : ℂ)) / 2 := by
  have hA := heegner_A_ne_zero Q
  simp only [HeegnerForm.tau, cmPoint]
  field_simp

theorem sqrt_neg_discOf (m f : ℕ) :
    Real.sqrt (-((discOf m f : ℤ) : ℝ)) =
      (if m % 4 = 3 then (f : ℝ) else 2 * f) * Real.sqrt m := by
  unfold discOf
  split_ifs with h
  · rw [show -(((-((f : ℤ) ^ 2 * m) : ℤ)) : ℝ) = (f : ℝ) ^ 2 * m by push_cast; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  · rw [show -(((-(4 * (f : ℤ) ^ 2 * m) : ℤ)) : ℝ) = (2 * f : ℝ) ^ 2 * m by push_cast; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **`κ(O) ⊆ ℤ + ℤ·Aτ_Q`** for a form `Q` of discriminant `D = disc(O)`, `O = ℤ + f𝓞_K`. -/
theorem kappa_order (hsq : Squarefree m) {D : ℤ} (hD : D = discOf m f) {N : ℕ} (Q : HeegnerForm N D)
    {o : QNeg m} (ho : o ∈ (conductorOrder (QNeg m) f).toSubalgebra) :
    ∃ u v : ℤ, kappa m o = u + v * ((Q.A : ℂ) * Q.tau) := by
  rw [conductorOrder_toSubalgebra, mem_conductorOrderSubalgebra] at ho
  obtain ⟨a, y, rfl⟩ := ho
  obtain ⟨a', t, Nn, ha, ht, hN⟩ := two_coords hsq y
  have hk : kappa m ((a : QNeg m) + f * (y : QNeg m)) =
      a + f * (((a' : ℂ) / 2) + ((t : ℂ) / 2) * (I * Real.sqrt m)) := by
    rw [← kappaAlg_apply, map_add, map_mul, map_intCast, map_natCast, kappaAlg_apply, kappa,
      show (y : QNeg m).re = (a' : ℚ) / 2 by linarith, show (y : QNeg m).im = (t : ℚ) / 2 by linarith]
    push_cast; ring
  have hsD : Real.sqrt (-(D : ℝ)) = (if m % 4 = 3 then (f : ℝ) else 2 * f) * Real.sqrt m := by
    rw [hD, sqrt_neg_discOf]
  rw [hk, heegner_A_mul_tau Q, hsD]
  have hdisc : Q.B ^ 2 - 4 * Q.A * Q.C = discOf m f := Q.disc.trans hD
  by_cases h3 : m % 4 = 3
  · simp only [h3, ite_true]
    have hm3 : (m : ℤ) % 4 = 3 := by exact_mod_cast h3
    have hpar := parity_three hm3 hN
    -- f ≡ B (mod 2)
    have hfB : 2 ∣ (f : ℤ) * a' + t * Q.B := by
      unfold discOf at hdisc; rw [if_pos h3] at hdisc
      have hBf : 2 ∣ (Q.B : ℤ) + f := by
        have h2 : (2 : ℤ) ∣ Q.B ^ 2 + (f : ℤ) ^ 2 * m := ⟨2 * Q.A * Q.C, by linear_combination hdisc⟩
        rcases Int.emod_two_eq_zero_or_one Q.B with hB | hB <;>
          rcases Int.emod_two_eq_zero_or_one (f : ℤ) with hf | hf
        · omega
        · exfalso
          obtain ⟨b, hb⟩ : ∃ b, Q.B = 2 * b := ⟨Q.B / 2, by omega⟩
          obtain ⟨c, hc⟩ : ∃ c, (f : ℤ) = 2 * c + 1 := ⟨f / 2, by omega⟩
          obtain ⟨e, he⟩ : ∃ e, (m : ℤ) = 4 * e + 3 := ⟨m / 4, by omega⟩
          rw [hb, hc, he] at h2
          obtain ⟨w, hw⟩ := h2
          have : (2 : ℤ) * (w - 2 * b ^ 2 - (2 * c ^ 2 + 2 * c) * (4 * e + 3) - 2 * e - 1) = 1 := by
            linear_combination (-1 : ℤ) * hw
          omega
        · exfalso
          obtain ⟨b, hb⟩ : ∃ b, Q.B = 2 * b + 1 := ⟨Q.B / 2, by omega⟩
          obtain ⟨c, hc⟩ : ∃ c, (f : ℤ) = 2 * c := ⟨f / 2, by omega⟩
          rw [hb, hc] at h2
          obtain ⟨w, hw⟩ := h2
          have : (2 : ℤ) * (2 * b ^ 2 + 2 * b + 2 * c ^ 2 * m - w) = -1 := by linear_combination hw
          omega
        · omega
      by_cases ha2 : 2 ∣ a'
      · obtain ⟨a'', rfl⟩ := ha2
        obtain ⟨t'', rfl⟩ := hpar.1 ⟨a'', rfl⟩
        exact ⟨f * a'' + t'' * Q.B, by ring⟩
      · have ht2 : ¬ 2 ∣ t := fun h => ha2 (hpar.2 h)
        obtain ⟨a'', ha''⟩ : ∃ a'', a' = 2 * a'' + 1 := ⟨a' / 2, by omega⟩
        obtain ⟨t'', ht''⟩ : ∃ t'', t = 2 * t'' + 1 := ⟨t / 2, by omega⟩
        obtain ⟨g, hg⟩ := hBf
        subst ha'' ht''
        exact ⟨f * a'' + t'' * Q.B + g, by linear_combination hg⟩
    obtain ⟨k, hk⟩ := hfB
    refine ⟨a + k, t, ?_⟩
    have hk' : ((f : ℂ) * a' + t * Q.B) = 2 * k := by exact_mod_cast hk
    push_cast
    linear_combination (1 / 2 : ℂ) * hk'
  · simp only [h3, ite_false]
    have hm3 : ¬ (m : ℤ) % 4 = 3 := by exact_mod_cast h3
    obtain ⟨⟨a'', rfl⟩, ⟨t'', rfl⟩⟩ := parity_other hsq hm3 hN
    have hB : 2 ∣ Q.B := by
      unfold discOf at hdisc; rw [if_neg h3] at hdisc
      have : (Q.B : ℤ) ^ 2 = 4 * (Q.A * Q.C - f ^ 2 * m) := by linear_combination hdisc
      have h4 : (2 : ℤ) ∣ Q.B ^ 2 := ⟨2 * (Q.A * Q.C - f ^ 2 * m), by rw [this]; ring⟩
      exact Int.prime_two.dvd_of_dvd_pow h4
    obtain ⟨b, hb⟩ := hB
    refine ⟨a + f * a'' + t'' * b, t'', ?_⟩
    have hb' : (Q.B : ℂ) = 2 * b := by exact_mod_cast hb
    rw [hb']
    push_cast
    ring

/-- **`κ(O)·⟨1, τ_Q⟩ ⊆ ⟨1, τ_Q⟩`.** -/
theorem kappa_mul_mem_lat (hsq : Squarefree m) {D : ℤ} (hD : D = discOf m f) {N : ℕ}
    (Q : HeegnerForm N D) {o : QNeg m} (ho : o ∈ (conductorOrder (QNeg m) f).toSubalgebra) :
    ∀ x ∈ Q.lat, kappa m o * x ∈ Q.lat := by
  obtain ⟨u, v, huv⟩ := kappa_order hsq hD Q ho
  have h1 : kappa m o * 1 ∈ Q.lat := by
    rw [mul_one, huv, HeegnerForm.lat]
    exact Submodule.mem_span_pair.2 ⟨u, v * Q.A, by push_cast; simp [zsmul_eq_mul]; ring⟩
  have hτ : kappa m o * Q.tau ∈ Q.lat := by
    have hq := heegner_tau_quad Q
    rw [HeegnerForm.lat]
    refine Submodule.mem_span_pair.2 ⟨-(v * Q.C), u - v * Q.B, ?_⟩
    rw [huv]
    simp only [zsmul_eq_mul]
    push_cast
    linear_combination (-(v : ℂ)) * hq
  intro x hx
  rw [HeegnerForm.lat] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · exact h1
    · exact hτ
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => rw [mul_add]; exact Submodule.add_mem _ hz hw
  | smul r z _ hz => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hz

/-- **`κ(O)·⟨1/32, τ_Q⟩ ⊆ ⟨1/32, τ_Q⟩`** (uses `32 ∣ A`). -/
theorem kappa_mul_mem_latN (hsq : Squarefree m) {D : ℤ} (hD : D = discOf m f)
    (Q : HeegnerForm 32 D) {o : QNeg m} (ho : o ∈ (conductorOrder (QNeg m) f).toSubalgebra) :
    ∀ x ∈ Q.latN, kappa m o * x ∈ Q.latN := by
  obtain ⟨u, v, huv⟩ := kappa_order hsq hD Q ho
  obtain ⟨A', hA'⟩ := Q.N_dvd
  have hA'C : (Q.A : ℂ) = 32 * A' := by exact_mod_cast hA'
  have h1 : kappa m o * (1 / ((32 : ℕ) : ℂ)) ∈ Q.latN := by
    rw [huv, HeegnerForm.latN]
    refine Submodule.mem_span_pair.2 ⟨u, v * A', ?_⟩
    simp only [zsmul_eq_mul]
    rw [hA'C]
    push_cast
    ring
  have hτ : kappa m o * Q.tau ∈ Q.latN := by
    have hq := heegner_tau_quad Q
    rw [HeegnerForm.latN]
    refine Submodule.mem_span_pair.2 ⟨-(32 * v * Q.C), u - v * Q.B, ?_⟩
    rw [huv]
    simp only [zsmul_eq_mul]
    push_cast
    linear_combination (-(v : ℂ)) * hq
  intro x hx
  rw [HeegnerForm.latN] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · exact h1
    · exact hτ
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => rw [mul_add]; exact Submodule.add_mem _ hz hw
  | smul r z _ hz => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hz

theorem one_mem_idealMeetOrder : (1 : QNeg m) ∈ idealMeetOrder m f ⊤ :=
  ⟨Subalgebra.one_mem _, 1, Submodule.mem_top, by simp⟩

/-- `κ(⊤ ∩ O)·L = L` for a lattice `L` stable under `κ(O)`. -/
theorem idealLat_top_mul {L : Submodule ℤ ℂ}
    (hL : ∀ o ∈ (conductorOrder (QNeg m) f).toSubalgebra, ∀ x ∈ L, kappa m o * x ∈ L) :
    idealLat m f ⊤ * L = L := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro a ha x hx
    rw [idealLat] at ha
    induction ha using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨o, ho, rfl⟩ := hz
      exact hL o ho.1 x hx
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add z w _ _ hz hw => rw [add_mul]; exact Submodule.add_mem _ hz hw
    | smul r z _ hz => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hz
  · intro x hx
    have h1 : (1 : ℂ) ∈ idealLat m f ⊤ := by
      have : kappa m 1 = 1 := by simp [kappa, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
      rw [← this]
      exact Submodule.subset_span ⟨1, one_mem_idealMeetOrder, rfl⟩
    simpa using Submodule.mul_mem_mul h1 hx

end Order

section FieldOfDefinition
open Polynomial

theorem exists_normalized_embed_any (m : ℕ) [NeZero m] :
    ∃ e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar,
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) := by
  set r := embed m (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)
  have hr : r ^ 2 = -(m : Qbar) := by
    simp only [r, ← map_pow, omega_sq', map_neg, map_natCast]
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hC : ιC r ^ 2 = (I * (Real.sqrt m : ℂ)) ^ 2 := by
    rw [← map_pow, hr, mul_pow, I_sq, sq, sqrt_mul_self_C]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hC with h | h
  · exact ⟨embed m, h⟩
  · obtain ⟨γ, hγ⟩ := exists_galQ_neg hm0 hr
    refine ⟨γ.toAlgHom.comp (embed m), ?_⟩
    show ιC (γ r) = _
    rw [hγ, map_neg, h, neg_neg]

theorem disc_mod_four {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : D % 4 = 0 ∨ D % 4 = 1 := by
  rw [← Q.disc, show 4 * Q.A * Q.C = 4 * (Q.A * Q.C) by ring]
  rcases sq_mod_four Q.B with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- **`CM.CMFieldOfDefinition ringClassFieldD` from the Shimura reciprocity leaf**: the case
`J = 𝓞_K` (trivial class, `ρ` fixing `H_O`) of `ShimuraReciprocityPic`, with `κ(O)·L = L` for the
lattices of every Heegner form (`kappa_order`), and infinite Galois theory (`ℚ̄^{Gal(ℚ̄/H)} = H`). -/
theorem cmFieldOfDefinition_of (hS : ShimuraReciprocityPic) : CMFieldOfDefinition ringClassFieldD := by
  intro D Q
  have hDneg := Q.D_neg
  have h4 := disc_mod_four Q
  obtain ⟨b, hb, hsq⟩ := sqfPart_spec D.natAbs
  have hspec := condD_spec h4 hDneg
  have hDa : (D.natAbs : ℤ) = -D := by omega
  have hm0 : sqfPart D.natAbs ≠ 0 := fun h => by rw [h, mul_zero] at hb; omega
  have hf0 : condD D ≠ 0 := by
    intro h; rw [h] at hspec; split_ifs at hspec <;> simp at hspec <;> omega
  have : NeZero (sqfPart D.natAbs) := ⟨hm0⟩
  have : NeZero (condD D) := ⟨hf0⟩
  set m := sqfPart D.natAbs with hm
  set f := condD D with hf
  have hD : D = discOf m f := by
    unfold discOf
    split_ifs at hspec ⊢ with h3
    · have := congrArg (fun k : ℕ => (k : ℤ)) hspec
      rw [hDa] at this; push_cast at this; linarith
    · have := congrArg (fun k : ℕ => (k : ℤ)) hspec
      rw [hDa] at this; push_cast at this; linarith
  have hK : ringClassFieldD D = ringClassFieldBar m f := by rw [ringClassFieldD, if_pos hDneg]
  obtain ⟨e, he⟩ := exists_normalized_embed_any m
  have hfix : ∀ ρ ∈ (ringClassFieldD D).fixingSubgroup, galPt ρ (heegnerPt Q) = heegnerPt Q := by
    intro ρ hρ
    have hρe : ∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass 1) x) := by
      intro x
      rw [map_one, map_one, AlgEquiv.one_apply]
      have hx : e x ∈ ringClassFieldD D := by
        rw [hK, ← ringClassFieldBar_eq_map m f e]
        exact ⟨x, x.2, rfl⟩
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hρ _ hx
    have hone : ((1 : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) :
        Ideal (𝓞 (QNeg m))) = ⊤ := by
      rw [OneMemClass.coe_one, Ideal.one_eq_top]
    have hmul : LinearMap.mulLeft ℤ (1 : ℂ) = LinearMap.id := by ext; simp
    refine hS m f hsq e he 1 ρ hρe D hD Q Q 1 ?_ ?_
    · rw [hone, hmul, Submodule.map_id]
      exact idealLat_top_mul (fun o ho => kappa_mul_mem_lat hsq hD Q ho)
    · rw [hone, hmul, Submodule.map_id]
      exact idealLat_top_mul (fun o ho => kappa_mul_mem_latN hsq hD Q ho)
  have hmem : ∀ x : Qbar, (∀ ρ ∈ (ringClassFieldD D).fixingSubgroup, ρ x = x) →
      x ∈ ringClassFieldD D := by
    intro x hx
    rw [← InfiniteGalois.fixedField_fixingSubgroup (ringClassFieldD D)]
    exact fun ρ => hx ρ.1 ρ.2
  rw [mem_ptsOver_iff]
  rcases hP : heegnerPt Q with _ | ⟨x, y, h⟩
  · trivial
  · refine ⟨hmem x fun ρ hρ => ?_, hmem y fun ρ hρ => ?_⟩
    · have := hfix ρ hρ
      rw [hP] at this
      obtain ⟨h', hh'⟩ := galPt_some ρ h
      rw [hh', WeierstrassCurve.Affine.Point.some.injEq] at this
      exact this.1
    · have := hfix ρ hρ
      rw [hP] at this
      obtain ⟨h', hh'⟩ := galPt_some ρ h
      rw [hh', WeierstrassCurve.Affine.Point.some.injEq] at this
      exact this.2

end FieldOfDefinition

/-- **The TYZ package leaf `Package.CMFieldOfDefinitionTYZ` from the main theorem of CM**
(through ring-class's `cmFieldTYZ_of_ringClassD`). -/
theorem cmFieldTYZ_of_shimura (hS : ShimuraReciprocityPic) :
    ZInQ.Contrib.TYZGenus.Package.CMFieldOfDefinitionTYZ :=
  RingClassBridge.cmFieldTYZ_of_ringClassD (cmFieldOfDefinition_of hS)

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus.Package in
/-- **Reading A of TYZ Theorem 3.5 with both CM leaves replaced by the main theorem of CM**:
from the three `𝓛`-leaves, `ShimuraReciprocityPic` (main theorem of CM, Gross's form), x0-32's
leaf `X0.EtaModelFricke`, TYZ Lemma 3.18 (literal) and the bundled `GenusPointLeafCM`
(`CMFieldOfDefinition ringClassFieldD` by `cmFieldOfDefinition_of`, `TYZSigmaFixesZn` by
`tyzSigmaFixesZn_of` of `ShimuraZn.lean`). -/
theorem tyzThm35ReadingA_of_shimura (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hS : ShimuraReciprocityPic) (hF : X0.EtaModelFricke)
    (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA :=
  RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD h11 h1 h29 (cmFieldOfDefinition_of hS)
    (tyzSigmaFixesZn_of hS hF) h318 hG

end ZInQ.Contrib.TYZGenus.Shimura
