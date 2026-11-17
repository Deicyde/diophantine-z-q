import ZInQKernel.Contrib.OneProof.HfxProof.Merge
import ZInQKernel.Contrib.OneProof.HfxProof.Finite3

/-!
# hfx-proof: the test vector for `n ≡ 3 (mod 8)`

Task hfx-proof. For squarefree `1 < n ≡ 3 (mod 8)` and admissible `τ`, `π_ℤ^{U_n}` has a nonzero generator
(`testVector_three`): `ω = (1 + τ(√−n))/2 ∈ O_B`, `K_{n,2}^× = ℚ_2^× ℤ_2[ω]^×`, and the table `tab3`
gives the two orbits of `K_{n,2}^×` on TYZ's 8 classes (sizes 2 and 6); the generator is `−3` on the
2-orbit and `1` on the 6-orbit.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! ## Rank one -/

theorem sum_two_values (F G : T8 → ℤ) (hF : ∀ t, F t = -3 ∨ F t = 1) (a c : ℤ)
    (hG : ∀ t, G t = if F t = -3 then a else c) :
    ∑ t, G t = a * (Finset.univ.filter (fun t => F t = -3)).card +
      c * (Finset.univ.filter (fun t => ¬ F t = -3)).card := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => F t = -3)]
  have e1 : ∑ t ∈ Finset.univ.filter (fun t => F t = -3), G t =
      ∑ t ∈ Finset.univ.filter (fun t => F t = -3), a :=
    Finset.sum_congr rfl (fun t ht => by rw [hG t, if_pos (Finset.mem_filter.mp ht).2])
  have e2 : ∑ t ∈ Finset.univ.filter (fun t => ¬ F t = -3), G t =
      ∑ t ∈ Finset.univ.filter (fun t => ¬ F t = -3), c :=
    Finset.sum_congr rfl (fun t ht => by rw [hG t, if_neg (Finset.mem_filter.mp ht).2])
  rw [e1, e2]
  simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem rank1_two (F G : T8 → ℤ) (hF : ∀ t, F t = -3 ∨ F t = 1) (hFs : ∑ t, F t = 0) {t1 : T8}
    (ht1 : F t1 = 1) (hG : ∀ t t', F t = F t' → G t = G t') (hGs : ∑ t, G t = 0) :
    ∃ c : ℤ, ∀ t, G t = c * F t := by
  classical
  have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset T8))
    (p := fun t => F t = -3)
  have hcard8 : (Finset.univ : Finset T8).card = 8 := rfl
  rw [hcard8] at hcard
  have hFs' := sum_two_values F F hF (-3) 1 (fun t => by rcases hF t with h | h <;> simp [h])
  rw [hFs] at hFs'
  have hS : (Finset.univ.filter (fun t => F t = -3)).card = 2 := by
    have : ((Finset.univ.filter (fun t => F t = -3)).card : ℤ) +
        (Finset.univ.filter (fun t => ¬ F t = -3)).card = 8 := by exact_mod_cast hcard
    have h2 : ((Finset.univ.filter (fun t => F t = -3)).card : ℤ) = 2 := by linarith
    exact_mod_cast h2
  obtain ⟨t0, ht0⟩ : (Finset.univ.filter (fun t => F t = -3)).Nonempty :=
    Finset.card_pos.mp (by rw [hS]; norm_num)
  have hF0 : F t0 = -3 := (Finset.mem_filter.mp ht0).2
  have hGs' := sum_two_values F G hF (G t0) (G t1) (fun t => by
    rcases hF t with h | h
    · rw [if_pos h]; exact hG t t0 (h.trans hF0.symm)
    · rw [if_neg (by rw [h]; norm_num)]; exact hG t t1 (h.trans ht1.symm))
  rw [hGs, hS] at hGs'
  have hS' : (Finset.univ.filter (fun t => ¬ F t = -3)).card = 6 := by omega
  rw [hS'] at hGs'
  refine ⟨G t1, fun t => ?_⟩
  rcases hF t with h | h
  · rw [hG t t0 (h.trans hF0.symm), h]; push_cast at hGs'; linarith
  · rw [hG t t1 (h.trans ht1.symm), h, mul_one]

/-! ## `ω` -/

/-- Hurwitz coordinates of `ω = (1 + a i + b j + c k)/2` for `a = 2a'+1`, `b = 2b'+1`, `c = 2c'+1`. -/
def ωH3 (a' b' c' : ℤ) : H4 ℤ := ⟨c' + 1, a' - c', b' - c', 2 * c' + 1⟩

theorem hurZ_ωH3 (a' b' c' : ℤ) :
    (hurZ (ωH3 a' b' c') : ℍ[ℚ]) = (1 / 2 : ℚ) • (1 + ⟨0, ((2 * a' + 1 : ℤ) : ℚ), ((2 * b' + 1 : ℤ) : ℚ),
      ((2 * c' + 1 : ℤ) : ℚ)⟩) := by
  ext <;> simp [hurZ, hur, ωH3, mapH] <;> ring

theorem isHurZ_hurZ (x : H4 ℤ) : IsHurZ (hurZ x : ℍ[ℚ]) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hc_hurZ, mapH] <;> exact mem_ZS.mpr ⟨_, rfl⟩

/-- The norm form `nrd(x + zω) = x² + xz + N z²`, `N` odd, is a unit when `x, z ∈ ℤ_2` are not both even. -/
theorem norm_quad_form {N : ℤ} (hN : Odd N) (t : ℤ_[2]) :
    ‖((1 + t + (N : ℤ_[2]) * t ^ 2 : ℤ_[2]) : ℚ_[2])‖ = 1 ∧
      ‖((t ^ 2 + t + (N : ℤ_[2]) : ℤ_[2]) : ℚ_[2])‖ = 1 := by
  have key : ∀ x : ℤ_[2], PadicInt.toZMod x ≠ 0 → ‖(x : ℚ_[2])‖ = 1 := by
    intro x hx
    rw [← PadicInt.norm_def, ← PadicInt.isUnit_iff]
    by_contra h
    have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[2] := h
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hm
    exact hx hm
  have hN1 : (N : ZMod 2) = 1 := by
    obtain ⟨k, rfl⟩ := hN; push_cast
    rw [show (2 : ZMod 2) = 0 from rfl]; ring
  have h1 : ∀ a : ZMod 2, 1 + a + 1 * a ^ 2 ≠ 0 := by decide
  have h2 : ∀ a : ZMod 2, a ^ 2 + a + 1 ≠ 0 := by decide
  constructor
  · refine key _ ?_
    simp only [map_add, map_one, map_mul, map_pow, map_intCast, hN1]
    exact h1 _
  · refine key _ ?_
    simp only [map_add, map_pow, map_intCast, hN1]
    exact h2 _

/-! ## Integer congruences from residues -/

theorem mapH_sub {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a b : H4 A) :
    mapH f ⟨a.a0 - b.a0, a.a1 - b.a1, a.a2 - b.a2, a.a3 - b.a3⟩ =
      ⟨f a.a0 - f b.a0, f a.a1 - f b.a1, f a.a2 - f b.a2, f a.a3 - f b.a3⟩ := by
  simp [mapH]

theorem exists_smulH_of_mod {E : H4 ℤ} {m : ℕ} (h : mapH (Int.castRingHom (ZMod m)) E = ⟨0, 0, 0, 0⟩) :
    ∃ C : H4 ℤ, E = smulH m C := by
  simp only [mapH, H4.mk.injEq, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  obtain ⟨⟨c0, h0⟩, ⟨c1, h1⟩, ⟨c2, h2⟩, ⟨c3, h3⟩⟩ := h
  exact ⟨⟨c0, c1, c2, c3⟩, by ext <;> simp [smulH, h0, h1, h2, h3]⟩

theorem getD_mem_unitList (i : Fin 24) : unitList.getD i.val ⟨1, 0, 0, 0⟩ ∈ unitList := by
  rw [List.getD_eq_getElem _ _ (by simp [unitList])]
  exact List.getElem_mem _

theorem nrdH_odd_of_mod4 {x : H4 ℤ} (h0 : nrdH (mapH (Int.castRingHom (ZMod 4)) x) ≠ 0) : nrdH x ≠ 0 := by
  intro h; apply h0; rw [← map_nrdH, h, map_zero]

/-! ## The local condition and `H ≤ SgC` -/

/-- `ℚ_2^× R_2^×` for `ω` with `ω² = ω − N`. -/
def C3 (ω : ℍ[ℚ]) (N : ℤ) (hωZ : IsHurZ ω) (h2 : ω * ω = ω - (N : ℚ) • 1)
    (hst : star ω = 1 - ω) : LocCond where
  P p _ y := Loc2OK (qp p ω) y
  one p _ _ := Loc2OK.one
  mul p _ _ y z hy hz := by
    have h2' : qp p ω * qp p ω = (1 : ℚ_[p]) • qp p ω - ((N : ℚ) : ℚ_[p]) • 1 := by
      rw [← map_mul, h2, map_sub, qp_smul, map_one, one_smul]
    exact Loc2OK.mul' (isHur_qp_hurZ' hωZ) (Zp p).one_mem
      (by rw [Rat.cast_intCast]; exact mem_Zp.mpr (Padic.norm_int_le_one N)) h2' hy hz
  inv p _ _ y z hy h := by
    have hst' : star (qp p ω) = (1 : ℚ_[p]) • 1 - qp p ω := by
      rw [qp, ← qmap_star, ← qp, hst, map_sub, map_one, one_smul]
    exact Loc2OK.of_mul_eq_one' (Zp p).one_mem hst' hy h

/-- **The centralizer of `τ(√−n)` at `2`, `n ≡ 3 (mod 8)`**, lies in `ℚ_2^× R_2^×`. -/
theorem loc2OK_of_commute3 {p : ℕ} [Fact p.Prime] (hp : p = 2) {a' b' c' N : ℤ}
    (hN : 4 * N = (2 * a' + 1) ^ 2 + (2 * b' + 1) ^ 2 + (2 * c' + 1) ^ 2 + 1) (hNo : Odd N)
    {y : ℍ[ℚ_[p]]} (hy : y ≠ 0)
    (hc : y * qp p ⟨0, ((2 * a' + 1 : ℤ) : ℚ), ((2 * b' + 1 : ℤ) : ℚ), ((2 * c' + 1 : ℤ) : ℚ)⟩ =
      qp p ⟨0, ((2 * a' + 1 : ℤ) : ℚ), ((2 * b' + 1 : ℤ) : ℚ), ((2 * c' + 1 : ℤ) : ℚ)⟩ * y) :
    Loc2OK (qp p (hurZ (ωH3 a' b' c'))) y := by
  subst hp
  set A : ℚ_[2] := ((2 * a' + 1 : ℤ) : ℚ_[2])
  set B : ℚ_[2] := ((2 * b' + 1 : ℤ) : ℚ_[2])
  set C : ℚ_[2] := ((2 * c' + 1 : ℤ) : ℚ_[2])
  have hv : qp 2 (⟨0, ((2 * a' + 1 : ℤ) : ℚ), ((2 * b' + 1 : ℤ) : ℚ), ((2 * c' + 1 : ℤ) : ℚ)⟩ : ℍ[ℚ]) =
      ⟨0, A, B, C⟩ := by ext <;> simp [qp, A, B, C]
  have hω : qp 2 (hurZ (ωH3 a' b' c') : ℍ[ℚ]) = ⟨1 / 2, A / 2, B / 2, C / 2⟩ := by
    rw [hurZ_ωH3]; ext <;> simp [qp, A, B, C] <;> ring
  rw [hv] at hc
  rw [hω]
  have e1 := congrArg (·.imJ) hc
  have e2 := congrArg (·.imK) hc
  simp at e1 e2
  have hA : A ≠ 0 := by
    have : ‖A‖ = 1 := norm_odd_int ⟨a', rfl⟩
    intro h; rw [h, norm_zero] at this; exact zero_ne_one this
  set lam := y.imI / A with hlam
  have hJ : y.imJ = lam * B := by rw [hlam]; field_simp; linear_combination (-1 / 2 : ℚ_[2]) * e2
  have hK : y.imK = lam * C := by rw [hlam]; field_simp; linear_combination (1 / 2 : ℚ_[2]) * e1
  have hdec : y = (y.re - lam) • (1 : ℍ[ℚ_[2]]) + (2 * lam) • (⟨1 / 2, A / 2, B / 2, C / 2⟩ : ℍ[ℚ_[2]]) := by
    ext
    · simp; ring
    · simp; rw [hlam]; field_simp
    · simp; rw [hJ]; ring
    · simp; rw [hK]; ring
  set X := y.re - lam
  set Y := 2 * lam
  have hN' : (4 : ℚ_[2]) * N = A ^ 2 + B ^ 2 + C ^ 2 + 1 := by
    simp only [A, B, C]; exact_mod_cast congrArg (fun z : ℤ => (z : ℚ_[2])) hN
  have hnorm : ∀ x z : ℚ_[2], Quaternion.normSq (x • (1 : ℍ[ℚ_[2]]) + z • (⟨1 / 2, A / 2, B / 2, C / 2⟩ : ℍ[ℚ_[2]])) =
      x ^ 2 + x * z + (N : ℚ_[2]) * z ^ 2 := by
    intro x z
    rw [Quaternion.normSq_def']; simp
    linear_combination (-(z ^ 2) / 4) * hN'
  have hωH : IsHur (Zp 2) (⟨1 / 2, A / 2, B / 2, C / 2⟩ : ℍ[ℚ_[2]]) := by
    rw [← hω]; exact isHur_qp_hurZ' (isHurZ_hurZ _)
  have hXY : X ≠ 0 ∨ Y ≠ 0 := by
    by_contra h; push_neg at h
    apply hy; rw [hdec, h.1, h.2, zero_smul, zero_smul, add_zero]
  rcases le_total ‖Y‖ ‖X‖ with hle | hle
  · have hX : X ≠ 0 := by
      rcases hXY with h | h
      · exact h
      · intro hX0; rw [hX0, norm_zero] at hle; exact h (norm_le_zero_iff.mp hle)
    have hYX : ‖Y / X‖ ≤ 1 := by rw [norm_div]; exact div_le_one_of_le₀ hle (norm_nonneg _)
    refine ⟨X, hX, (1 : ℚ_[2]) • 1 + (Y / X) • ⟨1 / 2, A / 2, B / 2, C / 2⟩, ?_, ?_, ?_, ?_⟩
    · rw [hdec, smul_add, smul_smul, smul_smul, mul_one, mul_div_cancel₀ _ hX]
    · exact (isHur_one.smul (by simp [mem_Zp])).add (hωH.smul (mem_Zp.mpr hYX))
    · rw [hnorm, one_pow, one_mul]
      have := (norm_quad_form hNo ⟨Y / X, hYX⟩).1
      exact this
    · exact ⟨1, Y / X, by simp, hYX, 0, isHur_zero, by simp⟩
  · have hY : Y ≠ 0 := by
      rcases hXY with h | h
      · intro hY0; rw [hY0, norm_zero] at hle; exact h (norm_le_zero_iff.mp hle)
      · exact h
    have hXY' : ‖X / Y‖ ≤ 1 := by rw [norm_div]; exact div_le_one_of_le₀ hle (norm_nonneg _)
    refine ⟨Y, hY, (X / Y) • 1 + (1 : ℚ_[2]) • ⟨1 / 2, A / 2, B / 2, C / 2⟩, ?_, ?_, ?_, ?_⟩
    · rw [hdec, smul_add, smul_smul, smul_smul, mul_one, mul_div_cancel₀ _ hY]
    · exact (isHur_one.smul (mem_Zp.mpr hXY')).add (hωH.smul (by simp [mem_Zp]))
    · rw [hnorm, one_pow, mul_one, mul_one]
      have := (norm_quad_form hNo ⟨X / Y, hXY'⟩).2
      exact this
    · exact ⟨X / Y, 1, hXY', by simp, 0, isHur_zero, by simp⟩

/-! ## The main theorem for `n ≡ 3 (mod 8)` -/

theorem chi0Rep_eq (t : T8) : chi0Rep t = chi0Z t := rfl

theorem zmod4_odd_cases (x : ZMod 4) : 2 * x + 1 = 1 ∨ 2 * x + 1 = 3 := by
  revert x; decide

theorem natCast_val_zmod4 (x : ZMod 4) : (((x.val : ℕ) : ℤ) : ZMod 4) = x := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem odd_N3 (a' b' c' : ℤ) : Odd (a' ^ 2 + a' + b' ^ 2 + b' + c' ^ 2 + c' + 1) := by
  have h1 : Even (a' ^ 2 + a') := by
    have := Int.even_mul_succ_self a'; rw [show a' ^ 2 + a' = a' * (a' + 1) by ring]; exact this
  have h2 : Even (b' ^ 2 + b') := by
    have := Int.even_mul_succ_self b'; rw [show b' ^ 2 + b' = b' * (b' + 1) by ring]; exact this
  have h3 : Even (c' ^ 2 + c') := by
    have := Int.even_mul_succ_self c'; rw [show c' ^ 2 + c' = c' * (c' + 1) by ring]; exact this
  have := ((h1.add h2).add h3).add_one
  convert this using 1; ring

/-- **The test vector for `n ≡ 3 (mod 8)`.** -/
theorem testVector_three {n : ℕ} [NeZero n] (hsq : Squarefree n) (h3 : n % 8 = 3)
    {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} (hτ : AdmissibleTau n τ) :
    ∃ f : ℍ[AQ] → ℤ, IsTestVector n τ f ∧ ∃ x : ℍ[AQ]ˣ, f x ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := exists_isPlaceTwo
  obtain ⟨a, b, c, hvq, hn, -⟩ := exists_abc hτ (Or.inr h3)
  have hk : (n : ℤ) = 8 * ((n / 8 : ℕ) : ℤ) + 3 := by
    have := Nat.div_add_mod n 8; rw [h3] at this; exact_mod_cast this.symm
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ := odd_of_three (hk ▸ hn)
  set ωZ := ωH3 a' b' c' with hωZ
  set ω : ℍ[ℚ] := hurZ ωZ with hωdef
  set N : ℤ := a' ^ 2 + a' + b' ^ 2 + b' + c' ^ 2 + c' + 1 with hNdef
  have hN : 4 * N = (2 * a' + 1) ^ 2 + (2 * b' + 1) ^ 2 + (2 * c' + 1) ^ 2 + 1 := by rw [hNdef]; ring
  have hNo : Odd N := odd_N3 a' b' c'
  have hω2 : ω * ω = ω - (N : ℚ) • 1 := by
    rw [hωdef, hurZ_ωH3, hNdef]; ext <;> simp <;> ring
  have hst : star ω = 1 - ω := by rw [hωdef, hurZ_ωH3]; ext <;> simp <;> ring
  have hωv : ω = (1 / 2 : ℚ) • (1 + τ (sqrtNeg n)) := by rw [hvq, hωdef, hurZ_ωH3]
  have hspan : ∀ x : 𝓞 (QNeg n), ∃ m s : ℤ, τ x = (m : ℍ[ℚ]) + (s : ℚ) • ω := by
    intro x; rw [hωv]; exact tau_span3 hsq h3 τ x
  set C := C3 ω N (isHurZ_hurZ _) hω2 hst with hCdef
  have hH : HgrpN n τ ≤ SgC v hv C := by
    refine HgrpN_le_SgC hv C (isHurZ_hurZ _) hspan ?_ ?_ ?_
    · intro p _ _ cc hcc; exact ⟨cc, hcc, 1, by simp, isHur_one, by simp, InR.one⟩
    · intro p _ _ u hu hnu hR; exact ⟨1, one_ne_zero, u, by simp, hu, hnu, hR⟩
    · intro p _ hp y hy hcomm
      rw [hvq] at hcomm
      exact loc2OK_of_commute3 hp hN hNo hy hcomm
  -- the table entry
  set r := mapH (Int.castRingHom (ZMod 4)) ωZ with hrdef
  obtain ⟨e, he, her⟩ := tab3_complete r.a0 r.a1 r.a2 r.a3
    (by show ((2 * c' + 1 : ℤ) : ZMod 4) = 1 ∨ ((2 * c' + 1 : ℤ) : ZMod 4) = 3
        push_cast; exact zmod4_odd_cases _)
    (by show 2 * ((c' + 1 : ℤ) : ZMod 4) = 1 + ((2 * c' + 1 : ℤ) : ZMod 4)
        push_cast; ring)
  have her' : e.r = r := her
  -- merges
  have hM0 : ∀ t, twoRep v t ∈ DC n τ (twoRep v (e.root t)) := by
    intro t
    obtain ⟨hm1, hm2, -⟩ := tab3_merge e he t
    set w := e.wit.getD (idx8 t) (0, 0, 0, 0)
    set μ := unitList.getD w.2.2.1.val ⟨1, 0, 0, 0⟩ with hμdef
    have hμ1 : nrdH μ = 1 := unitList_nrdH μ (getD_mem_unitList _)
    have hsg : (sg w.2.2.2 : ℤ) ^ 2 = 1 := by have := sg_sq w.2.2.2; exact_mod_cast this
    set αZ : H4 ℤ := ⟨(w.1.val : ℤ) + (w.2.1.val : ℤ) * ωZ.a0, (w.2.1.val : ℤ) * ωZ.a1,
      (w.2.1.val : ℤ) * ωZ.a2, (w.2.1.val : ℤ) * ωZ.a3⟩ with hαZ
    have hα4 : mapH (Int.castRingHom (ZMod 4)) αZ = alpha4 e.r w.1 w.2.1 := by
      rw [her', hrdef]; simp only [hαZ, mapH, alpha4, map_add, map_mul, eq_intCast, natCast_val_zmod4]
    set A : H4 ℤ := smulH (sg w.2.2.2) (mulH μ (βZ (e.root t))) with hAdef
    set B : H4 ℤ := mulH (βZ t) αZ with hBdef
    have hA4 : mapH (Int.castRingHom (ZMod 4)) A = rhoBeta4 w.2.2.1 w.2.2.2 (e.root t) := rfl
    have hE : mapH (Int.castRingHom (ZMod 4))
        (mulH (starH A) ⟨B.a0 - A.a0, B.a1 - A.a1, B.a2 - A.a2, B.a3 - A.a3⟩) = ⟨0, 0, 0, 0⟩ := by
      rw [mapH_mulH, mapH_starH, mapH_sub]
      have hB4 : mapH (Int.castRingHom (ZMod 4)) B =
          mulH (mapH (Int.castRingHom (ZMod 4)) (βZ t)) (alpha4 e.r w.1 w.2.1) := by
        rw [hBdef, mapH_mulH, hα4]
      show mulH (starH (mapH (Int.castRingHom (ZMod 4)) A))
        (sub4 (mapH (Int.castRingHom (ZMod 4)) B) (mapH (Int.castRingHom (ZMod 4)) A)) = _
      rw [hA4, hB4]; exact hm1
    obtain ⟨Cc, hCc⟩ := exists_smulH_of_mod hE
    have hα0 : (hurZ αZ : ℍ[ℚ]) ≠ 0 := by
      intro h0
      have := congrArg Quaternion.normSq h0
      rw [normSq_hurZ, map_zero] at this
      exact nrdH_odd_of_mod4 (by rw [hα4]; exact hm2) (by exact_mod_cast this)
    have hαω : (hurZ αZ : ℍ[ℚ]) = ((w.1.val : ℚ)) • 1 + ((w.2.1.val : ℚ)) • ω := by
      apply hc_injective
      rw [hc_hurZ, hc_add, hc_smul, hc_smul, hc_one, hωdef, hc_hurZ]
      ext <;> simp [hαZ, mapH]
    have hωc : ω * τ (sqrtNeg n) = τ (sqrtNeg n) * ω := by
      rw [hωv, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one]
    have hαc : (hurZ αZ : ℍ[ℚ]) * τ (sqrtNeg n) = τ (sqrtNeg n) * hurZ αZ := by
      rw [hαω, add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
        one_mul, mul_one, hωc]
    have hρ : Quaternion.normSq (hurZ (smulH (sg w.2.2.2) μ) : ℍ[ℚ]) = 1 := by
      rw [normSq_hurZ, nrdH_smulH, hμ1, hsg]; simp
    have hρ0 : (hurZ (smulH (sg w.2.2.2) μ) : ℍ[ℚ]) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hρ; exact zero_ne_one hρ
    have hAq : hurZ (smulH (sg w.2.2.2) μ) * twoRepQ (e.root t) = (hurZ A : ℍ[ℚ]) := by
      rw [twoRepQ_eq, hAdef, hurZ_smulH, hurZ_smulH, hurZ_mulH, smul_mul_assoc]
    have hBq : twoRepQ t * hurZ αZ = (hurZ B : ℍ[ℚ]) := by rw [twoRepQ_eq, hBdef, hurZ_mulH]
    have hnA : nrdH A = 2 ^ 0 * nrdH (βZ (e.root t)) := by
      rw [hAdef, nrdH_smulH, nrdH_mulH, hμ1, hsg]; ring
    have hloc := local_merge_cond (p := (Pw v : ℕ)) (Pw_eq_two hv) A B Cc 0 _ (nrdH_βZ_odd _) hnA
      (by rw [hCc]; norm_num)
    rw [← hAq, ← hBq] at hloc
    exact twoRep_mem_DC_of hv hα0 hαc hρ0 (isHurZ_hurZ _) (Or.inl hρ) hloc
  -- the obstruction
  have hS0 : twoRep v e.p1 ∉ DC n τ (twoRep v e.rc) := by
    refine twoRep_not_mem_DC hv C hH ?_
    intro p _ hp q nn k hq hk y hy heq
    subst hp
    obtain ⟨cc, hcc, u, rfl, hu, hnu, hR⟩ := hy
    rw [qp_hurZ] at hR
    obtain ⟨μ, hμ, X, Y, hrel⟩ := two_adic_b1 q hq nn k hk (βZ e.p1) (βZ e.rc) ωZ (nrdH_βZ_odd _)
      (nrdH_βZ_odd _) cc hcc u hnu hR heq
    exact tab3_sep e he μ hμ X Y (by rw [her']; exact hrel)
  -- assembly
  have hroot : ∀ t t', e.F t = e.F t' → e.root t = e.root t' := by
    intro t t' h
    simp only [E3.F, E3.root] at h ⊢
    split_ifs at h ⊢ <;> first | rfl | (exfalso; norm_num at h)
  have hFv : ∀ t, e.F t = -3 ∨ e.F t = 1 := fun t => by
    simp only [E3.F]; split_ifs <;> simp
  have hrootF : ∀ t, e.F (e.root t) = e.F t := by
    intro t
    have h := tab3_sums e he
    simp only [E3.root]
    split_ifs with h1
    · rw [h.2.2.2]; simp only [E3.F, if_pos h1]
    · rw [h.2.2.1]; simp only [E3.F, if_neg h1]
  obtain ⟨hs1, hs2, hs3, hs4⟩ := tab3_sums e he
  refine testVector_of_partition hv e.F (exists_twoRep τ hv) ?_ ?_ ⟨hs1, hs2⟩ ?_ ⟨e.rc, by rw [hs3]; norm_num⟩
  · intro t t' h
    have h2 := hM0 t'
    rw [← hroot t t' h] at h2
    exact DC_trans (DC_symm h2) (hM0 t)
  · intro t t' h hmem
    have h4 : twoRep v (e.root t) ∈ DC n τ (twoRep v (e.root t')) :=
      DC_trans (DC_trans (hM0 t') hmem) (DC_symm (hM0 t))
    simp only [E3.root] at h4
    simp only [E3.F] at h
    split_ifs at h4 h with h1 h2
    · exact h rfl
    · exact hS0 (DC_symm h4)
    · exact hS0 h4
    · exact h rfl
  · intro G hG hGs _
    exact rank1_two e.F G hFv hs1 hs3 hG hGs

end ZInQ.Contrib.HfxProof
