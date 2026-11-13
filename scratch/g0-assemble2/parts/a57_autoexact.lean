/-! ## g0-assemble2: aut-o-finite §9 (scratch/aut-o-finite/AutOFinite.lean lines 794-1036, verbatim; its §7-§8 are
mobius-glue's, in part a55) -/
/-! ## §9 The explicit computation: `Aut(𝒪)/Inn(𝒪^×)` has exactly four classes

Representatives: conjugation by `1, i, j, ij` (`rep 0, …, rep 3`). Every ring automorphism of `𝒪`
is `v · rep k · v⁻¹` for some `k` and `v ∈ 𝒪^×` (`rep_cover`), and `rep k`, `rep l` are conjugate
by a unit of `𝒪` only if `k = l` (`rep_distinct`: a conjugating unit would give
`nrd(t_k) = ± r² nrd(t_l)` with `r ∈ ℚ`, impossible as `nrd(1, i, j, ij) = 1, -2, 3, -6`). -/

namespace LeafQM

namespace AV

namespace Pin

namespace Exact

open NormO AutOExt

/-- The reduced norm of `B = (2, -3)_ℚ`. -/
def nrd (x : B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

theorem nrd_mul (x y : B) : nrd (x * y) = nrd x * nrd y := by
  simp [nrd]; ring

theorem nrd_algebraMap (q : ℚ) : nrd (algebraMap ℚ B q) = q ^ 2 := by
  simp [nrd, QuaternionAlgebra.algebraMap_eq]

theorem nrd_ofInt (n : Fin 4 → ℤ) : nrd (ofInt n) =
    ((n 0 ^ 2 + n 0 * n 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 + n 2 ^ 2 - 2 * n 3 ^ 2 : ℤ) : ℚ) := by
  simp [nrd, ofInt]; ring

theorem not_sq (s : ℚ) (c : ℤ) (hc : ¬ IsSquare c) (h : s ^ 2 = c) : False := by
  have h1 : IsSquare (c : ℚ) := ⟨s, by rw [← h]; ring⟩
  rw [Rat.isSquare_iff] at h1
  simp at h1
  exact hc h1

/-- An element of `B` commuting with `i` and `j` is a scalar. -/
theorem comm_scalar (w : B) (hi : w * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * w)
    (hj : w * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * w) : w = algebraMap ℚ B w.re := by
  have h1 := congrArg QuaternionAlgebra.imJ hi
  have h2 := congrArg QuaternionAlgebra.imK hi
  have h3 := congrArg QuaternionAlgebra.imI hj
  have h4 := congrArg QuaternionAlgebra.imK hj
  simp at h1 h2 h3 h4
  ext <;> simp [QuaternionAlgebra.algebraMap_eq] <;> linarith

/-- The norm of a unit of `𝒪` is `±1`. -/
theorem nrd_unit (v : Oˣ) : nrd ((v : O) : B) = 1 ∨ nrd ((v : O) : B) = -1 := by
  obtain ⟨n, hn⟩ := (v : O).2
  obtain ⟨m, hm⟩ := ((v⁻¹ : Oˣ) : O).2
  have h1 : ((v : O) : B) * (((v⁻¹ : Oˣ) : O) : B) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have h2 := congrArg nrd h1
  rw [nrd_mul, hn, hm, nrd_ofInt, nrd_ofInt] at h2
  have h3 : nrd 1 = 1 := by simp [nrd]
  rw [h3] at h2
  have h4 := Int.eq_one_or_neg_one_of_mul_eq_one (by exact_mod_cast h2)
  rw [hn, nrd_ofInt]
  rcases h4 with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

theorem isNorm_one : IsNorm 1 := by
  intro a ha
  exact ⟨by simpa using ha, by simpa using ha⟩

/-- Conjugation `a ↦ u a u⁻¹` by a unit `u ∈ B^×` normalizing `𝒪`, as a ring automorphism. -/
def conjO (u : Bˣ) (hu : IsNorm u) : O ≃+* O where
  toFun a := ⟨(u : B) * a * ((u⁻¹ : Bˣ) : B), (hu a a.2).1⟩
  invFun a := ⟨((u⁻¹ : Bˣ) : B) * a * u, (hu a a.2).2⟩
  left_inv a := by apply Subtype.ext; simp [mul_assoc]
  right_inv a := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]
  map_add' a b := by apply Subtype.ext; simp [mul_add, add_mul]

theorem conjO_apply (u : Bˣ) (hu : IsNorm u) (a : O) :
    ((conjO u hu a : O) : B) = (u : B) * a * ((u⁻¹ : Bˣ) : B) := rfl

/-- The representatives `1, i, j, ij` of `N(𝒪)/ℚ^×𝒪^×`. -/
def tt : Fin 4 → Bˣ := ![1, ui, uj, ui * uj]

theorem tt_isNorm (k : Fin 4) : IsNorm (tt k) := by
  fin_cases k
  exacts [isNorm_one, isNorm_ui, isNorm_uj, isNorm_ui.mul isNorm_uj]

/-- The four representatives of `Aut(𝒪)/Inn(𝒪^×)`: conjugation by `1, i, j, ij`. -/
def rep (k : Fin 4) : O ≃+* O := conjO (tt k) (tt_isNorm k)

/-- The reduced norms `1, -2, 3, -6` of `1, i, j, ij`. -/
def N : Fin 4 → ℤ := ![1, -2, 3, -6]

theorem nrd_tt (k : Fin 4) : nrd (tt k : B) = (N k : ℚ) := by
  fin_cases k
  · simp [tt, N, nrd]
  · change nrd (ofInt ei) = _
    simp [nrd_ofInt, ei, N]
  · change nrd (ofInt ej) = _
    simp [nrd_ofInt, ej, N]
  · change nrd (ofInt ei * ofInt ej) = _
    rw [nrd_mul]
    simp [nrd_ofInt, ei, ej, N]; norm_num

theorem tt_of_T (t : Bˣ) (ht : t ∈ T) : ∃ k, tt k = t := by
  rcases (T_mem_iff t).1 ht with rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

/-- The concrete normalizer statement (the body of `NormO.normalizerFinite`, with `T` named). -/
theorem normalizer_rep (u : Bˣ) (hu : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O) :
    ∃ t ∈ T, ∃ v : Oˣ, ∃ q : ℚ, q ≠ 0 ∧ (u : B) = algebraMap ℚ B q * ((v : O) : B) * (t : B) := by
  obtain ⟨m, hm, ⟨n, hn⟩⟩ := AutOExt.exists_nat_smul_mem (u : B)
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu0 : ((sc _ hm0 * u : Bˣ) : B) = ofInt n := by
    change algebraMap ℚ B m * u = _
    rw [← Algebra.smul_def]; exact hn
  have hN : IsNorm u := by
    intro a ha
    refine ⟨(hu a).1 ha, (hu _).2 ?_⟩
    simpa [mul_assoc] using ha
  obtain ⟨q, hq, v, t, ht, he⟩ := descent _ (sc _ hm0 * u) n hu0 rfl ((isNorm_sc _ hm0).mul hN)
  refine ⟨t, ht, v, (m : ℚ)⁻¹ * q, mul_ne_zero (inv_ne_zero hm0) hq, ?_⟩
  have : (u : B) = algebraMap ℚ B ((m : ℚ)⁻¹) * ((sc _ hm0 * u : Bˣ) : B) := by
    change _ = _ * (algebraMap ℚ B m * u)
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hm0, map_one, one_mul]
  rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

theorem key2 {R : Type*} [Ring R] (x y w w' c c' t t' : R) (hww : w * w' = 1)
    (hcc : c' * c = 1) (htt : t * t' = 1) (hc : c * x = x * c)
    (h : x * (c * w * t) = c * w * t * y) : x = w * (t * y * t') * w' := by
  have h1 : x * w * t = w * t * y := by
    calc x * w * t = c' * (c * x) * w * t := by rw [← mul_assoc, hcc, one_mul]
      _ = c' * (x * (c * w * t)) := by rw [hc]; simp only [mul_assoc]
      _ = c' * (c * w * t * y) := by rw [h]
      _ = w * t * y := by simp only [← mul_assoc]; rw [hcc, one_mul]
  calc x = x * (w * (t * t') * w') := by rw [htt, mul_one, hww, mul_one]
    _ = x * w * t * t' * w' := by simp only [mul_assoc]
    _ = w * t * y * t' * w' := by rw [h1]
    _ = w * (t * y * t') * w' := by simp only [mul_assoc]

/-- **Every automorphism of `𝒪` is `v · rep k · v⁻¹`** for some `k` and some `v ∈ 𝒪^×`. -/
theorem rep_cover (α : O ≃+* O) : ∃ k : Fin 4, ∃ v : Oˣ, ∀ a : O,
    α a = (v : O) * rep k a * ((v⁻¹ : Oˣ) : O) := by
  obtain ⟨u, hu⟩ := conj_of_skolem α
  have hback : ∀ b : B, extFun α.symm (extFun α b) = b := fun b =>
    congrArg (fun φ : B →ₐ[ℚ] B => φ b) (extAlgHom_symm_comp α)
  have hnorm : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    rw [← hu]
    constructor
    · intro ha
      rw [show a = ((⟨a, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α _).2
    · intro ha
      rw [← hback a, show extFun α a = ((⟨_, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α.symm _).2
  obtain ⟨t, ht, v, q, hq, huq⟩ := normalizer_rep u hnorm
  obtain ⟨k, rfl⟩ := tt_of_T t ht
  have hrel : ∀ a : O, ((α a : O) : B) * u = u * a := by
    intro a
    rw [← extFun_coe, hu, Units.inv_mul_cancel_right]
  refine ⟨k, v, fun a => Subtype.ext ?_⟩
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul]
  change _ = ((v : O) : B) * ((tt k : B) * a * (((tt k)⁻¹ : Bˣ) : B)) * (((v⁻¹ : Oˣ) : O) : B)
  have hvv : ((v : O) : B) * (((v⁻¹ : Oˣ) : O) : B) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have hcc : algebraMap ℚ B q⁻¹ * algebraMap ℚ B q = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hq, map_one]
  have h := hrel a
  rw [huq] at h
  exact key2 _ _ _ _ _ _ _ _ hvv hcc (Units.mul_inv _) (Algebra.commutes q _) h

/-- **The four representatives are pairwise non-conjugate by units of `𝒪`.** -/
theorem rep_distinct (k l : Fin 4) (v : Oˣ)
    (h : ∀ a : O, rep k a = (v : O) * rep l a * ((v⁻¹ : Oˣ) : O)) : k = l := by
  set V : B := ((v : O) : B) with hVdef
  set V' : B := (((v⁻¹ : Oˣ) : O) : B) with hV'def
  have hVV' : V * V' = 1 := by
    rw [hVdef, hV'def, ← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have hV'V : V' * V = 1 := by
    rw [hVdef, hV'def, ← MulMemClass.coe_mul, Units.inv_mul]; rfl
  have hV'Vx : ∀ X : B, V' * (V * X) = X := fun X => by rw [← mul_assoc, hV'V, one_mul]
  set P : B := (tt k : B) with hP
  set P' : B := (((tt k)⁻¹ : Bˣ) : B) with hP'
  set Q : B := (tt l : B) with hQ
  set Q' : B := (((tt l)⁻¹ : Bˣ) : B) with hQ'
  have hP'P : P' * P = 1 := Units.inv_mul _
  have hQ'Qx : ∀ X : B, Q' * (Q * X) = X := fun X => by
    rw [← mul_assoc, show Q' * Q = 1 from Units.inv_mul _, one_mul]
  have hQQ'x : ∀ X : B, Q * (Q' * X) = X := fun X => by
    rw [← mul_assoc, show Q * Q' = 1 from Units.mul_inv _, one_mul]
  have hVV'x : ∀ X : B, V * (V' * X) = X := fun X => by rw [← mul_assoc, hVV', one_mul]
  have hcomm : ∀ a ∈ O, (Q' * V' * P) * a = a * (Q' * V' * P) := by
    intro a ha
    have e : P * a * P' = V * (Q * a * Q') * V' := by
      have := congrArg Subtype.val (h ⟨a, ha⟩)
      rw [MulMemClass.coe_mul, MulMemClass.coe_mul] at this
      exact this
    calc Q' * V' * P * a = Q' * V' * (P * a * P') * P := by
          simp only [mul_assoc, hP'P, mul_one]
      _ = Q' * V' * (V * (Q * a * Q') * V') * P := by rw [e]
      _ = a * (Q' * V' * P) := by simp only [mul_assoc, hV'Vx, hQ'Qx]
  set W := Q' * V' * P with hW
  have hWs : W = algebraMap ℚ B W.re :=
    comm_scalar W (hcomm _ (mem_O_of_int 0 1 0 0)) (hcomm _ (mem_O_of_int 0 0 1 0))
  have hPW : P = V * Q * W := by
    rw [hW]; simp only [mul_assoc, hQQ'x, hVV'x]
  have e1 : (N k : ℚ) = nrd V * N l * W.re ^ 2 := by
    rw [← nrd_tt, ← nrd_tt, ← nrd_algebraMap, ← hWs, ← nrd_mul, ← nrd_mul]
    exact congrArg nrd hPW
  have hmain : ∀ ε : ℤ, nrd V = ε → ε ^ 2 = 1 →
      (W.re * N l) ^ 2 = ((ε * N k * N l : ℤ) : ℚ) := by
    intro ε hε hε2
    have hε2' : (ε : ℚ) ^ 2 = 1 := by exact_mod_cast hε2
    push_cast
    rw [e1, hε]
    linear_combination (-(W.re ^ 2 * (N l : ℚ) ^ 2)) * hε2'
  rcases nrd_unit v with h1 | h1
  · have hm := hmain 1 (by rw [← hVdef] at h1; simpa using h1) (by norm_num)
    fin_cases k <;> fin_cases l <;>
      first | rfl | exact (not_sq _ _ (by decide +kernel) hm).elim
  · have hm := hmain (-1) (by rw [← hVdef] at h1; simpa using h1) (by norm_num)
    fin_cases k <;> fin_cases l <;>
      first | rfl | exact (not_sq _ _ (by decide +kernel) hm).elim

/-- **Explicit computation of `Aut(𝒪)/Inn(𝒪^×)`: exactly four classes**, represented by
conjugation by `1, i, j, ij`. -/
theorem autO_mod_inner_exact : ∃ t : Fin 4 → (O ≃+* O),
    (∀ α : O ≃+* O, ∃ k, ∃ v : Oˣ, ∀ a : O, α a = (v : O) * t k a * ((v⁻¹ : Oˣ) : O)) ∧
    ∀ k l, (∃ v : Oˣ, ∀ a : O, t k a = (v : O) * t l a * ((v⁻¹ : Oˣ) : O)) → k = l :=
  ⟨rep, rep_cover, fun k l ⟨v, hv⟩ => rep_distinct k l v hv⟩

/-- `AutOInnerFinite` again, from the explicit computation. -/
theorem autOInnerFinite' : AutOInnerFinite := by
  refine ⟨Set.range rep, Set.finite_range rep, fun α => ?_⟩
  obtain ⟨k, v, hv⟩ := rep_cover α
  exact ⟨rep k, ⟨k, rfl⟩, v, hv⟩

end Exact

end Pin

end AV

end LeafQM
