import ZInQKernel.Contrib.OneProof.RC.Moving.Interface

/-!
# Lane RC4 (moving character): Proposition `ex:arith-moving-character`, assembled

Manuscript (11/5 version), tex 3500–3702: **One moving character for the complete active list.**

`moving_character` is Elliot's proposition, proved in Lean (`PROVED` relative to the interface
`MovingSetting`, whose fields are the `PRINT`/`GLUE` inputs with locators) by Elliot's steps in
Elliot's order:

1. (4.4a), tex 3545–3563: the prescribed multipliers `ζ^{−∑_j m_j^{(a)} w_j}` respect every
   Kummer relation (`kummer_prescription_respects`), so the Kummer pairing gives `σ₀ ∈ G_{F_∞}`;
2. (4.4c), tex 3597–3633: `Γ_{8d+10} ⊂ ρ_T(G_{L_∞})` (`four_four_c`; `G_{F_∞}/G_{L_∞}` is
   abelian because the Kummer multipliers embed it in an abelian group);
3. (4.4d), tex 3635–3668: a modification `σ ∈ σ₀ G_{L_∞}` with `v₂(2 ± tr ρ_T(σ)) ≤ c_E`,
   `c_E = 16d + 21` (`tate_trace_control`);
4. tex 3670–3679: Chebotarev with `B' = max(B, n, c_E + 1) > c_E`;
5. (4.4b), tex 3565–3595, 3677–3684: the character `ξ` (`ringClass_extends_iff`), surjective on
   inertia, trivial at `2N`, value one at each active orientation and minus one at its conjugate;
6. tex 3686–3693: `v₂(2 ± a_r) ≤ c_E` and `v₂ det(1 ± Fr_r) = v₂(1 ± a_r + r) ≤ c_E`
   (`frobenius_bounds`).

`moving_character_Psi` adds tex 3694–3701: for `n ≥ 2i`, `Ψ_i = (1+t)^{ξ_i}` is a character of
`Gal(H_{r_i}/K)` with values in `A_i^×`, value `1 + t` on an inertia element and on each active
oriented Frobenius; avoiding the earlier primes gives distinct `r_i`.

The constant `c_E = 16d + 21` depends only on the fixed Tate image `T` (through `T.d`), not on
`K`, `n`, `B`, the avoidance set or the active list, exactly as the proposition states.
-/

open Matrix
open scoped MatrixGroups commutatorElement

namespace ZInQ.Manuscript.RC.Moving

variable {T : TateImage} {n : ℕ}

/-- The Kummer layer is abelian: `[G_{F_∞}, G_{F_∞}] ⊂ G_{L_∞}` (tex 3624–3625). -/
theorem MovingSetting.commutator_le (M : MovingSetting T n) : ⁅M.GF, M.GF⁆ ≤ M.HL := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  have hk : M.kum ⁅(⟨g₁, h₁⟩ : M.GF), ⟨g₂, h₂⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  have := M.mem_HL_of_kum _ hk
  simpa [commutatorElement_def] using this

/-- **Proposition `ex:arith-moving-character`** (tex 3500–3702; `PROVED` from the interface).
For every `B` and finite avoidance set `S` there is a good split prime `r ∉ S` with
`r ≡ 1 (mod 2^B)` and a character `ξ : Gal(H_r/K) → ℤ/2^n` that is surjective on inertia at `r`,
trivial on the decomposition groups at the chosen primes over `2N` and their conjugates, takes
value one at every prescribed active orientation (and minus one at its conjugate), and satisfies
`v₂(2 ± a_r) ≤ c_E`, `v₂(1 ± a_r + r) ≤ c_E` (that is `v₂ det(1 ± Fr_r) ≤ c_E`, see
`det_one_add_bound`) and `v₂(a_r − 2χ) ≤ c_E` for `χ = ±1`, with `c_E = 16d + 21`.
("Infinitely many": `S` is arbitrary.) -/
theorem moving_character (M : MovingSetting T n) (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE T.d + 1) ∣ 2 + M.ap r ∧ ¬ (2 : ℤ) ^ (cE T.d + 1) ∣ 2 - M.ap r ∧
        ¬ (2 : ℤ) ^ (cE T.d + 1) ∣ 1 + M.ap r + r ∧
        ¬ (2 : ℤ) ^ (cE T.d + 1) ∣ 1 - M.ap r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) → ¬ (2 : ℤ) ^ (cE T.d + 1) ∣ M.ap r - 2 * χ := by
  classical
  -- weights and the prescribed multipliers (4.4a)
  set w : Fin M.s → ZMod (2 ^ n) := fun j => if M.act j then 1 else 0 with hw
  set φ : Fin M.t → ZMod (2 ^ n) := fun a => -∑ j, (M.m a j : ZMod (2 ^ n)) * w j with hφ_def
  have hφ : ∀ b ∈ M.KR, ∑ a, (b a : ZMod (2 ^ n)) * φ a = 0 := by
    intro b hb
    have := kummer_prescription_respects n M.m M.act b (M.KR_val b hb)
    simpa [hφ_def, hw] using this
  -- the Kummer automorphism, lifted to `σ₀ ∈ G_{F_∞}`
  obtain ⟨σ₀, hσ₀⟩ := M.kum_surj φ hφ
  -- (4.4c) + (4.4d)
  obtain ⟨σ, hσF, hσL, h1, h2⟩ := tate_trace_control T.ρ M.GF M.HL T.d T.serre M.GF_index
    M.commutator_le M.HL_le σ₀ σ₀.2
  -- `σ` preserves every prescribed radical multiplier
  have hkum : M.kum ⟨σ, hσF⟩ = Multiplicative.ofAdd φ := by
    have hn : (⟨(σ₀ : T.G)⁻¹ * σ, M.GF.mul_mem (M.GF.inv_mem σ₀.2) hσF⟩ : M.GF) =
        σ₀⁻¹ * ⟨σ, hσF⟩ := rfl
    have hL := M.kum_of_mem_HL ⟨(σ₀ : T.G)⁻¹ * σ, M.GF.mul_mem (M.GF.inv_mem σ₀.2) hσF⟩ hσL
    rw [hn, map_mul, map_inv, hσ₀] at hL
    have := congrArg (fun z => Multiplicative.ofAdd φ * z) hL
    simpa using this
  -- Chebotarev, with `B' = max(B, n, c_E + 1)`
  set B' := max (max B n) (cE T.d + 1) with hB'
  obtain ⟨r, v, hrS, hrp, hgood, hr1, htr, hres⟩ := M.cheb ⟨σ, hσF⟩ B' S
  have hBB' : B ≤ B' := le_trans (le_max_left _ _) (le_max_left _ _)
  have hnB' : n ≤ B' := le_trans (le_max_right _ _) (le_max_left _ _)
  have hcB' : cE T.d + 1 ≤ B' := le_max_right _ _
  -- (4.4b): the character `ξ`
  have hgen : ∀ c : M.Cl, ∃ v : Fin M.s → ℤ, ∑ j, v j • M.π r (M.q r j) = c := by
    intro c
    obtain ⟨v, hv⟩ := M.cls_gen c
    exact ⟨v, by simpa [M.π_q r hgood] using hv⟩
  have hR : ∀ v : Fin M.s → ℤ, ∑ j, v j • M.π r (M.q r j) = 0 →
      ∃ b : Fin M.t → ℤ, v = ∑ a, b a • M.m a := by
    intro v hv
    exact M.m_span v (by simpa [M.π_q r hgood] using hv)
  have hcond : ∀ a, M.κ r v (M.x r v a) = -∑ j, M.m a j • w j := by
    intro a
    rw [hres a, hkum]
    simp [hφ_def, zsmul_eq_mul]
  obtain ⟨ξ, hξq, hξδ⟩ := (ringClass_extends_iff (M.δ r v) (M.π r) (M.δ_inj r hgood v)
    (M.exact r hgood v) (M.q r) hgen M.m hR (M.x r v) (M.rel r hgood v) (M.κ r v) w).2 hcond
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ :=
    frobenius_bounds (M.ap r) r (tr (T.ρ σ)) (cE T.d) B' hcB' htr hr1 h1 h2
  refine ⟨r, hrS, hrp, hgood, (pow_dvd_pow 2 hBB').trans hr1, ξ, ?_, ?_, ?_,
    hb1, hb2, hb3, hb4, hb5⟩
  · -- surjective on inertia (local reciprocity; `κ_r` is onto since `r ≡ 1 (mod 2^n)`)
    intro y
    obtain ⟨u, hu⟩ := M.κ_surj r hgood v ((pow_dvd_pow 2 hnB').trans hr1) y
    refine ⟨M.δ r v u, by rw [M.inertia_eq r hgood v]; exact ⟨u, rfl⟩, ?_⟩
    rw [hξδ, hu]
  · -- trivial on the decomposition groups at `2N`: unramified with Frobenius value zero
    intro j hj z hz
    have hw0 : w j = 0 := by simp [hw, M.act_not_over2N j |>.mt (not_not.2 hj)]
    have hq0 : M.q r j ∈ ξ.ker := by rw [AddMonoidHom.mem_ker, hξq, hw0]
    have hqb0 : M.qbar r j ∈ ξ.ker := by
      rw [AddMonoidHom.mem_ker, conj_value ξ _ _ (M.qbar_eq r hgood j), hξq, hw0, neg_zero]
    have hle : M.decomp r j ⊔ M.decompBar r j ≤ ξ.ker := by
      rw [M.decomp_eq r hgood j, M.decompBar_eq r hgood j]
      exact sup_le (AddSubgroup.zmultiples_le.2 hq0) (AddSubgroup.zmultiples_le.2 hqb0)
    exact hle hz
  · -- value one at the active orientations; conjugation negates
    intro j hj
    have hw1 : w j = 1 := by simp [hw, hj]
    refine ⟨by rw [hξq, hw1], ?_⟩
    rw [conj_value ξ _ _ (M.qbar_eq r hgood j), hξq, hw1]

/-- `v₂ det(1 ± Fr_r) ≤ c_E` (tex 3690–3691): for any matrix `F` over `ℤ₂` with `tr F = a_r` and
`det F = r` (the Frobenius at `r` on `T₂E`, [Silverman, V.2.3.1]), `det(1 ± F) = 1 ± a_r + r`, so
the integer bounds of `moving_character` give the determinant bounds. -/
theorem det_one_add_bound (c : ℕ) (ar r : ℤ) (F : Matrix (Fin 2) (Fin 2) ℤ_[2])
    (htr : F.trace = ar) (hdet : F.det = r)
    (h1 : ¬ (2 : ℤ) ^ (c + 1) ∣ 1 + ar + r) (h2 : ¬ (2 : ℤ) ^ (c + 1) ∣ 1 - ar + r) :
    v2Le (1 + F).det c ∧ v2Le (1 - F).det c := by
  refine ⟨?_, ?_⟩
  · rw [det_one_add, htr, hdet, v2Le]
    have : (1 + (ar : ℤ_[2]) + (r : ℤ_[2])) = ((1 + ar + r : ℤ) : ℤ_[2]) := by push_cast; ring
    rw [this, int_two_pow_dvd_iff]
    exact h1
  · rw [det_one_sub, htr, hdet, v2Le]
    have : (1 - (ar : ℤ_[2]) + (r : ℤ_[2])) = ((1 - ar + r : ℤ) : ℤ_[2]) := by push_cast; ring
    rw [this, int_two_pow_dvd_iff]
    exact h2

/-- "Infinitely many" (tex 3502–3503), in set form: the primes `r` of `moving_character` form an
infinite set. -/
theorem moving_character_infinite (M : MovingSetting T n) (B : ℕ) :
    Set.Infinite {r : ℕ | r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE T.d + 1) ∣ 2 + M.ap r ∧ ¬ (2 : ℤ) ^ (cE T.d + 1) ∣ 2 - M.ap r ∧
        ¬ (2 : ℤ) ^ (cE T.d + 1) ∣ 1 + M.ap r + r ∧
        ¬ (2 : ℤ) ^ (cE T.d + 1) ∣ 1 - M.ap r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) → ¬ (2 : ℤ) ^ (cE T.d + 1) ∣ M.ap r - 2 * χ} := by
  intro hfin
  obtain ⟨r, hrS, hrp, hgood, hr1, hξ⟩ := moving_character M B hfin.toFinset
  exact hrS (hfin.mem_toFinset.2 ⟨hrp, hgood, hr1, hξ⟩)

/-- **The finite characters `Ψ_i`** (tex 3694–3701; `PROVED` from the interface).  Take
`n = n_i ≥ 2i`.  For every finite set `S` (the earlier primes `r_1, …, r_{i−1}`
and the avoidance set) there is `r_i ∉ S` with the properties of `moving_character` and a
character `Ψ_i = (1+t)^{ξ_i}` of `Gal(H_{r_i}/K)` with values in `A_i^×`, `A_i = (ℤ/2^i)[t]/(t^i)`,
taking the value `1 + t` on an inertia element and on every active oriented Frobenius. -/
theorem moving_character_Psi (i : ℕ) (hn : 2 * i ≤ n) (M : MovingSetting T n) (B : ℕ)
    (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ¬ (2 : ℤ) ^ (cE T.d + 1) ∣ 2 + M.ap r ∧ ¬ (2 : ℤ) ^ (cE T.d + 1) ∣ 2 - M.ap r ∧
      ∃ Ψ : M.P r →+ Additive (Acoef i)ˣ,
        (∃ z ∈ M.inertia r, ((Additive.toMul (Ψ z) : (Acoef i)ˣ) : Acoef i) = 1 + tA i) ∧
        (∀ j, M.act j → ((Additive.toMul (Ψ (M.q r j)) : (Acoef i)ˣ) : Acoef i) = 1 + tA i) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, Ψ z = 0) := by
  obtain ⟨r, hrS, hrp, hgood, hr1, ξ, hin, h2N, hact, hb1, hb2, -, -, -⟩ :=
    moving_character M B S
  obtain ⟨ψ, hψ⟩ := exists_psi i n hn
  refine ⟨r, hrS, hrp, hgood, hr1, hb1, hb2, ψ.comp ξ, ?_, ?_, ?_⟩
  · obtain ⟨z, hz, hξz⟩ := hin 1
    refine ⟨z, hz, ?_⟩
    rw [AddMonoidHom.comp_apply, hξz]
    have := hψ 1
    simpa using this
  · intro j hj
    rw [AddMonoidHom.comp_apply, (hact j hj).1]
    have := hψ 1
    simpa using this
  · intro j hj z hz
    rw [AddMonoidHom.comp_apply, h2N j hj z hz, map_zero]

end ZInQ.Manuscript.RC.Moving
