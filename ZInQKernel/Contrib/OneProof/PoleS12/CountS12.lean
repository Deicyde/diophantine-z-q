import ZInQKernel.Contrib.OneProof.PoleS12.Suff

/-!
# The dimension-three count following S12's `par:descent`

`dimThreeCount_S12 : LocalGoodUnram → DimThreeCount`. ELLIOT (supplement S12, `par:descent`,
lines 300–454). Compared with round 1's `dimThreeCount_of_local` (which takes the four
local-image Props `LocalTwo`, `LocalThree`, `LocalBad`, `LocalGood` as iff statements), every
necessary condition is now proved (`necAt_S12`), and sufficiency is needed only for the eight
candidate classes, which are torsion classes times squares at `2`, `3` and the primes of `ℓ`
(`cand_mem_S12`). The one remaining input is `LocalGoodUnram` (unramified classes are local at
a prime of good reduction), used only at primes `p ∤ 6ℓ` where `β` is a nonresidue.
-/

namespace ZInQ.Manuscript.PoleS12

open Matrix ZInQ.RouteK.Selmer ZInQ.Manuscript.PoleRC

/-- **The dimension-three count** (tex L1061–1074; S12 L300–454) from `LocalGoodUnram`. -/
theorem dimThreeCount_S12 (hG : LocalGoodUnram) : DimThreeCount := by
  classical
  intro ℓ β hℓ hsf h12 hβℓ hβ8 hM
  have hℓ0 : ℓ ≠ 0 := by omega
  have hβ0 : β ≠ 0 := by rintro rfl; rw [zero_dvd_iff] at hβℓ; omega
  obtain ⟨hb0, hb1, hKb, hker, -⟩ := id hM
  set ℓ' := ℓ / β with hℓ'
  have hℓ'd : ℓ' ∣ ℓ := Nat.div_dvd_of_dvd hβℓ
  have hℓeq : ℓ = β * ℓ' := (Nat.mul_div_cancel' hβℓ).symm
  have hcop : Nat.Coprime β ℓ' := (Nat.squarefree_mul_iff.mp (hℓeq ▸ hsf)).1
  have hindβ : ind ℓ (β : ℤ) = oneB ℓ β := by
    rw [ind_natCast_of_dvd hβ0]; rfl
  have hindℓ' : ind ℓ (ℓ' : ℤ) = 1 + oneB ℓ β := by
    rw [ind_natCast_of_dvd (Nat.pos_of_dvd_of_pos hℓ'd (by omega)).ne']
    funext i
    have hi : (i : ℕ) ∣ β * ℓ' := hℓeq ▸ supp_dvd i
    simp only [Pi.add_apply, Pi.one_apply, oneB]
    by_cases h : (i : ℕ) ∣ β
    · have : ¬ (i : ℕ) ∣ ℓ' := fun h' => (supp_prime i).one_lt.ne'
        ((Nat.Coprime.coprime_dvd_left h hcop).eq_one_of_dvd h')
      rw [if_neg this, if_pos h]; decide
    · have : (i : ℕ) ∣ ℓ' := ((supp_prime i).dvd_mul.mp hi).resolve_left h
      rw [if_pos this, if_neg h]; decide
  have hK1 : Kmat ℓ *ᵥ (1 + oneB ℓ β) = 0 := by
    rw [mulVec_add, kmat_mulVec_one, hKb, add_zero]
  have hind1 : ind ℓ ((1 : ℕ) : ℤ) = 0 := by rw [Nat.cast_one]; exact ind_one
  -- the 2-adic classes of `1, ℓ, β, ℓ/β`
  have hβsq : IsSquare (((β : ℕ) : ℤ) : ℚ_[2]) := by
    have := isSquare_intCast_div_two_adic (m := (β : ℤ)) (n := 1) odd_one
      (by rw [Int.ModEq]; omega)
    simpa using this
  have hβne : (((β : ℕ) : ℤ) : ℚ_[2]) ≠ 0 := by exact_mod_cast hβ0
  have h2one : SqEq (((1 : ℕ) : ℤ) : ℚ_[2]) 1 ∨ SqEq (((1 : ℕ) : ℤ) : ℚ_[2]) ((ℓ : ℕ) : ℚ_[2]) :=
    Or.inl (by simpa using SqEq.refl (1 : ℚ_[2]))
  have h2ell : SqEq (((ℓ : ℕ) : ℤ) : ℚ_[2]) 1 ∨ SqEq (((ℓ : ℕ) : ℤ) : ℚ_[2]) ((ℓ : ℕ) : ℚ_[2]) :=
    Or.inr (by simpa using SqEq.refl ((ℓ : ℕ) : ℚ_[2]))
  have h2β : SqEq (((β : ℕ) : ℤ) : ℚ_[2]) 1 ∨ SqEq (((β : ℕ) : ℤ) : ℚ_[2]) ((ℓ : ℕ) : ℚ_[2]) :=
    Or.inl (sqEq_one_of_isSquare hβne hβsq)
  have h2ℓ' : SqEq (((ℓ' : ℕ) : ℤ) : ℚ_[2]) 1 ∨
      SqEq (((ℓ' : ℕ) : ℤ) : ℚ_[2]) ((ℓ : ℕ) : ℚ_[2]) := by
    right
    refine (sqEq_of_eq_mul_sq (y := (((β : ℕ) : ℤ) : ℚ_[2])) ?_ hβne hβsq).symm
    have := congrArg (fun n : ℕ => (n : ℚ_[2])) hℓeq
    rw [this]; push_cast; ring
  -- the map and its image
  let T : Finset ((Supp ℓ → ZMod 2) × ZMod 2) :=
    ({0, 1, oneB ℓ β, 1 + oneB ℓ β} : Finset (Supp ℓ → ZMod 2)) ×ˢ ({0, 1} : Finset (ZMod 2))
  have hcand : ∀ c : ℕ, c ∣ ℓ → Kmat ℓ *ᵥ ind ℓ (c : ℤ) = 0 →
      (SqEq ((c : ℤ) : ℚ_[2]) 1 ∨ SqEq ((c : ℤ) : ℚ_[2]) ((ℓ : ℕ) : ℚ_[2])) → ∀ σ : Bool,
      ((if σ then 3 else 1) * (c : ℤ), if σ then -(ℓ : ℤ) else 1) ∈ SelM ℓ ∧
        (ind ℓ ((if σ then 3 else 1) * (c : ℤ)), sg (if σ then -(ℓ : ℤ) else 1)) =
          (ind ℓ (c : ℤ), if σ then 1 else 0) := by
    intro c hc hK h2 σ
    have hcpos : (0 : ℤ) < c := by
      have : 0 < c := Nat.pos_of_dvd_of_pos hc (by omega)
      exact_mod_cast this
    refine ⟨cand_mem_S12 hG hsf h12 hc hK h2 σ, ?_⟩
    cases σ with
    | false => simp [sg_one]
    | true =>
      simp only [if_true]
      rw [ind_three_mul h12 hcpos.ne', sg_negell hℓ]
  have hN := necAt_S12 hsf h12
  have himage : (fun ab : ℤ × ℤ => (ind ℓ ab.1, sg ab.2)) '' SelM ℓ = ↑T := by
    ext ⟨u, σ⟩
    simp only [T, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨a, b⟩, hab, he⟩
      obtain ⟨-, -, -, -, -, hKa⟩ := sel_necessary hN hsf h12 hM hab
      simp only [Prod.mk.injEq] at he
      rw [← he.1, ← he.2]
      exact ⟨hker _ hKa, PoleRC.zmod2_cases _⟩
    · rintro ⟨hu, hσ⟩
      have hget : ∀ c : ℕ, c ∣ ℓ → ind ℓ (c : ℤ) = u → Kmat ℓ *ᵥ u = 0 →
          (SqEq ((c : ℤ) : ℚ_[2]) 1 ∨ SqEq ((c : ℤ) : ℚ_[2]) ((ℓ : ℕ) : ℚ_[2])) →
          (u, σ) ∈ (fun ab : ℤ × ℤ => (ind ℓ ab.1, sg ab.2)) '' SelM ℓ := by
        intro c hc hcu hK h2
        rw [← hcu] at hK
        rcases hσ with rfl | rfl
        · exact ⟨_, (hcand c hc hK h2 false).1,
            (hcand c hc hK h2 false).2.trans (by rw [hcu]; rfl)⟩
        · exact ⟨_, (hcand c hc hK h2 true).1,
            (hcand c hc hK h2 true).2.trans (by rw [hcu]; rfl)⟩
      rcases hu with rfl | rfl | rfl | rfl
      · exact hget 1 (one_dvd _) hind1 (mulVec_zero _) h2one
      · exact hget ℓ dvd_rfl ind_ell kmat_mulVec_one h2ell
      · exact hget β hβℓ hindβ hKb h2β
      · exact hget ℓ' hℓ'd hindℓ' hK1 h2ℓ'
  have hinj := sel_injOn hN hsf h12 hM
  refine ⟨?_, ?_⟩
  · rw [← hinj.ncard_image, himage, Set.ncard_coe_finset, Finset.card_product]
    obtain ⟨⟨h01, h0b, h01b⟩, ⟨h1b, h11b⟩, hb1b⟩ := vec4_ne hb0 hb1
    rw [Finset.card_insert_of_notMem (by simp [h01, h0b, h01b]),
      Finset.card_insert_of_notMem (by simp [h1b, h11b]),
      Finset.card_insert_of_notMem (by simp [hb1b])]
    rfl
  · have := (hcand β hβℓ (by rw [hindβ]; exact hKb) h2β false).1
    simpa using this

end ZInQ.Manuscript.PoleS12
