
section B3bGauss

/-- The cyclotomic character on a primitive `p`-th root of unity: `s ζ = ζ ^ cyc(s)`. -/
theorem act_zeta (p : ℕ) [NeZero p] {ζ : Qbar} (hζ : IsPrimitiveRoot ζ p) (s : Gal) :
    s ζ = ζ ^ ((cyc p s : (ZMod p)ˣ) : ZMod p).val := by
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne p⟩
  have hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) p
  have h := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) hn (toRingAut s)
    (t := (hζ.toRootsOfUnity : Qbarˣ)) (hζ.toRootsOfUnity).2
  simp only [IsPrimitiveRoot.val_toRootsOfUnity_coe] at h
  exact h

/-- The quadratic Gauss sum `∑ₐ (a/p) ζ^a ∈ ℚ̄`. -/
noncomputable def gaussP (p : ℕ) [Fact p.Prime] {ζ : Qbar} (hζ : IsPrimitiveRoot ζ p) : Qbar :=
  gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Qbar))
    (AddChar.zmodChar p ((IsPrimitiveRoot.iff_def ζ p).mp hζ).left)

/-- `σ(g) = (cyc(σ)/p) · g` for the Gauss sum `g`. -/
theorem gaussP_transform (p : ℕ) [Fact p.Prime] {ζ : Qbar} (hζ : IsPrimitiveRoot ζ p) (s : Gal) :
    s (gaussP p hζ) =
      ((quadraticChar (ZMod p) ((cyc p s : (ZMod p)ˣ) : ZMod p) : ℤ) : Qbar) * gaussP p hζ := by
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Qbar)
  let ψ := AddChar.zmodChar p ((IsPrimitiveRoot.iff_def ζ p).mp hζ).left
  let c := cyc p s
  have hχ : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
  have hsψ : ∀ a, s (ψ a) = ψ.mulShift (c : ZMod p) a := by
    intro a
    have hca : (c : ZMod p) * a = ((c : ZMod p).val) • a := by
      rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
    rw [AddChar.mulShift_apply, hca, AddChar.map_nsmul_eq_pow, AddChar.zmodChar_apply, map_pow,
      act_zeta p hζ s, ← pow_mul, ← pow_mul, mul_comm]
  have hsχ : ∀ a, s (χ a) = χ a := by
    intro a
    show s ((Int.castRingHom Qbar) _) = (Int.castRingHom Qbar) _
    rw [eq_intCast, map_intCast]
  show s (gaussSum χ ψ) = _ * gaussSum χ ψ
  calc s (gaussSum χ ψ) = gaussSum χ (ψ.mulShift (c : ZMod p)) := by
        unfold gaussSum
        rw [map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_mul, hsψ, hsχ]
    _ = χ⁻¹ c * gaussSum χ ψ := gaussSum_mulShift_eq χ ψ c
    _ = _ := by
        rw [hχ.inv]
        show (Int.castRingHom Qbar) _ * _ = _
        rw [eq_intCast]

/-- `g² = (-1/p) p = ±p`. -/
theorem gaussP_sq (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {ζ : Qbar}
    (hζ : IsPrimitiveRoot ζ p) :
    gaussP p hζ ^ 2 = (p : Qbar) ∨ gaussP p hζ ^ 2 = -(p : Qbar) := by
  have hχ : ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Qbar)).IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod p)).comp _
  have hχ1 : (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Qbar) ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.castRingHom Qbar).injective_int).mpr
      (quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; exact hp2))
  unfold gaussP
  rw [gaussSum_sq hχ1 hχ (AddChar.zmodChar_primitive_of_primitive_root p hζ), ZMod.card,
    MulChar.ringHomComp_apply]
  rcases quadraticChar_dichotomy (F := ZMod p) (a := -1) (neg_ne_zero.mpr one_ne_zero) with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

/-- `±p` is not a square in `ℚ`, so some `σ ∈ G_ℚ` negates a square root of `±p`. -/
theorem exists_neg_of_sq (p : ℕ) (hp : p.Prime) {α : Qbar}
    (hα : α ^ 2 = (p : Qbar) ∨ α ^ 2 = -(p : Qbar)) : ∃ σ : Gal, σ α = -α := by
  by_contra hne
  push_neg at hne
  have hfix : ∀ g : Gal, g α = α := fun g => (smul_sq_cases hα g).resolve_right (hne g)
  have hbot : α ∈ (⊥ : IntermediateField ℚ Qbar) := (InfiniteGalois.mem_bot_iff_fixed α).mpr hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hbot
  rw [← hq] at hα
  rcases hα with h | h
  · have h' : q ^ 2 = (p : ℚ) := by
      apply (algebraMap ℚ Qbar).injective; rw [map_pow, h, map_natCast]
    have hsq : IsSquare (p : ℚ) := ⟨q, by rw [← h', sq]⟩
    rw [Rat.isSquare_natCast_iff] at hsq
    obtain ⟨r, hr⟩ := hsq
    rcases hp.eq_one_or_self_of_dvd r ⟨r, hr⟩ with h1 | h1
    · rw [h1] at hr; exact hp.one_lt.ne' (by simpa using hr)
    · rw [h1] at hr
      have h2 : p * 1 = p * p := by rw [mul_one]; exact hr
      exact hp.one_lt.ne (Nat.eq_of_mul_eq_mul_left hp.pos h2)
  · have h' : q ^ 2 = -(p : ℚ) := by
      apply (algebraMap ℚ Qbar).injective; rw [map_pow, h, map_neg, map_natCast]
    have : (0 : ℚ) < p := by exact_mod_cast hp.pos
    nlinarith [sq_nonneg q]

/-- **`LeafB3b` is glue** (proved from Mathlib): the Legendre character mod an odd prime `p`, as a
character of `G_ℚ`, is nontrivial on the inertia group of every place over `p`. -/
theorem leafB3b : LeafB3b := by
  intro p hp hp2 w hw
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero ((p : ℕ) : Qbar) := ⟨by exact_mod_cast hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar p
  have hα := gaussP_sq p hp2 hζ
  obtain ⟨σ, hσ⟩ := exists_neg_of_sq p hp hα
  obtain ⟨s, hs, hsα⟩ := exists_inertia_neg p hp w hw (gaussP p hζ) hα σ hσ
  refine ⟨s, hs, fun h1 => ?_⟩
  have hq : quadraticChar (ZMod p) ((cyc p s : (ZMod p)ˣ) : ZMod p) = 1 := by
    unfold etaP at h1
    rw [dif_pos hp] at h1
    unfold galChar at h1
    have h2 : (((legChar p).toUnitHom (cyc p s) : ℂˣ) : ℂ) = 1 := by
      have := congrArg Units.val h1; exact this
    rw [MulChar.coe_toUnitHom] at h2
    unfold legChar at h2
    rw [dif_pos hp, MulChar.ringHomComp_apply, eq_intCast] at h2
    exact_mod_cast h2
  have h3 := gaussP_transform p hζ s
  rw [hq, Int.cast_one, one_mul, hsα] at h3
  have h0 : gaussP p hζ = 0 := by
    have h4 : (2 : Qbar) * gaussP p hζ = 0 := by linear_combination -h3
    exact (mul_eq_zero.mp h4).resolve_left two_ne_zero
  rw [h0] at hα
  have hp0 : (p : Qbar) ≠ 0 := by exact_mod_cast hp.ne_zero
  rcases hα with h | h
  · exact hp0 (by rw [← h]; ring)
  · exact hp0 (by rw [← neg_eq_zero, ← h]; ring)

end B3bGauss
