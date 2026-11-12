
section B3bMain

open scoped Pointwise

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The inertia element.** If `α² = ±p` and some `σ ∈ G_ℚ` negates `α`, then some element of
the inertia group of any place `w` over `p` negates `α`. -/
theorem exists_inertia_neg (p : ℕ) (hp : p.Prime) (w : ValuationSubring Qbar) (hw : LiesOver w p)
    (α : Qbar) (hα : α ^ 2 = (p : Qbar) ∨ α ^ 2 = -(p : Qbar)) (σ : Gal) (hσ : σ α = -α) :
    ∃ s : Gal, s ∈ (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype ∧ s α = -α := by
  classical
  have hpint : IsIntegral ℤ (p : Qbar) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := Qbar) (x := (p : ℤ))
  have hαint : IsIntegral ℤ α := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rcases hα with h | h <;> rw [h]
    · exact hpint
    · exact hpint.neg
  let H : Subgroup Gal := MulAction.stabilizer Gal α
  have hH : ∀ g : Gal, g ∈ H ↔ g α = α := fun g => Iff.rfl
  have hHopen : IsOpen (H : Set Gal) := stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Qbar) α
  have hHclosed : IsClosed (H : Set Gal) := Subgroup.isClosed_of_isOpen H hHopen
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hHclosed.isCompact
  let A := FixedPoints.subalgebra ℤ B H
  let Q := centerIdeal w
  haveI : SMulCommClass H A B := ⟨fun h a b => by
    rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, smul_mul', a.2 h]⟩
  -- elements of `A` are fixed by every `g` fixing `α`
  have hAfix : ∀ (a : A) (g : Gal), g α = α → g ((a : B) : Qbar) = ((a : B) : Qbar) := by
    intro a g hg
    have := a.2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  -- the valuation input on `A`
  have hAval : ∀ (a : A) (σ' : Gal), σ' α = -α →
      w.valuation (((a : B) : Qbar) - σ' ((a : B) : Qbar)) < 1 := by
    intro a σ' hσ'
    have hai : IsIntegral ℤ ((a : B) : Qbar) := (mem_integralClosure_iff ℤ Qbar).mp (a : B).2
    obtain ⟨r, hr⟩ := exists_int_anti hα hαint hai (hAfix a) σ' hσ'
    exact val_sub_lt_one hp hw hα (val_le_one_of_isIntegral w hai)
      (val_le_one_of_isIntegral w (hai.map ((σ' : Qbar →+* Qbar).toIntAlgHom))) r hr
  -- step 1: `σ • Q` and `Q` lie over the same prime of `A`
  have hunder : (σ • Q).under A = Q.under A := by
    ext a
    rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_centerIdeal, mem_centerIdeal]
    have hσi : σ⁻¹ α = -α := by
      have h2 : (σ⁻¹ : Gal) (σ α) = α := by
        show (σ⁻¹ * σ) α = α
        rw [inv_mul_cancel]; rfl
      rw [hσ, map_neg] at h2
      exact neg_eq_iff_eq_neg.mp h2
    have h := hAval a σ⁻¹ hσi
    show w.valuation ((σ⁻¹ : Gal) ((a : B) : Qbar)) < 1 ↔ w.valuation ((a : B) : Qbar) < 1
    constructor
    · intro h1
      have : ((a : B) : Qbar) = (((a : B) : Qbar) - (σ⁻¹ : Gal) ((a : B) : Qbar)) +
          (σ⁻¹ : Gal) ((a : B) : Qbar) := by ring
      rw [this]; exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h h1)
    · intro h1
      have : (σ⁻¹ : Gal) ((a : B) : Qbar) = ((a : B) : Qbar) -
          (((a : B) : Qbar) - (σ⁻¹ : Gal) ((a : B) : Qbar)) := by ring
      rw [this]; exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1 h)
  -- step 2: transitivity over `A` gives `τ` stabilizing `Q` and negating `α`
  haveI hσQ : (σ • Q).IsPrime := by
    show (σ • centerIdeal w).IsPrime
    rw [← centerIdeal_smul]; infer_instance
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := A) (G := H)
    (σ • Q) Q hunder
  let τ : Gal := (g : Gal) * σ
  have hτQ : τ • Q = Q := by
    show ((g : Gal) * σ) • Q = Q
    rw [mul_smul]; exact hg.symm
  have hτα : τ α = -α := by
    show (g : Gal) (σ α) = -α
    rw [hσ, map_neg, (hH g).mp g.2]
  -- step 3: `τ` induces an `A/P`-automorphism of `B/Q`
  let f : B ≃+* B := MulSemiringAction.toRingEquiv Gal B τ
  have hQf : Q = Q.map f := by
    ext b
    rw [Ideal.mem_map_of_equiv]
    constructor
    · intro hb
      refine ⟨τ⁻¹ • b, ?_, by simp [f]⟩
      rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hτQ]; exact hb
    · rintro ⟨x, hx, rfl⟩
      rw [← hτQ]
      exact Ideal.smul_mem_pointwise_smul_iff.mpr hx
  let e : (B ⧸ Q) ≃+* (B ⧸ Q) := Ideal.quotientEquiv Q Q f hQf
  have he : ∀ b : B, e (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (τ • b) := fun b => rfl
  let φ : (B ⧸ Q) ≃ₐ[A ⧸ Q.under A] (B ⧸ Q) := AlgEquiv.ofRingEquiv (f := e) (by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, he, Ideal.Quotient.eq, mem_centerIdeal]
    have h := hAval a τ hτα
    rw [Valuation.map_sub_swap] at h
    exact h)
  -- step 4: Mathlib's surjectivity gives `h' ∈ H` acting on `B/Q` as `τ`
  obtain ⟨h', hh'⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under A) Q φ
  have hact : ∀ b : B, Ideal.Quotient.mk Q (((h' : H) : Gal) • b) =
      Ideal.Quotient.mk Q (τ • b) := by
    intro b
    have := congrArg (fun ψ => ψ (Ideal.Quotient.mk Q b)) hh'
    exact this
  let k : Gal := ((h' : H) : Gal)
  have hkQ : k • Q = Q := h'.2
  have hkα : k α = α := (h' : H).2
  let s : Gal := k⁻¹ * τ
  refine ⟨s, ?_, ?_⟩
  · apply mem_inertia_of_center hp hw s
    · show (k⁻¹ * τ) • Q = Q
      rw [mul_smul, hτQ, inv_smul_eq_iff, hkQ]
    · intro b
      have h1 := hact (s • b)
      have h2 : ((h' : H) : Gal) • (s • b) = τ • b := by
        show k • ((k⁻¹ * τ) • b) = τ • b
        rw [mul_smul, smul_inv_smul]
      rw [h2, Ideal.Quotient.eq] at h1
      -- `τ • b - τ • (s • b) ∈ Q`, hence `b - s • b ∈ Q`
      have h3 : b - s • b ∈ Q := by
        have h4 : τ • (b - s • b) ∈ τ • Q := by rw [hτQ, smul_sub]; exact h1
        rwa [Ideal.smul_mem_pointwise_smul_iff] at h4
      have := Q.neg_mem h3
      rwa [neg_sub] at this
  · show k⁻¹ (τ α) = -α
    rw [hτα, map_neg]
    congr 1
    have : k⁻¹ (k α) = α := by
      show (k⁻¹ * k) α = α
      rw [inv_mul_cancel]; rfl
    rwa [hkα] at this

end B3bMain
