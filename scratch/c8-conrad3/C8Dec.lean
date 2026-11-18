import ZInQKernel.Contrib.OneProof.C8Ladic

set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace HDec.G0Galois.C8Conrad

namespace DecDict

open _root_.GlueB3Unram NumberField
open scoped Pointwise NNReal

/-- An element of the inertia group of a place `w` of `ℚ̄` over `p` fixes every root of unity of order prime to `p`
(the core of `GlueB3Unram.cycUnram`, for `G_ℚ` written as `Gal`). -/
theorem inertia_fix_root (p : ℕ) (hp : p.Prime) (w : ValuationSubring Qbar) (hw : LiesOver w p) (s : Gal)
    (hs : s ∈ (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype) (N : ℕ) (hN : 0 < N)
    (hpN : ¬ p ∣ N) (t : Qbar) (htN : t ^ N = 1) : s t = t := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hs
  let x : w := ⟨t, rootOfUnity_mem w N hN t htN⟩
  have hres : IsLocalRing.residue w (g • x) = IsLocalRing.residue w x := by
    rw [IsLocalRing.ResidueField.residue_smul]
    have h1 : MulSemiringAction.toRingAut _ (IsLocalRing.ResidueField w) g = 1 := hg
    exact congrArg (fun f => f (IsLocalRing.residue w x)) h1
  set y : w := g • x with hydef
  have hy : (y : Qbar) = (g : Gal) t := rfl
  show (g : Gal) t = t
  by_contra hne
  let z : w := y * x ^ (N - 1)
  have hxN : x ^ N = 1 := Subtype.ext (by simp [x, htN])
  have hyN : y ^ N = 1 := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, hy, OneMemClass.coe_one]
    rw [← map_pow, htN, map_one]
  have hzN : z ^ N = 1 := by
    simp only [z, mul_pow, hyN, one_mul]
    rw [← pow_mul, mul_comm, pow_mul, hxN, one_pow]
  have hz1 : z ≠ 1 := by
    intro h
    apply hne
    have h2 : z * x = x := by rw [h, one_mul]
    have h3 : z * x = y := by
      simp only [z, mul_assoc, ← pow_succ, Nat.sub_add_cancel hN, hxN, mul_one]
    rw [h3] at h2
    rw [← hy, h2]
  have hsum : ∑ i ∈ Finset.range N, z ^ i = 0 := by
    have h := geom_sum_mul z N
    rw [hzN, sub_self] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hz1
  have hzres : IsLocalRing.residue w z = 1 := by
    simp only [z, map_mul, map_pow, hres]
    rw [← map_pow, ← map_mul, ← pow_succ', Nat.sub_add_cancel hN, hxN, map_one]
  have h := congrArg (IsLocalRing.residue w) hsum
  simp only [map_sum, map_pow, hzres, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, map_zero] at h
  apply residue_natCast_ne_zero w p hp hw N hpN
  rw [map_natCast]; exact h

/-- Two places of `ℚ̄` over `p` are conjugate (the proof of `GlueB3Unram.leafConj`, keeping the conjugating element). -/
theorem exists_conj (p : ℕ) (hp : p.Prime) (v v₀ : ValuationSubring Qbar) (hv : LiesOver v p)
    (hv₀ : LiesOver v₀ p) : ∃ g : Gal, v = g • v₀ := by
  have hpint : IsIntegral ℤ (p : Qbar) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := Qbar) (x := (p : ℤ))
  obtain ⟨g, hg⟩ := exists_smul_eq (centerIdeal v₀) (centerIdeal v)
    (by rw [centerIdeal_under v₀ p hp hv₀, centerIdeal_under v p hp hv])
  rw [← centerIdeal_smul] at hg
  have hc : ∀ y : Qbar, IsIntegral ℤ y → (v.valuation y < 1 ↔ (g • v₀).valuation y < 1) := by
    intro y hy
    have h := congrArg (fun I : Ideal B => (⟨y, (mem_integralClosure_iff ℤ Qbar).mpr hy⟩ : B) ∈ I) hg
    simp only [mem_centerIdeal] at h
    exact h.to_iff
  exact ⟨g, le_antisymm (le_of_center v (g • v₀) p hp hv hc)
    (le_of_center (g • v₀) v p hp ((hc _ hpint).mp hv) (fun y hy => (hc y hy).symm))⟩

/-- **`InertiaAtPDecomp` proved.** Every element of an inertia group of `ℚ̄` above `p` is conjugate in `G_ℚ` to
`decomp(σ)` with `σ` in the inertia group of `ℚ_p`. Proof: the place `v₀ = {‖jQ ·‖ ≤ 1}` cut out by the embedding
`jQ : ℚ̄ → ℚ̄_p` underlying `decomp` is conjugate to `v` (`exists_conj`), so the element moves to `τ' ∈ I_{v₀}`;
on each finite Galois `K ⊆ ℚ̄`, `τ'|_K` stabilizes the prime `{‖jQ ·‖ < 1}` of `𝓞 K` and lifts to `G_{ℚ_p}`
(G15's `exists_lift`, from Tau Ceti's Krasner-type extension lemma); by compactness of `G_{ℚ_p}` one `σ` has
`decomp σ = τ'`; `σ` fixes the roots of `X^{p^f} − X` (they are `jQ` of roots of unity of order prime to `p`, fixed by
`τ'` by `inertia_fix_root`), so `σ ∈ I_{ℚ_p}` (Tau Ceti's `mem_inertiaSubgroup_iff_pow_natCard_pow_eq_self`). -/
theorem inertiaAtPDecomp_proof : InertiaAtPDecomp := by
  intro p _ v hv0 τ0
  have hp : p.Prime := Fact.out
  have hv : LiesOver v p := (ValuationSubring.mem_nonunits_iff v).mp hv0
  obtain ⟨jQ, hjQ⟩ := Ladic.decomp_spec p
  let v₀ : ValuationSubring Qbar := (Ladic.nv jQ).valuationSubring
  have hv₀lt : ∀ y : Qbar, v₀.valuation y < 1 ↔ ‖jQ y‖ < 1 := by
    intro y
    have he := Valuation.isEquiv_valuation_valuationSubring (Ladic.nv jQ)
    have h1 : v₀.valuation y < 1 ↔ Ladic.nv jQ y < 1 := by
      rw [← not_le, ← not_le, ← map_one v₀.valuation, ← map_one (Ladic.nv jQ)]
      exact not_congr (he 1 y).symm
    rw [h1, Ladic.nv_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
  have hv₀ : LiesOver v₀ p := by
    show v₀.valuation (p : Qbar) < 1
    rw [hv₀lt, map_natCast]
    have h := PadicAlgCl.norm_extends p (p : ℚ_[p])
    rw [map_natCast] at h
    rw [h, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  obtain ⟨g, heq⟩ := exists_conj p hp v v₀ hv hv₀
  set τ : Gal := ((τ0 : v.decompositionSubgroup ℚ) : Gal) with hτdef
  have hτ : τ ∈ (v.inertiaSubgroup ℚ).map (v.decompositionSubgroup ℚ).subtype :=
    Subgroup.mem_map.mpr ⟨τ0, τ0.2, rfl⟩
  set τ' : Gal := g⁻¹ * τ * g with hτ'def
  have hτ' : τ' ∈ (v₀.inertiaSubgroup ℚ).map (v₀.decompositionSubgroup ℚ).subtype :=
    inertia_conj v₀ v g heq τ hτ
  have hτ'dec : τ' • v₀ = v₀ := by
    obtain ⟨t, -, e⟩ := Subgroup.mem_map.mp hτ'
    rw [← e]; exact t.2
  -- `τ'` preserves `{‖jQ ·‖ < 1}`
  have hpres : ∀ y : Qbar, ‖jQ (τ'⁻¹ y)‖ < 1 ↔ ‖jQ y‖ < 1 := by
    intro y
    have h := val_smul_lt_one_iff v₀ τ' y
    rw [hτ'dec, hv₀lt, hv₀lt] at h
    exact h.symm
  -- compactness of `G_{ℚ_p}`: one `σ` with `decomp σ = τ'`
  let T : Qbar → Set (PkgI4.GQp p) := fun y => {σ | PkgI4.decomp p σ y = τ' y}
  have hdc : Continuous (PkgI4.decomp p) :=
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous
  have hTc : ∀ y, IsClosed (T y) := by
    intro y
    have hS : IsClosed ((MulAction.stabilizer Gal y : Subgroup Gal) : Set Gal) :=
      Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Qbar) y)
    have hS' : IsClosed {h : Gal | τ'⁻¹ * h ∈ MulAction.stabilizer Gal y} :=
      hS.preimage (continuous_const.mul continuous_id)
    have hset : T y = PkgI4.decomp p ⁻¹' {h : Gal | τ'⁻¹ * h ∈ MulAction.stabilizer Gal y} := by
      ext σ
      simp only [T, Set.mem_ofPred_eq, Set.mem_preimage, MulAction.mem_stabilizer_iff]
      constructor
      · intro h1
        show (τ'⁻¹ * PkgI4.decomp p σ) y = y
        rw [AlgEquiv.mul_apply, h1]
        show (τ'⁻¹ * τ') y = y
        rw [inv_mul_cancel]; rfl
      · intro h1
        have h2 : (τ'⁻¹ * PkgI4.decomp p σ) y = y := h1
        rw [AlgEquiv.mul_apply] at h2
        have h3 := congrArg τ' h2
        rw [← h3]
        show PkgI4.decomp p σ y = (τ' * τ'⁻¹) (PkgI4.decomp p σ y)
        rw [mul_inv_cancel]; rfl
    rw [hset]
    exact hS'.preimage hdc
  have hTf : ∀ u : Finset Qbar, (Set.univ ∩ ⋂ y ∈ u, T y).Nonempty := by
    intro u
    let K₀ : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ (u : Set Qbar)
    haveI : FiniteDimensional ℚ K₀ :=
      IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
    let K : IntermediateField ℚ Qbar := IntermediateField.normalClosure ℚ K₀ Qbar
    haveI : FiniteDimensional ℚ K := normalClosure.is_finiteDimensional ℚ K₀ Qbar
    haveI : IsGalois ℚ K := IsGalois.normalClosure ℚ K₀ Qbar
    haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
    let j : K →+* PadicAlgCl p := jQ.comp (algebraMap K Qbar)
    have hinv : (τ'.restrictNormal K)⁻¹ = (τ'⁻¹).restrictNormal K :=
      ((AlgEquiv.restrictNormalHom K).map_inv τ').symm
    have hstab : τ'.restrictNormal K ∈ MulAction.stabilizer Gal(K/ℚ) (Ladic.primeOf j).asIdeal := by
      rw [MulAction.mem_stabilizer_iff]
      ext x
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ladic.mem_primeOf, Ladic.mem_primeOf]
      rw [Ladic.coe_smul, hinv]
      simp only [j, RingHom.comp_apply]
      rw [AlgEquiv.restrictNormal_commutes]
      exact hpres _
    obtain ⟨σ, hσ⟩ := Ladic.exists_lift j hstab
    refine ⟨σ, Set.mem_univ _, ?_⟩
    rw [Set.mem_iInter₂]
    intro y hy
    have hyK : y ∈ K := IntermediateField.le_normalClosure K₀ (IntermediateField.subset_adjoin ℚ _ hy)
    have h1 := hσ ⟨y, hyK⟩
    have e : algebraMap K Qbar ((τ'.restrictNormal K) ⟨y, hyK⟩) = τ' y :=
      AlgEquiv.restrictNormal_commutes τ' K ⟨y, hyK⟩
    simp only [j, RingHom.comp_apply, e] at h1
    show PkgI4.decomp p σ y = τ' y
    apply jQ.injective
    rw [hjQ]
    exact h1.symm
  obtain ⟨σ, -, hσ⟩ := isCompact_univ.inter_iInter_nonempty T hTc hTf
  rw [Set.mem_iInter] at hσ
  have hσdec : PkgI4.decomp p σ = τ' := AlgEquiv.ext fun y => hσ y
  refine ⟨σ, g, ?_, ?_⟩
  · rw [TauCeti.mem_inertiaSubgroup_iff_pow_natCard_pow_eq_self, Padic.natCard_residueField]
    intro x f hf hx
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]
    have hpf : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow hf p)
    set m := p ^ f - 1 with hmdef
    have hm : 0 < m := by omega
    have hpm : ¬ p ∣ m := by
      intro hd
      have h1 : p ∣ p ^ f := dvd_pow_self p hf
      have h2 : p ∣ p ^ f - m := Nat.dvd_sub h1 hd
      rw [show p ^ f - m = 1 by omega] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    have hxm : x ^ m = 1 := by
      have h1 : x ^ m * x = 1 * x := by
        rw [← pow_succ, show m + 1 = p ^ f by omega, one_mul]; exact hx
      exact mul_right_cancel₀ hx0 h1
    haveI : NeZero m := ⟨hm.ne'⟩
    obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar m
    have hζ' : IsPrimitiveRoot (jQ ζ₀) m := hζ₀.map_of_injective jQ.injective
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hxm
    rw [← hi, ← map_pow]
    show σ (jQ (ζ₀ ^ i)) = jQ (ζ₀ ^ i)
    rw [← hjQ, hσdec]
    congr 1
    refine inertia_fix_root p hp v₀ hv₀ τ' hτ' m hm hpm _ ?_
    rw [← pow_mul, mul_comm, pow_mul, hζ₀.pow_eq_one, one_pow]
  · show τ = g * PkgI4.decomp p σ * g⁻¹
    rw [hσdec, hτ'def]
    group

end DecDict

end HDec.G0Galois.C8Conrad

#print axioms HDec.G0Galois.C8Conrad.DecDict.inertiaAtPDecomp_proof
