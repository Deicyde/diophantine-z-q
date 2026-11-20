import ZInQKernel.Contrib.OneProof.RC.CMField2.ExactOrder
import ZInQKernel.Contrib.OneProof.RC.CMField2.NormCriterion

/-! The diagonal root support recovers the exact embedded order and closes
the modular-polynomial degree bounds. Provenance (c). -/

noncomputable section

open NumberField Module ModularCurve Polynomial IntermediateField TauCeti.GlobalNumberFields

namespace ZInQ.Manuscript.RC.CMField2

theorem periodMultipliers_idealPeriod {K : Type} [Field K] [NumberField K]
    (O : NumberFieldOrder K) (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (κ : K →+* ℂ) (I : O.invertibleProperFractionalIdeals) (z : ℂ) :
    z ∈ periodMultipliers (idealPeriod O hk hc κ I) ↔ z ∈ κ '' (O.toSubalgebra : Set K) := by
  let L := idealPeriod O hk hc κ I
  have hp := (O.isProperFractionalIdeal_iff I.val).mp (O.isProperFractionalIdeal_of_isUnit I.isUnit)
  change (∀ w ∈ L.lattice, z * w ∈ L.lattice) ↔ _
  simp only [← SetLike.mem_coe, L, idealPeriod_lattice]
  constructor
  · intro h
    have hx : L.ω₁ ∈ κ '' (I.val : Set K) := by
      rw [← idealPeriod_lattice O hk hc κ I]
      exact L.latticeBasis_zero ▸ (L.latticeBasis 0).property
    obtain ⟨x, hx, he⟩ := hx
    have hx0 : κ x ≠ 0 := he ▸ L.indep.ne_zero 0
    obtain ⟨y, hy, hye⟩ := h _ ⟨x, hx, rfl⟩
    have hz : κ (y / x) = z := by rw [map_div₀, hye, mul_div_cancel_right₀ _ hx0]
    refine ⟨y / x, hp _ (fun v hv => ?_), hz⟩
    obtain ⟨w, hw, he'⟩ := h _ ⟨v, hv, rfl⟩
    have h' : y / x * v = w := κ.injective (by rw [map_mul, hz, he'])
    exact h' ▸ hw
  · rintro ⟨s, hs, rfl⟩ _ ⟨v, hv, rfl⟩
    exact ⟨s * v, (O.mem_multiplierRing_iff I.val s).mp (O.order_le_multiplierRing I.val hs) v hv,
      map_mul κ s v⟩

private theorem same_normalized_order {L M : PeriodPair} {x : periodMultipliers L}
    {y : periodMultipliers M} {t u : ℤ} (hx : (t : ℝ) = 2 * (x : ℂ).re)
    (hy : (t : ℝ) = 2 * (y : ℂ).re) (hxu : (u : ℝ) = Complex.normSq (x : ℂ))
    (hyu : (u : ℝ) = Complex.normSq (y : ℂ))
    (hL : ∀ z : periodMultipliers L, ∃ a b : ℤ, (z : ℂ) = (a : ℂ) + (b : ℂ) * x)
    (hM : ∀ z : periodMultipliers M, ∃ a b : ℤ, (z : ℂ) = (a : ℂ) + (b : ℂ) * y) :
    periodMultipliers L = periodMultipliers M := by
  have int_mem (P : PeriodPair) (a : ℤ) : (a : ℂ) ∈ periodMultipliers P :=
    (a : periodMultipliers P).property
  have hre : (x : ℂ).re = (y : ℂ).re := by linarith
  have him : ((x : ℂ).im - (y : ℂ).im) * ((x : ℂ).im + (y : ℂ).im) = 0 := by
    rw [Complex.normSq_apply, hre] at hxu
    rw [Complex.normSq_apply] at hyu
    nlinarith
  have he : (x : ℂ) = (y : ℂ) ∨ (x : ℂ) = (t : ℂ) - (y : ℂ) := by
    rcases mul_eq_zero.mp him with h | h
    · exact Or.inl (Complex.ext hre (sub_eq_zero.mp h))
    · right
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.intCast_re]
        linarith
      · simp only [Complex.sub_im, Complex.intCast_im, zero_sub]
        linarith
  have hxy : (x : ℂ) ∈ periodMultipliers M := by
    rcases he with he | he
    · exact he ▸ y.property
    · rw [he]
      exact (periodMultipliers M).sub_mem (int_mem M t) y.property
  have hyx : (y : ℂ) ∈ periodMultipliers L := by
    rcases he with he | he
    · exact he ▸ x.property
    · have hy' : (y : ℂ) = (t : ℂ) - x := by rw [he]; ring
      rw [hy']
      exact (periodMultipliers L).sub_mem (int_mem L t) x.property
  ext z
  constructor
  · intro hz
    obtain ⟨a, b, h⟩ := hL ⟨z, hz⟩
    change z = _ at h
    rw [h]
    exact (periodMultipliers M).add_mem (int_mem M a) ((periodMultipliers M).mul_mem (int_mem M b) hxy)
  · intro hz
    obtain ⟨a, b, h⟩ := hM ⟨z, hz⟩
    change z = _ at h
    rw [h]
    exact (periodMultipliers L).add_mem (int_mem L a) ((periodMultipliers L).mul_mem (int_mem L b) hyx)

/-- The exact-order comparison follows by comparing primitive norm supports.
In particular, equality of the diagonal multiplicities is more than enough. -/
theorem exactMultiplierOrderOfDiagonalMultiplicities : ExactMultiplierOrderOfDiagonalMultiplicities := by
  intro K _ _ O hk hc κ I L h
  let M := idealPeriod O hk hc κ I
  obtain ⟨b, hb⟩ := exists_order_basis_one O hk
  let ω : periodMultipliers M := ⟨κ (b 1 : K),
    (periodMultipliers_idealPeriod O hk hc κ I _).mpr ⟨_, (b 1).property, rfl⟩⟩
  obtain ⟨x, t, u, hxi, ht, hu, hxT, hxU, hM⟩ :=
    exists_normalized_multiplier M ω (orderBasis_im_ne_zero O hc κ b hb)
  have hroot (m : ℕ) [NeZero m] (P : ModularPolynomialData m) :
      (P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) M.jLattice)).IsRoot M.jLattice ↔
      (P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) L.jLattice)).IsRoot L.jLattice := by
    rw [← rootMultiplicity_pos (P.monic.map _).ne_zero, ← rootMultiplicity_pos (P.monic.map _).ne_zero]
    have he := h m P
    change rootMultiplicity M.jLattice (P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) M.jLattice)) = _ at he
    rw [he]
  have hd : t ^ 2 < 4 * u := by
    exact_mod_cast (show (t : ℝ) ^ 2 < 4 * (u : ℝ) by
      rw [hxT, hxU, Complex.normSq_apply]
      nlinarith [sq_pos_of_ne_zero hxi])
  obtain ⟨n, s, hs, hlo, hhi⟩ := exists_nonsquare_quadratic_value t u hd
  let q := (n ^ 2 + t * n + u).toNat
  have hpos : 1 < n ^ 2 + t * n + u := by
    nlinarith [mul_nonneg (show 0 ≤ s - 1 by omega) (show 0 ≤ s + 1 by omega)]
  have hq : (q : ℤ) = n ^ 2 + t * n + u := Int.toNat_of_nonneg (by omega)
  have hq1 : 1 < q := by omega
  let : NeZero q := ⟨by omega⟩
  have hqns : ¬ IsSquare q := by
    rintro ⟨k, hk⟩
    have hke : (q : ℤ) = (k : ℤ) ^ 2 := by exact_mod_cast (hk.trans (pow_two k).symm)
    rw [← hq, hke] at hlo hhi
    rcases le_or_gt (k : ℤ) s with h | h
    · nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ s + (k : ℤ) by omega)]
    · have hh : s + 1 ≤ (k : ℤ) := by omega
      nlinarith [mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ (k : ℤ) + (s + 1) by omega)]
  obtain ⟨P⟩ := nonempty_modularPolynomialData q
  have hqmem : (q : ℤ) ∈ primitiveNormLevels t u := ⟨by omega, n, 1, by simp,
    by rw [hq]; ring⟩
  have hqroot := (hroot q P).mp ((diagonal_root_iff_primitive_norm M q hq1 P x hxi t u hxT hxU hM).mpr hqmem)
  obtain ⟨τ, hτ, v, hvi, hv, _, _⟩ := conjugate_has_nonreal_multiplier_of_root L.jLattice
    (RingHom.id ℂ) (RingHom.id ℂ) q P hqns hqroot
  let L' := PeriodPair.ofTau τ
  have hS := periodMultipliers_eq_of_jLattice_eq L' L ((PeriodPair.jLattice_ofTau τ).trans hτ)
  have hvS : (v : ℂ) ∈ periodMultipliers L' := by
    intro w hw
    apply hv
    change _ ∈ ((L'.scale v).lattice : Set ℂ)
    rw [lattice_scale]
    exact ⟨w, hw, rfl⟩
  obtain ⟨y, t', u', hyi, ht', hu', hyT, hyU, hL⟩ :=
    exists_normalized_multiplier L ⟨v, hS ▸ hvS⟩ hvi
  have hlevels : primitiveNormLevels t u = primitiveNormLevels t' u' := by
    ext m
    by_cases hm : 1 < m
    · let k := m.toNat
      have hk : (k : ℤ) = m := Int.toNat_of_nonneg (by omega)
      have hki : 1 < k := by omega
      let : NeZero k := ⟨by omega⟩
      obtain ⟨Pk⟩ := nonempty_modularPolynomialData k
      rw [← hk, ← diagonal_root_iff_primitive_norm M k hki Pk x hxi t u hxT hxU hM,
        ← diagonal_root_iff_primitive_norm L k hki Pk y hyi t' u' hyT hyU hL]
      exact hroot k Pk
    · exact ⟨fun h => (hm h.1).elim, fun h => (hm h.1).elim⟩
  obtain ⟨rfl, rfl⟩ := quadraticNormParameters_eq_of_primitiveNormLevels ht ht' hu hu' hlevels
  have hEq := same_normalized_order hxT hyT hxU hyU hM hL
  intro z
  change z ∈ periodMultipliers L ↔ _
  rw [← hEq]
  exact periodMultipliers_idealPeriod O hk hc κ I z

/-- Every rational conjugate of a singular modulus has the same exact order. -/
theorem conjugateSingularModulus : ConjugateSingularModulus :=
  conjugateSingularModulus_of_exactMultiplier exactMultiplierOrderOfDiagonalMultiplicities

/-- The degree of every singular modulus over ℚ is at most the proper class number. -/
theorem singularModulus_finrank_le {K : Type} [Field K] [NumberField K]
    (O : NumberFieldOrder K) (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (κ : K →+* ℂ) (I : O.invertibleProperFractionalIdeals) :
    finrank ℚ ℚ⟮singularModulus O hk hc κ I⟯ ≤ Nat.card (Pic O) :=
  singularModulus_finrank_le_of_conjugate conjugateSingularModulus O hk hc κ I

/-- The analogous degree bound after adjoining the singular modulus to the
quadratic field through the chosen embedding. -/
theorem singularModulus_finrank_over_base_le {K : Type} [Field K] [NumberField K]
    (O : NumberFieldOrder K) (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (κ : K →+* ℂ) (I : O.invertibleProperFractionalIdeals) :
    letI : Algebra K ℂ := κ.toAlgebra
    finrank K K⟮singularModulus O hk hc κ I⟯ ≤ Nat.card (Pic O) :=
  singularModulus_finrank_over_base_le_of_conjugate conjugateSingularModulus O hk hc κ I


end ZInQ.Manuscript.RC.CMField2
