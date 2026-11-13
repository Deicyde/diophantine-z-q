/-! ## rv-gluepieces2 check (d): x1-dirichlet's proof of field 22 from the bundle leaf `t17`
(body of scratch/x1-dirichlet/Dirichlet.lean, verbatim), applied to G0Assemble's constant. -/

section DirichletCopy
noncomputable section

namespace X1Dirichlet

open PkgI4 (Qbar GQ LiesOver IsArithFrob GaloisChar)
open TSkolemKW.KW hiding Qbar GQ  -- rv-gluepieces2: Leaves.lean's TSkolemKW.KW has its own Qbar, GQ

/-- **Kronecker–Weber at Frobenius (GLUE, unproved; from T17 `KroneckerWeber`).** A continuous
character `ψ : G_ℚ → ℚ̄_ℓ^×` of finite image is, at arithmetic Frobenius outside a finite set,
a Dirichlet character `ψD mod m` through `ιC`, `ιL`: `ψ` factors through
`Gal(ℚ(ζ_m)/ℚ) ≅ (ℤ/m)^×` (T17), arithmetic Frobenius at `p ∤ m` maps to `p`, and the values
(roots of unity) lie in `ιL(ℚ̄)`. -/
def DirichletOfFinite : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ψ : GaloisChar ℓ), (Set.range ψ.toHom).Finite →
    ∀ (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ),
    ∃ (m : ℕ) (ψD : DirichletCharacter ℂ m) (S : Finset ℕ), 0 < m ∧
      ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : Qbar, ιC β = ψD (p : ZMod m) ∧
        ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
          (ψ.toHom τ : PadicAlgCl ℓ) = ιL β

/-! ## §1. Roots of unity of `ℚ̄_ℓ` come from `ℚ̄` -/

theorem exists_preimage_of_pow_eq_one {E : Type*} [Field E] [Algebra ℚ E] (ι : Qbar →ₐ[ℚ] E)
    (N : ℕ+) (z : E) (hz : z ^ (N : ℕ) = 1) : ∃ β : Qbar, ι β = z := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_qbar N
  have h : IsPrimitiveRoot (ι ζ) (N : ℕ) := hζ.map_of_injective (RingHom.injective ι.toRingHom)
  obtain ⟨i, -, hi⟩ := h.eq_pow_of_pow_eq_one hz
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

/-! ## §2. Arithmetic Frobenius on roots of unity -/

/-- Roots of unity have valuation `1` at every place. -/
theorem valuation_eq_one_of_pow (v : ValuationSubring Qbar) {n : ℕ} (hn : n ≠ 0) {x : Qbar}
    (hx : x ^ n = 1) : v.valuation x = 1 := by
  have h := congrArg v.valuation hx
  rw [map_pow, map_one] at h
  exact (pow_eq_one_iff_of_nonneg zero_le hn).1 h

/-- **An arithmetic Frobenius at a place above `p ∤ m` has mod-`m` cyclotomic character `p`.** -/
theorem cycChar_frob (m : ℕ+) (p : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ (m : ℕ))
    (v : ValuationSubring Qbar) (τ : GQ) (hv : LiesOver v p) (hτ : IsArithFrob τ v p) :
    ((cycChar m τ : (ZMod m)ˣ) : ZMod m) = (p : ZMod m) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_qbar m
  have hm0 : (m : ℕ) ≠ 0 := m.ne_zero
  have hζm : ζ ^ (m : ℕ) = 1 := hζ.pow_eq_one
  set a := ((cycChar m τ : (ZMod m)ˣ) : ZMod m).val with ha
  have hτζ : τ ζ = ζ ^ a := cycChar_spec m τ ζ hζm
  have hζval : v.valuation ζ = 1 := valuation_eq_one_of_pow v hm0 hζm
  have hζv : ζ ∈ v := (v.valuation_le_one_iff ζ).1 hζval.le
  have hdiff : v.valuation (ζ ^ a - ζ ^ p) < 1 := by
    have := hτ.2 ζ hζv
    rw [hτζ] at this
    exact (v.mem_nonunits_iff).1 this
  have hpv : v.valuation (p : Qbar) < 1 := (v.mem_nonunits_iff).1 hv
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0
  have heq : ζ ^ a = ζ ^ p := by
    by_contra hne
    set η := ζ ^ a / ζ ^ p with hηdef
    have hη1 : η ≠ 1 := fun h => hne ((div_eq_one_iff_eq (pow_ne_zero _ hζ0)).1 h)
    have hηm : η ^ (m : ℕ) = 1 := by
      rw [hηdef, div_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm p, pow_mul, pow_mul, hζm,
        one_pow, one_pow, div_one]
    have hηval : v.valuation η = 1 := valuation_eq_one_of_pow v hm0 hηm
    have hηv : v.valuation (η - 1) < 1 := by
      have : η - 1 = (ζ ^ a - ζ ^ p) / ζ ^ p := by
        rw [sub_div, div_self (pow_ne_zero _ hζ0)]
      rw [this, map_div₀, map_pow, hζval, one_pow, div_one]
      exact hdiff
    have hsum : ∑ i ∈ Finset.range (m : ℕ), η ^ i = 0 := by
      rw [geom_sum_eq hη1, hηm, sub_self, zero_div]
    have hmv : v.valuation ((m : ℕ) : Qbar) < 1 := by
      have : ((m : ℕ) : Qbar) = ∑ i ∈ Finset.range (m : ℕ), (1 - η ^ i) := by
        rw [Finset.sum_sub_distrib, hsum, sub_zero]
        simp
      rw [this]
      apply Valuation.map_sum_lt _ one_ne_zero
      intro i _
      have h1 : 1 - η ^ i = -((η - 1) * ∑ j ∈ Finset.range i, η ^ j) := by
        rw [mul_comm, geom_sum_mul]
        ring
      rw [h1, Valuation.map_neg, map_mul]
      have hs : v.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 :=
        Valuation.map_sum_le _ (fun j _ => by rw [map_pow, hηval, one_pow])
      exact (mul_le_of_le_one_right' hs).trans_lt hηv
    -- `p` and `m` are coprime, but both lie in the maximal ideal of `v`
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
    have h1 : ((p : ℤ) * Nat.gcdA p m + ((m : ℕ) : ℤ) * Nat.gcdB p m : ℤ) = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, hcop]
      rfl
    have hint : ∀ k : ℤ, v.valuation (k : Qbar) ≤ 1 := fun k =>
      (v.valuation_le_one_iff _).2 (intCast_mem v k)
    have hlt : v.valuation
        ((((p : ℤ) * Nat.gcdA p m + ((m : ℕ) : ℤ) * Nat.gcdB p m : ℤ)) : Qbar) < 1 := by
      push_cast
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le hpv (hint _)
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le hmv (hint _)
    rw [h1, Int.cast_one, map_one] at hlt
    exact lt_irrefl _ hlt
  -- `ζ^a = ζ^p` with `ζ` primitive gives `a ≡ p (mod m)`
  have hmod : (a : ZMod m) = (p : ZMod m) := by
    rcases le_total p a with h | h
    · have hd : ζ ^ (a - p) = 1 := by
        have : ζ ^ (a - p) * ζ ^ p = 1 * ζ ^ p := by
          rw [← pow_add, Nat.sub_add_cancel h, one_mul, heq]
        exact mul_right_cancel₀ (pow_ne_zero _ hζ0) this
      have := (hζ.pow_eq_one_iff_dvd _).1 hd
      exact ((ZMod.natCast_eq_natCast_iff p a m).2 ((Nat.modEq_iff_dvd' h).2 this)).symm
    · have hd : ζ ^ (p - a) = 1 := by
        have : ζ ^ (p - a) * ζ ^ a = 1 * ζ ^ a := by
          rw [← pow_add, Nat.sub_add_cancel h, one_mul, heq]
        exact mul_right_cancel₀ (pow_ne_zero _ hζ0) this
      have := (hζ.pow_eq_one_iff_dvd _).1 hd
      exact (ZMod.natCast_eq_natCast_iff a p m).2 ((Nat.modEq_iff_dvd' h).2 this)
  rw [← hmod, ha, ZMod.natCast_zmod_val]

/-! ## §3. `DirichletOfFinite` -/

/-- **`DirichletOfFinite` (GLUE, proved from the leaf T17 in its cyclic form).** -/
theorem dirichletOfFinite_of_kroneckerWeberCyclic (hKW : KroneckerWeberCyclic) :
    DirichletOfFinite := by
  intro ℓ _ ψ hfin ιC ιL
  have hopen : IsOpen (ψ.toHom.ker : Set GQ) :=
    isOpen_ker_of_continuous ψ.toHom ψ.continuous_toHom hfin
  obtain ⟨m, χ, hχ⟩ := dirichletCharacter_of_kroneckerWeberCyclic hKW ψ.toHom hopen
  -- the values of `χ` on units are roots of unity of order dividing `N = #(ℤ/m)ˣ`
  let N : ℕ+ := ⟨Fintype.card (ZMod m)ˣ, Fintype.card_pos⟩
  have hpow : ∀ u : (ZMod m)ˣ, (χ u) ^ (N : ℕ) = 1 := by
    intro u
    have h1 : u ^ (N : ℕ) = 1 := pow_card_eq_one
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  choose β hβ using fun u : (ZMod m)ˣ => exists_preimage_of_pow_eq_one ιL N (χ u) (hpow u)
  have hβ0 : ∀ u, β u ≠ 0 := by
    intro u h
    have := hβ u
    rw [h, map_zero, ← MulChar.coe_toUnitHom] at this
    exact (χ.toUnitHom u).ne_zero this.symm
  have hinj : Function.Injective ιL := RingHom.injective ιL.toRingHom
  let χQ : (ZMod m)ˣ →* Qbarˣ :=
    { toFun := fun u => Units.mk0 (β u) (hβ0 u)
      map_one' := Units.ext (hinj (by simp [hβ]))
      map_mul' := fun u w => Units.ext (hinj (by simp [hβ, map_mul])) }
  let ψD : DirichletCharacter ℂ (m : ℕ) :=
    MulChar.ofUnitHom ((Units.map (ιC : Qbar →* ℂ)).comp χQ)
  refine ⟨m, ψD, (m : ℕ).primeFactors, m.pos, fun p hp hpS => ?_⟩
  have hpm : ¬ p ∣ (m : ℕ) := fun h =>
    hpS (Nat.mem_primeFactors.2 ⟨hp, h, m.ne_zero⟩)
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime p hcop
  have hu : ((u : (ZMod m)ˣ) : ZMod m) = (p : ZMod m) := ZMod.coe_unitOfCoprime p hcop
  refine ⟨β u, ?_, fun v τ hv hτ => ?_⟩
  · rw [← hu, MulChar.ofUnitHom_coe]
    rfl
  · rw [hχ τ, hβ u, cycChar_frob m p hp hpm v τ hv hτ, ← hu]

end X1Dirichlet
end
end DirichletCopy

namespace RvGP2
/-- Field 22 of `GluePieces2` from the bundle leaf `t.t17` (narrowed Kronecker–Weber). -/
theorem dirichletOfFinite (t : HSyn.TextbookLeaves) : G0ModNewform.DirichletOfFinite :=
  X1Dirichlet.dirichletOfFinite_of_kroneckerWeberCyclic t.t17
end RvGP2

#print axioms RvGP2.dirichletOfFinite
