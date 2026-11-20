import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Phase

/-! The finite rational idèle character of the negative discriminant.
Divide an idèle by the positive rational number with the same valuations
and apply the ramified Legendre factors to the resulting units. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic LocalWeights

/-- The additive valuation viewed as a multiplicative homomorphism on local units
of the field (without an integrality restriction). -/
def valHom (q : Prime) : ℚ_[q.val]ˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd u.val.valuation
  map_one' := by simp
  map_mul' u v := Padic.valuation_mul u.ne_zero v.ne_zero

/-- The restricted group of finite idèles of the rational field. -/
def rationalIdeles : Subgroup ((q : Prime) → ℚ_[q.val]ˣ) where
  carrier := {z | {q : Prime | valHom q (z q) ≠ 1}.Finite}
  one_mem' := by simp
  mul_mem' {x y} hx hy := (hx.union hy).subset fun q hq => by
    by_contra hn
    have h : ¬ valHom q (x q) ≠ 1 ∧ ¬ valHom q (y q) ≠ 1 := not_or.mp hn
    exact hq (by simp only [Pi.mul_apply, map_mul, not_not.mp h.1, not_not.mp h.2, mul_one])
  inv_mem' {x} hx := hx.subset fun q hq h => hq (by simp [h])

/-- Positive rational prime as a unit of the rational field. -/
def rationalPrime (q : Prime) : ℚˣ := Units.mk0 q.val (by exact_mod_cast q.prop.ne_zero)

def rationalToLocal (q : Prime) : ℚˣ →* ℚ_[q.val]ˣ :=
  Units.map (algebraMap ℚ ℚ_[q.val]).toMonoidHom

/-- Away from this prime the rational prime is a local unit. -/
theorem val_rationalPrime (p q : Prime) :
    (valHom p (rationalToLocal p (rationalPrime q))).toAdd = if q = p then 1 else 0 := by
  classical
  change ((q.val : ℚ_[p.val])).valuation = _
  rw [Padic.valuation_natCast]
  split_ifs with h
  · subst q
    simp [padicValNat_self]
  · have hn : ¬ p.val ∣ q.val := fun hd =>
        h (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.prop q.prop).mp hd).symm)
    rw [padicValNat.eq_zero_of_not_dvd hn, Nat.cast_zero]

private theorem rationalPart_support (z : rationalIdeles) :
    Function.HasFiniteMulSupport (fun q : Prime => rationalPrime q ^ (z.val q).val.valuation) :=
  z.prop.subset fun q hq h => hq (by
    have he : (z.val q).val.valuation = 0 := h
    simp [he])

/-- The positive rational with the same finite valuations as the idèle. -/
def rationalPart : rationalIdeles →* ℚˣ where
  toFun z := ∏ᶠ q : Prime, rationalPrime q ^ (z.val q).val.valuation
  map_one' := by
    apply finprod_eq_one_of_forall_eq_one
    simp
  map_mul' x y := by
    simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul]
    simp_rw [fun q : Prime => Padic.valuation_mul (x.val q).ne_zero (y.val q).ne_zero, zpow_add]
    exact finprod_mul_distrib (rationalPart_support x) (rationalPart_support y)

theorem rationalPart_pos (z : rationalIdeles) : 0 < (rationalPart z : ℚˣ).val := by
  change 0 < (↑(∏ᶠ q : Prime, rationalPrime q ^ (z.val q).val.valuation) : ℚ)
  rw [finprod_eq_prod _ (rationalPart_support z), Units.coe_prod]
  exact Finset.prod_pos (fun q _ => by
    rw [Units.val_zpow_eq_zpow_val]
    exact zpow_pos (show (0 : ℚ) < (q.val : ℚ) by exact_mod_cast q.prop.pos) _)

theorem rationalPart_valuation (p : Prime) (z : rationalIdeles) :
    valHom p (rationalToLocal p (rationalPart z)) = valHom p (z.val p) := by
  classical
  change ((valHom p).comp (rationalToLocal p)) (∏ᶠ q : Prime,
      rationalPrime q ^ (z.val q).val.valuation) = _
  rw [map_finprod _ (rationalPart_support z)]
  let f (q : Prime) := ((valHom p).comp (rationalToLocal p))
      (rationalPrime q ^ (z.val q).val.valuation)
  change (∏ᶠ q : Prime, f q) = _
  have hf : ∀ q : Prime, f q = if q = p then valHom p (z.val p) else 1 := by
    intro q
    simp only [f, map_zpow, MonoidHom.comp_apply]
    by_cases hq : q = p
    · subst q
      rw [ite_eq_left rfl]
      change Multiplicative.ofAdd
        ((z.val p).val.valuation * (valHom p (rationalToLocal p (rationalPrime p))).toAdd) = _
      rw [val_rationalPrime, ite_eq_left rfl, mul_one]
      rfl
    · rw [ite_eq_right hq]
      have h : valHom p (rationalToLocal p (rationalPrime q)) = 1 := by
        change Multiplicative.ofAdd ((valHom p (rationalToLocal p (rationalPrime q))).toAdd) = _
        rw [val_rationalPrime, ite_eq_right hq]
        rfl
      rw [h, one_zpow]
  rw [finprod_eq_single f p (fun q hq => (hf q).trans (ite_eq_right hq)), hf, ite_eq_left rfl]

private def normalizedUnit (p : Prime) (z : rationalIdeles) : ℚ_[p.val]ˣ :=
  z.val p / rationalToLocal p (rationalPart z)

private theorem normalized_valuation (p : Prime) (z : rationalIdeles) :
    (normalizedUnit p z).val.valuation = 0 := by
  change valHom p (normalizedUnit p z) = 1
  rw [normalizedUnit, map_div, rationalPart_valuation, div_self']

/-- View a field unit of valuation zero as a unit of the local integer ring. -/
def integralUnit (p : Prime) (u : ℚ_[p.val]ˣ) (h : u.val.valuation = 0) : ℤ_[p.val]ˣ :=
  { val := ⟨u.val, (Padic.norm_le_one_iff_val_nonneg _).mpr h.ge⟩
    inv := ⟨u.inv, (Padic.norm_le_one_iff_val_nonneg _).mpr (by
      rw [Units.inv_eq_val_inv, Units.val_inv_eq_inv_val, Padic.valuation_inv, h, neg_zero])⟩
    val_inv := Subtype.ext u.val_inv
    inv_val := Subtype.ext u.inv_val }

theorem integralUnit_val (p : Prime) (u : ℚ_[p.val]ˣ) (h : u.val.valuation = 0) :
    ((integralUnit p u h).val : ℚ_[p.val]) = u.val := rfl

/-- The unit component after removing the positive rational part. -/
def localUnitPart (p : Prime) (z : rationalIdeles) : ℤ_[p.val]ˣ :=
  integralUnit p (normalizedUnit p z) (normalized_valuation p z)

theorem localUnitPart_val (p : Prime) (z : rationalIdeles) :
    ((localUnitPart p z).val : ℚ_[p.val]) =
      (z.val p / rationalToLocal p (rationalPart z)).val := rfl

/-- The normalized unit component is multiplicative. -/
def unitPartHom (p : Prime) : rationalIdeles →* ℤ_[p.val]ˣ where
  toFun := localUnitPart p
  map_one' := by
    apply Units.ext
    apply Subtype.val_injective
    change ((localUnitPart p 1).val : ℚ_[p.val]) = 1
    rw [localUnitPart_val, map_one, map_one]
    simp
  map_mul' x y := by
    apply Units.ext
    apply Subtype.val_injective
    change ((localUnitPart p (x * y)).val : ℚ_[p.val]) =
      ((localUnitPart p x).val : ℚ_[p.val]) * ((localUnitPart p y).val : ℚ_[p.val])
    simp only [localUnitPart_val, map_mul, Subgroup.coe_mul, Pi.mul_apply]
    rw [← Units.val_mul, div_mul_div_comm]

/-- Finite idele character of `−m`, for squarefree `m ≡ 3 mod 4`.
`S` is the set of primes dividing `m`. -/
def discriminantCharacter {O : Type} [CommRing O] (S : Finset Prime) :
    rationalIdeles →* Oˣ where
  toFun z := ∏ q ∈ S, legendreUnit q.val (localUnitPart q z)
  map_one' := by
    apply Finset.prod_eq_one
    intro q _
    change legendreUnit q.val (unitPartHom q 1) = 1
    rw [map_one, map_one]
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro q _
    change legendreUnit q.val (unitPartHom q (x * y)) = _
    rw [map_mul, map_mul]
    rfl

theorem rationalPart_of_units (z : rationalIdeles)
    (hz : ∀ q : Prime, valHom q (z.val q) = 1) :
    rationalPart z = 1 := by
  apply finprod_eq_one_of_forall_eq_one
  intro q
  have hq : (z.val q).val.valuation = 0 := hz q
  rw [hq, zpow_zero]

/-- A positive rational number with zero valuation at every prime is one. -/
theorem positive_rational_unit (u : ℚˣ) (hpos : 0 < u.val)
    (h : ∀ q : Prime, valHom q (rationalToLocal q u) = 1) : u = 1 := by
  have hint (v : ℚˣ) (hv : ∀ q : Prime, valHom q (rationalToLocal q v) = 1) :
      ∃ a : ℤ, (a : ℚ) = v.val := by
    apply rat_integral_of_local
    intro q
    let w := rationalToLocal q v
    have hw : w.val.valuation = 0 := hv q
    exact ⟨(integralUnit q w hw).val, integralUnit_val q w hw⟩
  obtain ⟨a, ha⟩ := hint u h
  obtain ⟨b, hb⟩ := hint u⁻¹ (fun q => by rw [map_inv, map_inv, h q, inv_one])
  have hab : a * b = 1 := by
    exact_mod_cast (show (a : ℚ) * (b : ℚ) = 1 from by rw [ha, hb]; exact Units.mul_inv u)
  have hu : IsUnit a := isUnit_of_dvd_one ⟨b, hab.symm⟩
  apply Units.ext
  rcases Int.isUnit_iff.mp hu with h₁ | h₁
  · rw [← ha, h₁]
    rfl
  · exfalso
    rw [← ha, h₁] at hpos
    norm_num at hpos

/-- A positive diagonal is precisely its reconstructed valuation part. -/
theorem rationalPart_diagonal (z : rationalIdeles) (u : ℚˣ)
    (hpos : 0 < u.val) (h : ∀ q : Prime, z.val q = rationalToLocal q u) :
    rationalPart z = u := by
  have h₁ : rationalPart z / u = 1 := positive_rational_unit _
    (by
      push_cast
      exact div_pos (rationalPart_pos z) hpos)
    (fun q => by rw [map_div, map_div, rationalPart_valuation, h q, div_self'])
  exact div_eq_one.mp h₁

/-- The finite idèle character is trivial on positive rational diagonals. -/
theorem discriminantCharacter_diagonal {O : Type} [CommRing O] (S : Finset Prime)
    (z : rationalIdeles) (u : ℚˣ) (hpos : 0 < u.val)
    (h : ∀ q : Prime, z.val q = rationalToLocal q u) :
    discriminantCharacter (O := O) S z = 1 := by
  apply Finset.prod_eq_one
  intro q _
  have hu : localUnitPart q z = 1 := by
    apply Units.ext
    apply Subtype.val_injective
    rw [localUnitPart_val, rationalPart_diagonal z u hpos h, h q, div_self']
    rfl
  rw [hu, map_one]

end ZInQ.Manuscript.RC.ThetaJoin
