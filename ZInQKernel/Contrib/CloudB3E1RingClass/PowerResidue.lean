import ZInQKernel.Contrib.CloudB3E1RingClass.GenuineMovingData

/-!
# The `2^n`-th power-residue character on `𝐅_r^×` (the interface's `κ`, `κ_surj`)

Manuscript `diophantine_zq.tex`, tex 3585–3586: "`𝐅_r^×` is cyclic of order `r − 1`, so `κ_r` is
onto when `r ≡ 1 (mod 2^n)`", where `κ_r : 𝐅_r^× → ℤ/2^n` is the `2^n`-th power-residue character
normalized by a primitive `2^n`-th root of unity `ζ̄` (the reduction of `ζ_{2^n}` at the chosen
place).

For a prime `r` with `2^n ∣ r − 1` and a primitive `2^n`-th root of unity `ζ̄ ∈ 𝐅_r^×`,
`exists_powerResidueChar` gives `κ : 𝐅_r^× → ℤ/2^n`, a homomorphism with
`x^{(r−1)/2^n} = ζ̄^{κ(x)}` for every `x`, and onto. Hence the interface's `κ_surj` holds for the
power-residue characters. Kind: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

/-- **The `2^n`-th power-residue character** (tex 3585–3586): for a prime `r` with `2^n ∣ r − 1`
and a primitive `2^n`-th root of unity `ζ̄` in `𝐅_r`, there is an onto homomorphism
`κ : 𝐅_r^× → ℤ/2^n` with `x^{(r−1)/2^n} = ζ̄^{κ(x)}`. Kind: PROVED. -/
theorem exists_powerResidueChar {r n : ℕ} [Fact r.Prime] (hdvd : 2 ^ n ∣ r - 1)
    {ζ : (ZMod r)ˣ} (hζ : IsPrimitiveRoot ζ (2 ^ n)) :
    ∃ κ : Additive (ZMod r)ˣ →+ ZMod (2 ^ n), Function.Surjective κ ∧
      ∀ x : (ZMod r)ˣ, x ^ ((r - 1) / 2 ^ n) = ζ ^ (κ (Additive.ofMul x)).val := by
  classical
  set m := (r - 1) / 2 ^ n with hm
  have hpos : 0 < 2 ^ n := pow_pos two_pos n
  have hN : (r - 1) = 2 ^ n * m := (Nat.mul_div_cancel' hdvd).symm
  have hζ' : IsPrimitiveRoot ((ζ : (ZMod r)ˣ) : ZMod r) (2 ^ n) :=
    IsPrimitiveRoot.coe_units_iff.mpr hζ
  -- every `x^m` is a power of `ζ`
  have hroot : ∀ x : (ZMod r)ˣ, ∃ i < 2 ^ n, ζ ^ i = x ^ m := by
    intro x
    have hx : (((x ^ m : (ZMod r)ˣ)) : ZMod r) ^ (2 ^ n) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, ← hN, ZMod.units_pow_card_sub_one_eq_one,
        Units.val_one]
    obtain ⟨i, hi, hζi⟩ := hζ'.eq_pow_of_pow_eq_one hx
    exact ⟨i, hi, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hζi)⟩
  choose e he he' using hroot
  have hlog : ∀ x : (ZMod r)ˣ, x ^ m = ζ ^ ((e x : ZMod (2 ^ n))).val := by
    intro x
    rw [ZMod.val_natCast_of_lt (he x), he' x]
  let κ : Additive (ZMod r)ˣ →+ ZMod (2 ^ n) :=
    { toFun := fun x => (e (Additive.toMul x) : ZMod (2 ^ n))
      map_zero' := by
        change ((e 1 : ℕ) : ZMod (2 ^ n)) = 0
        have h1 : ζ ^ e 1 = ζ ^ 0 := by rw [he' 1, one_pow, pow_zero]
        rw [pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h1
        rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr h1, Nat.cast_zero]
      map_add' := fun x y => by
        change ((e (Additive.toMul x * Additive.toMul y) : ℕ) : ZMod (2 ^ n)) =
          (e (Additive.toMul x) : ZMod (2 ^ n)) + (e (Additive.toMul y) : ZMod (2 ^ n))
        have h1 : ζ ^ e (Additive.toMul x * Additive.toMul y) =
            ζ ^ (e (Additive.toMul x) + e (Additive.toMul y)) := by
          rw [he', pow_add, he', he', mul_pow]
        rw [pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h1
        rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr h1, Nat.cast_add] }
  refine ⟨κ, ?_, fun x => hlog x⟩
  -- onto: `ζ = y^m` for some `y`, then `κ(y^k) = k κ(y)` and `κ(y) = 1`
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (ZMod.isCyclic_units_prime (Fact.out : r.Prime))
  have hcard : Nat.card (ZMod r)ˣ = r - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hgm : IsPrimitiveRoot (g ^ m) (2 ^ n) := by
    refine IsPrimitiveRoot.iff_orderOf.mpr ?_
    have hmpos : 0 < m := Nat.pos_of_ne_zero (by
      intro h0; rw [h0, mul_zero] at hN
      have := (Fact.out : r.Prime).two_le; omega)
    rw [orderOf_pow' g hmpos.ne', hg, hcard, hN, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ hmpos]
  obtain ⟨j, -, hj⟩ := (IsPrimitiveRoot.coe_units_iff.mpr hgm).eq_pow_of_pow_eq_one
    (show ((ζ : (ZMod r)ˣ) : ZMod r) ^ (2 ^ n) = 1 by
      rw [← Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one])
  have hy : (g ^ j) ^ m = ζ := by
    apply Units.ext
    rw [← pow_mul, mul_comm, pow_mul, Units.val_pow_eq_pow_val]
    exact hj
  have hκy : κ (Additive.ofMul (g ^ j)) = 1 := by
    change ((e (g ^ j) : ℕ) : ZMod (2 ^ n)) = 1
    have h1 : ζ ^ e (g ^ j) = ζ ^ 1 := by rw [he', hy, pow_one]
    rw [pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h1
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr h1, Nat.cast_one]
  intro k
  refine ⟨k.val • Additive.ofMul (g ^ j), ?_⟩
  rw [map_nsmul, hκy, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

end ZInQ.Contrib.CloudB3E1RingClass
