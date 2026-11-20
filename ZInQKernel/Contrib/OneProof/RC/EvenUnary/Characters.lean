import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Assembly

/-! Periodic coefficient and scalar characters for the unary series
(tex 9548–9555 and 9618–9625). -/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Manuscript.RC.EvenUnary

open AddressGenuine AuxInputs EvenBudget EvenExpansion PrintsAnalytic Wiring
open ZInQ.Manuscript.RC.Even
open ZInQ.Contrib.CloudB3RC53

/-- The odd character with value `(-1/n)` on odd positive integers. -/
def signCharacter : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- Lifting to the full support modulus realizes the coprimality sieve by
the zero values at nonunits. The parity twist does not alter these zeros. -/
def sievedCharacter {N B : ℕ} (η : DirichletCharacter ℂ N)
    (hN : N ∣ B) (h4 : 4 ∣ B) (i : Fin 2) : DirichletCharacter ℂ B :=
  η.changeLevel hN * (signCharacter.changeLevel h4) ^ i.val

private theorem changeLevel_int {N B : ℕ} (η : DirichletCharacter ℂ N) (hN : N ∣ B)
    (n : ℤ) (hn : IsUnit (n : ZMod B)) : η.changeLevel hN n = η n := by
  rw [← hn.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd, hn.unit_spec,
    ZMod.cast_intCast hN]

private theorem character_pow_unit {B : ℕ} (χ : DirichletCharacter ℂ B)
    (k : ℕ) (a : ZMod B) (ha : IsUnit a) : (χ ^ k) a = χ a ^ k := by
  rw [← ha.unit_spec, MulChar.pow_apply_coe]

theorem sievedCharacter_odd {N B : ℕ} (η : DirichletCharacter ℂ N) (hN : N ∣ B)
    (h4 : 4 ∣ B) (i : Fin 2) (hodd : η (-1 : ZMod N) * (-1 : ℂ) ^ i.val = -1) :
    (sievedCharacter η hN h4 i).Odd := by
  have hn : IsUnit ((-1 : ℤ) : ZMod B) := by simp
  rw [DirichletCharacter.Odd, ← Int.cast_one, ← Int.cast_neg]
  rw [sievedCharacter, MulChar.mul_apply, character_pow_unit _ _ _ hn, changeLevel_int η hN _ hn,
    changeLevel_int signCharacter h4 _ hn]
  have he : signCharacter ((-1 : ℤ) : ZMod 4) = -1 := by
    change ((ZMod.χ₄ (-1) : ℤ) : ℂ) = -1
    rw [show ZMod.χ₄ (-1) = -1 by decide]
    norm_num
  rw [he]
  simpa only [Int.cast_neg, Int.cast_one] using hodd

theorem sievedCharacter_at_unit {N B : ℕ} (η : DirichletCharacter ℂ N) (hN : N ∣ B)
    (h4 : 4 ∣ B) (i : Fin 2) {n : ℕ} (hn : n.Coprime B) :
    sievedCharacter η hN h4 i n = η n * (jacobiSym (-1) n : ℂ) ^ i.val := by
  have hu : IsUnit ((n : ℤ) : ZMod B) := by
    rw [Int.cast_natCast, ZMod.isUnit_iff_coprime]
    exact hn
  have htwo : 2 ∣ B := (show (2 : ℕ) ∣ 4 by decide).trans h4
  have hodd : Odd n := odd_of_coprime_of_two_dvd htwo hn
  have he : signCharacter n = (jacobiSym (-1) n : ℂ) := by
    change ((ZMod.χ₄ n : ℤ) : ℂ) = _
    rw [jacobiSym.at_neg_one hodd, ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hodd)]
  rw [sievedCharacter, MulChar.mul_apply, ← Int.cast_natCast (R := ZMod B),
    character_pow_unit _ _ _ hu, changeLevel_int η hN _ hu,
    changeLevel_int signCharacter h4 _ hu]
  simp only [Int.cast_natCast, he]

theorem good_factors_iff_coprime {ℓ : ℕ} {W : WData ℓ} (hS : SupportSpec W)
    {k : ℕ} (hk : k ≠ 0) :
    (∀ p ∈ k.primeFactors, (evenTypes W.S hS.1).Good p) ↔
      k.Coprime (conductor W.S) := by
  rw [coprime_conductor hS.1 hS.2.1]
  constructor
  · intro h p hp hd
    exact ((good_iff hS p).mp (h p (Nat.mem_primeFactors.mpr ⟨hS.1 p hp, hd, hk⟩))).2 hp
  · intro h p hp
    obtain ⟨hp', hpk, _⟩ := Nat.mem_primeFactors.mp hp
    exact (good_iff hS p).mpr ⟨hp', fun hpS => h p hpS hpk⟩

theorem coprime_supportModulus {ℓ : ℕ} {W : WData ℓ}
    {L : CentralNormalization (Ecurve ℓ)} {τ : SqClass (conductor W.S)}
    (P : EvenSource W L τ) (hS : SupportSpec W) (n : ℕ) :
    n.Coprime (P.phaseData.N * conductor W.S) ↔ n.Coprime (conductor W.S) := by
  refine ⟨fun h => h.coprime_dvd_right (dvd_mul_left _ _), fun h => ?_⟩
  apply coprime_of_support
  · intro p hp hd
    exact (hp.dvd_mul.mp hd).elim (P.phaseData.hNS p hp)
      ((conductor_support hS.1 hS.2.1 hp).mp)
  · exact (coprime_conductor hS.1 hS.2.1 _).mp h

theorem four_mul_sq_dvd_cube {B : ℕ} (h4 : 4 ∣ B) : 4 * B ^ 2 ∣ B ^ 3 := by
  calc
    4 * B ^ 2 ∣ B * B ^ 2 := Nat.mul_dvd_mul_right h4 (B ^ 2)
    _ = B ^ 3 := by ring

private theorem odd_unit {M : ℕ} [NeZero M] (h4 : 4 ∣ M) (u : (ZMod M)ˣ) :
    Odd (u : ZMod M).val := by
  apply odd_of_coprime_of_two_dvd ((show (2 : ℕ) ∣ 4 by decide).trans h4)
  apply (ZMod.isUnit_iff_coprime _ M).mp
  rw [ZMod.natCast_zmod_val]
  exact u.isUnit

private theorem jacobiUnitHom_one {M : ℕ} [NeZero M] (h4 : 4 ∣ M) (D : ℤ) :
    (jacobiSym D ((1 : (ZMod M)ˣ) : ZMod M).val : ℂ) = 1 := by
  have hm : M ≠ 1 := fun h => by simp [h] at h4
  simp [ZMod.val_one'' hm, jacobiSym.one_right]

private def jacobiUnitHom {M : ℕ} [NeZero M] (h4 : 4 ∣ M)
    (D : ℤ) (hD : 4 * D.natAbs ∣ M) : (ZMod M)ˣ →* ℂ where
  toFun u := (jacobiSym D (u : ZMod M).val : ℂ)
  map_one' := jacobiUnitHom_one h4 D
  map_mul' u v := by
    let n := (u : ZMod M).val * (v : ZMod M).val
    have hn : Odd n := (odd_unit h4 u).mul (odd_unit h4 v)
    have huv : Odd (n % M) := by
      simpa only [n, ← ZMod.val_mul, ← Units.val_mul] using odd_unit h4 (u * v)
    change (jacobiSym D ((u * v : (ZMod M)ˣ) : ZMod M).val : ℂ) =
      (jacobiSym D (u : ZMod M).val : ℂ) * (jacobiSym D (v : ZMod M).val : ℂ)
    have hu : (u : ZMod M).val ≠ 0 := by obtain ⟨_, h⟩ := odd_unit h4 u; omega
    have hv : (v : ZMod M).val ≠ 0 := by obtain ⟨_, h⟩ := odd_unit h4 v; omega
    rw [Units.val_mul, ZMod.val_mul, ← Int.cast_mul, ← jacobiSym.mul_right' D hu hv]
    change (jacobiSym D (n % M) : ℂ) = (jacobiSym D n : ℂ)
    rw [jacobiSym.mod_right D huv, Nat.mod_mod_of_dvd _ hD, ← jacobiSym.mod_right D hn]

/-- The Jacobi symbol in the bottom-right entry is a genuine character
on the units whenever its period divides the level. -/
def jacobiCharacter {M : ℕ} [NeZero M] (h4 : 4 ∣ M)
    (D : ℤ) (hD : 4 * D.natAbs ∣ M) : DirichletCharacter ℂ M :=
  MulChar.ofUnitHom (jacobiUnitHom h4 D hD).toHomUnits

theorem jacobiCharacter_at_unit {M : ℕ} [NeZero M] (h4 : 4 ∣ M)
    (D : ℤ) (hD : 4 * D.natAbs ∣ M) {n : ℕ} (hn : n.Coprime M) :
    jacobiCharacter h4 D hD n = (kronecker D n : ℂ) := by
  have hu := (ZMod.isUnit_iff_coprime n M).mpr hn
  have ho : Odd n := odd_of_coprime_of_two_dvd ((show (2 : ℕ) ∣ 4 by decide).trans h4) hn
  have ho' : Odd (n % M) := by
    simpa only [hu.unit_spec, ZMod.val_natCast] using odd_unit h4 hu.unit
  have hk : n.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (Nat.not_even_iff_odd.mpr ho ∘ even_iff_two_dvd.mpr)
  rw [kronecker, hk, pow_zero, pow_zero, Nat.div_one, one_mul]
  conv_lhs => rw [← hu.unit_spec, jacobiCharacter, MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits]
  change (jacobiSym D (hu.unit : ZMod M).val : ℂ) = _
  rw [hu.unit_spec, ZMod.val_natCast, jacobiSym.mod_right D ho',
    Nat.mod_mod_of_dvd _ hD, ← jacobiSym.mod_right D ho]

end ZInQ.Manuscript.RC.EvenUnary
