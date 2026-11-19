import ZInQKernel.Contrib.OneProof.RC.O12Eisenstein.Characters

/-! At a good prime of the underlying Dirichlet pair, both Eisenstein
characters are unramified and have their ordered good Frobenius values.
This is the cyclotomic calculation for tex 9653–9654 and 9762–9767,
on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Formwise

open AddressGenuine PrintsArith O12Eisenstein

variable {K : Type} [Field K]

/-- The actual Dirichlet data behind a normalized Eisenstein source. Both
moduli divide the level of the occurrence, and the weight twist belongs to
the second character of the divisor sum. -/
structure EisensteinCharacters (α β : ℕ →* K) (level : ℕ) where
  leftMod : ℕ
  rightMod : ℕ
  left_ne : leftMod ≠ 0
  right_ne : rightMod ≠ 0
  left_dvd : leftMod ∣ level
  right_dvd : rightMod ∣ level
  left : DirichletCharacter K leftMod
  right : DirichletCharacter K rightMod
  left_eq : ∀ n : ℕ, left (n : ZMod leftMod) = α n
  right_eq : ∀ n : ℕ, right (n : ZMod rightMod) = β n
  coeffMap : ℤ_[2] →+* K

variable {α β : ℕ →* K} {level : ℕ} (E : EisensteinCharacters α β level)

def EisensteinCharacters.first : GalQ →* Kˣ :=
  letI : NeZero E.leftMod := ⟨E.left_ne⟩
  dirichletGalois E.left

def EisensteinCharacters.second : GalQ →* Kˣ :=
  letI : NeZero E.rightMod := ⟨E.right_ne⟩
  dirichletGalois E.right * weightTwist E.coeffMap

private theorem weight_mod (g : GalQ) (n : ℕ) :
    (cyclotomicCharacter Qbar 2 g.toRingEquiv).val.toZModPow n =
      (cycChar (2 ^ n) g : ZMod (2 ^ n)) := by
  rw [cyclotomicCharacter.toZModPow]
  rfl

private theorem odd_coprime_pow_two {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (n : ℕ) :
    q.Coprime (2 ^ n) :=
  ((hq.coprime_iff_not_dvd.mpr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).not.mpr h2)).pow_right n)

private theorem twist_frob (j : ℤ_[2] →+* K) {q : ℕ} {g : GalQ}
    (hq : q.Prime) (h2 : q ≠ 2) (hg : IsFrobAt g q) : (weightTwist j g : K) = q := by
  have h : (cyclotomicCharacter Qbar 2 g.toRingEquiv).val = (q : ℤ_[2]) := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    rw [weight_mod, map_natCast]
    exact cycChar_of_isFrobAt (2 ^ n) hq (odd_coprime_pow_two hq h2 n) hg
  change j (cyclotomicCharacter Qbar 2 g.toRingEquiv).val = _
  rw [h, map_natCast]

private theorem twist_inertia (j : ℤ_[2] →+* K) {q : ℕ}
    (hq : q.Prime) (h2 : q ≠ 2) {Q : Ideal Zbar}
    (hQ : Q.IsMaximal) (hqQ : ((q : ℤ) : Zbar) ∈ Q)
    {σ : GalQ} (hσ : σ ∈ Q.inertia GalQ) : (weightTwist j σ : K) = 1 := by
  have h : (cyclotomicCharacter Qbar 2 σ.toRingEquiv).val = 1 := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    rw [weight_mod, map_one,
      cycChar_eq_one_of_mem_inertia hq (odd_coprime_pow_two hq h2 n) hQ hqQ hσ,
      Units.val_one]
  change j (cyclotomicCharacter Qbar 2 σ.toRingEquiv).val = _
  rw [h, map_one]

/-- Arithmetic Frobenius evaluates the Dirichlet pair at the prime, with the
factor of `q` on the second line. -/
theorem EisensteinCharacters.frob_values {q : ℕ} {g : GalQ} (hq : q.Prime) (h2 : q ≠ 2)
    (hc : q.Coprime level) (hg : IsFrobAt g q) :
    (E.first g : K) = α q ∧ (E.second g : K) = (q : K) * β q := by
  let : NeZero E.leftMod := ⟨E.left_ne⟩
  let : NeZero E.rightMod := ⟨E.right_ne⟩
  constructor
  · change E.left ((cycChar E.leftMod g : (ZMod E.leftMod)ˣ) : ZMod E.leftMod) = α q
    rw [cycChar_of_isFrobAt _ hq (hc.of_dvd_right E.left_dvd) hg, E.left_eq]
  · change E.right ((cycChar E.rightMod g : (ZMod E.rightMod)ˣ) : ZMod E.rightMod) *
      (weightTwist E.coeffMap g : K) = _
    rw [cycChar_of_isFrobAt _ hq (hc.of_dvd_right E.right_dvd) hg, E.right_eq,
      twist_frob E.coeffMap hq h2 hg, mul_comm]

/-- Off the two character moduli and two, both lines fix inertia. -/
theorem EisensteinCharacters.inertia_values {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2)
    (hc : q.Coprime level) {Q : Ideal Zbar} (hQ : Q.IsMaximal) (hqQ : ((q : ℤ) : Zbar) ∈ Q)
    {σ : GalQ} (hσ : σ ∈ Q.inertia GalQ) : (E.first σ : K) = 1 ∧ (E.second σ : K) = 1 := by
  let : NeZero E.leftMod := ⟨E.left_ne⟩
  let : NeZero E.rightMod := ⟨E.right_ne⟩
  constructor
  · change E.left ((cycChar E.leftMod σ : (ZMod E.leftMod)ˣ) : ZMod E.leftMod) = 1
    rw [cycChar_eq_one_of_mem_inertia hq (hc.of_dvd_right E.left_dvd) hQ hqQ hσ,
      Units.val_one, map_one]
  · change E.right ((cycChar E.rightMod σ : (ZMod E.rightMod)ˣ) : ZMod E.rightMod) *
      (weightTwist E.coeffMap σ : K) = _
    rw [cycChar_eq_one_of_mem_inertia hq (hc.of_dvd_right E.right_dvd) hQ hqQ hσ,
      Units.val_one, map_one, twist_inertia E.coeffMap hq h2 hQ hqQ hσ, mul_one]

#print axioms weight_mod
#print axioms odd_coprime_pow_two
#print axioms twist_frob
#print axioms twist_inertia
#print axioms EisensteinCharacters.frob_values
#print axioms EisensteinCharacters.inertia_values

end ZInQ.Manuscript.RC.O12Formwise
