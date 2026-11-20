import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.LevelTheta
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Characters

/-! Appendix F (O.3): choose the finite level characters and realize all
their values in the valuation ring of their generated field. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaClose

open Adelic ThetaJoin LocalWeights NumberField IsDedekindDomain

/-- Arithmetic data from the fixed negative odd discriminant and the
detecting prime. The level is prime to the detecting prime separately. -/
structure DiscriminantData (m N ell : ℕ) : Prop where
  odd : m % 4 = 3
  squarefree : Squarefree m
  twoSplit : Int.ModEq 8 (-(m : ℤ)) 1
  levelSplit : ∀ q : Prime, q.val ≠ 2 → q.val ∣ N → jacobiSym (-(m : ℤ)) q.val = 1
  inert : jacobiSym (-(m : ℤ)) ell = -1

theorem prime_not_dvd_of_symbol_ne_zero (q : Prime) (n : ℕ)
    (hs : jacobiSym (-(n : ℤ)) q.val ≠ 0) : ¬ q.val ∣ n := by
  let : NeZero q.val := ⟨q.prop.ne_zero⟩
  have hc : (-(n : ℤ)).gcd q.val = 1 := by
    by_contra h
    exact hs (jacobiSym.eq_zero_iff_not_coprime.mpr h)
  rw [Int.gcd_eq_natAbs] at hc
  have hn : n.Coprime q.val := by simpa using hc
  exact q.prop.coprime_iff_not_dvd.mp hn.symm

theorem discriminantDisjoint {m N ell : ℕ} [Fact ell.Prime]
    (H : DiscriminantData m N ell) : DisjointDiscriminant m N ell := by
  have h₂ : ¬ 2 ∣ m := by
    have hm := H.odd
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  intro q hq
  have hne : q.val ≠ 2 := fun he => h₂ (he ▸ hq)
  refine ⟨?_, fun hd => prime_not_dvd_of_symbol_ne_zero q m
    (by rw [H.levelSplit q hne hd]; decide) hq, hne⟩
  intro he
  exact prime_not_dvd_of_symbol_ne_zero ⟨ell, Fact.out⟩ m (by rw [H.inert]; decide) (he ▸ hq)

private theorem levelCoprime {m N ell : ℕ} [Fact ell.Prime]
    (H : DiscriminantData m N ell) (q : Prime) (hq : q.val ∣ N) : m.Coprime q.val := by
  apply Nat.Coprime.symm
  apply q.prop.coprime_iff_not_dvd.mpr
  intro hm
  exact (discriminantDisjoint H q hm).2.1 hq

/-- The integer unit prescribed in (O.3), before passing to the coefficient ring. -/
def prescribedParity {m N ell : ℕ} [Fact ell.Prime] (H : DiscriminantData m N ell)
    (w : ℕ → ℤˣ) (q : Prime) (hq : q.val ∣ N) : ℤˣ :=
  w q.val * ((show IsUnit (jacobiSym (-(m : ℤ)) q.val) from by
    apply Int.isUnit_iff.mpr
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.gcd_eq_natAbs]
    simpa using levelCoprime H q hq).unit ^ N.factorization q.val)

theorem prescribedParity_val {m N ell : ℕ} [Fact ell.Prime] (H : DiscriminantData m N ell)
    (w : ℕ → ℤˣ) (q : Prime) (hq : q.val ∣ N) :
    (prescribedParity H w q hq : ℤ) =
      (w q.val : ℤ) * jacobiSym (-(m : ℤ)) q.val ^ N.factorization q.val := by
  unfold prescribedParity
  rw [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]

private theorem complexCharacter (q : Prime) (s : ℤˣ) :
    ∃ k : ℕ, ∃ α : (ZMod (rootModulus q))ˣ →* ℂˣ,
      α (-1) = Units.map (Int.castRingHom ℂ).toMonoidHom s ∧
      ∀ u, α u ^ (2 ^ k : ℕ) = 1 := by
  have hs : s = 1 ∨ s = -1 := by
    rcases Int.isUnit_iff.mp s.isUnit with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  let s' := Units.map (Int.castRingHom ℂ).toMonoidHom s
  have hs' : s' = 1 ∨ s' = -1 := by
    rcases hs with h | h
    · exact Or.inl (by simp [s', h])
    · right; apply Units.ext; simp [s', h]
  let P (n : ℕ) := ∃ k : ℕ, ∃ α : (ZMod n)ˣ →* ℂˣ,
    α (-1) = s' ∧ ∀ u, α u ^ (2 ^ k : ℕ) = 1
  change P (rootModulus q)
  by_cases he : q.val = 2
  · have hm : rootModulus q = 4 := by simp [rootModulus, he]
    rw [hm]
    obtain ⟨α, hα, hp⟩ := dyadic_character_exists s' hs'
    exact ⟨1, α, hα, by simpa using hp⟩
  · have hm : rootModulus q = q.val := by simp [rootModulus, he]
    rw [hm]
    exact odd_character_complex he s' hs'

variable {m N ell : ℕ} [Fact ell.Prime] (hN : 0 < N)
variable (H : DiscriminantData m N ell) (w : ℕ → ℤˣ)

private theorem chosen (q : Prime) (hq : q.val ∣ N) :
    ∃ k : ℕ, ∃ α : (ZMod (rootModulus q))ˣ →* ℂˣ,
      α (-1) = Units.map (Int.castRingHom ℂ).toMonoidHom (prescribedParity H w q hq) ∧
      ∀ u, α u ^ (2 ^ k : ℕ) = 1 :=
  complexCharacter q (prescribedParity H w q hq)

private def boundPrimes : Finset Prime := (finite_prime_dvd hN.ne').toFinset

private theorem mem_boundPrimes (q : Prime) : q ∈ boundPrimes hN ↔ q.val ∣ N := by
  simp [boundPrimes]

/-- Use the supremum of the individual two-power exponents over the level primes. -/
def complexRoots : LevelRoots ℂ N where
  alpha q hq := (chosen H w q hq).choose_spec.choose
  exponent := (boundPrimes hN).attach.sup fun q =>
    (chosen H w q.val ((mem_boundPrimes hN q.val).mp q.prop)).choose
  order q hq u := by
    let T := boundPrimes hN
    let i : T := ⟨q, (mem_boundPrimes hN q).mpr hq⟩
    have hi : i ∈ T.attach := Finset.mem_attach _ _
    have hk := Finset.le_sup (f := fun q : T =>
      (chosen H w q.val ((mem_boundPrimes hN q.val).mp q.prop)).choose) hi
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one
      ((chosen H w q hq).choose_spec.choose_spec.2 u)).trans (pow_dvd_pow 2 hk))

theorem complexRoots_parity (q : Prime) (hq : q.val ∣ N) :
    (complexRoots hN H w).alpha q hq (-1) =
      Units.map (Int.castRingHom ℂ).toMonoidHom (prescribedParity H w q hq) :=
  (chosen H w q hq).choose_spec.choose_spec.1

/-- All values of the chosen level characters, as complex numbers. -/
def characterValues : Set ℂ :=
  {z | ∃ (q : Prime) (hq : q.val ∣ N) (u : (ZMod (rootModulus q))ˣ),
    z = ((complexRoots hN H w).alpha q hq u : ℂ)}

theorem characterValues_order {z : ℂ} (hz : z ∈ characterValues hN H w) :
    z ^ (2 ^ (complexRoots hN H w).exponent : ℕ) = 1 := by
  obtain ⟨q, hq, u, rfl⟩ := hz
  exact congrArg Units.val ((complexRoots hN H w).order q hq u)

abbrev CharacterField := IntermediateField.adjoin ℚ (characterValues hN H w)

instance characterFieldNumberField : NumberField (CharacterField hN H w) :=
  characterField_numberField ⟨_, fun _ hz => characterValues_order hN H w hz⟩

/-- The coefficient place is chosen over two in the actual character field. -/
def coefficientPlace : HeightOneSpectrum (𝓞 (CharacterField hN H w)) :=
  (coefficientPlace_exists (CharacterField hN H w)).choose

theorem coefficientPlace_over_two :
    (2 : 𝓞 (CharacterField hN H w)) ∈ (coefficientPlace hN H w).asIdeal :=
  (coefficientPlace_exists (CharacterField hN H w)).choose_spec

abbrev Coefficients :=
  coefficientRing (CharacterField hN H w) (coefficientPlace hN H w)

private theorem liftCharacter (q : Prime) (hq : q.val ∣ N) :
    ∃ α : (ZMod (rootModulus q))ˣ →* (Coefficients hN H w)ˣ,
      ∀ u, ((((α u).val : CharacterField hN H w)) : ℂ) =
        ((complexRoots hN H w).alpha q hq u : ℂ) :=
  character_lifts_to_coefficients ((complexRoots hN H w).alpha q hq)
    (characterValues hN H w) (fun u => ⟨q, hq, u, rfl⟩) (by positivity)
    ((complexRoots hN H w).order q hq) (coefficientPlace hN H w)

/-- (O.3) in the coefficient ring at a place above two of the field of values. -/
def levelRoots : LevelRoots (Coefficients hN H w) N where
  alpha q hq := (liftCharacter hN H w q hq).choose
  exponent := (complexRoots hN H w).exponent
  order q hq u := by
    apply Units.ext
    apply Subtype.val_injective
    apply Subtype.val_injective
    change ((((liftCharacter hN H w q hq).choose u).val :
      CharacterField hN H w) : ℂ) ^ (2 ^ (complexRoots hN H w).exponent : ℕ) = 1
    rw [(liftCharacter hN H w q hq).choose_spec]
    exact congrArg Units.val ((complexRoots hN H w).order q hq u)

theorem levelRoots_parity :
    (levelRoots hN H w).ParityAt m
      (fun q => Units.map (Int.castRingHom (Coefficients hN H w)).toMonoidHom (w q)) := by
  intro q hq
  apply Subtype.val_injective
  apply Subtype.val_injective
  change ((((liftCharacter hN H w q hq).choose (-1)).val :
      CharacterField hN H w) : ℂ) =
    ((w q.val : ℤ) : ℂ) * (jacobiSym (-(m : ℤ)) q.val : ℂ) ^ N.factorization q.val
  rw [(liftCharacter hN H w q hq).choose_spec, complexRoots_parity]
  change ((prescribedParity H w q hq : ℤ) : ℂ) = _
  rw [prescribedParity_val, Int.cast_mul, Int.cast_pow]

end ZInQ.Manuscript.RC.ThetaClose
