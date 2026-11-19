import ZInQKernel.Contrib.OneProof.RC.ThetaCoeff.Blocks

/-! The common diamond group is the unit group of the common level. The
quadratic characters are constructed from Jacobi symbols (tex 9497–9555,
9618–9625), with least nonnegative representatives. -/

noncomputable section

namespace ZInQ.Manuscript.RC.BlocksPerU

open ThetaCoeff
open scoped BigOperators

variable {N : ℕ} [NeZero N]

abbrev representative (u : (ZMod N)ˣ) : ℕ := (u : ZMod N).val

theorem representative_modEq (q : ℕ) (h : q.Coprime N) :
    representative (ZMod.unitOfCoprime q h) ≡ q [MOD N] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [ZMod.natCast_zmod_val, ZMod.coe_unitOfCoprime]

omit [NeZero N] in
private theorem representative_odd (hN : 4 ∣ N) (u : (ZMod N)ˣ) :
    Odd (representative u) := by
  have h := (ZMod.val_coe_unit_coprime u).of_dvd_right
    (dvd_trans (by decide : 2 ∣ 4) hN)
  exact Nat.odd_iff.mpr (Nat.mod_two_ne_zero.mp (fun e =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h.symm (Nat.dvd_of_mod_eq_zero e)))

omit [NeZero N] in
private theorem jacobi_isUnit (d : ℤ) (hd : (4 * d : ℤ) ∣ (N : ℤ))
    (u : (ZMod N)ˣ) : IsUnit (jacobiSym d (representative u)) := by
  have hdiv : 4 * d.natAbs ∣ N := by
    simpa [Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr hd
  have hc : d.gcd (representative u : ℤ) = 1 :=
    ((ZMod.val_coe_unit_coprime u).of_dvd_right ((dvd_mul_left d.natAbs 4).trans hdiv)).symm
  rcases jacobiSym.eq_one_or_neg_one hc with h | h <;> rw [h] <;> simp

private def jacobiCharacter (hN : 4 ∣ N) (d : ℤ) (hd : (4 * d : ℤ) ∣ (N : ℤ)) :
    (ZMod N)ˣ →* ℤˣ where
  toFun u := (jacobi_isUnit d hd u).unit
  map_one' := by
    apply Units.ext
    rw [IsUnit.unit_spec, Units.val_one]
    have hn : 1 < N := by
      have := Nat.le_of_dvd (NeZero.pos N) hN
      omega
    change jacobiSym d (1 : ZMod N).val = 1
    rw [← Nat.cast_one, ZMod.val_natCast_of_lt hn, jacobiSym.one_right]
  map_mul' u v := by
    apply Units.ext
    rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, IsUnit.unit_spec]
    have hdiv : 4 * d.natAbs ∣ N := by
      simpa [Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr hd
    have hm : representative (u * v) ≡ representative u * representative v [MOD N] := by
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        Units.val_mul]
    rw [jacobiSym.mod_right d (representative_odd hN _),
      (hm.of_dvd hdiv), ← jacobiSym.mod_right d ((representative_odd hN u).mul
        (representative_odd hN v)),
      jacobiSym.mul_right' _ (by have := representative_odd hN u; rcases this with ⟨k, hk⟩; omega)
        (by have := representative_odd hN v; rcases this with ⟨k, hk⟩; omega)]

/-- Only discriminants whose indicated modulus divides the common level
have prescribed values; elsewhere use the trivial character. -/
def diamondCharacters {O : Type} [CommRing O] {ηsource : ℕ → O}
    (hN : 4 ∣ N) (η : (ZMod N)ˣ →* Oˣ)
    (hη : ∀ u, (η u : O) = ηsource (representative u))
    (horder : ∀ u, ∃ e : ℕ, (η u : O) ^ (2 ^ e : ℕ) = 1) :
    DiamondCharacters O (ZMod N)ˣ ηsource where
  level := N
  level_pos := NeZero.pos N
  four_dvd := hN
  minusOne := -1
  representative := representative
  representative_coprime := ZMod.val_coe_unit_coprime
  minusOne_rep := by
    apply (ZMod.natCast_eq_natCast_iff _ 0 N).mp
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
    simp
  η := η
  η_eval := hη
  symbol d := if hd : (4 * d : ℤ) ∣ (N : ℤ) then jacobiCharacter hN d hd else 1
  symbol_eval d u hd := by rw [dite_eq_left hd]; exact IsUnit.unit_spec _
  phase_order := horder

variable {O K G : Type} [CommRing O] [Field K] [Algebra O K] [Group G]
variable {ηsource : ℕ → O}

/-- Common-level character of the ternary-derived block. -/
def bCharacter (C : DiamondCharacters O G ηsource) (U : Finset ℕ) : G →* Kˣ :=
  (Units.map (algebraMap O K)).comp C.η *
    (Units.map (Int.castRingHom K)).comp (C.symbol (-1) * ∏ p ∈ U, C.symbol (p : ℤ))

/-- Common-level character of a unary correction. -/
def unaryCharacter (C : DiamondCharacters O G ηsource) (i : Fin 2) (j : ℕ) : G →* Kˣ :=
  (Units.map (algebraMap O K)).comp C.η *
    (Units.map (Int.castRingHom K)).comp (C.symbol (-1) ^ i.val * C.symbol (-(j : ℤ)))

theorem bCharacter_value (C : DiamondCharacters O G ηsource) (U : Finset ℕ) (u : G) :
    (bCharacter (K := K) C U u : K) = algebraMap O K (C.ψ U u) := by
  simp [bCharacter, DiamondCharacters.ψ, MonoidHom.finsetProd_apply]

theorem unaryCharacter_value (C : DiamondCharacters O G ηsource) (i : Fin 2) (j : ℕ) (u : G) :
    (unaryCharacter (K := K) C i j u : K) = algebraMap O K (C.unaryChar i j u) := by
  simp [unaryCharacter, DiamondCharacters.unaryChar]

#print axioms representative_modEq
#print axioms representative_odd
#print axioms jacobi_isUnit
#print axioms diamondCharacters
#print axioms bCharacter_value
#print axioms unaryCharacter_value

end ZInQ.Manuscript.RC.BlocksPerU
