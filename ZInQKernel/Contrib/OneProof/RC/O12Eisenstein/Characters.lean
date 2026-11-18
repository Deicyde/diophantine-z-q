import ZInQKernel.Contrib.OneProof.RC.O12Eisenstein.DivisorSum
import ZInQKernel.Contrib.OneProof.RC.O12.Local
import ZInQKernel.HDecomp.B3Unram.B3b

/-!
# The two normalized Eisenstein Galois characters

Tex 9652–9654, 9762–9771, 9862–9873 and 10358–10360. For the ordered
divisor sum the characters are `χ₁ᴳ` and `χ₂ᴳ ε₂`, with arithmetic
Frobenius. The explicit comparison with the cyclotomic and quadratic
characters already in the tree is on-the-spot (provenance (c)).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Eisenstein

open AddressGenuine O12 PrintsArith

variable {p : ℕ}

/-- Interpret a Dirichlet character on the action on roots of unity. -/
def dirichletGalois {K : Type*} [Field K] {m : ℕ} [NeZero m]
    (χ : DirichletCharacter K m) : GalQ →* Kˣ :=
  χ.toUnitHom.comp (cycChar m)

/-- Compatibility of the finite cyclotomic characters under reduction. -/
theorem cycChar_unitsMap {d m : ℕ} [NeZero d] [NeZero m] (h : d ∣ m) (σ : GalQ) :
    ZMod.unitsMap h (cycChar m σ) = cycChar d σ := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar d
  let a : ZMod m := (cycChar m σ : (ZMod m)ˣ)
  let b : ZMod d := (cycChar d σ : (ZMod d)ˣ)
  have hpow : ζ ^ m = 1 := by
    obtain ⟨k, rfl⟩ := h
    rw [pow_mul, hζ.pow_eq_one, one_pow]
  have he : ζ ^ (a.val % d) = ζ ^ b.val := by
    conv_lhs => rw [hζ.eq_orderOf, pow_mod_orderOf]
    exact (cycChar_spec m σ ζ hpow).symm.trans (cycChar_spec d σ ζ hζ.pow_eq_one)
  have hv := hζ.pow_inj (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne d))) (ZMod.val_lt b) he
  apply Units.ext
  change ZMod.cast a = b
  rw [← ZMod.natCast_zmod_val a, ZMod.cast_natCast h, ← ZMod.natCast_mod, hv,
    ZMod.natCast_zmod_val]

/-- The finite cyclotomic character is trivial on inertia away from its modulus. -/
theorem cycChar_eq_one_of_mem_inertia {m : ℕ} [NeZero m] (hp : p.Prime)
    (hm : p.Coprime m) {Q : Ideal Zbar} (hQ : Q.IsMaximal)
    (hpQ : ((p : ℤ) : Zbar) ∈ Q) {τ : GalQ} (ht : τ ∈ Q.inertia GalQ) :
    cycChar m τ = 1 := by
  obtain ⟨φ, hφ⟩ := exists_isArithFrobAt hQ hp hpQ
  have e₁ := cycChar_of_isFrobAt m hp hm ⟨Q, hQ, hpQ, hφ⟩
  have e₂ := cycChar_of_isFrobAt m hp hm ⟨Q, hQ, hpQ, isArithFrobAt_mul_of_mem_inertia hφ ht⟩
  have e : cycChar m (φ * τ) = cycChar m φ := Units.ext (e₂.trans e₁.symm)
  rw [map_mul] at e
  exact mul_left_cancel (e.trans (mul_one _).symm)

/-- The 2-adic weight-two twist with coefficients in `K`. -/
def weightTwist {K : Type*} [Field K] (j : ℤ_[2] →+* K) : GalQ →* Kˣ :=
  (Units.map j.toMonoidHom).comp
    ((cyclotomicCharacter Qbar 2).comp (MulSemiringAction.toRingAut GalQ Qbar))

private theorem weightTwist_mod (σ : GalQ) (n : ℕ) :
    (cyclotomicCharacter Qbar 2 σ.toRingEquiv).val.toZModPow n =
      (cycChar (2 ^ n) σ : ZMod (2 ^ n)) := by
  rw [cyclotomicCharacter.toZModPow]
  rfl

/-- At an odd `p`, the weight-two twist has arithmetic Frobenius value `p`. -/
theorem weightTwist_frob {K : Type*} [Field K] (j : ℤ_[2] →+* K) (P : LocalPair p)
    (hp : p.Prime) (hp₂ : p ≠ 2) : (weightTwist j P.φ : K) = (p : K) := by
  have h : (cyclotomicCharacter Qbar 2 P.φ.toRingEquiv).val = (p : ℤ_[2]) := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    rw [weightTwist_mod, map_natCast]
    exact cycChar_of_isFrobAt (2 ^ n) hp
      ((hp.coprime_iff_not_dvd.mpr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).not.mpr hp₂)).pow_right n)
      ⟨P.Q, P.maximal, P.above, P.frob⟩
  change j (cyclotomicCharacter Qbar 2 P.φ.toRingEquiv).val = _
  rw [h, map_natCast]

/-- The weight-two twist is trivial on inertia at odd `p`. -/
theorem weightTwist_inertia {K : Type*} [Field K] (j : ℤ_[2] →+* K) (P : LocalPair p)
    (hp : p.Prime) (hp₂ : p ≠ 2) : (weightTwist j P.τ : K) = 1 := by
  have h : (cyclotomicCharacter Qbar 2 P.τ.toRingEquiv).val = 1 := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    rw [weightTwist_mod, map_one,
      cycChar_eq_one_of_mem_inertia hp
        ((hp.coprime_iff_not_dvd.mpr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).not.mpr hp₂)).pow_right n)
        P.maximal P.above P.inertia, Units.val_one]
  change j (cyclotomicCharacter Qbar 2 P.τ.toRingEquiv).val = _
  rw [h, map_one]

/-- The primitive quadratic character of conductor `p`, with values in `K`. -/
def quadraticDirichlet (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] :
    DirichletCharacter K p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom K)

/-- The quadratic Dirichlet character reads the same inertia sign as the
local pair. Compare the quadratic Gauss sum with the existing square root
of `p*`. -/
theorem quadraticDirichlet_inertia (K : Type*) [Field K] [hp : Fact p.Prime]
    (hp₂ : p ≠ 2) (P : LocalPair p) :
    (dirichletGalois (quadraticDirichlet K p) P.τ : K) = -1 := by
  classical
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar p
  let s := GlueB3Unram.gaussP p hζ
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hs : s ^ 2 = (sstar p : Qbar) := by
    change GlueB3Unram.gaussP p hζ ^ 2 = _
    unfold GlueB3Unram.gaussP
    rw [gaussSum_sq
      ((MulChar.ringHomComp_ne_one_iff (Int.castRingHom Qbar).injective_int).mpr
        (quadraticChar_ne_one hchar))
      ((quadraticChar_isQuadratic (ZMod p)).comp _)
      (AddChar.zmodChar_primitive_of_primitive_root p hζ),
      MulChar.ringHomComp_apply, quadraticChar_neg_one hchar, ZMod.card,
      ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp (hp.out.odd_of_ne_two hp₂)), sstar]
    push_cast
    simp only [map_pow, map_neg, map_one]
  have hd : sstar p ≠ 0 := by simp [sstar, hp.out.ne_zero]
  have hτ : P.τ (sqrtQbar (sstar p)) ≠ sqrtQbar (sstar p) := by
    intro hfix
    have e : bitChar p P.τ = 1 := (sqrtChar_eq_one_iff _ hd _).mpr hfix
    rw [P.flip] at e
    exact (by decide : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1) e
  have hn : P.τ s ≠ s := by
    intro e
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hs.trans (sqrtQbar_sq _).symm) with h | h
    · exact hτ (h ▸ e)
    · exact hτ (neg_injective (by simpa only [h, map_neg] using e))
  let a : ZMod p := (cycChar p P.τ : (ZMod p)ˣ)
  have ha : a ≠ 0 := (cycChar p P.τ).ne_zero
  have hneg : quadraticChar (ZMod p) a = -1 := by
    rcases quadraticChar_dichotomy ha with h | h
    · apply (hn ?_).elim
      have e := GlueB3Unram.gaussP_transform p hζ P.τ
      change P.τ s = ((quadraticChar (ZMod p) a : ℤ) : Qbar) * s at e
      simpa [h] using e
    · exact h
  change (Int.castRingHom K) (quadraticChar (ZMod p) a) = -1
  rw [hneg]
  simp

/-- A pair at conductor exponent one, ordered by inertia. The ramified
Dirichlet character is its away-from-`p` part times the primitive
quadratic character at `p`. The weight twist is on the second character of
the divisor sum, and `twistUnramified` specifies which line that is. -/
structure CharacterPair (K : Type*) [Field K] (p : ℕ) where
  unramLevel : ℕ
  awayLevel : ℕ
  unramCoprime : p.Coprime unramLevel
  awayCoprime : p.Coprime awayLevel
  unram : DirichletCharacter K unramLevel
  away : DirichletCharacter K awayLevel
  twistUnramified : Bool

namespace CharacterPair

variable {K : Type*} [Field K] [hp : Fact p.Prime] (E : CharacterPair K p)

instance : NeZero E.unramLevel :=
  ⟨fun h => hp.out.ne_one (by simpa [h, Nat.Coprime] using E.unramCoprime)⟩

instance : NeZero E.awayLevel :=
  ⟨fun h => hp.out.ne_one (by simpa [h, Nat.Coprime] using E.awayCoprime)⟩

/-- The ramified Dirichlet character on the product of the two coprime moduli,
extended by zero on nonunits. -/
def ramified : DirichletCharacter K (p * E.awayLevel) :=
  (quadraticDirichlet K p).changeLevel (dvd_mul_right _ _) *
    E.away.changeLevel (dvd_mul_left _ _)

/-- The unramified line of the normalized Galois pair. -/
def unramLine (j : ℤ_[2] →+* K) : GalQ →* Kˣ :=
  if E.twistUnramified then dirichletGalois E.unram * weightTwist j else dirichletGalois E.unram

/-- The ramified line of the same pair. -/
def ramLine (j : ℤ_[2] →+* K) : GalQ →* Kˣ :=
  if E.twistUnramified then dirichletGalois E.ramified else
    dirichletGalois E.ramified * weightTwist j

/-- The positive Fourier coefficients of the same ordered pair. -/
def coeff (n : ℕ) : K :=
  if E.twistUnramified then divisorCoeff E.ramified E.unram n else
    divisorCoeff E.unram E.ramified n

/-- The corresponding weight-two Fourier eigenvalue. -/
def scalar : K :=
  if E.twistUnramified then E.unram (p : ZMod E.unramLevel) * (p : K) else
    E.unram (p : ZMod E.unramLevel)

theorem coeff_mul {n : ℕ} (hn : n ≠ 0) :
    E.coeff (p * n) = E.scalar * E.coeff n := by
  have hz := dirichlet_apply_prime_eq_zero hp.out (dvd_mul_right p E.awayLevel) E.ramified
  by_cases h : E.twistUnramified = true
  · simpa only [coeff, scalar, h, ite_true] using divisorCoeff_mul_of_left_zero hp.out hn _ _ hz
  · simpa only [coeff, scalar, h, Bool.false_eq_true, ite_false] using divisorCoeff_mul_of_right_zero hp.out hn _ _ hz

private theorem unramified_value {m : ℕ} [NeZero m] (χ : DirichletCharacter K m)
    (hm : p.Coprime m) (P : LocalPair p) :
    (dirichletGalois χ P.φ : K) = χ (p : ZMod m) :=
  congrArg χ (cycChar_of_isFrobAt m hp.out hm ⟨P.Q, P.maximal, P.above, P.frob⟩)

/-- The arithmetic Frobenius eigenvalue on the unramified line is the
scalar obtained from the divisor sum, in both orders. -/
theorem unramLine_frob (j : ℤ_[2] →+* K) (hp₂ : p ≠ 2) (P : LocalPair p) :
    (E.unramLine j P.φ : K) = E.scalar := by
  have h := unramified_value E.unram E.unramCoprime P
  by_cases e : E.twistUnramified = true
  · simp only [unramLine, scalar, e, ite_true, MonoidHom.mul_apply, Units.val_mul, h,
      weightTwist_frob j P hp.out hp₂]
  · simpa only [unramLine, scalar, e, Bool.false_eq_true, ite_false] using h

/-- The inertia eigenvalues in the unramified-first order. -/
theorem inertia_lines (j : ℤ_[2] →+* K) (hp₂ : p ≠ 2) (P : LocalPair p) :
    (E.unramLine j P.τ : K) = 1 ∧ (E.ramLine j P.τ : K) = -1 := by
  have hUn : (dirichletGalois E.unram P.τ : K) = 1 := by
    simp [dirichletGalois, cycChar_eq_one_of_mem_inertia hp.out E.unramCoprime
      P.maximal P.above P.inertia]
  have hRam : (dirichletGalois E.ramified P.τ : K) = -1 := by
    have e := quadraticDirichlet_inertia K hp₂ P
    simp only [dirichletGalois, MonoidHom.comp_apply, MulChar.coe_toUnitHom] at e ⊢
    rw [ramified, MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      DirichletCharacter.changeLevel_eq_cast_of_dvd]
    have e₁ := congrArg Units.val (cycChar_unitsMap (dvd_mul_right p E.awayLevel) P.τ)
    have e₂ := congrArg Units.val (cycChar_unitsMap (dvd_mul_left E.awayLevel p) P.τ)
    rw [ZMod.unitsMap_val] at e₁ e₂
    rw [e₁, e₂, e,
      cycChar_eq_one_of_mem_inertia hp.out E.awayCoprime P.maximal P.above P.inertia,
      Units.val_one, MulChar.map_one, mul_one]
  by_cases h : E.twistUnramified = true <;>
    simp only [unramLine, ramLine, h, Bool.false_eq_true, ite_true, ite_false, MonoidHom.mul_apply, Units.val_mul,
      hUn, hRam, weightTwist_inertia j P hp.out hp₂, mul_one, and_self]

end CharacterPair

#print axioms cycChar_unitsMap
#print axioms cycChar_eq_one_of_mem_inertia
#print axioms weightTwist_mod
#print axioms weightTwist_frob
#print axioms weightTwist_inertia
#print axioms quadraticDirichlet_inertia
#print axioms CharacterPair.coeff_mul
#print axioms CharacterPair.unramified_value
#print axioms CharacterPair.unramLine_frob
#print axioms CharacterPair.inertia_lines

end ZInQ.Manuscript.RC.O12Eisenstein
