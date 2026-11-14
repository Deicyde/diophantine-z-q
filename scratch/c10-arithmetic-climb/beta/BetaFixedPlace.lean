import CharacterDescent
import ZInQKernel.HDecomp.Descent.B2Assembly
import BetaTransportExpected

/-!
# Fixed-place coefficient transport of a GIVEN B2 cochain `β`

PRIVATE CANDIDATE (climb/beta-fixed-place). Not a public claim, not a provider, not an
adoption. It proves the two independently stated targets of `ClimbBetaExpected`
(`BetaTransportExpected.lean`, sha256
dcf079cc79d8a9fb3a52370f76f9a418ebe579a3396475f1ca9fb2fcc9fcf26d) and one actual-B2
application, and nothing else.

What is transported: the literal values and equations of a β that is GIVEN (the output of
`GlueDescent.B2Q.b2_of_leaves`, or any datum of that shape), along the SAME fixed complex
place `ρ : GlueC10.Qbar →ₐ[ℚ] ℂ` used by the character lane. Each value is a root of unity
because the GIVEN square equation `β g ^ 2 = galChar χ g` forces `β g ^ (2 * φ N) = 1`
(`ZMod.pow_totient`), with `φ N > 0` from the level's own `NeZero`.

What is NOT done here:
* no construction of `β` — Hasse (L-B2a), local-two (L-B2b), the square-root criterion
  (L-B2c) and L-B2d remain exactly the inputs they already are;
* no new coboundary `dB` and no re-choice of `ε`: the `ε`-side is either the caller's
  PRESCRIBED `ε₀` with its explicit image equation, or — only where the source itself gives
  `IsSignCocycle ε`, whose values satisfy `ε x y ^ 2 = 1` — the pointwise lift of those same
  values (`exists_signCocycle_lift`). Nothing is normalized silently: `IsSignCocycle` carries
  no `ε 1 1 = 1`, so `β₀ 1 = 1` is proved only from an explicit unit equation
  (`normalizationFromUnitEquation`);
* no arithmetic coefficient field `C`, no finite `E`, no `af`/`a`/`T` datum, no θ/Tate/
  topology/finite-image assumption, and no C10 or Hilbert 10 closure.

The root-of-unity preimage lemma is reused from the already-compiled
`ClimbCharacterDescent` (character lane); it is not reproved here.
-/

noncomputable section

open GlueDescent GlueDescent.B2 GlueDescent.B2Q ClimbBetaExpected

namespace ClimbBetaFixedPlace

/-! ## 1. The fixed place on units -/

theorem unitPlace_injective (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) :
    Function.Injective (unitPlace ρ) :=
  Units.map_injective (f := ρ.toRingHom.toMonoidHom) (RingHom.injective _)

/-- Unit-level preimage of a root of unity, from the character lane's field-level lemma. -/
theorem exists_unit_preimage_of_pow_eq_one (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) {z : ℂˣ} {k : ℕ}
    (hk : 0 < k) (hz : z ^ k = 1) : ∃ w : GlueC10.Qbarˣ, unitPlace ρ w = z := by
  obtain ⟨w, hw⟩ := ClimbCharacterDescent.exists_preimage_of_pow_eq_one
    (K := GlueC10.Qbar) ρ.toRingHom (z := (z : ℂ)) (k := k) hk
    (by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one])
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hw
    exact z.ne_zero hw.symm
  exact ⟨Units.mk0 w hw0, Units.ext (by simpa [unitPlace] using hw)⟩

/-! ## 2. The root-of-unity power is DERIVED from the given square equation -/

theorem beta_pow_eq_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (hsq : ∀ g, β g ^ 2 = galChar χ g) (g : GQ) :
    β g ^ (2 * N.totient) = 1 := by
  rw [pow_mul, hsq]
  show χ.toUnitHom (cyc N g) ^ N.totient = 1
  rw [← map_pow, ZMod.pow_totient, map_one]

theorem two_mul_totient_pos (N : ℕ) [NeZero N] : 0 < 2 * N.totient := by
  have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  omega

/-! ## 3. The target: literal transport of the given values and equations -/

theorem givenB2CoefficientTransport : ClimbBetaExpected.GivenB2CoefficientTransport := by
  intro N _ ρ χ₀ χ hχ β hβlc hβsq ε₀ hco
  have hinj := unitPlace_injective ρ
  have hpre : ∀ g : GQ, ∃ w : GlueC10.Qbarˣ, unitPlace ρ w = β g := fun g =>
    exists_unit_preimage_of_pow_eq_one ρ (two_mul_totient_pos N) (beta_pow_eq_one χ β hβsq g)
  choose β₀ hβ₀ using hpre
  have hgal : ∀ g : GQ, unitPlace ρ (galCharacter χ₀ g) = galChar χ g := by
    intro g
    refine Units.ext ?_
    show ρ ((χ₀.toUnitHom (cyc N g) : GlueC10.Qbar)) = ((χ.toUnitHom (cyc N g) : ℂ))
    rw [MulChar.coe_toUnitHom, MulChar.coe_toUnitHom, hχ]
  have hlc : IsLocallyConstant β₀ := by
    refine IsLocallyConstant.desc β₀ (unitPlace ρ) ?_ hinj
    have : (unitPlace ρ) ∘ β₀ = β := funext hβ₀
    rw [this]
    exact hβlc
  refine ⟨β₀, hβ₀, hlc, fun g => hinj ?_, fun g h => hinj ?_, fun g => (β₀ g).ne_zero⟩
  · rw [map_pow, hβ₀, hβsq, hgal]
  · rw [map_mul, map_mul, hβ₀, hβ₀, hβ₀, hco]

/-- Normalization is a separate source condition: `IsSignCocycle` does not give `ε 1 1 = 1`,
so `β₀ 1 = 1` is proved only from the explicit unit equation. -/
theorem normalizationFromUnitEquation : ClimbBetaExpected.NormalizationFromUnitEquation := by
  intro ε₀ β₀ hco hε
  have h := hco 1 1
  rw [hε, one_mul, mul_one] at h
  exact mul_eq_left.mp h

/-! ## 4. Permitted strengthening: the SIGN cocycle's own values lift

`GlueDescent.B2.IsSignCocycle` already states `ε x y ^ 2 = 1`, so the given complex values are
square roots of unity and lift through the same place. No new `dB` is introduced and no other
`ε` is chosen: the lifted cochain's values are exactly the preimages of the given ones. -/

theorem exists_signCocycle_lift (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (ε : GQ → GQ → ℂˣ)
    (hε : IsSignCocycle ε) :
    ∃ ε₀ : GQ → GQ → GlueC10.Qbarˣ,
      (∀ g h, unitPlace ρ (ε₀ g h) = ε g h) ∧ IsSignCocycle ε₀ := by
  have hinj := unitPlace_injective ρ
  have hpre : ∀ p : GQ × GQ, ∃ w : GlueC10.Qbarˣ, unitPlace ρ w = ε p.1 p.2 := fun p =>
    exists_unit_preimage_of_pow_eq_one ρ (by norm_num) (hε.2.1 p.1 p.2)
  choose e he using hpre
  refine ⟨fun g h => e (g, h), fun g h => he (g, h), ?_, fun g h => hinj ?_, fun x y z => hinj ?_⟩
  · refine IsLocallyConstant.desc _ (unitPlace ρ) ?_ hinj
    have : (unitPlace ρ) ∘ (Function.uncurry fun g h => e (g, h)) = Function.uncurry ε := by
      funext p; exact he p
    rw [this]
    exact hε.1
  · rw [map_pow, he, hε.2.1, map_one]
  · rw [map_mul, map_mul, he, he, he, he, hε.2.2]

/-! ## 5. The actual B2 application

Every hypothesis of `GlueDescent.B2Q.b2_of_leaves` is passed through unchanged: the four
leaves, the actual `L`, the actual complex sign cocycle `ε` with its inflation, and the actual
`T` with its primality and unramifiedness. Nothing on that side is weakened, and none of it is
proved here. -/

theorem actualB2Transport (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε)
    (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p)
    (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) :
    ∃ (N : ℕ) (_ : NeZero N) (χ₀ : DirichletCharacter GlueC10.Qbar N)
      (ε₀ : GQ → GQ → GlueC10.Qbarˣ) (β₀ : GQ → GlueC10.Qbarˣ),
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T) ∧
      orderOf χ₀ ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) ∧
      IsSignCocycle ε₀ ∧ (∀ g h, unitPlace ρ (ε₀ g h) = ε g h) ∧
      IsLocallyConstant β₀ ∧ (∀ g, β₀ g ^ 2 = galCharacter χ₀ g) ∧
      (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) ∧ (∀ g, (β₀ g : GlueC10.Qbar) ≠ 0) := by
  obtain ⟨N, hN, χ, β, hsupp, hord, hβlc, hβsq, hβco⟩ :=
    b2_of_leaves hHasse hTwo hSq hUnr L ε hε hinf T hT hram
  have : NeZero N := hN
  obtain ⟨χ₀, hχval, hχord⟩ := ClimbCharacterDescent.fixedPlaceDescent N ρ χ
  obtain ⟨ε₀, hε₀val, hε₀sign⟩ := exists_signCocycle_lift ρ ε hε
  obtain ⟨β₀, hβ₀val, hβ₀lc, hβ₀sq, hβ₀co, hβ₀ne⟩ :=
    givenB2CoefficientTransport N ρ χ₀ χ hχval β hβlc hβsq ε₀
      (fun g h => by rw [hε₀val]; exact hβco g h)
  exact ⟨N, hN, χ₀, ε₀, β₀, hsupp, hχord ▸ hord, hε₀sign, hε₀val, hβ₀lc, hβ₀sq, hβ₀co, hβ₀ne⟩

end ClimbBetaFixedPlace

/-! ## 6. Reports -/

#print axioms ClimbBetaFixedPlace.unitPlace_injective
#print axioms ClimbBetaFixedPlace.exists_unit_preimage_of_pow_eq_one
#print axioms ClimbBetaFixedPlace.beta_pow_eq_one
#print axioms ClimbBetaFixedPlace.two_mul_totient_pos
#print axioms ClimbBetaFixedPlace.givenB2CoefficientTransport
#print axioms ClimbBetaFixedPlace.normalizationFromUnitEquation
#print axioms ClimbBetaFixedPlace.exists_signCocycle_lift
#print axioms ClimbBetaFixedPlace.actualB2Transport

#check @ClimbBetaFixedPlace.unitPlace_injective
#check @ClimbBetaFixedPlace.exists_unit_preimage_of_pow_eq_one
#check @ClimbBetaFixedPlace.beta_pow_eq_one
#check @ClimbBetaFixedPlace.two_mul_totient_pos
#check @ClimbBetaFixedPlace.givenB2CoefficientTransport
#check @ClimbBetaFixedPlace.normalizationFromUnitEquation
#check @ClimbBetaFixedPlace.exists_signCocycle_lift
#check @ClimbBetaFixedPlace.actualB2Transport
