import ZInQKernel.Contrib.RC53Assist.IntegralDuality.IntegralTatePairing
import ZInQKernel.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralLocalFit

/-!
# The source-fixed central cyclotomic coefficient reduction

The trace coefficient map is constant reduction into the existing finite
cyclotomic line, not into untwisted finite coefficients. Its Galois covariance
comes from the existing finite reduction of the two-adic cyclotomic character.
The central Tate module and its determinant form are those of the actual
quadratic twist. The finite right coefficient map is typed with the preserved
proof that the central character is self-inverse.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open NumberField IsDedekindDomain TensorProduct
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef two_pow_A)
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.DerivedKummer.CentralLocalFit (charInv_centralChar centralRoots)

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- Full torsion for the actual central curve, with no additional input. -/
instance centralFullTwoTorsion (D : GenuineKummerData K E₀ hZ) :
    HasFullTwoTorsion K D.S (centralCurve D) := ⟨centralFullTorsion D⟩

/-- Two-power roots of unity on the actual support, supplied by the source full torsion. -/
instance centralTwoPowerRoots (D : GenuineKummerData K E₀ hZ) : HasTwoPowerRoots K D.S :=
  hasTwoPowerRoots_of_fullTwoTorsion K D.S (centralCurve D)

/-- The actual central integral coefficient pairing. -/
abbrev centralIntegralBeta (D : GenuineKummerData K E₀ hZ) :
    TateS K D.S (centralCurve D) →ₗ[ℤ_[2]]
      TateS K D.S (centralCurve D) →ₗ[ℤ_[2]] IntegralTate1 K D.S :=
  integralBeta

/-- Constant reduction factors through the genuine finite cyclotomic coefficient ring. -/
theorem constRed_eq_toZModPow (i : ℕ) (a : ℤ_[2]) :
    constRed i a = algebraMap (ZMod (2 ^ i)) (Acoef i) (PadicInt.toZModPow i a) := by
  rw [algebraMap_zmod_eq_val]
  exact lamToAcoef_algebraMap i a

/-- Reduction of the integral trace coefficient into the existing finite cyclotomic line. -/
def centralTraceCoefficientReduction (D : GenuineKummerData K E₀ hZ) (i : ℕ) :
    IntegralTate1 K D.S →ₛₗ[constRed i] Tate1 (Acoef i) (centralRoots D i) where
  toFun a := constRed i (ContinuousCharacterLine.equiv ℤ_[2] (cyc2 K D.S) a)
  map_add' a b := map_add (constRed i) _ _
  map_smul' a b := map_mul (constRed i) _ _

/-- The trace coefficient map is exactly constant reduction in the fixed trivializations. -/
theorem centralTraceCoefficientReduction_underlying (D : GenuineKummerData K E₀ hZ)
    (i : ℕ) (a : IntegralTate1 K D.S) :
    CharMod.equiv (Acoef i) (cycA (Acoef i) (centralRoots D i))
        (centralTraceCoefficientReduction D i a) =
      constRed i (ContinuousCharacterLine.equiv ℤ_[2] (cyc2 K D.S) a) := rfl

/-- The trace coefficient reduction is equivariant for the genuine cyclotomic actions. -/
theorem centralTraceCoefficientReduction_galois (D : GenuineKummerData K E₀ hZ) (i : ℕ)
    (σ : GKS K D.S) (a : IntegralTate1 K D.S) :
    centralTraceCoefficientReduction D i (σ • a) = σ • centralTraceCoefficientReduction D i a := by
  change constRed i ((cyc2 K D.S σ : ℤ_[2]) * (show ℤ_[2] from a)) =
    (cycA (Acoef i) (centralRoots D i) σ : Acoef i) * constRed i (show ℤ_[2] from a)
  rw [map_mul, constRed_eq_toZModPow, toZModPow_cyc2 i (centralRoots D i)]
  rfl

/-- The finite trace coefficient map is continuous from the inherited two-adic topology. -/
theorem centralTraceCoefficientReduction_continuous (D : GenuineKummerData K E₀ hZ) (i : ℕ) :
    Continuous (centralTraceCoefficientReduction D i) := by
  let f : ℤ_[2] →+ Tate1 (Acoef i) (centralRoots D i) :=
    { toFun := fun a => constRed i a
      map_zero' := map_zero (constRed i)
      map_add' := map_add (constRed i) }
  have hf : Continuous f := by
    apply continuous_of_ker_mem_nhds f
    apply Filter.mem_of_superset ((isOpen_span_two_pow i).mem_nhds (Ideal.zero_mem _))
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    change constRed i (c * (2 : ℤ_[2]) ^ i) = 0
    rw [map_mul, map_pow, map_ofNat, two_pow_A, mul_zero]
  exact hf.comp (ContinuousCharacterLine.homeomorph ℤ_[2] (cyc2 K D.S)).continuous

/-- The identity of the underlying tensor modules. Its Galois compatibility below is
proved using the preserved self-inverse-character theorem. -/
def centralRightCoefficientEquiv (D : GenuineKummerData K E₀ hZ) (i : ℕ) :
    Mcoef K D.S D.W i (centralChar i D.s D.hs D.hs0) ≃ₗ[Acoef i]
      Mcoef K D.S D.W i (charInv (centralChar i D.s D.hs D.hs0)) :=
  (CoefMod.equiv (Acoef i) (centralChar i D.s D.hs D.hs0)
    (TorsS K D.S D.W ((2 ^ i : ℕ) : ℤ))).symm.trans
      (CoefMod.equiv (Acoef i) (charInv (centralChar i D.s D.hs D.hs0))
        (TorsS K D.S D.W ((2 ^ i : ℕ) : ℤ)))

/-- Character transport is the identity on the actual underlying coefficients. -/
theorem centralRightCoefficientEquiv_apply (D : GenuineKummerData K E₀ hZ) (i : ℕ)
    (x : Mcoef K D.S D.W i (centralChar i D.s D.hs D.hs0)) :
    (show (Acoef i) ⊗[ℤ] TorsS K D.S D.W ((2 ^ i : ℕ) : ℤ) from
        centralRightCoefficientEquiv D i x) =
      (show (Acoef i) ⊗[ℤ] TorsS K D.S D.W ((2 ^ i : ℕ) : ℤ) from x) := rfl

/-- The right-hand transport respects the genuine action because the central
character is its own inverse. -/
theorem centralRightCoefficientEquiv_galois (D : GenuineKummerData K E₀ hZ) (i : ℕ)
    (σ : GKS K D.S) (x : Mcoef K D.S D.W i (centralChar i D.s D.hs D.hs0)) :
    centralRightCoefficientEquiv D i (σ • x) = σ • centralRightCoefficientEquiv D i x := by
  change ((centralChar i D.s D.hs D.hs0 σ : Acoef i) •
      ZInQ.Contrib.CloudB3RC53.Duality.baseChangeAct (Acoef i)
        (TorsS K D.S D.W ((2 ^ i : ℕ) : ℤ)) σ (show (Acoef i) ⊗[ℤ] _ from x)) =
    ((charInv (centralChar i D.s D.hs D.hs0) σ : Acoef i) •
      ZInQ.Contrib.CloudB3RC53.Duality.baseChangeAct (Acoef i)
        (TorsS K D.S D.W ((2 ^ i : ℕ) : ℤ)) σ (show (Acoef i) ⊗[ℤ] _ from x))
  rw [charInv_centralChar]

/-- On both central coefficient modules the existing finite Weil pairing is
Galois equivariant. This uses action compatibility, not merely equality of
underlying tensor types. -/
theorem centralFinitePairing_galois (D : GenuineKummerData K E₀ hZ) (i : ℕ)
    (σ : GKS K D.S)
    (x y : Mcoef K D.S D.W i (centralChar i D.s D.hs D.hs0)) :
    weilPairingM (S := D.S) D.W (centralRoots D i) (Acoef i)
        (centralChar i D.s D.hs D.hs0) (σ • x) (centralRightCoefficientEquiv D i (σ • y)) =
      σ • weilPairingM (S := D.S) D.W (centralRoots D i) (Acoef i)
        (centralChar i D.s D.hs D.hs0) x (centralRightCoefficientEquiv D i y) := by
  rw [centralRightCoefficientEquiv_galois]
  exact weilPairingM_smul D.W (centralRoots D i) (Acoef i)
    (centralChar i D.s D.hs D.hs0) σ x (centralRightCoefficientEquiv D i y)

end ZInQ.Contrib.RC53Assist.IntegralDuality
