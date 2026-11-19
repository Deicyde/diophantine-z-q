import ZInQKernel.Contrib.RC53Assist.CoordLink.Transport
import ZInQKernel.Contrib.CloudB3RC53.CoordLink.E1aG
import ZInQKernel.Contrib.CloudB3RC53.Torsion.ConeCoord

/-!
# Common coefficient realizations before completion

The fraction field of the integral power-series ring has actual injective
realizations in the rational Laurent carrier and in the clearing field.
Sign evaluation of the finite integral matrices and vectors commutes with both
realizations.  Inverses and Schur complements are taken in this common field,
not asserted to lift to integral units.

These are coefficient diagrams for finite models.  They do not supply a map
from the entire completed ring to the Laurent carrier, or an identification of
the stored endpoint finite model with the actual Selmer cochains.
The locators are TeX 4142–4240 and 5481–5730.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients

open Matrix
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK signEval)
open ZInQ.Contrib.CloudB3RC53.CoordLink
open ZInQ.Contrib.CloudB3RC53.ClearingComplex (φO signEval_φO map_inv_of_isUnit PreComplex)
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central ZInQ.Manuscript.RC.Wiring
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate

/-- The common field is formed before either coefficient realization. -/
abbrev CommonField := FractionRing Lam

abbrev ofIntegral : Lam →+* CommonField := algebraMap Lam CommonField

abbrev powerSeriesToLaurent : PowerSeries ℚ_[2] →+* LaurentSeries ℚ_[2] :=
  algebraMap (PowerSeries ℚ_[2]) (LaurentSeries ℚ_[2])

abbrev integralToLaurent : Lam →+* LaurentSeries ℚ_[2] :=
  powerSeriesToLaurent.comp ιQ

theorem integralToLaurent_injective : Function.Injective integralToLaurent :=
  (IsFractionRing.injective (PowerSeries ℚ_[2]) (LaurentSeries ℚ_[2])).comp ιQ_injective

theorem integralToClearing_injective : Function.Injective ψO := by
  exact (IsFractionRing.injective OO (FractionRing OO)).comp
    (show Function.Injective (algebraMap Lam OO) from ZInQ.Manuscript.RC.Determinant.lamToO_injective)

/-- The Laurent realization is extended from the actual integral inclusion. -/
abbrev toLaurent : CommonField →+* LaurentSeries ℚ_[2] :=
  IsFractionRing.lift (g := integralToLaurent) integralToLaurent_injective

/-- The clearing realization is extended from the actual integral inclusion. -/
abbrev toClearing : CommonField →+* FractionRing OO :=
  IsFractionRing.lift (g := ψO) integralToClearing_injective

theorem toLaurent_injective : Function.Injective toLaurent := toLaurent.injective

theorem toClearing_injective : Function.Injective toClearing := toClearing.injective

@[simp] theorem toLaurent_ofIntegral (a : Lam) : toLaurent (ofIntegral a) = integralToLaurent a :=
  IsFractionRing.lift_algebraMap integralToLaurent_injective a

@[simp] theorem toClearing_ofIntegral (a : Lam) : toClearing (ofIntegral a) = ψO a :=
  IsFractionRing.lift_algebraMap integralToClearing_injective a

variable {b : ℕ}

/-- Sign evaluation of the actual integral coefficient algebra into the common field. -/
abbrev signToCommon (χ : SignGroup b →* ℤˣ) : MonoidAlgebra Lam (SignGroup b) →+* CommonField :=
  ofIntegral.comp (ZInQ.Manuscript.RC.Determinant.signEval χ).toRingHom

theorem sign_toLaurent (χ : SignGroup b →* ℤˣ) (a : MonoidAlgebra Lam (SignGroup b)) :
    toLaurent (signToCommon χ a) = integralToLaurent (ZInQ.Manuscript.RC.Determinant.signEval χ a) :=
  toLaurent_ofIntegral _

/-- This is the actual coefficient-change/sign-evaluation square of the integral family. -/
theorem sign_toClearing (χ : SignGroup b →* ℤˣ) (a : MonoidAlgebra Lam (SignGroup b)) :
    toClearing (signToCommon χ a) = evK χ (φO b a) := by
  change toClearing (ofIntegral (ZInQ.Manuscript.RC.Determinant.signEval χ a)) = evK χ (φO b a)
  rw [toClearing_ofIntegral]
  change algebraMap OO (FractionRing OO) (algebraMap Lam OO (ZInQ.Manuscript.RC.Determinant.signEval χ a)) =
    algebraMap OO (FractionRing OO) (ZInQ.Manuscript.RC.Determinant.signEval χ (φO b a))
  rw [signEval_φO]

section FiniteDiagrams

variable {ι κ : Type}

/-- All actual rectangular finite-model matrices obey the same clearing square. -/
theorem matrix_toClearing (χ : SignGroup b →* ℤˣ) (D : Matrix ι κ (MonoidAlgebra Lam (SignGroup b))) :
    (D.map (signToCommon χ)).map toClearing = (D.map (φO b)).map (evK χ) := by
  ext i j
  exact sign_toClearing χ (D i j)

theorem matrix_toLaurent (χ : SignGroup b →* ℤˣ) (D : Matrix ι κ (MonoidAlgebra Lam (SignGroup b))) :
    (D.map (signToCommon χ)).map toLaurent = D.map (integralToLaurent.comp (ZInQ.Manuscript.RC.Determinant.signEval χ).toRingHom) := by
  exact Matrix.ext (fun i j => sign_toLaurent χ (D i j))

/-- The same integral class or functional vector is realized in the clearing field. -/
theorem vector_toClearing (χ : SignGroup b →* ℤˣ) (z : ι → MonoidAlgebra Lam (SignGroup b)) :
    toClearing ∘ (signToCommon χ ∘ z) = evK χ ∘ (φO b ∘ z) := by
  funext i
  exact sign_toClearing χ (z i)

theorem vector_toLaurent (χ : SignGroup b →* ℤˣ) (z : ι → MonoidAlgebra Lam (SignGroup b)) :
    toLaurent ∘ (signToCommon χ ∘ z) = integralToLaurent ∘ ((ZInQ.Manuscript.RC.Determinant.signEval χ).toRingHom ∘ z) := by
  funext i
  exact sign_toLaurent χ (z i)

end FiniteDiagrams

section Inverses

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Regular finite blocks are inverted before completion; their inverse has the actual Laurent realization. -/
theorem inverse_toLaurent (B : Matrix ι ι CommonField) (hB : B.det ≠ 0) :
    (B⁻¹).map toLaurent = (B.map toLaurent)⁻¹ :=
  map_inv_of_isUnit toLaurent B (isUnit_iff_ne_zero.mpr hB)

/-- The same inverse has the actual clearing realization. -/
theorem inverse_toClearing (B : Matrix ι ι CommonField) (hB : B.det ≠ 0) :
    (B⁻¹).map toClearing = (B.map toClearing)⁻¹ :=
  map_inv_of_isUnit toClearing B (isUnit_iff_ne_zero.mpr hB)

variable {r c : Type}

/-- The same local cancellation differential is realized in both coefficient fields. -/
theorem schur_toClearing (P : Matrix r c CommonField) (Q : Matrix r ι CommonField)
    (T : Matrix ι c CommonField) (B : Matrix ι ι CommonField) (hB : B.det ≠ 0) :
    (P - Q * B⁻¹ * T).map toClearing =
      P.map toClearing - Q.map toClearing * (B.map toClearing)⁻¹ * T.map toClearing := by
  rw [Matrix.map_sub, Matrix.map_mul, Matrix.map_mul, inverse_toClearing B hB]
  exact fun a b => map_sub toClearing a b

theorem schur_toLaurent (P : Matrix r c CommonField) (Q : Matrix r ι CommonField)
    (T : Matrix ι c CommonField) (B : Matrix ι ι CommonField) (hB : B.det ≠ 0) :
    (P - Q * B⁻¹ * T).map toLaurent =
      P.map toLaurent - Q.map toLaurent * (B.map toLaurent)⁻¹ * T.map toLaurent := by
  rw [Matrix.map_sub, Matrix.map_mul, Matrix.map_mul, inverse_toLaurent B hB]
  exact fun a b => map_sub toLaurent a b

end Inverses

/-- The existing cleared power-series representative has a common fractional expression. -/
abbrev correctedCommon (e : ℕ) (a : Lam) : CommonField := ofIntegral a / (2 : CommonField) ^ e

theorem corrected_toClearing (e : ℕ) (a : Lam) :
    toClearing (correctedCommon e a) = ZInQ.Manuscript.RC.Determinant.uK e a := by
  simp [correctedCommon, ZInQ.Manuscript.RC.Determinant.uK, ψO, map_ofNat]

theorem corrected_toLaurent_fraction (e : ℕ) (a : Lam) :
    toLaurent (correctedCommon e a) = integralToLaurent a / (2 : LaurentSeries ℚ_[2]) ^ e := by
  simp [correctedCommon, map_ofNat]

/-- The Laurent image is the already supplied corrected power-series representative. -/
theorem corrected_toLaurent_rep (e : ℕ) (a : Lam) :
    toLaurent (correctedCommon e a) =
      powerSeriesToLaurent (PowerSeries.C ((2 : ℚ_[2]) ^ e)⁻¹ * ιQ a) := by
  have hPow : powerSeriesToLaurent (PowerSeries.C ((2 : ℚ_[2]) ^ e)) =
      (2 : LaurentSeries ℚ_[2]) ^ e := by
    rw [map_pow, map_ofNat, map_pow, map_ofNat]
  have hInv : powerSeriesToLaurent ((PowerSeries.C ((2 : ℚ_[2]) ^ e))⁻¹) =
      ((2 : LaurentSeries ℚ_[2]) ^ e)⁻¹ := by
    have h := congrArg powerSeriesToLaurent
      (PowerSeries.inv_mul_cancel (PowerSeries.C ((2 : ℚ_[2]) ^ e))
        (by simpa only [PowerSeries.constantCoeff_C] using pow_ne_zero e (two_ne_zero : (2 : ℚ_[2]) ≠ 0)))
    rw [map_mul, map_one, hPow] at h
    exact eq_inv_of_mul_eq_one_left h
  rw [corrected_toLaurent_fraction, ← PowerSeries.C_inv, map_mul, hInv]
  change integralToLaurent a / (2 : LaurentSeries ℚ_[2]) ^ e =
    ((2 : LaurentSeries ℚ_[2]) ^ e)⁻¹ * integralToLaurent a
  rw [div_eq_mul_inv, mul_comm]

/-- The actual integral pre-complex has a common finite model before completion. -/
abbrev commonPre (C : PreComplex (MonoidAlgebra Lam (SignGroup b))) (χ : SignGroup b →* ℤˣ) :
    PreComplex CommonField := C.map (signToCommon χ)

/-- Degreewise realization gives the identical actual clearing pre-complex. -/
theorem commonPre_toClearing (C : PreComplex (MonoidAlgebra Lam (SignGroup b))) (χ : SignGroup b →* ℤˣ) :
    PreComplex'.toFour ((commonPre C χ).map toClearing) =
      PreComplex'.toFour ((C.map (φO b)).map (evK χ)) := by
  refine FourCx.ext' (C := PreComplex'.toFour ((commonPre C χ).map toClearing))
    (C' := PreComplex'.toFour ((C.map (φO b)).map (evK χ))) ?_ ?_ ?_
  · exact matrix_toClearing χ C.c0
  · change fromRows ((C.X.map (signToCommon χ)).map toClearing)
        ((C.Y.map (signToCommon χ)).map toClearing) =
      fromRows ((C.X.map (φO b)).map (evK χ)) ((C.Y.map (φO b)).map (evK χ))
    exact congrArg₂ fromRows (matrix_toClearing χ C.X) (matrix_toClearing χ C.Y)
  · change fromBlocks ((C.P.map (signToCommon χ)).map toClearing)
        ((C.Q.map (signToCommon χ)).map toClearing) ((C.T.map (signToCommon χ)).map toClearing)
        ((C.B.map (signToCommon χ)).map toClearing) =
      fromBlocks ((C.P.map (φO b)).map (evK χ)) ((C.Q.map (φO b)).map (evK χ))
        ((C.T.map (φO b)).map (evK χ)) ((C.B.map (φO b)).map (evK χ))
    rw [matrix_toClearing χ C.P, matrix_toClearing χ C.Q,
      matrix_toClearing χ C.T, matrix_toClearing χ C.B]

/-- Its Laurent realization has the same integral family differentials. -/
theorem commonPre_toLaurent (C : PreComplex (MonoidAlgebra Lam (SignGroup b))) (χ : SignGroup b →* ℤˣ) :
    PreComplex'.toFour ((commonPre C χ).map toLaurent) =
      PreComplex'.toFour (C.map (integralToLaurent.comp (ZInQ.Manuscript.RC.Determinant.signEval χ).toRingHom)) := by
  refine FourCx.ext' (C := PreComplex'.toFour ((commonPre C χ).map toLaurent))
    (C' := PreComplex'.toFour (C.map (integralToLaurent.comp (ZInQ.Manuscript.RC.Determinant.signEval χ).toRingHom))) ?_ ?_ ?_
  · exact matrix_toLaurent χ C.c0
  · change fromRows ((C.X.map (signToCommon χ)).map toLaurent)
        ((C.Y.map (signToCommon χ)).map toLaurent) =
      fromRows (C.X.map (integralToLaurent.comp (ZInQ.Manuscript.RC.Determinant.signEval χ).toRingHom))
        (C.Y.map (integralToLaurent.comp (ZInQ.Manuscript.RC.Determinant.signEval χ).toRingHom))
    exact congrArg₂ fromRows (matrix_toLaurent χ C.X) (matrix_toLaurent χ C.Y)
  · change fromBlocks ((C.P.map (signToCommon χ)).map toLaurent)
        ((C.Q.map (signToCommon χ)).map toLaurent) ((C.T.map (signToCommon χ)).map toLaurent)
        ((C.B.map (signToCommon χ)).map toLaurent) =
      fromBlocks (C.P.map (integralToLaurent.comp (ZInQ.Manuscript.RC.Determinant.signEval χ).toRingHom))
        (C.Q.map (integralToLaurent.comp (ZInQ.Manuscript.RC.Determinant.signEval χ).toRingHom))
        (C.T.map (integralToLaurent.comp (ZInQ.Manuscript.RC.Determinant.signEval χ).toRingHom))
        (C.B.map (integralToLaurent.comp (ZInQ.Manuscript.RC.Determinant.signEval χ).toRingHom))
    rw [matrix_toLaurent χ C.P, matrix_toLaurent χ C.Q,
      matrix_toLaurent χ C.T, matrix_toLaurent χ C.B]

/-- Actual invertibility after coefficient change makes every sign-evaluated
local block regular in the common field, without an integral unit assumption. -/
theorem local_block_regular_common {ι : Type} [Fintype ι] [DecidableEq ι]
    (χ : SignGroup b →* ℤˣ) (B : Matrix ι ι (MonoidAlgebra Lam (SignGroup b)))
    (hB : IsUnit (B.map (φO b)).det) : (B.map (signToCommon χ)).det ≠ 0 := by
  have hk : IsUnit ((B.map (φO b)).map (evK χ)).det := by
    have h := hB.map (evK χ)
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply] using h
  have hm : toClearing ((B.map (signToCommon χ)).det) =
      ((B.map (φO b)).map (evK χ)).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, matrix_toClearing χ B]
  intro hzero
  apply hk.ne_zero
  rw [← hm, hzero, map_zero]

end ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients
