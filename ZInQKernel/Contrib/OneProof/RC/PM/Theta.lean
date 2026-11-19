import ZInQKernel.Contrib.OneProof.RC.PM.Stage

/-! Integral lifts and the fields supplied to the existing theta interfaces.
The coefficient and local-frame data are supplied by the theta construction. -/

noncomputable section

open scoped WeierstrassCurve

namespace ZInQ.Manuscript.RC.PM

open Eichler

set_option maxHeartbeats 800000

variable {a b : ℚ} {R : Order a b} {ell N : ℕ} [Fact ell.Prime]
variable {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K] [IsSepClosed K]
variable {Ebar : WeierstrassCurve (ZMod ell)} [Ebar.IsElliptic] {ap : ℕ → ℤ} {M : ℕ}
variable (G : Geometry (K := K) R N Ebar ap) (d : Evaluation K Ebar M) (L : ℕ)

/-- The condition on an arbitrary integral lift of `P_M` (tex 8493). -/
def IsLift (u : ClassSet R → ℤ) : Prop := ∀ z, (u z : ZMod (2 ^ M)) = P G d L z

/-- One choice of lift, by least nonnegative representatives (tex 8493). -/
def valLift (z : ClassSet R) : ℤ := (P G d L z).val

theorem isLift_valLift : IsLift G d L (valLift G d L) := by
  let : NeZero (2 ^ M) := ⟨pow_ne_zero _ (by decide)⟩
  intro z
  exact (Int.cast_natCast _).trans (ZMod.natCast_zmod_val _)

private theorem dvd_sub_of_cast_eq {M : ℕ} {u v : ℤ}
    (h : (u : ZMod (2 ^ M)) = (v : ZMod (2 ^ M))) : (2 : ℤ) ^ M ∣ u - v := by
  exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub v u (2 ^ M)).mp h.symm

/-- Any two choices of lift differ by a multiple of `2^M` at every class (tex 8619–8620). -/
theorem lifts_dvd {u v : ClassSet R → ℤ} (hu : IsLift G d L u) (hv : IsLift G d L v)
    (z : ClassSet R) : (2 : ℤ) ^ M ∣ u z - v z :=
  dvd_sub_of_cast_eq ((hu z).trans (hv z).symm)

/-- Atkin–Lehner sign in the lift congruence used for the orientation change
(tex 9331–9339). The norm-character factor is separate. -/
theorem lift_atkin_dvd {u : ClassSet R → ℤ} (hu : IsLift G d L u)
    (p : ℕ) (hp : p.Prime) (he : 0 < N.factorization p) (hL : L • G.cusp p = 0)
    (z : ClassSet R) : (2 : ℤ) ^ M ∣ u (G.atkin p hp he z) - G.atkinSign p * u z := by
  apply dvd_sub_of_cast_eq (M := M)
  rw [Int.cast_mul, hu, hu, P_atkin G d L p hp he hL]

/-- The uniformizer leaves the lift unchanged at the retained precision
(tex 9343–9358). The norm-character factor is separate. -/
theorem lift_uniformizer_dvd {u : ClassSet R → ℤ} (hu : IsLift G d L u) (z : ClassSet R) :
    (2 : ℤ) ^ M ∣ u (G.uniformizer z) - u z :=
  dvd_sub_of_cast_eq ((hu _).trans ((P_uniformizer G d L z).trans (hu z).symm))

/-- The norm-weighted Atkin–Lehner sign in `Odd.orientation_signs`
(tex 9336–9339, 9359–9362), given the normalizer's norm-character identity. -/
theorem normWeighted_atkin_dvd {O : Type*} [CommRing O] {u : ClassSet R → ℤ}
    (hu : IsLift G d L u) (p : ℕ) (hp : p.Prime) (he : 0 < N.factorization p)
    (hL : L • G.cusp p = 0) (z : ClassSet R) (χN : ClassSet R → O) (χp : O)
    (hχ : χN (G.atkin p hp he z) = χp ^ N.factorization p * χN z) :
    (2 : O) ^ M ∣ χN (G.atkin p hp he z) * (u (G.atkin p hp he z) : O) -
      ((G.atkinSign p : O) * χp ^ N.factorization p) * (χN z * (u z : O)) := by
  have h := map_dvd (Int.castRingHom O) (lift_atkin_dvd G d L hu p hp he hL z)
  simp only [map_sub, map_mul, map_pow, eq_intCast, Int.cast_ofNat] at h
  rw [hχ]
  convert dvd_mul_of_dvd_right h (χp ^ N.factorization p * χN z) using 1
  ring

/-- The uniformizer contributes only the norm-character sign to the norm-weighted
parametrization value (tex 9346–9358). -/
theorem normWeighted_uniformizer_dvd {O : Type*} [CommRing O] {u : ClassSet R → ℤ}
    (hu : IsLift G d L u) (z : ClassSet R) (χN : ClassSet R → O)
    (hχ : χN (G.uniformizer z) = -χN z) :
    (2 : O) ^ M ∣ χN (G.uniformizer z) * (u (G.uniformizer z) : O) -
      -(χN z * (u z : O)) := by
  have h := map_dvd (Int.castRingHom O) (lift_uniformizer_dvd G d L hu z)
  simp only [map_sub, map_pow, eq_intCast, Int.cast_ofNat] at h
  rw [hχ]
  convert dvd_mul_of_dvd_right h (-χN z) using 1
  ring

/-- On-the-spot (c): fill the pointwise lift premise of `Visibility.lamOf_reduction`.
Supply the geometric reduction identity at the given Heegner class. The stage evaluation
on the source group is the composite of the same `lam` with its reduction map. -/
theorem lift_at_reduction {Y : Type*} [AddCommGroup Y] (red : Y →+ ReducedPoints (K := K) Ebar)
    {u : ClassSet R → ℤ} (hu : IsLift G d L u) (z : ClassSet R) (y : Y)
    (hred : G.pi z = red y) :
    (2 : ℤ) ^ M ∣ u z - (((lam d).comp red (L • y)).val : ℤ) := by
  let : NeZero (2 ^ M) := ⟨pow_ne_zero _ (by decide)⟩
  apply dvd_sub_of_cast_eq (M := M)
  rw [Int.cast_natCast, ZMod.natCast_zmod_val, hu]
  change lam d (L • G.pi z) = lam d (red (L • y))
  rw [hred, map_nsmul red]

section Visibility

variable {O : Type*} [CommRing O] (ha : a < 0) (hb : b < 0)
  (f : ClassSet R → B a b → O)
  (hf : ∀ z, ∀ u ∈ classG ha hb z, ∀ x, f z (↑u * x * ↑u⁻¹) = f z x)
  (χN : ClassSet R → O)
  (finiteSupp : ∀ z (n : ℚ), {x : B a b | x.re = 0 ∧ Visibility.nrd x = n ∧ f z x ≠ 0}.Finite)

/-- Fill the class, weight and lift fields of a visibility stage. `hu` identifies its
`P` with a lift of the same residue function used in the App F stage. -/
def visibilityStage (u : ClassSet R → ℤ) (_hu : IsLift G d L u) : Visibility.ThetaStage O a b where
  X := ClassSet R
  fintypeX := classFintype R ha hb
  G := classG ha hb
  card_G_dvd := class_card_G_dvd ha hb
  f := f
  f_conj := hf
  χN := χN
  P := u
  finite_supp := finiteSupp

/-- Replacing an integral lift in the visibility stage preserves every coefficient
modulo `2^M O` (tex 8619–8621, 9373–9377). -/
theorem visibility_relift_dvd {u v : ClassSet R → ℤ} (hu : IsLift G d L u)
    (hv : IsLift G d L v) (n : ℚ) :
    let S := visibilityStage G d L ha hb f hf χN finiteSupp u hu
    (2 : O) ^ M ∣ Visibility.thetaCoeff (S.relift v) n - Visibility.thetaCoeff S n := by
  let S := visibilityStage G d L ha hb f hf χN finiteSupp u hu
  change (2 : O) ^ M ∣ Visibility.thetaCoeff (S.relift v) n - Visibility.thetaCoeff S n
  exact Visibility.thetaCoeff_relift_dvd S M v (lifts_dvd G d L hv hu) n

end Visibility

/-- The canonical map from the residue of an integer to App F's coefficient ring
`O/2^M O`. On-the-spot (c) realization of the coefficient-ring map. -/
def stageCast (O : Type*) [CommRing O] (M : ℕ) :
    ZMod (2 ^ M) →+* Odd.StageRing O M :=
  ZMod.castHom (m := ringChar (Odd.StageRing O M)) (by
    apply (CharP.cast_eq_zero_iff (Odd.StageRing O M) _ _).mp
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton ((2 : O) ^ M)))
    simpa only [map_pow, map_ofNat, Nat.cast_pow, Nat.cast_ofNat] using h) _

/-- The image of the finite function equals the image of any integer lift. -/
theorem stageCast_P {O : Type*} [CommRing O] {u : ClassSet R → ℤ}
    (hu : IsLift G d L u) (z : ClassSet R) :
    stageCast O M (P G d L z) = (u z : Odd.StageRing O M) := by
  rw [← hu z, map_intCast]

/-- Assemble `AppF.ThetaStage` using the same residue function as the visibility stage.
The norm characters, inner theta sums and local frames remain parameters. -/
def appFStage {O : Type*} [CommRing O] (ha : a < 0) (hb : b < 0)
    (χN : ClassSet R → Odd.StageRing O M) (θ : ClassSet R → ℕ → Odd.StageRing O M)
    (m : ℕ) (Good : ℕ → Prop) (prime : ∀ p, Good p → p.Prime)
    (away : ∀ p, Good p → ¬ p ∣ N * ell)
    (neTwo : ∀ p, Good p → p ≠ 2) (goodM : ∀ p, Good p → ¬ p ∣ m)
    (lines : ∀ p (hp : Good p), LineIndex R p (prime p hp).ne_zero)
    (s sinv η : ℕ → Odd.StageRing O M)
    (sUnit : ∀ p, Good p → s p * sinv p = 1)
    (ηMul : ∀ x y, η (x * y) = η x * η y) (ηOne : η 1 = 1)
    (ηGood : ∀ p, Good p → η p = s p * (jacobiSym (-(m : ℤ)) p : Odd.StageRing O M))
    (frame : ∀ p, Good p → ClassSet R → AppF.PFrame p (Odd.StageRing O M))
    (frameTheta : ∀ p (hp : Good p) z k, θ z k = (frame p hp z).theta k)
    (frameScale : ∀ p (hp : Good p) z x,
      (frame p hp z).F ((frame p hp z).scale x) = s p * (frame p hp z).F x)
    (frameNb : ∀ p (hp : Good p) z i n,
      χN (nb prime lines p z i) * θ (nb prime lines p z i) n =
        (jacobiSym (-(m : ℤ)) p : Odd.StageRing O M) * χN z * (sinv p * (frame p hp z).nbrSum i n))
    (thetaZero : ∀ z, θ z 0 = 0) : AppF.ThetaStage (Odd.StageRing O M) where
  ℓ₀ := ell
  qa := a
  qb := b
  ram := G.ram
  X := ClassSet R
  fin := classFintype R ha hb
  w := classWeight ha hb
  w_pos := classWeight_pos ha hb
  w_dvd := classWeight_dvd ha hb
  P := stageCast O M ∘ P G d L
  χN := χN
  θ := θ
  m := m
  Good := Good
  good_prime := prime
  good_ne_two := neTwo
  good_m := goodM
  ap := ap
  s := s
  sinv := sinv
  s_unit := sUnit
  η := η
  η_mul := ηMul
  η_one := ηOne
  η_good := ηGood
  nb := nb prime lines
  hecke := by
    intro p hp z
    let : NeZero p := ⟨(prime p hp).ne_zero⟩
    simpa only [Function.comp_apply, map_sum, map_mul, map_intCast] using
      congrArg (stageCast O M) (P_hecke G d L prime away lines p hp z)
  adjoint := Eichler.adjoint ha hb prime lines
  frame := frame
  frame_theta := frameTheta
  frame_scale := frameScale
  frame_nbr := frameNb
  theta_zero := thetaZero

#print axioms isLift_valLift
#print axioms dvd_sub_of_cast_eq
#print axioms lifts_dvd
#print axioms lift_atkin_dvd
#print axioms lift_uniformizer_dvd
#print axioms normWeighted_atkin_dvd
#print axioms normWeighted_uniformizer_dvd
#print axioms lift_at_reduction
#print axioms visibilityStage
#print axioms visibility_relift_dvd
#print axioms stageCast
#print axioms stageCast_P
#print axioms appFStage

end ZInQ.Manuscript.RC.PM
