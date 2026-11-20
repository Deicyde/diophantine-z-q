import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.ThetaGauss
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! Evaluation of the ordinary quadratic sum needed for the unary
multiplier after moving the lower-right entry to an odd prime. -/

noncomputable section
set_option maxHeartbeats 800000

namespace ZInQ.Manuscript.RC.EvenUnary

open HalfIntegral

private def primeCharacter (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

private theorem primeQuadraticFourier {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (b : (ZMod p)ˣ) :
    quadraticFourier (b : ZMod p) 0 =
      primeCharacter p b * gaussSum (primeCharacter p) ZMod.stdAddChar := by
  classical
  let χ := primeCharacter p
  let ψ := ZMod.stdAddChar (N := p)
  let f (y : ZMod p) := ψ ((b : ZMod p) * y)
  have hs (y : ZMod p) :
      (∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ^ 2 = y), f y) =
        (χ y + 1) * f y := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have he := quadraticChar_card_sqrts
      (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using hp) y
    simp only [Set.toFinset_ofPred] at he
    have hc : ((Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)).card : ℂ) = χ y + 1 := by
      change _ = ((quadraticChar (ZMod p) y : ℤ) : ℂ) + 1
      exact_mod_cast he
    rw [hc]
  have hsum :
      (∑ x : ZMod p, f (x ^ 2)) = ∑ y : ZMod p, (χ y + 1) * f y := by
    rw [← Finset.sum_fiberwise_of_maps_to' (g := fun x : ZMod p => x ^ 2)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _) f]
    refine Finset.sum_congr rfl fun y _ => hs y
  have hz : ∑ y : ZMod p, f y = 0 := by
    have he := Fintype.sum_equiv b.mulLeft (fun y => f y) (fun y => ψ y) (fun _ => rfl)
    rw [he]
    apply AddChar.sum_eq_zero_of_ne_one
    intro h
    have hh := DFunLike.congr_fun h (1 : ZMod p)
    have hh' : ψ (1 : ZMod p) = ψ 0 := by simpa [ψ] using hh
    exact one_ne_zero (ZMod.injective_stdAddChar hh')
  have he : quadraticFourier (b : ZMod p) 0 = gaussSum χ (ψ.mulShift b) := by
    simp only [quadraticFourier, zero_mul, add_zero]
    change (∑ x : ZMod p, f (x ^ 2)) = _
    rw [hsum]
    simp only [add_mul, one_mul, Finset.sum_add_distrib, hz, add_zero, f, gaussSum,
      AddChar.mulShift_apply]
  rw [he, gaussSum_mulShift_eq, show χ⁻¹ = χ from
    ((quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)).inv]

theorem primeGauss_scale {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (b j : (ZMod p)ˣ) :
    quadraticFourier ((j * b : (ZMod p)ˣ) : ZMod p) 0 =
      primeCharacter p j * quadraticFourier (b : ZMod p) 0 := by
  rw [primeQuadraticFourier hp (j*b), primeQuadraticFourier hp b, Units.val_mul, map_mul, mul_assoc]

theorem primeGauss_sq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (b : (ZMod p)ˣ) :
    quadraticFourier (b : ZMod p) 0 ^ 2 =
      primeCharacter p (-1 : ZMod p) * (p : ℂ) := by
  let χ := primeCharacter p
  have hq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
  have hnt : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.castRingHom ℂ).injective_int).mpr
      (quadraticChar_ne_one (by simpa only [ZMod.ringChar_zmod_n] using hp))
  have hb : χ b ^ 2 = 1 := by
    rw [← MulChar.pow_apply_coe, hq.sq_eq_one, MulChar.one_apply_coe]
  rw [primeQuadraticFourier hp b, mul_pow, hb, one_mul,
    gaussSum_sq hnt hq (ZMod.isPrimitive_stdAddChar p), ZMod.card]

private theorem primeCharacter_at_int (p : ℕ) [Fact p.Prime] (n : ℤ) :
    primeCharacter p (n : ZMod p) = (jacobiSym n p : ℂ) := by
  change ((legendreSym p n : ℤ) : ℂ) = _
  rw [jacobiSym.legendreSym.to_jacobiSym]

/-- Multiplying the numerator of a nondegenerate prime quadratic sum
multiplies that sum by the Jacobi symbol of the multiplier. -/
theorem primeGauss_scale_jacobi {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {b j : ℤ} (hb : IsUnit (b : ZMod p)) (hj : IsUnit (j : ZMod p)) :
    quadraticFourier (((j * b : ℤ)) : ZMod p) 0 =
      (jacobiSym j p : ℂ) * quadraticFourier (b : ZMod p) 0 := by
  simpa only [Units.val_mul, hb.unit_spec, hj.unit_spec, Int.cast_mul,
    primeCharacter_at_int] using primeGauss_scale hp hb.unit hj.unit

theorem primeGauss_sq_jacobi {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {b : ℤ} (hb : IsUnit (b : ZMod p)) :
    quadraticFourier (b : ZMod p) 0 ^ 2 =
      (jacobiSym (-1) p : ℂ) * (p : ℂ) := by
  have hm : primeCharacter p (-1 : ZMod p) = (jacobiSym (-1) p : ℂ) := by
    simpa only [Int.cast_neg, Int.cast_one] using primeCharacter_at_int p (-1)
  simpa only [hb.unit_spec, hm] using primeGauss_sq hp hb.unit

end ZInQ.Manuscript.RC.EvenUnary
