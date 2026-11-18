import ZInQKernel.Contrib.OneProof.RC.Stages.FiniteField
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Surjective

/-! The map of tex 8378–8391 on Mathlib's geometric points of a reduced
elliptic curve, with its rational points represented as fixed points. -/

noncomputable section

open scoped WeierstrassCurve
open WeierstrassCurve Polynomial

namespace ZInQ.Manuscript.RC.Stages

set_option maxHeartbeats 100000

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [Algebra (ZMod p) K] [DecidableEq K]
variable (E : WeierstrassCurve (ZMod p))

/-- Arithmetic Frobenius on the geometric points of the reduction. -/
def curveFrob : (E⁄K).toAffine.Point →+ (E⁄K).toAffine.Point :=
  Affine.Point.map (W' := E) (FiniteField.frobeniusAlgHom (ZMod p) K)

private theorem frob_apply (x : K) :
    FiniteField.frobeniusAlgHom (ZMod p) K x = x ^ p := by
  change x ^ Fintype.card (ZMod p) = _
  rw [ZMod.card]

private theorem mem_roots_of_frob_sq {x : K}
    (hx : FiniteField.frobeniusAlgHom (ZMod p) K
      (FiniteField.frobeniusAlgHom (ZMod p) K x) = x) :
    x ∈ (X ^ (p * p) - X : K[X]).rootSet K := by
  rw [frob_apply, frob_apply, ← pow_mul] at hx
  have hne : (X ^ (p * p) - X : K[X]) ≠ 0 := by
    intro h
    have hd := congrArg (fun f : K[X] => f.coeff (p * p)) h
    have hp : p * p ≠ 1 := by
      intro h
      have h₁ : p ∣ 1 := ⟨p, h.symm⟩
      exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h₁)
    simp [coeff_X, hp, Ne.symm hp] at hd
  apply (mem_rootSet_of_ne hne).mpr
  simp [hx]

/-- The fixed group of arithmetic Frobenius squared is finite: its affine coordinates
are roots of X^(p²) - X. -/
theorem finite_curveFrob_fixedSq : Finite (FixedSq (curveFrob (K := K) E)) := by
  let roots := (X ^ (p * p) - X : K[X]).rootSet K
  letI : Finite roots := ((X ^ (p * p) - X : K[X]).rootSet_finite K).to_subtype
  let coord : FixedSq (curveFrob (K := K) E) → Option (roots × roots)
    | ⟨.zero, _⟩ => none
    | ⟨.some x y hxy, hP⟩ => by
      have h := (mem_fixedSq (curveFrob (K := K) E)).mp hP
      change Affine.Point.some _ _ _ = Affine.Point.some x y hxy at h
      have hh := Affine.Point.some.inj h
      exact some (⟨x, mem_roots_of_frob_sq hh.1⟩, ⟨y, mem_roots_of_frob_sq hh.2⟩)
  apply Finite.of_injective coord
  intro P Q h
  apply Subtype.ext
  rcases P with ⟨P, hP⟩
  rcases Q with ⟨Q, hQ⟩
  cases P <;> cases Q <;> simpa [coord, id, Affine.Point.some.injEq] using h

/-- The normalized Kummer map on the fixed subgroup over the quadratic field. The
only torsion hypothesis is the conclusion of specialization of the stage's Frobenius. -/
def reducedKappa [IsSepClosed K] [E.IsElliptic] (hp : p ≠ 2) (M : ℕ)
    (htriv : ∀ t : (E⁄K).toAffine.Point, (2 ^ M : ℕ) • t = 0 →
      curveFrob (K := K) E (curveFrob (K := K) E t) = t) :
    FixedSq (curveFrob (K := K) E) →+
      AddSubgroup.torsionBy (E⁄K).toAffine.Point (2 ^ M : ℕ) :=
  kappa (curveFrob (K := K) E) (2 ^ M) ((E⁄K).toAffine.nsmul_surjective (by
    push_cast
    refine pow_ne_zero _ ?_
    have hz : (2 : ZMod p) ≠ 0 := by
      change ((2 : ℕ) : ZMod p) ≠ 0
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).not.mpr hp
    have hK : (2 : K) ≠ 0 := by
      intro h
      apply hz
      apply (algebraMap (ZMod p) K).injective
      rw [map_ofNat, map_zero]
      exact h
    exact hK)) htriv

/-- Surjectivity on the reduced curve, using only the quadratic fixed-group count. -/
theorem reducedKappa_surjective [IsSepClosed K] [E.IsElliptic] (hp : p ≠ 2) (M : ℕ)
    (htriv : ∀ t : (E⁄K).toAffine.Point, (2 ^ M : ℕ) • t = 0 →
      curveFrob (K := K) E (curveFrob (K := K) E t) = t) :
    Function.Surjective (reducedKappa (K := K) E hp M htriv) := by
  letI : Finite (FixedSq (curveFrob (K := K) E)) := finite_curveFrob_fixedSq (K := K) E
  unfold reducedKappa
  apply kappa_surjective

#print axioms frob_apply
#print axioms mem_roots_of_frob_sq
#print axioms finite_curveFrob_fixedSq
#print axioms reducedKappa
#print axioms reducedKappa_surjective

end ZInQ.Manuscript.RC.Stages
