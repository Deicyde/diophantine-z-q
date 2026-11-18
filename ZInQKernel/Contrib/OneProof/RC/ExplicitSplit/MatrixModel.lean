import Mathlib
import ZInQKernel.Contrib.OneProof.RC.ExplicitSplit.Lattice
import ZInQKernel.Contrib.OneProof.RC.ExplicitSplit.Scalars

/-!
# The explicit level-one split model

On-the-spot (c), for tex 8464–8465 and the local matrix model at 9041.
The same formulas work at two. The inverse on the explicit coordinates
only divides by the unit `-ell`.
-/

namespace ZInQ.Manuscript.RC.ExplicitSplit

open Eichler
open scoped Quaternion

noncomputable section

variable {R : Type*} [CommRing R]

private def encode (a b : R) (v : Fin 4 → R) : M2 R :=
  !![v 0 + a * v 2 - b * v 3, -v 1 + b * v 2 + (a - 1) * v 3;
     v 1 + b * v 2 + a * v 3, v 0 + (1 - a) * v 2 + b * v 3]

private def decode (a b r : R) (M : M2 R) : Fin 4 → R :=
  let u := 2 * a - 1
  let v := 2 * b
  let x := M 0 0 - M 1 1
  let y := M 0 1 + M 1 0
  let c := r * (u * x + v * y)
  let d := r * (u * y - v * x)
  ![M 0 0 - a * c + b * d, M 1 0 - b * c - a * d, c, d]

private theorem decode_encode (a b r : R)
    (hr : r * ((2 * a - 1) ^ 2 + (2 * b) ^ 2) = 1) (v : Fin 4 → R) :
    decode a b r (encode a b v) = v := by
  ext i
  fin_cases i <;> simp [decode, encode]
  · linear_combination (-a * v 2 + b * v 3) * hr
  · linear_combination (-b * v 2 - a * v 3) * hr
  · linear_combination v 2 * hr
  · linear_combination v 3 * hr

private theorem encode_decode (a b r : R)
    (hr : r * ((2 * a - 1) ^ 2 + (2 * b) ^ 2) = 1) (M : M2 R) :
    encode a b (decode a b r M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [decode, encode]
  · ring
  · linear_combination (M 0 1 + M 1 0) * hr
  · ring
  · linear_combination (M 1 1 - M 0 0) * hr

private theorem encode_map {S : Type*} [CommRing S] (f : R →+* S)
    (a b : R) (v : Fin 4 → R) :
    (encode a b v).map f = encode (f a) (f b) (fun i => f (v i)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [encode]

variable {K : Type*} [Field K] [CharZero K]

private def matrixBasis (a b c d : K) (hc : c = -1)
    (hd : (2 * a - 1) ^ 2 + (2 * b) ^ 2 = d) :
    QuaternionAlgebra.Basis (M2 K) c 0 d where
  i := !![0,-1;1,0]
  j := !![2 * a - 1,2 * b;2 * b,-(2 * a - 1)]
  k := !![-(2 * b),2 * a - 1;2 * a - 1,2 * b]
  i_mul_i := by
    rw [hc, Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  j_mul_j := by
    rw [← hd, Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  i_mul_j := by simp
  j_mul_i := by
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

private theorem lift_eq_encode (a b c d : K) (hc : c = -1)
    (hd : (2 * a - 1) ^ 2 + (2 * b) ^ 2 = d) (v : Fin 4 → K) :
    (matrixBasis a b c d hc hd).liftHom
        ⟨v 0 + v 2 / 2, v 1 + v 3 / 2, v 2 / 2, v 3 / 2⟩ = encode a b v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixBasis, QuaternionAlgebra.Basis.lift, Matrix.algebraMap_matrix_apply, encode] <;>
    ring

variable {p : ℕ} [Fact p.Prime]

/-- At a prime other than `ell`, the explicit completed order is taken onto
the standard integral matrix order by a local algebra equivalence. -/
theorem explicit_split_profile {ell : ℕ} (hell : ell.Prime) (h : ell % 4 = 3)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ ell) :
    ∃ f : Bp p (-1) (-(ell : ℚ)) ≃ₐ[ℚ_[p]] M2 ℚ_[p],
      f '' ((explicitOrderAt ell h).completion p : Set (Bp p (-1) (-(ell : ℚ)))) =
        standardLevel p 0 := by
  obtain ⟨a, b, hab⟩ := integral_parameters hell h hp
  have hunit : IsUnit (-(ell : ℤ_[p])) := by
    apply IsUnit.neg
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff,
      Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)]
    exact fun hd => hp ((Nat.prime_dvd_prime_iff_eq Fact.out hell).mp hd)
  obtain ⟨unit, hu⟩ := hunit
  let r : ℤ_[p] := ↑unit⁻¹
  have hr : r * ((2 * a - 1) ^ 2 + (2 * b) ^ 2) = 1 := by
    rw [hab, ← hu, Units.inv_mul]
  let ι : ℤ_[p] →+* ℚ_[p] := algebraMap _ _
  have hab' : (2 * ι a - 1) ^ 2 + (2 * ι b) ^ 2 = ((-(ell : ℚ)) : ℚ_[p]) := by
    simpa only [map_add, map_mul, map_pow, map_sub, map_neg, map_one, map_ofNat,
      map_natCast, Rat.cast_neg, Rat.cast_natCast] using congrArg ι hab
  have hr' : ι r * ((2 * ι a - 1) ^ 2 + (2 * ι b) ^ 2) = 1 := by
    simpa only [map_add, map_mul, map_pow, map_sub, map_one, map_ofNat] using congrArg ι hr
  let q : QuaternionAlgebra.Basis (M2 ℚ_[p]) ((-1 : ℚ) : ℚ_[p]) 0
      ((-(ell : ℚ)) : ℚ_[p]) :=
    matrixBasis (ι a) (ι b) _ _ (by simp) hab'
  let g : Bp p (-1) (-(ell : ℚ)) →ₐ[ℚ_[p]] M2 ℚ_[p] := q.liftHom
  let e := localCoords p (-(ell : ℚ))
  have hg (v : Fin 4 → ℚ_[p]) : g (e.symm v) = encode (ι a) (ι b) v :=
    lift_eq_encode (ι a) (ι b) _ _ (by simp) hab' v
  have hbij : Function.Bijective g := by
    constructor
    · intro x y hxy
      apply e.injective
      rw [← e.symm_apply_apply x, ← e.symm_apply_apply y, hg, hg] at hxy
      have he := congrArg (decode (ι a) (ι b) (ι r)) hxy
      simpa only [decode_encode _ _ _ hr'] using he
    · intro M
      exact ⟨e.symm (decode (ι a) (ι b) (ι r) M),
        (hg _).trans (encode_decode _ _ _ hr' M)⟩
  let f := AlgEquiv.ofBijective g hbij
  refine ⟨f, ?_⟩
  rw [standardLevel_zero]
  ext M
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨v, rfl⟩ := (completion_coeffs p ell h x).mp hx
    exact ⟨encode a b v, (encode_map ι a b v).trans (hg _).symm⟩
  · rintro ⟨m, rfl⟩
    let v := decode a b r m
    let x := e.symm (fun i => ι (v i))
    refine ⟨x, (completion_coeffs p ell h x).mpr ⟨v, rfl⟩, ?_⟩
    change g (e.symm (fun i => ι (v i))) = m.map ι
    rw [hg, ← encode_map ι, encode_decode _ _ _ hr m]

/-- The split half of the Eichler profile, with the ramified half as input. -/
theorem explicit_isEichler_of_ramified_maximal {ell : ℕ}
    (hell : ell.Prime) (h : ell % 4 = 3)
    (hmax : ∀ (p : ℕ) [Fact p.Prime], p = ell →
      IsMaximalLocalOrder p ((explicitOrderAt ell h).completion p)) :
    IsEichler ell 1 (explicitOrderAt ell h) :=
  ⟨hell, Nat.one_pos, Nat.coprime_one_left _, hmax,
    fun p _ hp => by simpa using explicit_split_profile hell h p hp⟩

#print axioms decode_encode
#print axioms encode_decode
#print axioms encode_map
#print axioms lift_eq_encode
#print axioms explicit_split_profile
#print axioms explicit_isEichler_of_ramified_maximal

end

end ZInQ.Manuscript.RC.ExplicitSplit
