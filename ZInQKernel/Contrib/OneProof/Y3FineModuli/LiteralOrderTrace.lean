import ZInQKernel.HDecomp.QM.Structures
import Mathlib.LinearAlgebra.Trace

/-!
# Trace of a two-dimensional action of the literal project quaternion order

This proves the linear-algebra prerequisite of the source's `act_trace` condition
for `LeafQM.O` itself. It does not construct a tangent model, a Tate module,
a moduli scheme, or a universal family. The dimension-two hypothesis belongs to
this representation lemma; it must be proved from actual tangent points before
using it in the geometric trace condition. No maximal-order or ramification
hypothesis is supplied by the caller or re-proved here.
-/

noncomputable section

open scoped Quaternion

namespace ZInQ.Contrib.OneProof.Y3FineModuli

open LeafQM LeafQM.AV

section Trace

variable {k V : Type*} [Field k] [CharZero k] [AddCommGroup V] [Module k V]

private theorem intCast_mul_end (z : ℤ) (X : Module.End k V) :
    (z : Module.End k V) * X = (z : k) • X := by
  ext v
  simp [Module.End.mul_apply, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]

private theorem natCast_mul_end (z : ℕ) (X : Module.End k V) :
    (z : Module.End k V) * X = (z : k) • X := by
  ext v
  simp [Module.End.mul_apply, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]

private theorem trace_zero_of_anticommute
    (X Y : Module.End k V) (c : k) (hc : c ≠ 0)
    (hanti : Y * X = -(X * Y)) (hY : Y * Y = c • (1 : Module.End k V)) :
    LinearMap.trace k V X = 0 := by
  have hcyc := LinearMap.trace_mul_cycle k Y X Y
  have hleft : Y * X * Y = -(c • X) := by
    rw [hanti, neg_mul, mul_assoc, hY, mul_smul_comm, mul_one]
  have hright : Y * Y * X = c • X := by
    rw [hY, smul_mul_assoc, one_mul]
  simp only [hleft, hright, map_neg, map_smul] at hcyc
  have hzero : (2 * c) * LinearMap.trace k V X = 0 := by
    simp only [smul_eq_mul] at hcyc
    linear_combination -hcyc
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (by norm_num) hc)

/-- The `i`, `j`, and `ij` operators have trace zero in any characteristic-zero
linear action of the actual order. This assertion does not use a dimension-four
Tate representation or assume the trace condition. -/
theorem quaternion_generators_trace_zero (ρ : LeafQM.O →+* Module.End k V) :
    LinearMap.trace k V (ρ oi) = 0 ∧
      LinearMap.trace k V (ρ oj) = 0 ∧
      LinearMap.trace k V (ρ (oi * oj)) = 0 := by
  let I := ρ oi
  let J := ρ oj
  have hanti : J * I = -(I * J) := by
    have h := congrArg ρ oj_mul_oi_add
    simp only [map_add, map_mul, map_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  have hanti' : I * J = -(J * I) := by
    have h := congrArg ρ oj_mul_oi_add
    simp only [map_add, map_mul, map_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  have hI : I * I = (2 : k) • (1 : Module.End k V) := by
    change ρ oi * ρ oi = _
    rw [← map_mul, oi_mul_oi, map_ofNat]
    simpa only [mul_one, Nat.cast_ofNat] using natCast_mul_end (k := k) (V := V) 2 1
  have hJ : J * J = (-3 : k) • (1 : Module.End k V) := by
    change ρ oj * ρ oj = _
    rw [← map_mul, oj_mul_oj, map_neg, map_ofNat]
    have hcast : (3 : Module.End k V) = (3 : k) • (1 : Module.End k V) := by
      simpa only [mul_one, Nat.cast_ofNat] using natCast_mul_end (k := k) (V := V) 3 1
    rw [hcast, neg_smul]
  have htI : LinearMap.trace k V I = 0 :=
    trace_zero_of_anticommute I J (-3) (by norm_num) hanti hJ
  have htJ : LinearMap.trace k V J = 0 :=
    trace_zero_of_anticommute J I 2 (by norm_num) hanti' hI
  have htr := LinearMap.trace_mul_comm k J I
  rw [hanti, map_neg] at htr
  have htIJ : LinearMap.trace k V (I * J) = 0 := by
    have hzero : (2 : k) * LinearMap.trace k V (I * J) = 0 := by
      linear_combination -htr
    exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
  exact ⟨htI, htJ, by simpa [I, J, map_mul] using htIJ⟩

/-- Integer reduced trace agrees with the trace of a two-dimensional linear
representation of the literal project order. All algebraic trace content is
proved here; the source's geometric tangent-dimension and operator-transport
steps are separate prerequisites. -/
theorem literal_order_trace_eq_intCast [FiniteDimensional k V]
    (ρ : LeafQM.O →+* Module.End k V) (hV : Module.finrank k V = 2)
    (m : LeafQM.O) (z : ℤ)
    (hz : (m : LeafQM.B) + star (m : LeafQM.B) = ((z : ℚ) : LeafQM.B)) :
    LinearMap.trace k V (ρ m) = (z : k) := by
  obtain ⟨n, hn⟩ := m.property
  obtain ⟨htI, htJ, htIJ⟩ := quaternion_generators_trace_zero ρ
  have hcoords : (2 : LeafQM.O) * m =
      ((2 * n 0 + n 2 : ℤ) : LeafQM.O) +
      ((2 * n 1 + n 3 : ℤ) : LeafQM.O) * oi +
      ((n 2 : ℤ) : LeafQM.O) * oj +
      ((n 3 : ℤ) : LeafQM.O) * (oi * oj) := by
    apply Subtype.val_injective
    change LeafQM.O.subtype ((2 : LeafQM.O) * m) = LeafQM.O.subtype
      (((2 * n 0 + n 2 : ℤ) : LeafQM.O) +
      ((2 * n 1 + n 3 : ℤ) : LeafQM.O) * oi +
      ((n 2 : ℤ) : LeafQM.O) * oj +
      ((n 3 : ℤ) : LeafQM.O) * (oi * oj))
    simp only [map_mul, map_add, map_intCast, map_ofNat]
    change (2 : LeafQM.B) * (m : LeafQM.B) =
      ((2 * n 0 + n 2 : ℤ) : LeafQM.B) +
      ((2 * n 1 + n 3 : ℤ) : LeafQM.B) * (oi : LeafQM.B) +
      ((n 2 : ℤ) : LeafQM.B) * (oj : LeafQM.B) +
      ((n 3 : ℤ) : LeafQM.B) * ((oi : LeafQM.B) * (oj : LeafQM.B))
    rw [hn]
    ext <;> simp [LeafQM.ofInt, oi, oj, Nat.cast_ofNat,
      QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
      QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring
  have hscalar : ∀ a : ℤ, LinearMap.trace k V (a : Module.End k V) = (a : k) * 2 := by
    intro a
    have hcast : (a : Module.End k V) = (a : k) • (1 : Module.End k V) := by
      simpa only [mul_one] using intCast_mul_end (k := k) (V := V) a 1
    rw [hcast, map_smul, LinearMap.trace_one, hV]
    simp [smul_eq_mul]
  have htIJ' : LinearMap.trace k V (ρ oi * ρ oj) = 0 := by
    simpa only [map_mul] using htIJ
  have htr := congrArg (fun a : LeafQM.O => LinearMap.trace k V (ρ a)) hcoords
  simp only [map_mul, map_add, map_intCast, map_ofNat] at htr
  have htwoMul : (2 : Module.End k V) * ρ m = (2 : k) • ρ m := by
    simpa only [Nat.cast_ofNat] using natCast_mul_end (k := k) (V := V) 2 (ρ m)
  rw [htwoMul] at htr
  simp only [intCast_mul_end, map_smul, htI, htJ, htIJ',
    smul_zero, add_zero, hscalar, smul_eq_mul] at htr
  have hc : LinearMap.trace k V (ρ m) = ((2 * n 0 + n 2 : ℤ) : k) := by
    have htwo : (2 : k) ≠ 0 := by norm_num
    apply (mul_left_cancel₀ htwo)
    simpa [mul_comm] using htr
  have hzre := congrArg QuaternionAlgebra.re hz
  rw [hn] at hzre
  simp [LeafQM.ofInt, QuaternionAlgebra.star_mk] at hzre
  have hzin : (2 * n 0 + n 2 : ℤ) = z := by
    have hq : ((2 * n 0 + n 2 : ℤ) : ℚ) = z := by
      push_cast
      linarith
    exact_mod_cast hq
  simpa [hzin] using hc

end Trace

end ZInQ.Contrib.OneProof.Y3FineModuli
