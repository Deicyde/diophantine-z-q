import ZInQKernel.Contrib.AdelicNormalizer.Local
import ZInQKernel.HDecomp.Repo.A1Quaternion
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Actual objects for the adelic normalizer calculation

The rational order is `GlueRepo.A1.O`.  The local carrier and the local
normalizer results are the unchanged proof source in `Local.lean`; this module
adds its subring and subgroup structures and the comparison maps.  The scalar
ring is Mathlib's `IsDedekindDomain.FiniteAdeleRing ℤ ℚ`, not a full product.
This is a contribution, not an acceptance record.
-/

open Quaternion
open scoped RestrictedProduct
open IsDedekindDomain

namespace G1

noncomputable section

/-- Coefficient-wise scalar extension for the quaternion algebra `(2,-3)`. -/
@[simps]
def quaternionMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    ℍ[R, 2, 0, -3] →+* ℍ[S, 2, 0, -3] where
  toFun x := ⟨f x.re, f x.imI, f x.imJ, f x.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp [map_add, map_mul, map_sub, map_ofNat]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

/-- The same integral structure constants as `GlueRepo.A1.combMul`. -/
def coordMul {R : Type*} [CommRing R] (n m : Fin 4 → R) : Fin 4 → R :=
  ![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

@[simp] theorem coordMul_int (n m : Fin 4 → ℤ) :
    coordMul n m = GlueRepo.A1.combMul n m := rfl

@[simp] theorem coordMul_mod3 (n m : Fin 4 → ZMod 3) :
    coordMul n m = GlueRepo.A1.mul3 n m := rfl

section LocalOrder

variable (p : ℕ) [Fact p.Prime]

abbrev Bp := GlueVigneras.Bp p

/-- Scalar extension of the actual rational algebra. -/
def rationalToLocal : GlueRepo.A1.B →+* Bp p := quaternionMap (algebraMap ℚ ℚ_[p])

theorem rationalToLocal_comb (n : Fin 4 → ℤ) :
    rationalToLocal p (GlueRepo.A1.comb n) =
      GlueVigneras.combp p (fun k => (n k : ℤ_[p])) := by
  ext <;> simp [rationalToLocal, quaternionMap, GlueRepo.A1.comb, GlueVigneras.combp]

/-- Scalar extension respects the four ordered basis vectors, including at two. -/
theorem rationalToLocal_basis (k : Fin 4) :
    rationalToLocal p (GlueRepo.A1.e k) = GlueVigneras.ek p k := by
  fin_cases k <;> ext <;>
    simp [rationalToLocal, quaternionMap, GlueRepo.A1.e, GlueVigneras.ek, GlueVigneras.combp]

theorem combp_mul (n m : Fin 4 → ℤ_[p]) :
    GlueVigneras.combp p n * GlueVigneras.combp p m =
      GlueVigneras.combp p (coordMul n m) := by
  ext <;> simp [GlueVigneras.combp, coordMul] <;> push_cast <;> ring

/-- The full `ℤ_p`-span of the actual order basis, as a subring. -/
def localOrder : Subring (Bp p) where
  carrier := GlueVigneras.Op p
  one_mem' := ⟨![1, 0, 0, 0], by ext <;> simp [GlueVigneras.combp]⟩
  zero_mem' := ⟨0, by ext <;> simp [GlueVigneras.combp]⟩
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨n + m, by ext <;> simp [GlueVigneras.combp] <;> ring⟩
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    exact ⟨-n, by ext <;> simp [GlueVigneras.combp] <;> ring⟩
  mul_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨coordMul n m, (combp_mul p n m).symm⟩

@[simp] theorem mem_localOrder (x : Bp p) :
    x ∈ localOrder p ↔ x ∈ GlueVigneras.Op p := Iff.rfl

/-- Order units in the ambient local quaternion unit group. -/
def localOrderUnits : Subgroup (Bp p)ˣ := (localOrder p).toSubmonoid.units

@[simp] theorem mem_localOrderUnits (u : (Bp p)ˣ) :
    u ∈ localOrderUnits p ↔ u ∈ GlueVigneras.OpUnits p := Iff.rfl

/-- Normalizer of the order, not merely of a selected collection of units. -/
def localNormalizer : Subgroup (Bp p)ˣ where
  carrier := GlueVigneras.normalizerOp p
  one_mem' := by simp [GlueVigneras.normalizerOp]
  mul_mem' := by
    intro a b ha hb y
    calc
      y ∈ GlueVigneras.Op p ↔
          (b : Bp p) * y * ((b⁻¹ : (Bp p)ˣ) : Bp p) ∈ GlueVigneras.Op p := hb y
      _ ↔ (a : Bp p) * ((b : Bp p) * y * ((b⁻¹ : (Bp p)ˣ) : Bp p)) *
          ((a⁻¹ : (Bp p)ˣ) : Bp p) ∈ GlueVigneras.Op p := ha _
      _ ↔ ((a * b : (Bp p)ˣ) : Bp p) * y *
          (((a * b)⁻¹ : (Bp p)ˣ) : Bp p) ∈ GlueVigneras.Op p := by
        simp [mul_assoc]
  inv_mem' := by
    intro a ha y
    have h := ha (((a⁻¹ : (Bp p)ˣ) : Bp p) * y * (a : Bp p))
    simpa [mul_assoc] using h.symm

@[simp] theorem mem_localNormalizer (u : (Bp p)ˣ) :
    u ∈ localNormalizer p ↔ u ∈ GlueVigneras.normalizerOp p := Iff.rfl

theorem localOrderUnits_le_normalizer : localOrderUnits p ≤ localNormalizer p := by
  intro u hu y
  rcases hu with ⟨hu, hui⟩
  constructor
  · intro hy
    exact (localOrder p).mul_mem ((localOrder p).mul_mem hu hy) hui
  · intro hy
    have h := (localOrder p).mul_mem ((localOrder p).mul_mem hui hy) hu
    simpa [mul_assoc] using h

/-- The central embedding of local scalar units. -/
def localScalar : ℚ_[p]ˣ →* (Bp p)ˣ :=
  Units.map (algebraMap ℚ_[p] (Bp p)).toMonoidHom

@[simp] theorem localScalar_val (c : ℚ_[p]ˣ) :
    ((localScalar p c : (Bp p)ˣ) : Bp p) = algebraMap ℚ_[p] (Bp p) c := rfl

theorem localScalar_mem_normalizer (c : ℚ_[p]ˣ) :
    localScalar p c ∈ localNormalizer p := by
  intro y
  have h : (localScalar p c : Bp p) * y *
      ((localScalar p c)⁻¹ : (Bp p)ˣ) = y := by
    change ((c : ℚ_[p]) : Bp p) * y * (((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) : Bp p) = y
    rw [QuaternionAlgebra.coe_mul_eq_smul, QuaternionAlgebra.mul_coe_eq_smul, smul_smul]
    simp
  rw [h]

end LocalOrder

/-- Mathlib's indexing set includes every finite prime. -/
abbrev Place := HeightOneSpectrum ℤ

/-- All rational finite primes, with no exclusions. -/
abbrev primeAt (v : Place) : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v

instance primeAt_fact (v : Place) : Fact (primeAt v).1.Prime := ⟨(primeAt v).2⟩

abbrev Qv (v : Place) := ℚ_[(primeAt v).1]
abbrev Zv (v : Place) := ℤ_[(primeAt v).1]
abbrev Bv (v : Place) := Bp (primeAt v).1

/-- Actual finite adeles; the completion API is not replaced by a full product. -/
abbrev Af := IsDedekindDomain.FiniteAdeleRing ℤ ℚ

/-- A coordinate realization of the scalar finite adele ring over the same index set. -/
abbrev PadicAf := Πʳ v : Place, [Qv v, PadicInt.subring (primeAt v).1]

/-- Actual completion comparison supplied by Mathlib. -/
def completionEquiv (v : Place) : v.adicCompletion ℚ ≃+* Qv v :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv

theorem completionEquiv_mem (v : Place) (x : v.adicCompletion ℚ) :
    completionEquiv v x ∈ PadicInt.subring (primeAt v).1 ↔
      x ∈ v.adicCompletionIntegers ℚ := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ :=
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).surjOn hx
    exact (completionEquiv v).injective hxy ▸ hy
  · intro hx
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo hx

/-- Scalar finite-adele comparison, with both integral carriers checked. -/
def scalarEquiv : Af ≃+* PadicAf where
  toFun a := ⟨fun v => completionEquiv v (a v), by
    filter_upwards [a.2] with v hv
    exact (completionEquiv_mem v _).2 hv⟩
  invFun a := ⟨fun v => (completionEquiv v).symm (a v), by
    filter_upwards [a.2] with v hv
    apply (completionEquiv_mem v _).1
    rw [(completionEquiv v).apply_symm_apply]
    exact hv⟩
  left_inv a := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro v
    exact (completionEquiv v).symm_apply_apply _
  right_inv a := by ext v; exact (completionEquiv v).apply_symm_apply _
  map_mul' a b := by ext v; exact map_mul (completionEquiv v) _ _
  map_add' a b := by ext v; exact map_add (completionEquiv v) _ _

/-- Evaluation is a ring homomorphism, not a chosen pointwise correspondence. -/
def scalarEval (v : Place) : Af →+* Qv v :=
  (RestrictedProduct.evalRingHom (fun v : Place => Qv v) v).comp scalarEquiv.toRingHom

theorem scalarEval_apply (a : Af) (v : Place) :
    scalarEval v a = completionEquiv v (a v) := rfl

@[simp] theorem scalarEval_rat (v : Place) (q : ℚ) :
    scalarEval v (algebraMap ℚ Af q) = algebraMap ℚ (Qv v) q := by
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).commutes q

/-- The actual scalar-extended quaternion algebra over Mathlib's finite adeles. -/
abbrev BA := ℍ[Af, 2, 0, -3]

/-- Evaluation of the actual adelic quaternion algebra at a finite prime. -/
def quaternionEval (v : Place) : BA →+* Bv v := quaternionMap (scalarEval v)

/-- The completed order in the actual finite-adelic quaternion algebra. -/
def completedOrder : Subring BA where
  carrier := {x | ∀ v, quaternionEval v x ∈ localOrder (primeAt v).1}
  zero_mem' v := by simpa using (localOrder (primeAt v).1).zero_mem
  one_mem' v := by simpa using (localOrder (primeAt v).1).one_mem
  add_mem' hx hy v := by simpa using (localOrder (primeAt v).1).add_mem (hx v) (hy v)
  neg_mem' hx v := by simpa using (localOrder (primeAt v).1).neg_mem (hx v)
  mul_mem' hx hy v := by simpa using (localOrder (primeAt v).1).mul_mem (hx v) (hy v)

/-- The order unit subgroup in actual adelic units. -/
def K0 : Subgroup BAˣ := completedOrder.toSubmonoid.units

/-- Actual finite ideles embedded as central quaternion units. -/
def scalarIdeles : Afˣ →* BAˣ := Units.map (algebraMap Af BA).toMonoidHom

/-- The scalar subgroup is the image of actual finite ideles. -/
def scalarSubgroup : Subgroup BAˣ := scalarIdeles.range

end

end G1
