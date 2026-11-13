import ZInQKernel.Contrib.AdelicNormalizer.GlobalQuotient

/-!
# Prime evaluation and actual integral scalar units

The comparison between Mathlib's height-one places and rational primes is
transported explicitly.  In particular, evaluation at three has codomain the
same local quaternion algebra and order used by `Residue.lean`.
-/

open Quaternion
open IsDedekindDomain
open scoped RestrictedProduct

namespace G1

noncomputable section

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

abbrev primePlace (p : Nat.Primes) : Place := Rat.HeightOneSpectrum.primesEquiv.symm p

/-- Transport the local quaternion algebra along the actual prime/place equivalence. -/
def primeQuaternionEquiv (p : Nat.Primes) : Bv (primePlace p) ≃+* Bp p.1 :=
  RingEquiv.cast (R := fun q : Nat.Primes => Bp q.1)
    (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p)

/-- The corresponding scalar-field comparison. -/
def primeScalarEquiv (p : Nat.Primes) : Qv (primePlace p) ≃+* ℚ_[p.1] :=
  RingEquiv.cast (R := fun q : Nat.Primes => ℚ_[q.1])
    (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p)

theorem cast_mem_localOrder {p q : Nat.Primes} (h : p = q) (x : Bp p.1) :
    RingEquiv.cast (R := fun r : Nat.Primes => Bp r.1) h x ∈ localOrder q.1 ↔
      x ∈ localOrder p.1 := by
  cases h
  rfl

theorem cast_mem_localUnits {p q : Nat.Primes} (h : p = q) (x : (Bp p.1)ˣ) :
    Units.mapEquiv (RingEquiv.cast (R := fun r : Nat.Primes => Bp r.1) h).toMulEquiv x ∈
      localOrderUnits q.1 ↔ x ∈ localOrderUnits p.1 := by
  cases h
  rfl

theorem cast_mem_localNormalizer {p q : Nat.Primes} (h : p = q) (x : (Bp p.1)ˣ) :
    Units.mapEquiv (RingEquiv.cast (R := fun r : Nat.Primes => Bp r.1) h).toMulEquiv x ∈
      localNormalizer q.1 ↔ x ∈ localNormalizer p.1 := by
  cases h
  rfl

theorem cast_scalar {p q : Nat.Primes} (h : p = q) (c : ℚ_[p.1]ˣ) :
    Units.mapEquiv (RingEquiv.cast (R := fun r : Nat.Primes => Bp r.1) h).toMulEquiv
      (localScalar p.1 c) =
    localScalar q.1
      (Units.mapEquiv (RingEquiv.cast (R := fun r : Nat.Primes => ℚ_[r.1]) h).toMulEquiv c) := by
  cases h
  rfl

def quaternionAtPrime (p : Nat.Primes) : BA →+* Bp p.1 :=
  (primeQuaternionEquiv p).toRingHom.comp (quaternionEval (primePlace p))

def unitAtPrime (p : Nat.Primes) : BAˣ →* (Bp p.1)ˣ :=
  (Units.mapEquiv (primeQuaternionEquiv p).toMulEquiv).toMonoidHom.comp
    (unitEval (primePlace p))

def scalarUnitAtPrime (p : Nat.Primes) : Afˣ →* ℚ_[p.1]ˣ :=
  (Units.mapEquiv (primeScalarEquiv p).toMulEquiv).toMonoidHom.comp
    ((RestrictedProduct.evalMonoidHom (fun v : Place => (Qv v)ˣ) (primePlace p)).comp
      ideleEquiv.toMonoidHom)

@[simp] theorem unitAtPrime_val (p : Nat.Primes) (u : BAˣ) :
    ((unitAtPrime p u : (Bp p.1)ˣ) : Bp p.1) = quaternionAtPrime p (u : BA) := rfl

@[simp] theorem unitEval_unitEquiv_symm (x : UnitRP) (v : Place) :
    unitEval v (unitEquiv.symm x) = x v :=
  congrArg (fun y : UnitRP => y v) (unitEquiv.apply_symm_apply x)

theorem unitAtPrime_mem_K0 (p : Nat.Primes) {u : BAˣ} (hu : u ∈ K0) :
    unitAtPrime p u ∈ localOrderUnits p.1 :=
  (cast_mem_localUnits _ _).2 ((mem_K0 u).1 hu (primePlace p))

theorem unitAtPrime_mem_N (p : Nat.Primes) {u : BAˣ} (hu : u ∈ N) :
    unitAtPrime p u ∈ localNormalizer p.1 :=
  (cast_mem_localNormalizer _ _).2 ((mem_N u).1 hu (primePlace p))

theorem unitAtPrime_scalar (p : Nat.Primes) (c : Afˣ) :
    unitAtPrime p (scalarIdeles c) = localScalar p.1 (scalarUnitAtPrime p c) := by
  change Units.mapEquiv (primeQuaternionEquiv p).toMulEquiv
    (unitEval (primePlace p) (scalarIdeles c)) = _
  rw [unitEval_scalar]
  exact cast_scalar _ _

/-- Evaluation of actual completed-order units at the given rational prime. -/
def K0AtPrime (p : Nat.Primes) : K0 →* localOrderUnits p.1 where
  toFun u := ⟨unitAtPrime p u.val, unitAtPrime_mem_K0 p u.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u w := Subtype.ext (map_mul _ _ _)

/-- An actual adelic unit supported at one prime. -/
def liftLocalUnit (p : Nat.Primes) (u : localOrderUnits p.1) : K0 := by
  classical
  let e := Units.mapEquiv (primeQuaternionEquiv p).toMulEquiv
  let z : (Bv (primePlace p))ˣ := e.symm u.val
  have hz : z ∈ localOrderUnits (primeAt (primePlace p)).1 := by
    apply (cast_mem_localUnits (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p) z).1
    change e (e.symm u.val) ∈ localOrderUnits p.1
    rw [e.apply_symm_apply]
    exact u.property
  let x : UnitRP := RestrictedProduct.mulSingle (fun v => localOrderUnits (primeAt v).1)
    (primePlace p) z
  refine ⟨unitEquiv.symm x, (mem_K0 _).2 ?_⟩
  intro v
  have h := congrArg (fun y : UnitRP => y v) (unitEquiv.apply_symm_apply x)
  rw [h]
  by_cases hv : v = primePlace p
  · subst v
    simpa only [x, RestrictedProduct.mulSingle_eq_same] using hz
  · simp [x, RestrictedProduct.mulSingle_eq_of_ne _ _ hv]

theorem K0AtPrime_liftLocalUnit (p : Nat.Primes) (u : localOrderUnits p.1) :
    K0AtPrime p (liftLocalUnit p u) = u := by
  classical
  apply Subtype.ext
  let e := Units.mapEquiv (primeQuaternionEquiv p).toMulEquiv
  change e (unitEval (primePlace p) (unitEquiv.symm
    (RestrictedProduct.mulSingle (fun v => localOrderUnits (primeAt v).1)
      (primePlace p) (e.symm u.val)))) = u.val
  rw [unitEval_unitEquiv_symm, RestrictedProduct.mulSingle_eq_same]
  exact e.apply_symm_apply _

theorem K0AtPrime_surjective (p : Nat.Primes) : Function.Surjective (K0AtPrime p) :=
  fun u => ⟨liftLocalUnit p u, K0AtPrime_liftLocalUnit p u⟩

/-- Integral finite scalars as a subring of the actual finite adeles. -/
def Zhat : Subring Af where
  carrier := {a | ∀ v, scalarEquiv a v ∈ PadicInt.subring (primeAt v).1}
  zero_mem' v := by simp
  one_mem' v := by simp
  add_mem' ha hb v := by
    simpa only [map_add, RestrictedProduct.add_apply] using
      (PadicInt.subring (primeAt v).1).add_mem (ha v) (hb v)
  neg_mem' ha v := by
    simpa only [map_neg, RestrictedProduct.neg_apply] using
      (PadicInt.subring (primeAt v).1).neg_mem (ha v)
  mul_mem' ha hb v := by
    simpa only [map_mul, RestrictedProduct.mul_apply] using
      (PadicInt.subring (primeAt v).1).mul_mem (ha v) (hb v)

def ZhatUnits : Subgroup Afˣ := Zhat.toSubmonoid.units

/-- Integral scalar subgroup in quaternion units. -/
def Z0 : Subgroup BAˣ := scalarSubgroup ⊓ K0

theorem scalarIdeles_mem_K0 (c : Afˣ) : scalarIdeles c ∈ K0 ↔ c ∈ ZhatUnits := by
  rw [mem_K0]
  simp only [unitEquiv_apply, unitEval_scalar, scalar_mem_localUnits]
  change (∀ v, ideleEquiv c v ∈ (PadicInt.subring (primeAt v).1).toSubmonoid.units) ↔
    ((∀ v, scalarEquiv (c : Af) v ∈ PadicInt.subring (primeAt v).1) ∧
      ∀ v, scalarEquiv ((c⁻¹ : Afˣ) : Af) v ∈ PadicInt.subring (primeAt v).1)
  exact forall_and

theorem Z0_eq_integralScalars : Z0 = ZhatUnits.map scalarIdeles := by
  ext u
  constructor
  · rintro ⟨⟨c, rfl⟩, hc⟩
    exact ⟨c, (scalarIdeles_mem_K0 c).1 hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c, rfl⟩, (scalarIdeles_mem_K0 c).2 hc⟩

end

end G1
