import ZInQKernel.Contrib.AdelicNormalizer.LevelThree

/-!
# Actual integral scalar images at level three

Integral scalar units are lifted as actual finite ideles, with value one at
all other places.  Their reduction image is exactly the central scalar residue
subgroup, not merely a subgroup of the same asserted cardinality.
-/

open Quaternion
open IsDedekindDomain
open scoped RestrictedProduct

namespace G1

noncomputable section

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem mem_ZhatUnits (c : Afˣ) :
    c ∈ ZhatUnits ↔ ∀ v, ideleEquiv c v ∈
      (PadicInt.subring (primeAt v).1).toSubmonoid.units := by
  change ((∀ v, scalarEquiv (c : Af) v ∈ PadicInt.subring (primeAt v).1) ∧
    ∀ v, scalarEquiv ((c⁻¹ : Afˣ) : Af) v ∈ PadicInt.subring (primeAt v).1) ↔
    ∀ v, ideleEquiv c v ∈ (PadicInt.subring (primeAt v).1).toSubmonoid.units
  exact forall_and.symm

theorem cast_mem_integralScalars {p q : Nat.Primes} (h : p = q) (c : ℚ_[p.1]ˣ) :
    Units.mapEquiv (RingEquiv.cast (R := fun r : Nat.Primes => ℚ_[r.1]) h).toMulEquiv c ∈
      (PadicInt.subring q.1).toSubmonoid.units ↔
    c ∈ (PadicInt.subring p.1).toSubmonoid.units := by
  cases h
  rfl

@[simp] theorem ideleEquiv_symm_eval (c : IdeleRP) (v : Place) :
    ideleEquiv (ideleEquiv.symm c) v = c v :=
  congrArg (fun y : IdeleRP => y v) (ideleEquiv.apply_symm_apply c)

/-- An integral local scalar unit, lifted to actual integral finite ideles. -/
def liftIntegralScalar (p : Nat.Primes) (c : ℤ_[p.1]ˣ) : ZhatUnits := by
  classical
  let q : ℚ_[p.1]ˣ := Units.map PadicInt.Coe.ringHom.toMonoidHom c
  have hq : q ∈ (PadicInt.subring p.1).toSubmonoid.units :=
    ⟨PadicInt.norm_le_one _, PadicInt.norm_le_one _⟩
  let e := Units.mapEquiv (primeScalarEquiv p).toMulEquiv
  let z : (Qv (primePlace p))ˣ := e.symm q
  have hz : z ∈ (PadicInt.subring (primeAt (primePlace p)).1).toSubmonoid.units := by
    apply (cast_mem_integralScalars (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p) z).1
    change e (e.symm q) ∈ (PadicInt.subring p.1).toSubmonoid.units
    rw [e.apply_symm_apply]
    exact hq
  let x : IdeleRP := RestrictedProduct.mulSingle
    (fun v => (PadicInt.subring (primeAt v).1).toSubmonoid.units) (primePlace p) z
  refine ⟨ideleEquiv.symm x, (mem_ZhatUnits _).2 ?_⟩
  intro v
  rw [ideleEquiv_symm_eval]
  by_cases hv : v = primePlace p
  · subst v
    simpa only [x, RestrictedProduct.mulSingle_eq_same] using hz
  · simp [x, RestrictedProduct.mulSingle_eq_of_ne _ _ hv]

theorem scalarUnitAtPrime_liftIntegralScalar (p : Nat.Primes) (c : ℤ_[p.1]ˣ) :
    scalarUnitAtPrime p (liftIntegralScalar p c).val =
      Units.map PadicInt.Coe.ringHom.toMonoidHom c := by
  classical
  let e := Units.mapEquiv (primeScalarEquiv p).toMulEquiv
  let q : ℚ_[p.1]ˣ := Units.map PadicInt.Coe.ringHom.toMonoidHom c
  change e (ideleEquiv (ideleEquiv.symm
    (RestrictedProduct.mulSingle
      (fun v => (PadicInt.subring (primeAt v).1).toSubmonoid.units)
      (primePlace p) (e.symm q))) (primePlace p)) = q
  rw [ideleEquiv_symm_eval, RestrictedProduct.mulSingle_eq_same]
  exact e.apply_symm_apply _

/-- A field unit integral in both directions, as an actual `ℤ_3` unit. -/
def integralPadicUnit (c : ℚ_[3]ˣ)
    (hc : c ∈ (PadicInt.subring 3).toSubmonoid.units) : ℤ_[3]ˣ where
  val := ⟨c, hc.1⟩
  inv := ⟨((c⁻¹ : ℚ_[3]ˣ) : ℚ_[3]), hc.2⟩
  val_inv := by apply PadicInt.ext; exact c.val_inv
  inv_val := by apply PadicInt.ext; exact c.inv_val

theorem map_integralPadicUnit (c : ℚ_[3]ˣ)
    (hc : c ∈ (PadicInt.subring 3).toSubmonoid.units) :
    Units.map PadicInt.Coe.ringHom.toMonoidHom (integralPadicUnit c hc) = c :=
  Units.ext rfl

/-- Actual integral finite scalar units embedded into actual adelic order units. -/
def integralScalarK0 : ZhatUnits →* K0 where
  toFun c := ⟨scalarIdeles c.val, (scalarIdeles_mem_K0 c.val).2 c.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' c d := Subtype.ext (map_mul _ _ _)

theorem K0AtThree_integralScalar (c : ZhatUnits) :
    ∃ q : ℤ_[3]ˣ, K0AtPrime primeThree (integralScalarK0 c) = Residue.localIntScalar q := by
  let q := scalarUnitAtPrime primeThree c.val
  have hq : q ∈ (PadicInt.subring 3).toSubmonoid.units := by
    apply (scalar_mem_localUnits 3 q).1
    have h := unitAtPrime_mem_K0 primeThree (integralScalarK0 c).property
    change unitAtPrime primeThree (scalarIdeles c.val) ∈ localOrderUnits 3 at h
    rwa [unitAtPrime_scalar] at h
  refine ⟨integralPadicUnit q hq, Subtype.ext ?_⟩
  change unitAtPrime primeThree (scalarIdeles c.val) =
    localScalar 3 (Units.map PadicInt.Coe.ringHom.toMonoidHom (integralPadicUnit q hq))
  rw [unitAtPrime_scalar, map_integralPadicUnit]

theorem K0AtThree_liftIntegralScalar (q : ℤ_[3]ˣ) :
    K0AtPrime primeThree (integralScalarK0 (liftIntegralScalar primeThree q)) =
      Residue.localIntScalar q := by
  apply Subtype.ext
  change unitAtPrime primeThree (scalarIdeles (liftIntegralScalar primeThree q).val) =
    localScalar 3 (Units.map PadicInt.Coe.ringHom.toMonoidHom q)
  rw [unitAtPrime_scalar, scalarUnitAtPrime_liftIntegralScalar]

/-- The reductions of actual integral finite scalar units are exactly all
scalar residue units.  Both inclusions have actual map witnesses. -/
theorem range_reduction3_integralScalar :
    (reduction3.comp integralScalarK0).range = Residue.scalarUnits.range := by
  ext w
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨q, hq⟩ := K0AtThree_integralScalar c
    change Residue.unitReduction (K0AtPrime primeThree (integralScalarK0 c)) ∈ _
    rw [hq, Residue.unitReduction_localIntScalar]
    exact ⟨_, rfl⟩
  · intro hw
    have hq : w ∈ (Residue.unitReduction.comp Residue.localIntScalar).range :=
      Residue.range_unitReduction_localIntScalar.symm ▸ hw
    obtain ⟨q, hq⟩ := hq
    refine ⟨liftIntegralScalar primeThree q, ?_⟩
    change Residue.unitReduction
      (K0AtPrime primeThree (integralScalarK0 (liftIntegralScalar primeThree q))) = w
    rw [K0AtThree_liftIntegralScalar]
    exact hq

instance Z0_normal : Z0.Normal := by
  apply Subgroup.normal_of_le_center
  rintro _ ⟨⟨c, rfl⟩, _⟩
  exact Subgroup.mem_center_iff.2 fun u => (scalarIdeles_comm c u).symm

end

end G1
