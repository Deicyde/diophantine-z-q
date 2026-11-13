import ZInQKernel.Contrib.AdelicNormalizer.Objects

/-!
# Restricted-product realization of the actual adelic quaternion algebra

No global normalizer is defined as the desired product.  The normalizer below
acts by conjugation on `completedOrder` in `BAˣ`.  The componentwise description
is a theorem, using single-place order elements for the reverse comparison.
-/

open Quaternion
open IsDedekindDomain
open scoped RestrictedProduct

namespace G1

noncomputable section

abbrev QuaternionRP := Πʳ v : Place, [Bv v, localOrder (primeAt v).1]
abbrev UnitRP := Πʳ v : Place, [(Bv v)ˣ, localOrderUnits (primeAt v).1]
abbrev IdeleRP := Πʳ v : Place, [(Qv v)ˣ,
  (PadicInt.subring (primeAt v).1).toSubmonoid.units]

/-- Evaluation separates actual adelic quaternion elements. -/
theorem quaternionEval_injective {x y : BA}
    (h : ∀ v, quaternionEval v x = quaternionEval v y) : x = y := by
  apply QuaternionAlgebra.ext
  all_goals
    apply scalarEquiv.injective
    apply RestrictedProduct.ext
    intro v
  · exact congrArg QuaternionAlgebra.re (h v)
  · exact congrArg QuaternionAlgebra.imI (h v)
  · exact congrArg QuaternionAlgebra.imJ (h v)
  · exact congrArg QuaternionAlgebra.imK (h v)

/-- Evaluation has the restrictedness condition for the actual order basis. -/
def toQuaternionRP (x : BA) : QuaternionRP :=
  ⟨fun v => quaternionEval v x, by
    filter_upwards [(scalarEquiv x.re).2, (scalarEquiv x.imI).2,
      (scalarEquiv x.imJ).2, (scalarEquiv x.imK).2] with v hr hi hj hk
    change scalarEval v x.re ∈ PadicInt.subring (primeAt v).1 at hr
    change scalarEval v x.imI ∈ PadicInt.subring (primeAt v).1 at hi
    change scalarEval v x.imJ ∈ PadicInt.subring (primeAt v).1 at hj
    change scalarEval v x.imK ∈ PadicInt.subring (primeAt v).1 at hk
    have htwo : (2 : Qv v) ∈ PadicInt.subring (primeAt v).1 := by
      simpa using (intCast_mem (PadicInt.subring (primeAt v).1) (2 : ℤ))
    change quaternionEval v x ∈ localOrder (primeAt v).1
    rw [mem_localOrder, GlueVigneras.mem_Op_iff_coord]
    intro k
    fin_cases k
    · simpa [GlueVigneras.coord, quaternionEval, quaternionMap] using
        (PadicInt.subring (primeAt v).1).sub_mem hr hj
    · simpa [GlueVigneras.coord, quaternionEval, quaternionMap] using
        (PadicInt.subring (primeAt v).1).sub_mem hi hk
    · simpa [GlueVigneras.coord, quaternionEval, quaternionMap] using
        (PadicInt.subring (primeAt v).1).mul_mem
          htwo hj
    · simpa [GlueVigneras.coord, quaternionEval, quaternionMap] using
        (PadicInt.subring (primeAt v).1).mul_mem
          htwo hk⟩

@[simp] theorem toQuaternionRP_apply (x : BA) (v : Place) :
    toQuaternionRP x v = quaternionEval v x := rfl

/-- Recover one order-basis coordinate as an actual finite adele. -/
def globalCoord (x : QuaternionRP) (k : Fin 4) : Af :=
  scalarEquiv.symm ⟨fun v => GlueVigneras.coord (primeAt v).1 (x v) k, by
    filter_upwards [x.2] with v hv
    exact (GlueVigneras.mem_Op_iff_coord _ _).1 hv k⟩

@[simp] theorem globalCoord_eval (x : QuaternionRP) (k : Fin 4) (v : Place) :
    scalarEval v (globalCoord x k) = GlueVigneras.coord (primeAt v).1 (x v) k := by
  exact congrArg (fun y : PadicAf => y v) (scalarEquiv.apply_symm_apply _)

/-- Assembly uses the same four basis vectors, not the standard integral
quaternion lattice at the prime two. -/
def fromQuaternionRP (x : QuaternionRP) : BA :=
  let h : Af := algebraMap ℚ Af (1 / 2)
  ⟨globalCoord x 0 + h * globalCoord x 2,
    globalCoord x 1 + h * globalCoord x 3,
    h * globalCoord x 2, h * globalCoord x 3⟩

@[simp] theorem quaternionEval_from (x : QuaternionRP) (v : Place) :
    quaternionEval v (fromQuaternionRP x) = x v := by
  ext <;> simp [quaternionEval, quaternionMap, fromQuaternionRP, globalCoord_eval,
    GlueVigneras.coord] <;> ring

/-- The actual quaternion algebra over finite adeles is the restricted product
of the local algebras with respect to the completed manuscript order. -/
def quaternionEquiv : BA ≃+* QuaternionRP where
  toFun := toQuaternionRP
  invFun := fromQuaternionRP
  left_inv x := quaternionEval_injective (by intro v; simp)
  right_inv x := by
    apply RestrictedProduct.ext
    intro v
    exact quaternionEval_from x v
  map_mul' x y := by
    apply RestrictedProduct.ext
    intro v
    exact map_mul (quaternionEval v) x y
  map_add' x y := by
    apply RestrictedProduct.ext
    intro v
    exact map_add (quaternionEval v) x y

/-- Units inherit the checked restricted-product comparison. -/
def unitEquiv : BAˣ ≃* UnitRP :=
  (Units.mapEquiv quaternionEquiv.toMulEquiv).trans
    (RestrictedProduct.unitsEquiv (fun v : Place => Bv v))

/-- Actual finite ideles, with integrality of both value and inverse almost everywhere. -/
def ideleEquiv : Afˣ ≃* IdeleRP :=
  (Units.mapEquiv scalarEquiv.toMulEquiv).trans
    (RestrictedProduct.unitsEquiv (fun v : Place => Qv v))

/-- Evaluation on local units is a group homomorphism. -/
def unitEval (v : Place) : BAˣ →* (Bv v)ˣ := Units.map (quaternionEval v).toMonoidHom

theorem unitEval_val (u : BAˣ) (v : Place) :
    ((unitEval v u : (Bv v)ˣ) : Bv v) = quaternionEval v (u : BA) := rfl

@[simp] theorem unitEquiv_apply (u : BAˣ) (v : Place) :
    unitEquiv u v = unitEval v u := rfl

/-- The completed order corresponds to the full product of local orders. -/
theorem mem_completedOrder (x : BA) :
    x ∈ completedOrder ↔ ∀ v, quaternionEquiv x v ∈ localOrder (primeAt v).1 := Iff.rfl

/-- The actual adelic order units are exactly the componentwise local order units. -/
theorem mem_K0 (u : BAˣ) :
    u ∈ K0 ↔ ∀ v, unitEquiv u v ∈ localOrderUnits (primeAt v).1 := by
  change ((∀ v, quaternionEval v (u : BA) ∈ localOrder (primeAt v).1) ∧
    ∀ v, quaternionEval v ((u⁻¹ : BAˣ) : BA) ∈ localOrder (primeAt v).1) ↔
    ∀ v, quaternionEval v (u : BA) ∈ localOrder (primeAt v).1 ∧
      quaternionEval v ((u⁻¹ : BAˣ) : BA) ∈ localOrder (primeAt v).1
  exact forall_and.symm

/-- Conjugation normalizer of the actual completed order inside actual adelic units. -/
def N : Subgroup BAˣ where
  carrier := {u | ∀ x : BA, x ∈ completedOrder ↔
    (u : BA) * x * ((u⁻¹ : BAˣ) : BA) ∈ completedOrder}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb x
    calc
      x ∈ completedOrder ↔ (b : BA) * x * ((b⁻¹ : BAˣ) : BA) ∈ completedOrder := hb x
      _ ↔ (a : BA) * ((b : BA) * x * ((b⁻¹ : BAˣ) : BA)) *
          ((a⁻¹ : BAˣ) : BA) ∈ completedOrder := ha _
      _ ↔ ((a * b : BAˣ) : BA) * x * (((a * b)⁻¹ : BAˣ) : BA) ∈ completedOrder := by
        simp [mul_assoc]
  inv_mem' := by
    intro a ha x
    have h := ha (((a⁻¹ : BAˣ) : BA) * x * (a : BA))
    simpa [mul_assoc] using h.symm

/-- A single-place quaternion, constructed in the actual adelic algebra. -/
def singlePlace (v : Place) (x : Bv v) : BA :=
  letI := Classical.decEq Place
  quaternionEquiv.symm (RestrictedProduct.single (fun w => localOrder (primeAt w).1) v x)

@[simp] theorem singlePlace_same (v : Place) (x : Bv v) :
    quaternionEval v (singlePlace v x) = x := by
  classical
  change quaternionEquiv (quaternionEquiv.symm _) v = x
  simp [singlePlace, RestrictedProduct.single_eq_same]

theorem singlePlace_mem (v : Place) {x : Bv v} (hx : x ∈ localOrder (primeAt v).1) :
    singlePlace v x ∈ completedOrder := by
  classical
  intro w
  change quaternionEquiv (quaternionEquiv.symm _) w ∈ _
  rw [quaternionEquiv.apply_symm_apply]
  by_cases hw : w = v
  · subst w
    simpa [RestrictedProduct.single_eq_same] using hx
  · simp [RestrictedProduct.single_eq_of_ne _ _ hw]

/-- Testing a single-place element gives the forward local conjugation condition. -/
theorem local_conjugation_of_mem_N {u : BAˣ} (hu : u ∈ N) (v : Place)
    (y : Bv v) (hy : y ∈ localOrder (primeAt v).1) :
    (unitEval v u : Bv v) * y * ((unitEval v u)⁻¹ : (Bv v)ˣ) ∈
      localOrder (primeAt v).1 := by
  have h := (hu (singlePlace v y)).1 (singlePlace_mem v hy)
  simpa only [map_mul, singlePlace_same, ← unitEval_val, map_inv] using h v

/-- Componentwise characterization of the actual normalizer.  The forward
implication tests every local order element using `singlePlace`. -/
theorem mem_N (u : BAˣ) :
    u ∈ N ↔ ∀ v, unitEval v u ∈ localNormalizer (primeAt v).1 := by
  constructor
  · intro hu v y
    constructor
    · exact local_conjugation_of_mem_N hu v y
    · intro hy
      have h := local_conjugation_of_mem_N (N.inv_mem hu) v
        ((unitEval v u : Bv v) * y * ((unitEval v u)⁻¹ : (Bv v)ˣ)) hy
      simpa [map_inv, mul_assoc] using h
  · intro hu x
    change (∀ v, quaternionEval v x ∈ localOrder (primeAt v).1) ↔ _
    change _ ↔ ∀ v, quaternionEval v ((u : BA) * x * ((u⁻¹ : BAˣ) : BA)) ∈
      localOrder (primeAt v).1
    simp only [map_mul, ← unitEval_val, map_inv]
    exact forall_congr' fun v => hu v (quaternionEval v x)

end

end G1
