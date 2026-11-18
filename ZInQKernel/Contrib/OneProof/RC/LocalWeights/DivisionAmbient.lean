import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Division
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.SplitAmbient
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Product
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Transport

/-! The division-prime adapter (tex 8462–8465, 8551–8556, 8563–8577).
The local algebra and maximal-order identification are interface data.
The extension to the ambient trace-zero space is provenance (c). -/

namespace ZInQ.Manuscript.RC.LocalWeights

open Topology Set

variable {p : ℕ} [Fact p.Prime]
variable {D : Type*} [DivisionRing D] [Algebra ℚ_[p] D] [Algebra ℤ_[p] D] [TopologicalSpace D]

/-- Properties of the local quaternion model used by the weights; these accompany
the division-order coordinates supplied by the order construction. -/
structure DivisionLocalModel (C : DivisionCoordinates p D) where
  rank_four : Module.finrank ℚ_[p] D = 4
  finite_order : Module.Finite ℤ_[p] C.order
  maximal_order : ∀ S : Subalgebra ℤ_[p] D, Module.Finite ℤ_[p] S →
    C.order ≤ S → S = C.order
  red_nonunit : ∀ a : C.order, C.red a = 0 ↔ ¬ IsUnit a
  uniformizer_norm : (C.nrd C.uniformizer.val).valuation = 1
  tr_continuous : Continuous C.tr
  tr_conj : ∀ (u : Dˣ) (x : D), C.tr ((↑u⁻¹ : D) * x * (u : D)) = C.tr x
  norm_units : C.orderˣ →* ℤ_[p]ˣ
  norm_units_eq : ∀ u : C.orderˣ, ((norm_units u).val : ℚ_[p]) = C.nrd u.val.val
  scalar_compat : ∀ a : ℤ_[p],
    algebraMap ℤ_[p] D a = algebraMap ℚ_[p] D (a : ℚ_[p])

/-- At the division prime, the sibling supplies the completed order and algebra
identifications preserving inclusions, reduced trace, and reduced norm. -/
structure DivisionIdentification (C : DivisionCoordinates p D) (R B : Type*) [Ring R] [Ring B]
    [Algebra ℤ_[p] R] [Algebra ℚ_[p] B] (incl : R →+* B) (tr : B → ℚ_[p]) (nrd : B → ℚ_[p]) where
  order : R ≃ₐ[ℤ_[p]] C.order
  ambient : B ≃ₐ[ℚ_[p]] D
  compatible : ∀ x, ambient (incl x) = (order x).val
  trace : ∀ x, C.tr (ambient x) = tr x
  norm : ∀ x, C.nrd (ambient x) = nrd x

namespace DivisionCoordinates

variable (C : DivisionCoordinates p D)
variable (H : DivisionLocalModel C)

abbrev RationalZero := {x : D // C.tr x = 0}

abbrev IntegralZero := {x : C.order // C.tr x.val = 0}

def zeroInclusion (x : C.IntegralZero) : C.RationalZero := ⟨x.val.val, x.property⟩

theorem zeroInclusion_openEmbedding : IsOpenEmbedding C.zeroInclusion :=
  openEmbedding_restrictPreimage C.order_open.isOpenEmbedding_subtypeVal {x : D | C.tr x = 0}

include H in
theorem integralZero_compactSpace : CompactSpace C.IntegralZero := by
  have : CompactSpace C.order := isCompact_iff_compactSpace.mp C.order_compact
  have hc : IsClosed {x : C.order | C.tr x.val = 0} :=
    isClosed_singleton.preimage (H.tr_continuous.comp
      (continuous_subtype_val : Continuous (Subtype.val : C.order → D)))
  exact isCompact_iff_compactSpace.mp hc.isCompact

/-- The (ℓ₀) weight on the rational trace-zero space. -/
noncomputable def divisionSchwartz {O : Type*} [Ring O] : C.RationalZero → O :=
  extendWeight C.zeroInclusion fun x => C.divisionWeight x.val

include H in
theorem divisionSchwartz_compactOpen {O : Type*} [Ring O] [T2Space D] :
    IsLocallyConstant (C.divisionSchwartz : C.RationalZero → O) ∧
      IsCompact (Function.support (C.divisionSchwartz : C.RationalZero → O)) ∧
      IsOpen (Function.support (C.divisionSchwartz : C.RationalZero → O)) := by
  have := C.integralZero_compactSpace H
  exact extendWeight_compactOpen C.zeroInclusion_openEmbedding
    (C.divisionWeight_locallyConstant.comp_continuous continuous_subtype_val)

def conjZero (u : Dˣ) (x : C.RationalZero) : C.RationalZero :=
  ⟨(↑u⁻¹ : D) * x.val * (u : D), (H.tr_conj u x.val).trans x.property⟩

theorem conjZero_inverse (u : Dˣ) : Function.LeftInverse (C.conjZero H u⁻¹) (C.conjZero H u) := by
  intro x
  apply Subtype.ext
  change (↑u⁻¹⁻¹ : D) * ((↑u⁻¹ : D) * x.val * (u : D)) * (↑u⁻¹ : D) = x.val
  simp only [inv_inv, mul_assoc, Units.mul_inv, mul_one,
    ← mul_assoc (u : D) (↑u⁻¹ : D) x.val, one_mul]

noncomputable def conjOrder (u : C.orderˣ) (x : C.IntegralZero) : C.IntegralZero :=
  ⟨(↑u⁻¹ : C.order) * x.val * (u : C.order),
    (H.tr_conj (Units.map C.order.val.toMonoidHom u) x.val.val).trans x.property⟩

noncomputable def scaleZero (v : ℚ_[p]ˣ) (x : C.RationalZero) : C.RationalZero :=
  ⟨v.val • x.val, by rw [map_smul, x.property, smul_zero]⟩

theorem scaleZero_inverse (v : ℚ_[p]ˣ) :
    Function.LeftInverse (C.scaleZero v⁻¹) (C.scaleZero v) := by
  intro x
  apply Subtype.ext
  change (↑v⁻¹ : ℚ_[p]) • (v.val • x.val) = x.val
  rw [smul_smul, Units.inv_mul, one_smul]

noncomputable def scaleOrder (v : ℤ_[p]ˣ) (x : C.IntegralZero) : C.IntegralZero :=
  ⟨algebraMap ℤ_[p] C.order v.val * x.val, by
    change C.tr ((algebraMap ℤ_[p] D v.val) * x.val.val) = 0
    rw [H.scalar_compat, ← Algebra.smul_def, map_smul, x.property, smul_zero]⟩

theorem scaleZero_inclusion (v : ℤ_[p]ˣ) (x : C.IntegralZero) :
    C.scaleZero (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom v) (C.zeroInclusion x) =
      C.zeroInclusion (C.scaleOrder H v x) := by
  apply Subtype.ext
  change (v.val : ℚ_[p]) • x.val.val = (algebraMap ℤ_[p] D v.val) * x.val.val
  rw [H.scalar_compat, Algebra.smul_def]

/-- Order-unit conjugation is trivial; scalar units act by the residue Legendre symbol. -/
noncomputable def divisionRule {O : Type*} [CommRing O] :
    LocalRule (O := O) C.RationalZero C.orderˣ ℤ_[p]ˣ where
  weight := C.divisionSchwartz
  conj u := C.conjZero H (Units.map C.order.val.toMonoidHom u)
  scale v := C.scaleZero (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom v)
  norm := H.norm_units
  normChar := 1
  alpha := legendreUnit p
  weight_conj u x := by
    simp only [MonoidHom.one_apply, inv_one, Units.val_one]
    exact extendWeight_transform _ C.zeroInclusion_openEmbedding.injective _ 1
      _ (C.conjOrder H u) (C.conjZero H (Units.map C.order.val.toMonoidHom u⁻¹)) (C.conjOrder H u⁻¹)
      (by rw [map_inv]; exact C.conjZero_inverse H _)
      (fun _ => rfl) (fun _ => rfl)
      (fun a => (C.divisionWeight_conj u a.val).trans (one_mul _).symm) x
  weight_scale v x := by
    rw [legendreUnit_apply]
    exact extendWeight_transform _ C.zeroInclusion_openEmbedding.injective _ _
      _ (C.scaleOrder H v)
      (C.scaleZero (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom v⁻¹)) (C.scaleOrder H v⁻¹)
      (by rw [map_inv]; exact C.scaleZero_inverse _)
      (C.scaleZero_inclusion H v) (C.scaleZero_inclusion H v⁻¹)
      (fun a => C.divisionWeight_scale a.val a.property v) x

/-- The division uniformizer acts on the full ambient weight by (-1). -/
theorem divisionSchwartz_uniformizer {O : Type*} [Ring O] (hp : p % 4 = 3)
    (x : C.RationalZero) :
    C.divisionSchwartz (C.conjZero H C.uniformizer x) = -(C.divisionSchwartz x : O) := by
  let u (a : C.IntegralZero) : C.IntegralZero :=
    ⟨C.uniformizer_order a.val, by rw [C.uniformizer_conj, H.tr_conj, a.property]⟩
  -- The inverse keeps the order because the supplied Frobenius action is induced by an order equivalence.
  let u' (a : C.IntegralZero) : C.IntegralZero :=
    ⟨C.uniformizer_order.symm a.val, by
      rw [← H.tr_conj C.uniformizer (C.uniformizer_order.symm a.val).val,
        ← C.uniformizer_conj, RingEquiv.apply_symm_apply, a.property]⟩
  have h (a : C.IntegralZero) :
      C.conjZero H C.uniformizer (C.zeroInclusion a) = C.zeroInclusion (u a) :=
    Subtype.ext (C.uniformizer_conj a.val).symm
  have h' (a : C.IntegralZero) :
      C.conjZero H C.uniformizer⁻¹ (C.zeroInclusion a) = C.zeroInclusion (u' a) := by
    have he : C.conjZero H C.uniformizer (C.zeroInclusion (u' a)) = C.zeroInclusion a := by
      rw [h]
      apply congrArg C.zeroInclusion
      exact Subtype.ext (C.uniformizer_order.apply_symm_apply a.val)
    rw [← he]
    exact C.conjZero_inverse H C.uniformizer _
  rw [← neg_one_mul]
  exact extendWeight_transform _ C.zeroInclusion_openEmbedding.injective _ (-1)
    _ u _ u' (C.conjZero_inverse H _) h h'
    (fun a => (C.divisionWeight_uniformizer a.val a.property hp).trans (neg_one_mul _).symm) x

end DivisionCoordinates
end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights
#print axioms DivisionCoordinates.zeroInclusion_openEmbedding
#print axioms DivisionCoordinates.integralZero_compactSpace
#print axioms DivisionCoordinates.divisionSchwartz_compactOpen
#print axioms DivisionCoordinates.conjZero_inverse
#print axioms DivisionCoordinates.scaleZero_inverse
#print axioms DivisionCoordinates.scaleZero_inclusion
#print axioms DivisionCoordinates.divisionRule
#print axioms DivisionCoordinates.divisionSchwartz_uniformizer
