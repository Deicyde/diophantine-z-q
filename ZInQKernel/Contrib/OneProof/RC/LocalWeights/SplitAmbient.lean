import ZInQKernel.Contrib.OneProof.RC.LocalWeights.LevelRules
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.NilpotentRules
import Mathlib.Topology.LocalAtTarget

/-!
# The compact open lattices in the split ambient trace-zero spaces

The weights on the lattices are extended by zero (tex 8496, 8563–8566).
At a level prime the lattice is the affine image (x=2y-1) of the trace-one
part of the Eichler order. The topology in these coordinates is provenance (c).
-/

namespace ZInQ.Manuscript.RC.LocalWeights

open Matrix Topology Set

variable (p : ℕ) [Fact p.Prime]

/-- In the split identification, trace and norm are matrix trace and determinant.
At positive level the cyclic quotient is the specified quotient of the column
lattice, in the coordinate supplied by the sibling. -/
structure SplitIdentification (e : ℕ) (R B : Type*) [Ring R] [Ring B]
    [Algebra ℤ_[p] R] [Algebra ℚ_[p] B] (incl : R →+* B)
    (tr nrd : B → ℚ_[p]) (quotientAction : R →+* ZMod (p ^ e))
    extends SplitCoordinates p e R B incl where
  trace : ∀ x, (ambient x).trace = tr x
  norm : ∀ x, (ambient x).det = nrd x
  quotient : ∀ x, level p e (order x) = quotientAction x

/-- Restricting an open embedding to the preimage of a subspace gives an open embedding. -/
theorem openEmbedding_restrictPreimage {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {i : A → B} (hi : IsOpenEmbedding i) (s : Set B) :
    IsOpenEmbedding (s.restrictPreimage i) :=
  .of_isEmbedding_isOpenMap (hi.isEmbedding.restrictPreimage s)
    (hi.isOpenMap.restrictPreimage s)

/-- The coefficient inclusion from the integral matrices. -/
noncomputable def integralMat : Mat ℤ_[p] →+* Mat ℚ_[p] :=
  (PadicInt.Coe.ringHom (p := p)).mapMatrix

theorem integralMat_openEmbedding : IsOpenEmbedding (integralMat p) :=
  PadicInt.isOpenEmbedding_coe.matrix_map

theorem integralMat_trace (x : Mat ℤ_[p]) : (integralMat p x).trace = (x.trace : ℚ_[p]) := by
  simp only [Matrix.trace_fin_two, PadicInt.coe_add]
  rfl

/-- The trace-zero inclusion of the full split order into the rational space. -/
noncomputable def integralZero (x : TraceZero ℤ_[p]) : TraceZero ℚ_[p] :=
  ⟨integralMat p x.val, by rw [integralMat_trace, x.property, PadicInt.coe_zero]⟩

theorem integralZero_openEmbedding : IsOpenEmbedding (integralZero p) := by
  let S : Set (Mat ℚ_[p]) := {x | x.trace = 0}
  have h := openEmbedding_restrictPreimage (integralMat_openEmbedding p) S
  let E : TraceZero ℤ_[p] ≃ₜ (integralMat p ⁻¹' S) :=
    Homeomorph.setCongr (by
      ext x
      change x.trace = 0 ↔ (integralMat p x).trace = 0
      rw [integralMat_trace, PadicInt.coe_eq_zero])
  exact h.comp E.isOpenEmbedding

theorem traceZero_compactSpace : CompactSpace (TraceZero ℤ_[p]) := by
  have ht : Continuous (fun x : Mat ℤ_[p] => x.trace) := by
    simp only [Matrix.trace_fin_two]
    exact (continuous_apply_apply 0 0).add (continuous_apply_apply 1 1)
  exact isCompact_iff_compactSpace.mp (isClosed_singleton.preimage ht).isCompact

/-- The weight at (p∣m) on the rational trace-zero space. -/
noncomputable def nilSchwartz {O : Type*} [Ring O] : TraceZero ℚ_[p] → O :=
  extendWeight (integralZero p) (nilWeight p)

theorem nilSchwartz_compactOpen {O : Type*} [Ring O] :
    IsLocallyConstant (nilSchwartz p : TraceZero ℚ_[p] → O) ∧
      IsCompact (Function.support (nilSchwartz p : TraceZero ℚ_[p] → O)) ∧
      IsOpen (Function.support (nilSchwartz p : TraceZero ℚ_[p] → O)) := by
  have := traceZero_compactSpace p
  exact extendWeight_compactOpen (integralZero_openEmbedding p) nilWeight_compactOpen.1

/-- The Eichler order has compact open image in the ambient matrix algebra. -/
theorem eichler_openEmbedding (e : ℕ) :
    IsOpenEmbedding (fun y : eichler p e => integralMat p y.val) := by
  have ho : IsOpen (eichler p e : Set (Mat ℤ_[p])) := by
    have hs : (eichler p e : Set (Mat ℤ_[p])) = (fun x : Mat ℤ_[p] => x 1 0) ⁻¹'
        {a : ℤ_[p] | PadicInt.toZModPow e a = 0} := by
      ext x
      change (p : ℤ_[p]) ^ e ∣ x 1 0 ↔ PadicInt.toZModPow e (x 1 0) = 0
      simpa only [map_zero, sub_zero] using (red_eq_iff p e (x 1 0) 0).symm
    rw [hs]
    exact ((red_locallyConstant p e).isOpen_fiber 0).preimage (continuous_apply_apply 1 0)
  exact (integralMat_openEmbedding p).comp ho.isOpenEmbedding_subtypeVal

theorem eichler_compactSpace (e : ℕ) : CompactSpace (eichler p e) := by
  have hc : IsClosed (eichler p e : Set (Mat ℤ_[p])) := by
    have hs : (eichler p e : Set (Mat ℤ_[p])) = (fun x : Mat ℤ_[p] => x 1 0) ⁻¹'
        {a : ℤ_[p] | PadicInt.toZModPow e a = 0} := by
      ext x
      change (p : ℤ_[p]) ^ e ∣ x 1 0 ↔ PadicInt.toZModPow e (x 1 0) = 0
      simpa only [map_zero, sub_zero] using (red_eq_iff p e (x 1 0) 0).symm
    rw [hs]
    exact ((red_locallyConstant p e).isClosed_fiber 0).preimage (continuous_apply_apply 1 0)
  exact isCompact_iff_compactSpace.mp hc.isCompact

/-- Coordinate (x=2y-1) in the rational split algebra. -/
noncomputable def affineInclusion {e : ℕ} (y : eichler p e) : Mat ℚ_[p] :=
  (2 : ℚ_[p]) • integralMat p y.val - 1

/-- The trace-one restriction is exactly the preimage of trace zero. -/
theorem affineInclusion_trace_iff {e : ℕ} (y : eichler p e) :
    (affineInclusion p y).trace = 0 ↔ y.val.trace = 1 := by
  rw [affineInclusion, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, integralMat_trace,
    Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat]
  rw [sub_eq_zero]
  constructor
  · intro h
    have h' : (2 : ℚ_[p]) * (y.val.trace : ℚ_[p]) = 2 * 1 := h.trans (mul_one _).symm
    have ht := mul_left_cancel₀ (by norm_num : (2 : ℚ_[p]) ≠ 0) h'
    exact PadicInt.coe_inj.mp ht
  · intro h
    rw [h, PadicInt.coe_one, mul_one]

abbrev AffineOrder (e : ℕ) := {y : eichler p e // y.val.trace = 1}

noncomputable def affineZero {e : ℕ} (y : AffineOrder p e) : TraceZero ℚ_[p] :=
  ⟨affineInclusion p y.val, (affineInclusion_trace_iff p y.val).mpr y.property⟩

theorem affineZero_openEmbedding (e : ℕ) : IsOpenEmbedding (affineZero p (e := e)) := by
  let S : Set (Mat ℚ_[p]) := {x | x.trace = 0}
  have hl : IsOpenEmbedding (affineInclusion p (e := e)) := by
    let H := (Homeomorph.smulOfNeZero (α := Mat ℚ_[p]) (2 : ℚ_[p])
      (by norm_num)).trans (Homeomorph.addRight (-1 : Mat ℚ_[p]))
    have hh : affineInclusion p (e := e) = H ∘ fun y : eichler p e => integralMat p y.val := by
      funext y
      change (2 : ℚ_[p]) • integralMat p y.val - 1 = (2 : ℚ_[p]) • integralMat p y.val + -1
      rw [sub_eq_add_neg]
    rw [hh]
    exact H.isOpenEmbedding.comp (eichler_openEmbedding p e)
  let E : AffineOrder p e ≃ₜ (affineInclusion p ⁻¹' S) :=
    Homeomorph.setCongr (by
      ext y
      exact (affineInclusion_trace_iff p y).symm)
  exact (openEmbedding_restrictPreimage hl S).comp E.isOpenEmbedding

theorem affineOrder_compactSpace (e : ℕ) : CompactSpace (AffineOrder p e) := by
  have := eichler_compactSpace p e
  have ht : Continuous (fun x : Mat ℤ_[p] => x.trace) := by
    simp only [Matrix.trace_fin_two]
    exact (continuous_apply_apply 0 0).add (continuous_apply_apply 1 1)
  exact isCompact_iff_compactSpace.mp (isClosed_singleton.preimage
    (ht.comp (continuous_subtype_val : Continuous (Subtype.val : eichler p e → Mat ℤ_[p])))).isCompact

/-- The positive-level Schwartz weight (odd or dyadic) in the ambient local space. -/
noncomputable def levelSchwartz {O : Type*} [CommRing O] {e k : ℕ}
    (χ : (ZMod (p ^ k))ˣ →* Oˣ) : TraceZero ℚ_[p] → O :=
  extendWeight (affineZero p (e := e)) fun y =>
    levelWeight (χ.comp (Units.map (PadicInt.toZModPow k : ℤ_[p] →+* _).toMonoidHom)) y.val

theorem levelSchwartz_compactOpen {O : Type*} [CommRing O] {e k : ℕ}
    (he : 0 < e) (hk : 0 < k) (χ : (ZMod (p ^ k))ˣ →* Oˣ) :
    IsLocallyConstant (levelSchwartz p (e := e) χ) ∧
      IsCompact (Function.support (levelSchwartz p (e := e) χ)) ∧
      IsOpen (Function.support (levelSchwartz p (e := e) χ)) := by
  have := affineOrder_compactSpace p e
  exact extendWeight_compactOpen (affineZero_openEmbedding p e) (levelWeight_locallyConstant he hk χ)

end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights
#print axioms openEmbedding_restrictPreimage
#print axioms integralMat_openEmbedding
#print axioms integralMat_trace
#print axioms integralZero_openEmbedding
#print axioms traceZero_compactSpace
#print axioms nilSchwartz_compactOpen
#print axioms eichler_openEmbedding
#print axioms eichler_compactSpace
#print axioms affineInclusion_trace_iff
#print axioms affineZero_openEmbedding
#print axioms affineOrder_compactSpace
#print axioms levelSchwartz_compactOpen
