import ZInQKernel.Contrib.OneProof.RC.LocalWeights.DivisionAmbient
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Dyadic

/-! Uniform congruence bounds including outside the support, tex 8563–8564.
The passage from reduction in the order to translation in the ambient space is
provenance (c). -/

namespace ZInQ.Manuscript.RC.LocalWeights

open Matrix

/-- Zero extension preserves a period if translation in both directions
preserves the chart. -/
theorem extendWeight_period {X A O : Type*} [AddGroup X] [Zero O]
    (i : A → X) (hi : Function.Injective i) (f : A → O) (δ : X)
    (add sub : A → A) (hadd : ∀ a, i (add a) = i a + δ)
    (hsub : ∀ a, i (sub a) = i a - δ)
    (hf : ∀ a, f (add a) = f a) (x : X) :
    extendWeight i f (x + δ) = extendWeight i f x := by
  have hs := extendWeight_spec i f hi
  by_cases hx : x ∈ Set.range i
  · obtain ⟨a, rfl⟩ := hx
    rw [← hadd, hs.1, hs.1, hf]
  · have hh : x + δ ∉ Set.range i := by
      rintro ⟨a, ha⟩
      exact hx ⟨sub a, by rw [hsub, ha, add_sub_cancel_right]⟩
    rw [hs.2 _ hh, hs.2 _ hx]

variable {p : ℕ} [Fact p.Prime]

private noncomputable def zeroMat : AddSubgroup (Mat ℚ_[p]) where
  carrier := {x | x.trace = 0}
  zero_mem' := Matrix.trace_zero (Fin 2) ℚ_[p]
  add_mem' := fun {x y} hx hy => by
    change x.trace = 0 at hx
    change y.trace = 0 at hy
    change (x + y).trace = 0
    rw [Matrix.trace_add, hx, hy, add_zero]
  neg_mem' := fun {x} hx => by
    change x.trace = 0 at hx
    change (-x).trace = 0
    rw [Matrix.trace_neg, hx, neg_zero]

/-- The period for the nilpotent weight is the trace-zero lattice modulo
(p^2), including when the argument itself is nonintegral. -/
theorem nilSchwartz_period {O : Type*} [Ring O] (a : TraceZero ℤ_[p])
    (ha : redMat p 2 a.val = 0) (x : TraceZero ℚ_[p]) :
    nilSchwartz p (⟨x.val + integralMat p a.val,
      by rw [Matrix.trace_add, x.property, integralMat_trace, a.property,
        PadicInt.coe_zero, add_zero]⟩) = (nilSchwartz p x : O) := by
  let plus (y : TraceZero ℤ_[p]) : TraceZero ℤ_[p] :=
    ⟨y.val + a.val, by rw [Matrix.trace_add, y.property, a.property, add_zero]⟩
  let minus (y : TraceZero ℤ_[p]) : TraceZero ℤ_[p] :=
    ⟨y.val - a.val, by rw [Matrix.trace_sub, y.property, a.property, sub_zero]⟩
  change extendWeight (integralZero p) (nilWeight p)
    ((show zeroMat (p := p) from x) + (show zeroMat (p := p) from integralZero p a)) = _
  refine extendWeight_period (X := zeroMat (p := p)) _ (integralZero_openEmbedding p).injective
    _ (integralZero p a) plus minus ?_ ?_ ?_ x
  · intro y
    apply Subtype.ext
    exact map_add (integralMat p) y.val a.val
  · intro y
    apply Subtype.ext
    exact map_sub (integralMat p) y.val a.val
  · intro y
    apply nilWeight_congr
    change redMat p 2 (y.val + a.val) = _
    rw [map_add, ha, add_zero]

/-- Fixed precision on the affine chart is an ambient period: adding twice
a trace-zero order element congruent to zero modulo (p^k) leaves the
zero-extended weight unchanged. -/
theorem affineSchwartz_period {O : Type*} [Zero O] {e k : ℕ} (f : AffineOrder p e → O)
    (hf : ∀ y z, redMat p k y.val.val = redMat p k z.val.val → f y = f z)
    (a : eichler p e) (hta : a.val.trace = 0) (ha : redMat p k a.val = 0)
    (x : TraceZero ℚ_[p]) :
    extendWeight (affineZero p) f (⟨x.val + (2 : ℚ_[p]) • integralMat p a.val,
      by rw [Matrix.trace_add, x.property, Matrix.trace_smul, integralMat_trace,
        hta, PadicInt.coe_zero, smul_zero, add_zero]⟩) =
      extendWeight (affineZero p) f x := by
  let plus (y : AffineOrder p e) : AffineOrder p e :=
    ⟨y.val + a, by change (y.val.val + a.val).trace = 1
                   rw [Matrix.trace_add, y.property, hta, add_zero]⟩
  let minus (y : AffineOrder p e) : AffineOrder p e :=
    ⟨y.val - a, by change (y.val.val - a.val).trace = 1
                   rw [Matrix.trace_sub, y.property, hta, sub_zero]⟩
  let δ : zeroMat (p := p) := ⟨(2 : ℚ_[p]) • integralMat p a.val,
    by change ((2 : ℚ_[p]) • integralMat p a.val).trace = 0
       rw [Matrix.trace_smul, integralMat_trace, hta, PadicInt.coe_zero, smul_zero]⟩
  change extendWeight (affineZero p) f ((show zeroMat (p := p) from x) + δ) = _
  refine extendWeight_period (X := zeroMat (p := p)) _ (affineZero_openEmbedding p e).injective
    _ δ plus minus ?_ ?_ ?_ x
  · intro y
    apply Subtype.ext
    change (2 : ℚ_[p]) • integralMat p (y.val.val + a.val) - 1 =
      (2 : ℚ_[p]) • integralMat p y.val.val - 1 + (2 : ℚ_[p]) • integralMat p a.val
    rw [map_add, smul_add]
    abel
  · intro y
    apply Subtype.ext
    change (2 : ℚ_[p]) • integralMat p (y.val.val - a.val) - 1 =
      (2 : ℚ_[p]) • integralMat p y.val.val - 1 - (2 : ℚ_[p]) • integralMat p a.val
    rw [map_sub, smul_sub]
    abel
  · intro y
    apply hf
    change redMat p k (y.val.val + a.val) = _
    rw [map_add, ha, add_zero]

/-- A finite-level character gives the congruence hypothesis for the ambient
period lemma. -/
theorem levelSchwartz_chart_congr {O : Type*} [CommRing O] {e k : ℕ} (he : 0 < e) (hk : 0 < k)
    (χ : (ZMod (p ^ k))ˣ →* Oˣ) (y z : AffineOrder p e)
    (h : redMat p k y.val.val = redMat p k z.val.val) :
    levelSchwartz p (e := e) χ (affineZero p y) = levelSchwartz p (e := e) χ (affineZero p z) := by
  unfold levelSchwartz
  rw [(extendWeight_spec _ _ (affineZero_openEmbedding p e).injective).1,
    (extendWeight_spec _ _ (affineZero_openEmbedding p e).injective).1]
  exact levelWeight_congr he hk χ y.property z.property h

namespace DivisionCoordinates

variable {D : Type*} [DivisionRing D] [Algebra ℚ_[p] D] [Algebra ℤ_[p] D] [TopologicalSpace D]
variable (C : DivisionCoordinates p D)

/-- Every multiple of the scalar (p) in the order is zero in the residue field. -/
theorem red_prime_mul (a : C.order) :
    C.red (algebraMap ℤ_[p] C.order (p : ℤ_[p]) * a) = 0 := by
  rw [map_mul, C.red_scalar, map_natCast, ZMod.natCast_self, map_zero, zero_mul]

private noncomputable def traceZeroAddGroup : AddSubgroup D := (C.tr : D →+ ℚ_[p]).ker

/-- The division weight is periodic by trace-zero order elements reducing to
zero, so scalar (p)-precision in the integral coordinates suffices. -/
theorem divisionSchwartz_period {O : Type*} [Ring O] (a : C.IntegralZero)
    (ha : C.red a.val = 0) (x : C.RationalZero) :
    C.divisionSchwartz (⟨x.val + a.val.val, by rw [map_add, x.property, a.property, add_zero]⟩) =
      (C.divisionSchwartz x : O) := by
  let plus (y : C.IntegralZero) : C.IntegralZero :=
    ⟨y.val + a.val, by change C.tr (y.val.val + a.val.val) = 0
                       rw [map_add, y.property, a.property, add_zero]⟩
  let minus (y : C.IntegralZero) : C.IntegralZero :=
    ⟨y.val - a.val, by change C.tr (y.val.val - a.val.val) = 0
                       rw [map_sub, y.property, a.property, sub_zero]⟩
  change extendWeight C.zeroInclusion (fun y : C.IntegralZero => C.divisionWeight y.val)
    ((show C.traceZeroAddGroup from x) + (show C.traceZeroAddGroup from C.zeroInclusion a)) = _
  refine extendWeight_period (X := C.traceZeroAddGroup) _ C.zeroInclusion_openEmbedding.injective
    _ (C.zeroInclusion a) plus minus (fun _ => rfl) (fun _ => rfl) ?_ x
  intro y
  change C.residueWeight (C.red (y.val + a.val)) = _
  rw [map_add, ha, add_zero]
  rfl

end DivisionCoordinates

end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights
#print axioms extendWeight_period
#print axioms nilSchwartz_period
#print axioms affineSchwartz_period
#print axioms levelSchwartz_chart_congr
#print axioms DivisionCoordinates.red_prime_mul
#print axioms DivisionCoordinates.divisionSchwartz_period
