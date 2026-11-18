import ZInQKernel.Contrib.OneProof.RC.DivisionJoin.Order
import ZInQKernel.Contrib.OneProof.RC.LocalDivision.Model

/-!
# The detecting-prime identification and weight

The assembled identification uses the explicit completed global order. Pulling the
weight back along it is on-the-spot (c), for tex 8551–8561.
-/

namespace ZInQ.Manuscript.RC.DivisionJoin

open Eichler LocalDivision LocalWeights

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- The exact detecting-prime join, including the two reduced invariants. -/
noncomputable def identification :
    DivisionIdentification (coordinates p) (completedOrder p Fact.out) (LocalB p)
      (completedOrder p Fact.out).val.toRingHom (reducedTrace p) (reducedNorm p) where
  order := orderEquiv p Fact.out
  ambient := ambientEquiv p
  compatible := order_compatible p Fact.out
  trace := ambient_trace p
  norm := ambient_norm p

/-- Residue in the detecting-prime field, computed in the completed explicit order. -/
noncomputable def reduction : completedOrder p Fact.out →+* GaloisField p 2 :=
  (coordinates p).red.comp (identification p).order.toRingHom

/-- The detecting-prime weight on the completed explicit order. -/
noncomputable def weight {O : Type*} [Ring O] (x : completedOrder p Fact.out) : O :=
  (coordinates p).divisionWeight ((identification p).order x)

/-- Inverse conjugation by the division uniformizer, on the completed explicit order. -/
noncomputable def uniformizerAction :
    completedOrder p Fact.out ≃+* completedOrder p Fact.out :=
  let e := (identification p).order.toRingEquiv
  (e.trans uniformizerOrder).trans e.symm

private theorem trace_transferred (x : completedOrder p Fact.out) :
    tr ((identification p).order x).val = reducedTrace p x.val := by
  rw [← (identification p).compatible x]
  exact (identification p).trace x.val

variable {O : Type*} [Ring O]

theorem divisionWeight_eq (x : completedOrder p Fact.out) (t : ZMod p)
    (hx : reduction p x = algebraMap (ZMod p) (GaloisField p 2) t * beta) :
    (weight p x : O) = (quadraticChar (ZMod p) t : O) :=
  LocalDivision.divisionWeight_eq ((identification p).order x) t hx

theorem divisionWeight_nonzero_iff [Nontrivial O] (x : completedOrder p Fact.out)
    (hx : reducedTrace p x.val = 0) :
    (weight p x : O) ≠ 0 ↔ reduction p x ≠ 0 :=
  LocalDivision.divisionWeight_nonzero_iff _ ((trace_transferred p x).trans hx)

theorem divisionWeight_conj (u : (completedOrder p Fact.out)ˣ) (x : completedOrder p Fact.out) :
    weight p ((↑u⁻¹ : completedOrder p Fact.out) * x * (u : completedOrder p Fact.out)) =
      (weight p x : O) := by
  let e := (identification p).order
  let eu := Units.map e.toMonoidHom u
  change (coordinates p).divisionWeight (e (_ * x * _)) = _
  rw [map_mul, map_mul]
  exact LocalDivision.divisionWeight_conj eu (e x)

theorem divisionWeight_scale (x : completedOrder p Fact.out)
    (hx : reducedTrace p x.val = 0) (v : ℤ_[p]ˣ) :
    weight p (algebraMap ℤ_[p] (completedOrder p Fact.out) v.val * x) =
      (quadraticChar (ZMod p) (PadicInt.toZMod v.val) : O) * weight p x := by
  let e := (identification p).order
  change (coordinates p).divisionWeight (e (_ * x)) = _
  rw [map_mul, e.commutes]
  exact LocalDivision.divisionWeight_scale (e x) ((trace_transferred p x).trans hx) v

theorem divisionWeight_uniformizer (x : completedOrder p Fact.out)
    (hx : reducedTrace p x.val = 0) :
    weight p (uniformizerAction p x) = -(weight p x : O) := by
  let e : completedOrder p Fact.out ≃ₐ[ℤ_[p]] LocalDivision.order p := (identification p).order
  let y := uniformizerOrder (e x)
  change (coordinates p).divisionWeight (e (e.symm y)) = _
  exact (congrArg (fun z : LocalDivision.order p => ((coordinates p).divisionWeight z : O))
    (e.apply_symm_apply y)).trans
    (LocalDivision.divisionWeight_uniformizer (e x) ((trace_transferred p x).trans hx))

/-- A nonzero residue on the trace-zero line gives a nonzero square norm residue. -/
theorem norm_residue_nonzero_square (x : completedOrder p Fact.out)
    (hx : reducedTrace p x.val = 0) (hr : reduction p x ≠ 0) :
    ∃ (n : ℤ_[p]) (t : ZMod p), (n : ℚ_[p]) = reducedNorm p x.val ∧
      t ≠ 0 ∧ PadicInt.toZMod n = t ^ 2 := by
  let y := (identification p).order x
  obtain ⟨t, ht, hs⟩ := LocalDivision.norm_residue_nonzero_square y
    ((trace_transferred p x).trans hx) hr
  refine ⟨integralNorm y, t, ?_, ht, hs⟩
  change nrd y.val = reducedNorm p x.val
  rw [← (identification p).compatible x]
  exact (identification p).norm x.val

#print axioms identification
#print axioms reduction
#print axioms weight
#print axioms uniformizerAction
#print axioms trace_transferred
#print axioms divisionWeight_eq
#print axioms divisionWeight_nonzero_iff
#print axioms divisionWeight_conj
#print axioms divisionWeight_scale
#print axioms divisionWeight_uniformizer
#print axioms norm_residue_nonzero_square

end ZInQ.Manuscript.RC.DivisionJoin
