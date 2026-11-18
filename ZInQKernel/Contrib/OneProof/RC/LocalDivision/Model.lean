import ZInQKernel.Contrib.OneProof.RC.LocalDivision.Residue
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.DivisionAmbient

/-! The division-prime inputs and their weight rules (tex 8551–8566). -/

namespace ZInQ.Manuscript.RC.LocalDivision

open LocalWeights

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- The detecting prime coordinates in the explicit local division algebra. -/
noncomputable def coordinates : DivisionCoordinates p (D p) where
  order := order p
  tr := tr
  nrd := nrd
  red := red
  red_surj := red_surj
  red_scalar := red_scalar
  red_locallyConstant := red_locallyConstant
  order_open := order_open
  order_compact := order_compact
  beta := beta
  beta_ne_zero := beta_ne_zero
  trace_line := trace_line
  uniformizer := uniformizer
  uniformizer_order := uniformizerOrder
  uniformizer_conj := uniformizer_conj
  uniformizer_frobenius := uniformizer_frobenius
  beta_frobenius := beta_frobenius

/-- The detecting prime model, with no local algebra hypotheses left over. -/
noncomputable def localModel : DivisionLocalModel (coordinates p) where
  rank_four := rank_four
  finite_order := finite_order
  maximal_order := maximal_order
  red_nonunit := red_nonunit
  uniformizer_norm := uniformizer_norm
  tr_continuous := tr_continuous
  tr_conj := tr_conj
  norm_units := normUnits
  norm_units_eq := normUnits_eq
  scalar_compat := scalar_compat

variable {p} {O : Type*} [Ring O]

theorem divisionWeight_eq (x : order p) (t : ZMod p)
    (hx : red x = algebraMap (ZMod p) (GaloisField p 2) t * beta) :
    ((coordinates p).divisionWeight x : O) = (quadraticChar (ZMod p) t : O) := by
  change (coordinates p).residueWeight (red x) = _
  rw [hx]
  exact (coordinates p).residueWeight_eq t

theorem divisionWeight_nonzero_iff [Nontrivial O] (x : order p) (hx : tr x.val = 0) :
    ((coordinates p).divisionWeight x : O) ≠ 0 ↔ red x ≠ 0 :=
  (coordinates p).divisionWeight_nonzero_iff x hx

/-- On the stated nonzero support, the integral norm has a nonzero square residue. -/
theorem norm_residue_nonzero_square (x : order p) (hx : tr x.val = 0) (hr : red x ≠ 0) :
    ∃ t : ZMod p, t ≠ 0 ∧ PadicInt.toZMod (integralNorm x) = t ^ 2 := by
  have h : ((orderEquiv.symm x).re : ℚ_[p]) = 0 := by
    rw [tr_apply, ← includeIntegral_symm x] at hx
    exact (mul_eq_zero.mp hx).resolve_left (by norm_num)
  have h₀ : PadicInt.toZMod (orderEquiv.symm x).re = 0 := by
    rw [PadicInt.coe_eq_zero.mp h, map_zero]
  let t := PadicInt.toZMod (orderEquiv.symm x).imI
  refine ⟨t, fun ht => hr ((red_eq_zero_iff x).mpr ⟨h₀, ht⟩), ?_⟩
  rw [integralNorm_red, h₀, zero_pow (by decide : 2 ≠ 0), zero_add]

theorem divisionWeight_conj (u : (order p)ˣ) (x : order p) :
    (coordinates p).divisionWeight ((↑u⁻¹ : order p) * x * (u : order p)) =
      ((coordinates p).divisionWeight x : O) :=
  (coordinates p).divisionWeight_conj u x

theorem divisionWeight_scale (x : order p) (hx : tr x.val = 0) (v : ℤ_[p]ˣ) :
    (coordinates p).divisionWeight (algebraMap ℤ_[p] (order p) v.val * x) =
      (quadraticChar (ZMod p) (PadicInt.toZMod v.val) : O) * (coordinates p).divisionWeight x :=
  (coordinates p).divisionWeight_scale x hx v

theorem divisionWeight_uniformizer (x : order p) (hx : tr x.val = 0) :
    (coordinates p).divisionWeight (uniformizerOrder x) = -((coordinates p).divisionWeight x : O) :=
  (coordinates p).divisionWeight_uniformizer x hx Fact.out

theorem divisionSchwartz_compactOpen :
    IsLocallyConstant ((coordinates p).divisionSchwartz : (coordinates p).RationalZero → O) ∧
      IsCompact (Function.support ((coordinates p).divisionSchwartz : (coordinates p).RationalZero → O)) ∧
      IsOpen (Function.support ((coordinates p).divisionSchwartz : (coordinates p).RationalZero → O)) :=
  (coordinates p).divisionSchwartz_compactOpen (localModel p)

theorem divisionSchwartz_uniformizer (x : (coordinates p).RationalZero) :
    (coordinates p).divisionSchwartz ((coordinates p).conjZero (localModel p) uniformizer x) =
      -((coordinates p).divisionSchwartz x : O) :=
  (coordinates p).divisionSchwartz_uniformizer (localModel p) Fact.out x

/-- The ambient order-unit and scalar-unit rules specialized to the explicit model. -/
noncomputable def divisionRule (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    {A : Type*} [CommRing A] : LocalRule (O := A) (coordinates p).RationalZero (order p)ˣ ℤ_[p]ˣ :=
  (coordinates p).divisionRule (localModel p)

#print axioms coordinates
#print axioms localModel
#print axioms divisionWeight_eq
#print axioms divisionWeight_nonzero_iff
#print axioms norm_residue_nonzero_square
#print axioms divisionWeight_conj
#print axioms divisionWeight_scale
#print axioms divisionWeight_uniformizer
#print axioms divisionSchwartz_compactOpen
#print axioms divisionSchwartz_uniformizer
#print axioms divisionRule

end ZInQ.Manuscript.RC.LocalDivision
