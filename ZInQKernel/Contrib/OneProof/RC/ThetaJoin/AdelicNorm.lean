import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.NormCharacter
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.ReducedNorm

/-! The reduced norm from the restricted adelic quaternion group to rational
idèles. The values on local order units are integral units. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic Eichler

variable {ell N : ℕ} [Fact ell.Prime] (h : ell % 4 = 3) (hN : 0 < N)

/-- The reduced norm on the ambient local multiplicative group. -/
def localNormHom (q : Prime) : (Bp q.val (-1) (-(ell : ℚ)))ˣ →* ℚ_[q.val]ˣ :=
  Units.map (reducedNorm ((-1 : ℚ) : ℚ_[q.val]) ((-(ell : ℚ)) : ℚ_[q.val]))

/-- A unit of the completed order has valuation zero under the reduced norm. -/
theorem val_localNorm_of_orderUnit (q : Prime) (u : localUnits (levelOrder ell h N hN) q) :
    valHom q (localNormHom q u.val) = 1 := by
  let v := localNormHom q u.val
  obtain ⟨x, hx⟩ := completion_norm_integral h hN q _ u.prop.1
  obtain ⟨y, hy⟩ := completion_norm_integral h hN q _ u.prop.2
  have hpos : 0 ≤ v.val.valuation := by
    change 0 ≤ ((reducedNorm _ _) u.val.val).valuation
    rw [← hx]
    exact PadicInt.valuation_coe_nonneg
  have hneg : 0 ≤ (v⁻¹).val.valuation := by
    have he : (v⁻¹).val = (localNormHom q (u.val⁻¹)).val :=
      congrArg Units.val (map_inv (localNormHom q) u.val).symm
    change (↑y : ℚ_[q.val]) = (localNormHom q (u.val⁻¹)).val at hy
    rw [he, ← hy]
    exact PadicInt.valuation_coe_nonneg
  rw [Units.val_inv_eq_inv_val, Padic.valuation_inv] at hneg
  exact le_antisymm (neg_nonneg.mp hneg) hpos

/-- Reduced norm preserves the restricted product. -/
def normIdeles : FiniteUnits (levelOrder ell h N hN) →* rationalIdeles where
  toFun z := ⟨fun q => localNormHom q (z.val q), z.prop.subset fun q hq hU =>
    hq (val_localNorm_of_orderUnit h hN q ⟨z.val q, hU⟩)⟩
  map_one' := Subtype.ext (funext fun q => map_one (localNormHom q))
  map_mul' x y := Subtype.ext (funext fun q => map_mul (localNormHom q) (x.val q) (y.val q))

/-- The product over ramified discriminant primes, pulled back by reduced norm. -/
def normCharacter {O : Type} [CommRing O] (S : Finset Prime) :
    FiniteUnits (levelOrder ell h N hN) →* Oˣ :=
  (discriminantCharacter S).comp (normIdeles h hN)

/-- The local integral norm of an order unit. -/
def normUnit (q : Prime) (u : localUnits (levelOrder ell h N hN) q) : ℤ_[q.val]ˣ :=
  integralUnit q (localNormHom q u.val) (val_localNorm_of_orderUnit h hN q u)

theorem normUnit_val (q : Prime) (u : localUnits (levelOrder ell h N hN) q) :
    ((normUnit h hN q u).val : ℚ_[q.val]) = (localNormHom q u.val).val := rfl

/-- At integral idèles the normalization removes nothing. -/
theorem normCharacter_integral {O : Type} [CommRing O] (S : Finset Prime)
    (r : integralUnits (levelOrder ell h N hN)) :
    normCharacter (O := O) h hN S r.val =
      ∏ q ∈ S, LocalWeights.legendreUnit q.val (normUnit h hN q ⟨r.val.val q, r.prop q⟩) := by
  classical
  let z := normIdeles h hN r.val
  have hz : rationalPart z = 1 :=
    rationalPart_of_units z (fun q => val_localNorm_of_orderUnit h hN q ⟨r.val.val q, r.prop q⟩)
  change (∏ q ∈ S, LocalWeights.legendreUnit q.val (localUnitPart q z)) = _
  apply Finset.prod_congr rfl
  intro q _
  congr 1
  apply Units.ext
  apply Subtype.val_injective
  rw [localUnitPart_val, hz, map_one, div_one]
  rfl

/-- The character of a definite rational reduced norm is one. -/
theorem normCharacter_diagonal {O : Type} [CommRing O] (S : Finset Prime)
    (u : (B (-1) (-(ell : ℚ)))ˣ) :
    normCharacter (O := O) h hN S (diagonal (levelOrder ell h N hN) u) = 1 := by
  let v := Units.map (reducedNorm (-1 : ℚ) (-(ell : ℚ))) u
  have hpos : 0 < v.val :=
    nrd_pos (by norm_num) (neg_lt_zero.mpr (Nat.cast_pos.mpr (Fact.out : ell.Prime).pos)) u.ne_zero
  apply discriminantCharacter_diagonal S _ v hpos
  intro q
  apply Units.ext
  exact norm_toLocal q u.val

end ZInQ.Manuscript.RC.ThetaJoin
