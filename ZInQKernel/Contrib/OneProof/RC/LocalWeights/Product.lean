import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Models
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! The finite product in tex 8571–8577. It may be evaluated on the local coordinates
of a global vector. No adelic class set or lattice at a class is used. -/

namespace ZInQ.Manuscript.RC.LocalWeights

variable {O : Type*} [CommRing O]

/-- The ramified quadratic character on local units at (p∣m).
The local norm character is trivial at the other primes. -/
noncomputable def legendreUnit (p : ℕ) [Fact p.Prime] : ℤ_[p]ˣ →* Oˣ :=
  ((Units.map (Int.castRingHom O).toMonoidHom).comp (quadraticChar (ZMod p)).toUnitHom).comp
    (Units.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p).toMonoidHom)

theorem legendreUnit_apply (p : ℕ) [Fact p.Prime] (v : ℤ_[p]ˣ) :
    ((legendreUnit (O := O) p v : Oˣ) : O) =
      (quadraticChar (ZMod p) (PadicInt.toZMod v.val) : ℤ) := rfl

theorem legendreUnit_inv (p : ℕ) [Fact p.Prime] (v : ℤ_[p]ˣ) :
    (legendreUnit (O := O) p v)⁻¹ = legendreUnit p v := by
  let a := (quadraticChar (ZMod p)).toUnitHom
    (Units.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p).toMonoidHom v)
  have ha : a⁻¹ = a := by
    have hsq : a * a = 1 := by
      apply Units.ext
      change (a.val : ℤ) * a.val = 1
      rcases Int.isUnit_iff.mp a.isUnit with h | h <;> rw [h] <;> decide
    exact inv_eq_of_mul_eq_one_right hsq
  change ((Units.map (Int.castRingHom O).toMonoidHom) a)⁻¹ = _
  rw [← map_inv, ha]
  rfl

/-- Local rules on an ambient trace-zero model. The norm of an order unit
lands in the local integer unit group. `normChar` is the local factor of
the restriction of `χ_{h_*}` to units. -/
structure LocalRule (X G V : Type*) [Monoid G] [Monoid V] where
  weight : X → O
  conj : G → X → X
  scale : V → X → X
  norm : G →* V
  normChar : V →* Oˣ
  alpha : V →* Oˣ
  weight_conj : ∀ u x,
    weight (conj u x) = (((normChar (norm u))⁻¹ : Oˣ) : O) * weight x
  weight_scale : ∀ v x, weight (scale v x) = (alpha v : O) * weight x

section Product

variable {ι : Type*} {X G V : ι → Type*} [∀ i, Monoid (G i)] [∀ i, Monoid (V i)]

/-- The product over any finite set containing the special primes, with the
characteristic functions included at every other prime in the set. -/
def finiteWeight (S : Finset ι) (W : ∀ i, LocalRule (O := O) (X i) (G i) (V i))
    (x : ∀ i, X i) : O := ∏ i ∈ S, (W i).weight (x i)

/-- The finite-idele unit restriction of the norm character, as the product
of the local factors. -/
def finiteNormChar (S : Finset ι) (W : ∀ i, LocalRule (O := O) (X i) (G i) (V i))
    (v : ∀ i, V i) : Oˣ := ∏ i ∈ S, (W i).normChar (v i)

/-- The global scaling character on the finite product of the local unit groups. -/
def finiteAlpha (S : Finset ι) (W : ∀ i, LocalRule (O := O) (X i) (G i) (V i))
    (v : ∀ i, V i) : Oˣ := ∏ i ∈ S, (W i).alpha (v i)

theorem finiteWeight_conj (S : Finset ι) (W : ∀ i, LocalRule (O := O) (X i) (G i) (V i))
    (u : ∀ i, G i) (x : ∀ i, X i) :
    finiteWeight S W (fun i => (W i).conj (u i) (x i)) =
      (((finiteNormChar S W (fun i => (W i).norm (u i)))⁻¹ : Oˣ) : O) * finiteWeight S W x := by
  simp only [finiteWeight, finiteNormChar, LocalRule.weight_conj, Finset.prod_mul_distrib,
    ]
  rw [← Finset.prod_inv_distrib, Units.coe_prod]

theorem finiteWeight_scale (S : Finset ι) (W : ∀ i, LocalRule (O := O) (X i) (G i) (V i))
    (v : ∀ i, V i) (x : ∀ i, X i) :
    finiteWeight S W (fun i => (W i).scale (v i) (x i)) =
      (finiteAlpha S W v : O) * finiteWeight S W x := by
  simp only [finiteWeight, finiteAlpha, LocalRule.weight_scale, Finset.prod_mul_distrib,
    Units.coe_prod]

end Product

end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights
#print axioms legendreUnit_apply
#print axioms legendreUnit_inv
#print axioms finiteWeight_conj
#print axioms finiteWeight_scale
