import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Parametrization
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.IdeleClass

/-! The chosen representative of a Picard label, tex 9155–9169.
The quotient computation is on-the-spot (c). -/

noncomputable section

open scoped NumberField
open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing

namespace ZInQ.Manuscript.RC.O7Residual

open Eichler Adelic O7Actual O7Orbits PicardFibers Visibility O7Assemble

section Quotient

variable {F : Type} [Field F] [NumberField F]
variable {G : Type} [Group G]
variable (L H U : Subgroup G) (hLH : L ≤ H) (z : G)
    (e : (FiniteAdeleRing (𝓞 F) F)ˣ ≃* H)
    (hr : ∀ a, (e a : G) ∈ L ↔ a ∈ (FiniteAdeleRing.unitEmbedding (𝓞 F) F).range)
    (hi : ∀ a, z⁻¹ * (e a : G) * z ∈ U ↔ a ∈ (ideleToIdeal (R := 𝓞 F) (K := F)).ker)

/-- The idele class equivalence sends the class of a representative to the
double class of its image times the base. -/
theorem ideleOrbitEquiv_toClassGroup (a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((ideleOrbitEquiv L H U hLH z e hr hi) (toClassGroup (𝓞 F) F a)).val =
      DoubleCoset.mk L U ((e a).val * z) := by
  rw [← ideleClass_mk a]
  let q : (FiniteAdeleRing (𝓞 F) F)ˣ ⧸ ideleClassSubgroup (𝓞 F) F := QuotientGroup.mk a
  have hq : (ideleClassEquiv (R := 𝓞 F) (K := F)).symm (ideleClassEquiv q) = q :=
    MulEquiv.symm_apply_apply _ _
  unfold ideleOrbitEquiv
  erw [Equiv.trans_apply]
  change _ = DoubleCoset.mk L U ((e a).val * z)
  erw [hq]
  rfl

end Quotient

section Fibre

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m D : ℤ}
    {F : Type} [Field F] [NumberField F]
    (s : StageAt O N M hN m) (A : AdmissibleD s D) (H : SupportBridge s D)
    (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)

set_option maxHeartbeats 450000 in
set_option backward.isDefEq.respectTransparency false in
/-- Remove the representative chosen by the based fibre equivalence. -/
theorem basedFiberEquiv_mk
    (x₀ : (B (-1) (-(s.ell : ℚ)))ˣ) {α : B (-1) (-(s.ell : ℚ))}
    (hα : 2 * α - 1 = x₀.val) (hx : x₀.val.re = 0) (hn : nrd x₀.val = index s D)
    (z : {z : FiniteUnits (ActualOrder s) // AdelicAdmissible α z})
    (t : Orientations N.primeFactors.card)
    (ht : orientation s H (orbitFromRep s H hα hx hn z) = t)
    (g : adelicCentralizer (ActualOrder s) (diagonal (ActualOrder s) x₀).val) :
    let q := fun g : adelicCentralizer (ActualOrder s) (diagonal (ActualOrder s) x₀).val =>
      DoubleCoset.mk (diagonalCentralizer (ActualOrder s) x₀) (integralUnits (ActualOrder s))
        (g.val * z.val)
    let b : Set.range q := ⟨q g, g, rfl⟩
    (basedFiberEquiv s A H hh x₀ hα hx hn z t ht b).val =
      orbitFromRep s H hα hx hn
        ⟨g.val * z.val, centralizer_mul_admissible _ x₀ hα g z.prop⟩ := by
  let q := fun g : adelicCentralizer (ActualOrder s) (diagonal (ActualOrder s) x₀).val =>
    DoubleCoset.mk (diagonalCentralizer (ActualOrder s) x₀) (integralUnits (ActualOrder s))
      (g.val * z.val)
  let b : Set.range q := ⟨q g, g, rfl⟩
  let Z (k : adelicCentralizer (ActualOrder s) (diagonal (ActualOrder s) x₀).val) :
      {z : FiniteUnits (ActualOrder s) // AdelicAdmissible α z} :=
    ⟨k.val * z.val, centralizer_mul_admissible _ x₀ hα k z.prop⟩
  change (basedFiberEquiv s A H hh x₀ hα hx hn z t ht b).val = _
  simp only [basedFiberEquiv, Equiv.coe_ofBijective]
  change orbitFromRep s H hα hx hn (Z b.prop.choose) = orbitFromRep s H hα hx hn (Z g)
  have he : q b.prop.choose = q g := b.prop.choose_spec
  have he' : DoubleCoset.mk (diagonalCentralizer (ActualOrder s) x₀)
      (integralUnits (ActualOrder s)) (Z b.prop.choose).val =
      DoubleCoset.mk (diagonalCentralizer (ActualOrder s) x₀)
      (integralUnits (ActualOrder s)) (Z g).val := he
  rw [DoubleCoset.eq] at he'
  obtain ⟨_, ⟨k, hk, rfl⟩, r, hr, h⟩ := he'
  exact (orbitFromRep_eq_iff s H x₀ hα hx hn _ _).mpr
    ⟨k, Subgroup.mem_centralizer_singleton_iff.mp hk, ⟨r, hr⟩, h⟩

end Fibre

end ZInQ.Manuscript.RC.O7Residual
