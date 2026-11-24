import ZInQKernel.Contrib.OneProof.CMjBridgesArithmetic
import ZInQKernel.Contrib.OneProof.CMjBridgesPeriods

namespace HDec.CMBranch.CMjBridges

open scoped UpperHalfPlane

/-- **Open glue: field of definition of the analytic j-value.**
For a CM elliptic curve as a scheme over a number field `L`, the modular
`j(τ)` of a period of `E(ℂ)_σ` belongs to `σ(L)`. The usual proof compares
the period's lattice j with the j of a Weierstrass model of that very scheme
over `L` (then uses `weierstrass_j_map`). For the bound only this membership
is needed; no normal-form construction, canonical j function, or choice of
model is part of the statement. This is a scope marker, not a published leaf. -/
def CMPeriodJDescends : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (E : ZInQ.DefFaltings.AbVar L), E.dim = 1 →
    ∀ (k : Type) [Field k] [NumberField k] (R : Subring k),
      IsImagQuadOrder k R → IsCMBy E k R →
      ∀ (σ : L →+* ℂ) (τ : ℍ), IsPeriodAt (LeafAdopt.abVarEquiv L E) σ τ →
        modularJ τ ∈ Set.range σ

/-- Once the field of definition comparison is proved, Fowler's equality is
the only input needed for the live row. This theorem records the dependency
explicitly and does not supply an unconditional discharge. -/
theorem cmjDegree_of_print_of_periodJDescends (hDesc : CMPeriodJDescends) :
    CMjDegreePrint → CMjDegree := by
  intro hPrint L _ _ E hE k _ _ R hR hCM
  let σ : L →+* ℂ := Classical.choice inferInstance
  obtain ⟨τ, hPeriod, hDisc⟩ := exists_cm_period E hE R hR hCM σ
  exact card_pic_le_of_singular_modulus hPrint σ R hR
    (hDesc L E hE k R hR hCM σ τ hPeriod) ⟨τ, rfl, hDisc⟩

end HDec.CMBranch.CMjBridges
