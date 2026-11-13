
/-! ## §5 (local-data). The tail of `ModularConstituent` with G15 fed by G7/G8 (proved) -/

namespace G0ModNewform

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
open PkgI3 PkgI3.AbVar LeafModCurves C9Rhof
open CategoryTheory AlgebraicGeometry

/-- **G8's data for a representation `r` at coefficient prime `ℓ`, with the G4/G7 clauses and
the local glue at the primes `p ∈ P`** (`G15Ram.G7Clauses`, `G15Ram.LocalGlue`). -/
def G8LocalPack (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (a β : GQ → PadicAlgCl ℓ)
    (ε : GQ → GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ Qbar),
    G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧ G15Ram.G7Clauses β ε L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p → @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a β L

/-- **G13-G16 with G15 fed by G7/G8 (GLUE, proved).** As `modularConstituent_tail_G`, with
`G15RamG D u` replaced by: `D.r5` and `D.r3` come from G8 on G7's data (`G8LocalPack`, with the
local glue at `p ≠ 5`, resp. `p = 5`) and G11's output. -/
theorem modularConstituent_tail_L (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧
      G8LocalPack 5 D.r5 (fun p => p ≠ 5) ∧ G8LocalPack 3 D.r3 (fun p => p = 5) ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5 ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩,
    ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩, h11a, h11b⟩ := h
  exact modularConstituent_tail_G lv hJac hX hSw hL8 hAd A u
    ⟨D, h12, hc, G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃
      (hG₃ 5 (by norm_num) rfl) h11a h11b⟩

end G0ModNewform

#print axioms G0ModNewform.modularConstituent_tail_L
