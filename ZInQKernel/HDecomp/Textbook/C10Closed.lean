import ZInQKernel.HDecomp.Textbook.BrauerNesbitt
import ZInQKernel.HDecomp.C10.C10

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt5b from
`scratch/t-skolem-kw/C10Closed.lean` (its last part).
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-!
# t-skolem-kw: C10 from Chebotarev alone

The draft `C10Closed.lean` is `BrauerNesbitt.lean` (adopted as
`ZInQKernel.HDecomp.Textbook.BrauerNesbitt`), then glue-c10's namespace `GlueC10` verbatim
(adopted as `ZInQKernel.HDecomp.C10.C10`), then the part below.
-/

open NumberField
open GlueC10

namespace TSkolemKW.C10

/-- `GlueC10.BrauerNesbittChar0` is the same Prop as `TSkolemKW.BrauerNesbittChar0`. -/
theorem brauerNesbittChar0' : BrauerNesbittChar0 := TSkolemKW.brauerNesbittChar0

/-- **C10 from Chebotarev alone (GLUE, proved).** `GlueC10.c10` with the Brauer–Nesbitt
hypothesis discharged by `TSkolemKW.brauerNesbittChar0`. -/
theorem c10_of_chebotarev (hC : ChebotarevExists) (S : Finset ℕ)
    (C : Type) [Field C] (c a : ℕ → C)
    (k₅ V₅ W₅ : Type) [Field k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (r₅ : Representation k₅ GQ V₅) (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ V₅ (r₅ g) = LinearMap.trace k₅ W₅ (ρ₅ g))
    (hr₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ V₅ (r₅ g) = ι₅ (c p))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (a p))
    (k V W ι κ : Type) [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (r₃ : Representation k GQ V) (ρ₃ : Representation k GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bV bV (r₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k GQ) r₃.asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k GQ) ρ₃.asModule)
    (hr₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k V (r₃ g) = ι₃ (c p))
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k W (ρ₃ g) = ι₃ (a p)) :
    Nonempty (r₃.asModule ≃ₗ[MonoidAlgebra k GQ] ρ₃.asModule) :=
  c10 hC brauerNesbittChar0' S C c a k₅ V₅ W₅ ι₅ r₅ ρ₅ h₅ hr₅ hρ₅ k V W ι κ ι₃ bV bW
    r₃ ρ₃ hrc hρc hr hρ hr₃ hρ₃

end TSkolemKW.C10
