/-
S1 checks. Private isolated source, scaled/semisimplicity.

Trust-0 style evidence for the S1 packet:
  * `#print axioms` on every new declaration (must show only propext / Classical.choice /
    Quot.sound — no `sorryAx`, no project axiom, no recovery declaration);
  * `#check` of the full types actually proved;
  * the CALLER BIND: `GlueC10Link.c10_of_squares` applied with its `hr` slot filled by the new
    helper and EVERY other hypothesis still an open binder. This proves only that the helper's
    type is the consumer's `hr`; it closes nothing. C10 is not proved: `hC`, `hBN`, `hM`, the
    modular `hρ`, `hρ₃`, C9 `h₅`, the squares `hSq`, continuity `hrc`/`hρc`, the S2 premise
    `hRM` and the global-comparison supplier premises all remain hypotheses.
-/

import S1Twist
import S1Mapped

open GlueDescent GlueC10 GlueC10Link PkgI3
open scoped TensorProduct

namespace ScaledS1Checks

/-! ## Full types -/

#check @ScaledS1.le_comap_smul_iff
#check @ScaledS1.forall_le_comap_iff_of_smul_twist
#check @ScaledS1.twistOrderIso
#check @ScaledS1.isSemisimpleRepresentation_iff_of_smul_twist
#check @ScaledS1.isSemisimpleRepresentation_of_smul_twist
#check @ScaledS1.scalar_ne_zero_of_group_rep
#check @ScaledS1.compOrderIso
#check @ScaledS1.isSemisimpleRepresentation_of_comp_surjective
#check @ScaledS1.transport
#check @ScaledS1Mapped.RelativeMaschke
#check @ScaledS1Mapped.semisimple_rL_of_globalTateComparison

/-! ## Axioms (expect: propext, Classical.choice, Quot.sound; nothing else) -/

#print axioms ScaledS1.le_comap_smul_iff
#print axioms ScaledS1.forall_le_comap_iff_of_smul_twist
#print axioms ScaledS1.twistOrderIso
#print axioms ScaledS1.isSemisimpleRepresentation_iff_of_smul_twist
#print axioms ScaledS1.isSemisimpleRepresentation_of_smul_twist
#print axioms ScaledS1.scalar_ne_zero_of_group_rep
#print axioms ScaledS1.compOrderIso
#print axioms ScaledS1.isSemisimpleRepresentation_of_comp_surjective
#print axioms ScaledS1.transport
#print axioms ScaledS1Mapped.semisimple_rL_of_globalTateComparison

/-! ## Caller bind: the helper fills the `hr` slot of the ORIGINAL `c10_of_squares`.

Everything else is still a binder. This is a type-level bind, not a proof of C10. -/

theorem c10_of_squares_hr_discharged
    -- the S2 interface and the new supplier premises
    (hRM : ScaledS1Mapped.RelativeMaschke)
    (hFS : PkgI3.FaltingsSemisimple) (hTF : PkgI3.TateModuleFree)
    -- the original hypotheses of `GlueC10Link.c10_of_squares`, verbatim, minus `hr`
    (hC : ChebotarevExists) (hBN : BrauerNesbittChar0)
    (hM : CharPolyIndepOfEll) (S : Finset ℕ) (h3S : 3 ∈ S) (h5S : 5 ∈ S)
    (C : Type) [Field C] [CharZero C]
    (c ε : GQ → GQ → C) (a β : GQ → C) (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0) (ha1 : a 1 = 1)
    (hβ1 : β 1 = 1) (af : ℕ → C)
    (k₅ V₅ W₅ : Type) [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (T₅ : GQ → Module.End k₅ V₅) (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h))
    (hT₅1 : T₅ 1 = 1) (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ u₅.W (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) =
        LinearMap.trace k₅ W₅ (ρ₅ g))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (af p))
    (k₃ V₃ W₃ ιI κ : Type) [Field k₃] [Algebra ℚ_[3] k₃] [CharZero k₃] [TopologicalSpace k₃]
    [IsTopologicalRing k₃] [T2Space k₃] [AddCommGroup V₃] [Module k₃ V₃]
    [FiniteDimensional k₃ V₃] [AddCommGroup W₃] [Module k₃ W₃] [FiniteDimensional k₃ W₃]
    [Fintype ιI] [DecidableEq ιI] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k₃)
    (T₃ : GQ → Module.End k₃ V₃) (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h))
    (hT₃1 : T₃ 1 = 1) (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (bV : Module.Basis ιI k₃ u₃.W) (bW : Module.Basis κ k₃ W₃) (ρ₃ : Representation k₃ GQ W₃)
    (hrc : Continuous fun g =>
      LinearMap.toMatrix bV bV (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hρ : IsSemisimpleModule (MonoidAlgebra k₃ GQ) ρ₃.asModule)
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₃ W₃ (ρ₃ g) = ι₃ (af p))
    (hSq : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      ∃ (L : Type) (_ : Field L) (k : Type) (_ : Field k), CharP k p ∧
        ∃ (A Aσ : AbVar L) (mu : AbVar.Hom Aσ A) (Ab Ab' : AbVar k) (F : AbVar.Hom Ab Ab')
          (mub : AbVar.Hom Ab' Ab) (N : ℕ), N ≠ 0 ∧
          FrobSquares 3 mu F mub (T₃ g) N ∧ FrobSquares 5 mu F mub (T₅ g) N)
    -- the global Tate comparison: ONE number field, ONE abelian variety, ONE global `Ψ`
    (L₀ : Type) [Field L₀] [NumberField L₀] (A₀ : PkgI3.AbVar L₀)
    (jj : Field.absoluteGaloisGroup L₀ →* GQ)
    (hidx : (((MonoidHom.range jj).index : ℕ) : k₃) ≠ 0)
    (Ψ : V₃ ≃ₗ[k₃] TensorProduct ℚ_[3] k₃ (A₀.V 3))
    (χ : Field.absoluteGaloisGroup L₀ → k₃) (hχ : ∀ σ, χ σ ≠ 0)
    (hΨ : ∀ σ, Ψ.toLinearMap ∘ₗ T₃ (jj σ) =
      χ σ • ((GlueI3.repBaseChange k₃ (A₀.galRep 3) σ) ∘ₗ Ψ.toLinearMap)) :
    Nonempty ((rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule ≃ₗ[MonoidAlgebra k₃ GQ]
      ρ₃.asModule) :=
  c10_of_squares hC hBN hM S h3S h5S C c ε a β ha hβ hβ0 ha1 hβ1 af k₅ V₅ W₅ ι₅ T₅ hT₅ hT₅1 u₅ hu₅
    ρ₅ h₅ hρ₅ k₃ V₃ W₃ ιI κ ι₃ T₃ hT₃ hT₃1 u₃ hu₃ bV bW ρ₃ hrc hρc
    (ScaledS1Mapped.semisimple_rL_of_globalTateComparison hRM hFS hTF c ε a β ha hβ hβ0 ha1 hβ1
      ι₃ T₃ hT₃ hT₃1 u₃ hu₃ A₀ jj hidx Ψ χ hχ hΨ)
    hρ hρ₃ hSq

#print axioms c10_of_squares_hr_discharged

end ScaledS1Checks
