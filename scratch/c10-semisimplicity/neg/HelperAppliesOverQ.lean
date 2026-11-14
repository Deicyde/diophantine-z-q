/-
POSITIVE typed helper test (must COMPILE). NEW fixture, 2026-11-14.

Exercises the ACTUAL helper `ScaledS1Mapped.semisimple_rL_of_globalTateComparison` at a concrete
base field that IS a number field (`L := ℚ`), with every other parameter supplied as a legitimate
binder of its full telescope. Its only role is to be the positive counterpart of
`BadS1HelperNoNumberField.lean`: it shows that the rejection there is caused solely by the missing
`NumberField` instance and by nothing else in the telescope.

This is NOT a non-vacuity witness: `A`, `jj`, `Ψ`, `χ`, `hΨ` are hypotheses here, not constructed
objects. Whether such a bundle exists for the actual surface is OPEN (see the packet supplement).
-/

import S1Mapped

open GlueDescent GlueC10 GlueC10Link PkgI3
open scoped TensorProduct

namespace ScaledS1HelperFixture

theorem helper_applies_over_Q
    (hRM : ScaledS1Mapped.RelativeMaschke)
    (hS : PkgI3.FaltingsSemisimple) (hTF : PkgI3.TateModuleFree)
    {C : Type} [Field C] [CharZero C]
    (c ε : GQ → GQ → C) (a β : GQ → C)
    (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (ha1 : a 1 = 1) (hβ1 : β 1 = 1)
    {k₃ V₃ : Type} [Field k₃] [Algebra ℚ_[3] k₃] [CharZero k₃]
    [AddCommGroup V₃] [Module k₃ V₃]
    (ι₃ : C →+* k₃) (T₃ : GQ → Module.End k₃ V₃)
    (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h)) (hT₃1 : T₃ 1 = 1)
    (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (A : PkgI3.AbVar ℚ)
    (jj : Field.absoluteGaloisGroup ℚ →* GQ)
    (hidx : (((MonoidHom.range jj).index : ℕ) : k₃) ≠ 0)
    (Ψ : V₃ ≃ₗ[k₃] TensorProduct ℚ_[3] k₃ (A.V 3))
    (χ : Field.absoluteGaloisGroup ℚ → k₃) (hχ : ∀ σ, χ σ ≠ 0)
    (hΨ : ∀ σ, Ψ.toLinearMap ∘ₗ T₃ (jj σ) =
      χ σ • ((GlueI3.repBaseChange k₃ (A.galRep 3) σ) ∘ₗ Ψ.toLinearMap)) :
    IsSemisimpleModule (MonoidAlgebra k₃ GQ)
      (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule :=
  ScaledS1Mapped.semisimple_rL_of_globalTateComparison hRM hS hTF c ε a β ha hβ hβ0 ha1 hβ1
    ι₃ T₃ hT₃ hT₃1 u₃ hu₃ A jj hidx Ψ χ hχ hΨ

#print axioms helper_applies_over_Q

end ScaledS1HelperFixture
