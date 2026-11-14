/-
NEGATIVE control on the ACTUAL HELPER (must be REJECTED). NEW fixture, 2026-11-14.

This is the control that `BadS1NoNumberField.lean` was NOT: it APPLIES
`ScaledS1Mapped.semisimple_rL_of_globalTateComparison` at a base field that is not a number field
(`L := ℚ_[3]`), with every other parameter of the full telescope supplied as a legitimate binder
and no `sorry` anywhere.

Intended rejection: the SOLE failure is the missing `NumberField ℚ_[3]` instance demanded by the
helper (because `PkgI3.FaltingsSemisimple` holds only over number fields) — not a parse error, not
an unrelated synthesis failure, and not a mismatch anywhere else in the telescope. The positive
counterpart `HelperAppliesOverQ.lean` compiles with the identical telescope at `L := ℚ`.
-/

import S1Mapped

open GlueDescent GlueC10 GlueC10Link PkgI3
open scoped TensorProduct

namespace ScaledS1HelperBad

theorem helper_rejected_over_Qp
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
    (A : PkgI3.AbVar ℚ_[3])
    (jj : Field.absoluteGaloisGroup ℚ_[3] →* GQ)
    (hidx : (((MonoidHom.range jj).index : ℕ) : k₃) ≠ 0)
    (Ψ : V₃ ≃ₗ[k₃] TensorProduct ℚ_[3] k₃ (A.V 3))
    (χ : Field.absoluteGaloisGroup ℚ_[3] → k₃) (hχ : ∀ σ, χ σ ≠ 0)
    (hΨ : ∀ σ, Ψ.toLinearMap ∘ₗ T₃ (jj σ) =
      χ σ • ((GlueI3.repBaseChange k₃ (A.galRep 3) σ) ∘ₗ Ψ.toLinearMap)) :
    IsSemisimpleModule (MonoidAlgebra k₃ GQ)
      (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule :=
  ScaledS1Mapped.semisimple_rL_of_globalTateComparison hRM hS hTF c ε a β ha hβ hβ0 ha1 hβ1
    ι₃ T₃ hT₃ hT₃1 u₃ hu₃ A jj hidx Ψ χ hχ hΨ

end ScaledS1HelperBad
