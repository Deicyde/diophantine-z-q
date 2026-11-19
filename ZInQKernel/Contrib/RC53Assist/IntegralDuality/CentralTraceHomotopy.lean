import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralCompactTrace
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.IntegralTraceHomotopy

/-!
# Trace homotopy for the actual truncated compact target

The existing cone projection is onto in every degree and an isomorphism
above degree three. It transports the proved next-degree exactness and
next-next-term torsion-freeness from the full cyclotomic cone to its local
truncation. The integral trace comparison consequently applies to the
actual central target with only the existing arithmetic support inputs.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.InnerLimitArith

section Truncated

variable {R : Type} [CommRing R] {D D' : SelData R}

/-- The projection transports degree-four exactness, with the unchanged cone differential signs. -/
theorem truncatedCone_degree_four_exact (Q : SelPairDataTrunc D D')
    (hnext : ∀ z : (coneCx Q.resE).X 4, (coneCx Q.resE).d 4 5 rfl z = 0 →
      ∃ y : (coneCx Q.resE).X 3, (coneCx Q.resE).d 3 4 rfl y = z)
    (z' : (coneCx Q.toSelPairData.resE).X 4)
    (hz' : (coneCx Q.toSelPairData.resE).d 4 5 rfl z' = 0) :
    ∃ y' : (coneCx Q.toSelPairData.resE).X 3,
      (coneCx Q.toSelPairData.resE).d 3 4 rfl y' = z' := by
  obtain ⟨z, rfl⟩ := coneProj_surjective Q 4 z'
  have hz : (coneCx Q.resE).d 4 5 rfl z = 0 := by
    apply coneProj_injective Q (n := 5) (by norm_num)
    rw [map_zero, coneProj_d]
    exact hz'
  obtain ⟨y, hy⟩ := hnext z hz
  exact ⟨coneProj Q 3 y, (coneProj_d Q 3 4 rfl y).symm.trans (congrArg (coneProj Q 4) hy)⟩

/-- The projection above degree three transfers torsion-freeness as a linear equivalence. -/
theorem truncatedCone_degree_five_torsionFree (Q : SelPairDataTrunc D D')
    [Module.IsTorsionFree R ((coneCx Q.resE).X 5)] :
    Module.IsTorsionFree R ((coneCx Q.toSelPairData.resE).X 5) := by
  let e := LinearEquiv.ofBijective (coneProj Q 5)
    ⟨coneProj_injective Q (by norm_num), coneProj_surjective Q 5⟩
  exact Function.Injective.moduleIsTorsionFree e.symm e.symm.injective
    (fun r x => e.symm.map_smul r x)

end Truncated

section CompactScalar

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
  {D D' : SelData R} {A B : GCx R}

/-- Integral trace comparison on the truncated cone uses the proved full-cone support witnesses. -/
theorem truncatedTraceAdjoints_quasiIso_iff (Q : SelPairDataTrunc D D')
    (P : GPair A B (coneCx Q.toSelPairData.resE))
    (tr₁ tr₂ : (coneCx Q.toSelPairData.resE).X 3 →ₗ[R] R)
    (htr₁ : ∀ z, tr₁ ((coneCx Q.toSelPairData.resE).d 2 3 rfl z) = 0)
    (htr₂ : ∀ z, tr₂ ((coneCx Q.toSelPairData.resE).d 2 3 rfl z) = 0)
    [Module.IsTorsionFree R ((coneCx Q.resE).X 5)]
    (hnext : ∀ z : (coneCx Q.resE).X 4, (coneCx Q.resE).d 4 5 rfl z = 0 →
      ∃ y : (coneCx Q.resE).X 3, (coneCx Q.resE).d 3 4 rfl y = z)
    (hcyc : ∀ z : (coneCx Q.toSelPairData.resE).X 3,
      (coneCx Q.toSelPairData.resE).d 3 4 rfl z = 0 → tr₁ z = tr₂ z) :
    Nonempty (Homotopy (GHom.toCC (adjHom P 3 tr₁ htr₁))
      (GHom.toCC (adjHom P 3 tr₂ htr₂))) ∧
      (QuasiIso (GHom.toCC (adjHom P 3 tr₁ htr₁)) ↔
        QuasiIso (GHom.toCC (adjHom P 3 tr₂ htr₂))) := by
  let : Module.IsTorsionFree R ((coneCx Q.toSelPairData.resE).X (3 + 2)) :=
    truncatedCone_degree_five_torsionFree Q
  exact adjHom_quasiIso_iff_of_eq_on_cycles_compact P 3 tr₁ tr₂ htr₁ htr₂
    (truncatedCone_degree_four_exact Q hnext) hcyc

end CompactScalar

/-- The exact central target supplies the support witnesses from the existing Milne inputs. -/
theorem centralTraceAdjoints_quasiIso_iff_of_eq_on_cycles
    {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
    (D : GenuineKummerData K E₀ hZ) (I : CentralIntegralTruncIsotropy D)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    {A B : GCx ℤ_[2]}
    (P : GPair A B (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE))
    (tr₁ tr₂ : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr₁ : ∀ z, tr₁ ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (htr₂ : ∀ z, tr₂ ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (hcyc : ∀ z : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3,
      (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 3 4 rfl z = 0 → tr₁ z = tr₂ z) :
    Nonempty (Homotopy (GHom.toCC (adjHom P 3 tr₁ htr₁))
      (GHom.toCC (adjHom P 3 tr₂ htr₂))) ∧
      (QuasiIso (GHom.toCC (adjHom P 3 tr₁ htr₁)) ↔
        QuasiIso (GHom.toCC (adjHom P 3 tr₂ htr₂))) := by
  let Q := centralIntegralPairDataTrunc D I
  let : Module.IsTorsionFree ℤ_[2] ((coneCx Q.resE).X 5) :=
    integralCompactTarget_torsionFree (K := K) (S := D.S) 5
  exact truncatedTraceAdjoints_quasiIso_iff Q P tr₁ tr₂ htr₁ htr₂
    (integralCompactTarget_degree_four_exact (S := D.S) hglob hloc hglobal hlocal hK D.hSfin h2) hcyc

end ZInQ.Contrib.RC53Assist.IntegralDuality
