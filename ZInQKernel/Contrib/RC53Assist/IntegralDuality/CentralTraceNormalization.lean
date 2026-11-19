import ZInQKernel.Contrib.RC53Assist.IntegralDuality.TraceUnitNormalization
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralTraceHomotopy
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralLocalTrace

/-!
# One global unit for the actual central trace family

Any two traces inducing the top compact scalar isomorphism differ on
cycles by one unique global unit. Their local restrictions therefore use
the same unit at every finite place, and their mod-two values on cycles
agree. The compact support witnesses already proved from the arithmetic
inputs make quasi-isomorphy of the traced adjoints independent of this
choice. No equality on cycles is taken as a new hypothesis.

These statements compare traces on the same actual global target and
its specified local restrictions. They do not identify an unrelated
local trace, prove local Kummer orthogonality or discharge self-duality.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000
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

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- Any two valid traces of the same actual global target differ on all cycles by one unit. -/
theorem centralTrace_unit_on_cycles (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D)
    (tr₁ tr₂ : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr₁ : ∀ z, tr₁ ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (htr₂ : ∀ z, tr₂ ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (ht₁ : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr₁)
    (ht₂ : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr₂) :
    ∃ u : ℤ_[2]ˣ, ∀ z : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3,
      (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 3 4 rfl z = 0 →
        tr₁ z = (u : ℤ_[2]) * tr₂ z :=
  topTraceUnit_on_cycles ⟨htr₁, ht₁⟩ ⟨htr₂, ht₂⟩

/-- Actual arithmetic support makes the traced-adjoint quasi-isomorphism verdict trace-independent. -/
theorem centralTraceAdjoints_quasiIso_iff_of_traceIsomorphisms
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
    (ht₁ : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr₁)
    (ht₂ : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr₂) :
    QuasiIso (GHom.toCC (adjHom P 3 tr₁ htr₁)) ↔
      QuasiIso (GHom.toCC (adjHom P 3 tr₂ htr₂)) := by
  let Q := centralIntegralPairDataTrunc D I
  let : Module.IsTorsionFree ℤ_[2] ((coneCx Q.resE).X 5) :=
    integralCompactTarget_torsionFree (K := K) (S := D.S) 5
  let : Module.IsTorsionFree ℤ_[2] ((coneCx Q.toSelPairData.resE).X (3 + 2)) :=
    truncatedCone_degree_five_torsionFree Q
  exact adjHom_quasiIso_iff_of_topTraceIso_compact P 3 tr₁ tr₂ ⟨htr₁, ht₁⟩ ⟨htr₂, ht₂⟩
    (truncatedCone_degree_four_exact Q
      (integralCompactTarget_degree_four_exact (S := D.S)
        hglob hloc hglobal hlocal hK D.hSfin h2))

/-- The same unit relates every local restricted trace on local cycles; there is no placewise choice. -/
theorem centralLocalTraces_one_unit (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D)
    (tr₁ tr₂ : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr₁ : ∀ z, tr₁ ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (htr₂ : ∀ z, tr₂ ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (ht₁ : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr₁)
    (ht₂ : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr₂) :
    ∃ u : ℤ_[2]ˣ, ∀ (v : Places K D.S) (c : (centralLocalCyclotomicCx D v).X 2),
      (centralLocalCyclotomicCx D v).d 2 3 rfl c = 0 →
        centralLocalIntegralTrace D I tr₁ v c = (u : ℤ_[2]) * centralLocalIntegralTrace D I tr₂ v c := by
  let Q := centralIntegralPairDataTrunc D I
  obtain ⟨u, hu⟩ := centralTrace_unit_on_cycles D I tr₁ tr₂ htr₁ htr₂ ht₁ ht₂
  refine ⟨u, fun v c hc => ?_⟩
  let f := integralLocalToCompactTarget K D.S v
  have hd : (shiftDown (centralLocalCyclotomicCx D v)).d 3 4 rfl c = 0 := by
    change -((centralLocalCyclotomicCx D v).d 2 3 rfl c) = 0
    rw [hc, neg_zero]
  have hz : (coneCx Q.resE).d 3 4 rfl (f.f 3 3 rfl c) = 0 := by
    have h := f.comm 3 4 3 4 rfl rfl rfl rfl c
    rw [hd, map_zero] at h
    exact h.symm
  have hproj := (coneProj3_cocycle_iff Q (f.f 3 3 rfl c)).2 hz
  exact hu (ZInQ.Manuscript.RC.SelmerComplex.coneProj Q 3 (f.f 3 3 rfl c)) hproj

/-- A two-adic scalar unit has residue one, with the actual residue map. -/
theorem padicUnit_toZMod_two_eq_one (u : ℤ_[2]ˣ) :
    (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) (u : ℤ_[2]) = 1 :=
  zmod_two_eq_one_of_ne_zero _ (u.isUnit.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)).ne_zero

/-- The same actual local traces have equal mod-two values on cycles, without a normalization premise. -/
theorem centralLocalTraces_modTwo_eq_on_cycles (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D)
    (tr₁ tr₂ : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr₁ : ∀ z, tr₁ ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (htr₂ : ∀ z, tr₂ ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (ht₁ : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr₁)
    (ht₂ : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr₂)
    (v : Places K D.S) (c : (centralLocalCyclotomicCx D v).X 2)
    (hc : (centralLocalCyclotomicCx D v).d 2 3 rfl c = 0) :
    (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) (centralLocalIntegralTrace D I tr₁ v c) =
      (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) (centralLocalIntegralTrace D I tr₂ v c) := by
  obtain ⟨u, hu⟩ := centralLocalTraces_one_unit D I tr₁ tr₂ htr₁ htr₂ ht₁ ht₂
  rw [hu v c hc, map_mul, padicUnit_toZMod_two_eq_one, one_mul]

end ZInQ.Contrib.RC53Assist.IntegralDuality
