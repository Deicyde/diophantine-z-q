import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralTraceNormalization

/-!
# Trace choice for the literal local duality map

The local duality map is the traced adjoint of an explicit pairing
`Cone(U → L)[−1] × U' → Cone(E → E_L)[−1]`. Its Leibniz rule follows
from the existing Selmer cup product: the first input has zero global
component, so the second input's compact component does not contribute.

Consequently the proved global-unit normalization and compact-scalar
trace homotopy apply to the literal local map, not an unnamed comparison.
This transfers quasi-isomorphy between valid traces on the same target;
it does not prove local Kummer orthogonality or self-duality.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.InnerLimitArith

section LocalPair

universe u
variable {R : Type u} [CommRing R] {D D' : SelData R}

/-- On a local first input, the Selmer cup depends only on the second local condition component. -/
theorem localConditionCup_ignore_compact (Q : SelPairData D D')
    (i j k : ℤ) (h : i + j = k) (c : (locCx D).X i)
    (b : D'.G.X j) (v : D'.U.X j) (y : D'.L.X (j - 1)) :
    selCup Q i j k h ((inclLoc D).f i i rfl c) ((b, v, y) : selT D' j) =
      selCup Q i j k h ((inclLoc D).f i i rfl c) (secU D' j v) := by
  obtain ⟨a, x⟩ := c
  change selCupFun Q i j k h (0, a, x) (b, v, y) =
    selCupFun Q i j k h (0, a, x) (0, v, 0)
  simp only [selCupFun, map_zero, LinearMap.zero_apply, smul_zero, add_zero]

/-- The actual pairing whose traced adjoint is the literal local duality map. -/
def localConditionCupPair (Q : SelPairData D D') :
    GPair (locCx D) D'.U (coneCx Q.resE) where
  P i j k h := (selCup Q i j k h).compl₁₂ ((inclLoc D).f i i rfl) (secU D' j)
  leib i i₁ j j₁ k k₁ h hi hj hk c v := by
    have hl := (selPair Q).leib i i₁ j j₁ k k₁ h hi hj hk
      ((inclLoc D).f i i rfl c) (secU D' j v)
    have hf := (inclLoc D).comm i i₁ i i₁ rfl hi hi rfl c
    have hs : selCup Q i j₁ k₁ (by omega) ((inclLoc D).f i i rfl c)
        ((selCx D').d j j₁ hj (secU D' j v)) =
      selCup Q i j₁ k₁ (by omega) ((inclLoc D).f i i rfl c)
        (secU D' j₁ (D'.U.d j j₁ hj v)) := by
      exact localConditionCup_ignore_compact Q i j₁ k₁ (by omega) c
        (D'.G.d j j₁ hj 0) (D'.U.d j j₁ hj v)
        (D'.res.f j (j₁ - 1) (by omega) 0 -
          D'.ι.f j (j₁ - 1) (by omega) v - D'.L.d (j - 1) (j₁ - 1) (by omega) 0)
    erw [← hf, hs] at hl
    exact hl

/-- The pairing has the original local cup and isotropy term, with no extra sign or global component. -/
theorem localConditionCupPair_apply (Q : SelPairData D D')
    (i j k : ℤ) (h : i + j = k) (a : D.U.X i) (x : D.L.X (i - 1)) (v : D'.U.X j) :
    (localConditionCupPair Q).P i j k h ((a, x) : (locCx D).X i) v =
      ((0, Q.cupL.P (i - 1) j (k - 1) (by omega) x (D'.ι.f j j rfl v) +
        Q.hU i j (k - 1) (by omega) a v) : (coneCx Q.resE).X k) := by
  change selCupFun Q i j k h (0, a, x) (0, v, 0) = _
  simp only [selCupFun, map_zero, LinearMap.zero_apply, smul_zero, add_zero]

/-- The fixed local duality map is exactly this pairing's traced adjoint. -/
theorem localDualityMap_eq_localConditionAdjoint (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0) :
    GHom.toCC (localDualityMap Q tr htr) =
      GHom.toCC (adjHom (localConditionCupPair Q) 3 tr htr) := by
  apply GHom.toCC_ext
  intro n c
  apply dualCx_ext
  intro v
  rfl

/-- Rescaling the trace by a unit rescales the same literal local map by a complex isomorphism. -/
theorem localDualityMap_unit_trace_eq_comp (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0) (a : Rˣ) :
    GHom.toCC (localDualityMap Q ((a : R) • tr) (unitScaledTrace_boundary 3 tr htr a)) =
      GHom.toCC (localDualityMap Q tr htr) ≫ (unitScalarCochainIso (dualCx D'.U 3) a).hom := by
  rw [localDualityMap_eq_localConditionAdjoint, localDualityMap_eq_localConditionAdjoint]
  exact adjHom_unit_trace_eq_comp (localConditionCupPair Q) 3 tr htr a

end LocalPair

section Central

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- A single unit simultaneously gives the global and all finite-place cycle relations. -/
theorem centralGlobalAndLocalTraces_one_unit (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D)
    (tr₁ tr₂ : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr₁ : ∀ z, tr₁ ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (htr₂ : ∀ z, tr₂ ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (ht₁ : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr₁)
    (ht₂ : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr₂) :
    ∃ a : ℤ_[2]ˣ,
      (∀ z : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3,
        (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 3 4 rfl z = 0 →
          tr₁ z = (a : ℤ_[2]) * tr₂ z) ∧
      ∀ (v : Places K D.S) (c : (centralLocalCyclotomicCx D v).X 2),
        (centralLocalCyclotomicCx D v).d 2 3 rfl c = 0 →
          centralLocalIntegralTrace D I tr₁ v c =
            (a : ℤ_[2]) * centralLocalIntegralTrace D I tr₂ v c := by
  let Q := centralIntegralPairDataTrunc D I
  obtain ⟨a, ha⟩ := centralTrace_unit_on_cycles D I tr₁ tr₂ htr₁ htr₂ ht₁ ht₂
  refine ⟨a, ha, fun v c hc => ?_⟩
  let f := integralLocalToCompactTarget K D.S v
  have hd : (shiftDown (centralLocalCyclotomicCx D v)).d 3 4 rfl c = 0 := by
    change -((centralLocalCyclotomicCx D v).d 2 3 rfl c) = 0
    rw [hc, neg_zero]
  have hz : (coneCx Q.resE).d 3 4 rfl (f.f 3 3 rfl c) = 0 := by
    have h := f.comm 3 4 3 4 rfl rfl rfl rfl c
    rw [hd, map_zero] at h
    exact h.symm
  exact ha (ZInQ.Manuscript.RC.SelmerComplex.coneProj Q 3 (f.f 3 3 rfl c))
    ((coneProj3_cocycle_iff Q (f.f 3 3 rfl c)).2 hz)

/-- The literal local-map quasi-isomorphism verdict is independent of valid trace choice on the same target.
This is trace transport only: it does not assert that either local map is a quasi-isomorphism. -/
theorem centralLocalDuality_quasiIso_iff_of_traceIsomorphisms
    (D : GenuineKummerData K E₀ hZ) (I : CentralIntegralTruncIsotropy D)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (tr₁ tr₂ : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr₁ : ∀ z, tr₁ ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (htr₂ : ∀ z, tr₂ ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (ht₁ : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr₁)
    (ht₂ : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr₂) :
    QuasiIso (GHom.toCC (localDualityMap (centralIntegralPairDataTrunc D I).toSelPairData tr₁ htr₁)) ↔
      QuasiIso (GHom.toCC (localDualityMap (centralIntegralPairDataTrunc D I).toSelPairData tr₂ htr₂)) := by
  rw [localDualityMap_eq_localConditionAdjoint, localDualityMap_eq_localConditionAdjoint]
  exact centralTraceAdjoints_quasiIso_iff_of_traceIsomorphisms D I
    hglob hloc hglobal hlocal hK h2
    (localConditionCupPair (centralIntegralPairDataTrunc D I).toSelPairData)
    tr₁ tr₂ htr₁ htr₂ ht₁ ht₂

end Central

end ZInQ.Contrib.RC53Assist.IntegralDuality
