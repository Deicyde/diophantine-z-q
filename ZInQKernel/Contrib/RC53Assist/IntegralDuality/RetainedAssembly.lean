import ZInQKernel.Contrib.RC53Assist.IntegralDuality.RetainedDualComparison
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralRetainedSupport

/-!
# Conditional assembly of the exact retained central duality map

The actual global map is supplied by the general cited global theorem and
proved arithmetic data. A proved local Kummer orthogonality supplier is
still required. Given that exact local map, the split Selmer sequences
make the raw Selmer adjoint a quasi-isomorphism. Pullback through the fixed
retained comparison and its proved torsion-free dual comparison gives a
quasi-isomorphism of the two actual bounded finite free retained models.

This file assembles the final consumer conditionally; it does not prove
local isotropy or local Kummer orthogonality, and is not an arithmetic
inhabitant of central self-duality without those missing suppliers.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.CalibrationModel
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.InnerLimitArith

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The same traced Selmer cup adjoint pulled back through the fixed retained comparison on both sides. -/
def retainedCentralCupDualityMap (D : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n))
    (I : CentralIntegralTruncIsotropy D)
    (tr : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0) :
    (centralRetainedGCx D hfinite).toCC ⟶ (dualCx (centralRetainedGCx D hfinite) 3).toCC :=
  retainedCentralComparison D hfinite ≫
    GHom.toCC (selmerDualityMap (centralIntegralPairDataTrunc D I).toSelPairData tr htr) ≫
      retainedCentralDualComparison D hfinite 3

/-- The pullback has the exact original traced-cup evaluation, including both fixed comparisons. -/
theorem retainedCentralCupDualityMap_apply (D : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n))
    (I : CentralIntegralTruncIsotropy D)
    (tr : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (n : ℤ) (x : (centralRetainedGCx D hfinite).X n)
    (y : (centralRetainedGCx D hfinite).X (3 - n)) :
    asDual (((retainedCentralCupDualityMap D hfinite I tr htr).f n).hom x) y =
      tr (selCup (centralIntegralPairDataTrunc D I).toSelPairData n (3 - n) 3 (by omega)
        (((retainedCentralComparison D hfinite).f n).hom x)
        (((retainedCentralComparison D hfinite).f (3 - n)).hom y)) := rfl

/-- The raw five-lemma and two proved comparisons yield the exact retained quasi-isomorphism.
The local-map premise is the explicitly remaining arithmetic obligation, not a new printed leaf. -/
theorem retainedCentralCupDualityMap_quasiIso_of_local (D : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n))
    (I : CentralIntegralTruncIsotropy D) (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (tr : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (ht : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr)
    (hL : QuasiIso (GHom.toCC (localDualityMap (centralIntegralPairDataTrunc D I).toSelPairData tr htr))) :
    QuasiIso (retainedCentralCupDualityMap D hfinite I tr htr) := by
  let Q := (centralIntegralPairDataTrunc D I).toSelPairData
  have hG : QuasiIso (GHom.toCC (globalDualityMap Q tr htr)) :=
    centralRawGlobalDuality_quasiIso D I h543 hglob hloc hglobal hlocal hK h2 tr htr ht
  have hS : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)) :=
    quasiIso_τ₂ (sesHom Q tr htr) (sesTop_shortExact (compactCentralSelData D))
      (sesBot_shortExact (compactCentralSelData D)) hL hG
  have : QuasiIso (retainedCentralComparison D hfinite) := retainedCentralComparison_quasiIso D hfinite
  have : QuasiIso (retainedCentralDualComparison D hfinite 3) :=
    retainedCentralDualComparison_quasiIso D hfinite 3
  have : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)) := hS
  dsimp only [retainedCentralCupDualityMap]
  infer_instance

/-- Conditional final retained homotopy equivalence, with its hom map fixed by the original cup.
No desired retained or derived isomorphism is an input. The actual local-map proof is still required. -/
theorem retainedCentralHomotopyEquiv_of_local (D : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n))
    (I : CentralIntegralTruncIsotropy D) (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (tr : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (ht : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr)
    (hL : QuasiIso (GHom.toCC (localDualityMap (centralIntegralPairDataTrunc D I).toSelPairData tr htr))) :
    ∃ e : HomotopyEquiv (centralRetainedGCx D hfinite).toCC
      (dualCx (centralRetainedGCx D hfinite) 3).toCC,
      e.hom = retainedCentralCupDualityMap D hfinite I tr htr := by
  let P := centralRetainedGCx D hfinite
  let P' := dualCx P 3
  let hout := compactCentral_support_zero_three D hloc hglob hlocal hglobal hK h2
  let : P.toCC.IsStrictlyGE (-1) := (CochainComplex.isStrictlyGE_iff P.toCC (-1)).2 (by
    intro n hn
    let : Subsingleton (P.X n) := centralRetainedGCx_bounded_weak D hfinite hout n (Or.inl hn)
    exact ModuleCat.isZero_of_subsingleton (P.X n))
  let : P.toCC.IsStrictlyLE 4 := (CochainComplex.isStrictlyLE_iff P.toCC 4).2 (by
    intro n hn
    let : Subsingleton (P.X n) := centralRetainedGCx_bounded_weak D hfinite hout n (Or.inr (by omega))
    exact ModuleCat.isZero_of_subsingleton (P.X n))
  let : P'.toCC.IsStrictlyGE (-1) := (CochainComplex.isStrictlyGE_iff P'.toCC (-1)).2 (by
    intro n hn
    let : Subsingleton (P'.X n) := centralRetainedDual_bounded_weak D hfinite hout n (Or.inl (by omega))
    exact ModuleCat.isZero_of_subsingleton (P'.X n))
  let : P'.toCC.IsStrictlyLE 4 := (CochainComplex.isStrictlyLE_iff P'.toCC 4).2 (by
    intro n hn
    let : Subsingleton (P'.X n) := centralRetainedDual_bounded_weak D hfinite hout n (Or.inr hn)
    exact ModuleCat.isZero_of_subsingleton (P'.X n))
  let : ∀ n, Module.Free ℤ_[2] (P.toCC.X n) := fun n => (centralRetainedGCx_terms D hfinite n).1
  let : ∀ n, Module.Free ℤ_[2] (P'.toCC.X n) := fun n =>
    ((centralRetainedDual_boundedFiniteFree_weak D hfinite hout).2 n).1
  have : QuasiIso (retainedCentralCupDualityMap D hfinite I tr htr) :=
    retainedCentralCupDualityMap_quasiIso_of_local D hfinite I h543
      hglob hloc hglobal hlocal hK h2 tr htr ht hL
  exact homotopyEquiv_of_quasiIso_free (-1) 4 (retainedCentralCupDualityMap D hfinite I tr htr)

/-- The exact original consumer follows once the independently supplied actual local obligation is proved. -/
theorem integralCentralKummerDuality_of_local (D : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n))
    (I : CentralIntegralTruncIsotropy D) (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (tr : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (ht : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr)
    (hL : QuasiIso (GHom.toCC (localDualityMap (centralIntegralPairDataTrunc D I).toSelPairData tr htr))) :
    IntegralCentralKummerDuality D hfinite := by
  obtain ⟨e, _⟩ := retainedCentralHomotopyEquiv_of_local D hfinite I h543
    hglob hloc hglobal hlocal hK h2 tr htr ht hL
  exact ⟨e⟩

end ZInQ.Contrib.RC53Assist.IntegralDuality
