import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralCoefficients
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.TateModuleTopology
import ZInQKernel.Contrib.RC53Assist.CalibrationShape.CalibrationDischarge

/-!
# Actual global Tate cohomology hypotheses for integral duality

The existing two-adic Tate limit and finite-level Milne inputs give finite
generation of genuine global and local cohomology. The compact-support cone
has the corresponding finite generation and support in degrees zero through
three. These ordinary hypotheses supply finite free models; no model
comparison, global duality map, Kummer duality or rank symmetry is assumed.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.CalibrationModel
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.Finiteness
open ZInQ.Contrib.RC53Assist.InnerLimitArith

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The genuine global data with strict conditions and the actual central Tate coefficients. -/
abbrev centralStrictIntegralSelData (D : GenuineKummerData K E₀ hZ) : SelData ℤ_[2] :=
  selData ℤ_[2] (GKS K D.S) (fun v : Places K D.S => Gloc K v.1)
    (fun v => locMap K D.S v.1) (TateS K D.S (centralCurve D))
    (strictConditions ℤ_[2] (GKS K D.S) (fun v : Places K D.S => Gloc K v.1)
      (fun v => locMap K D.S v.1) (TateS K D.S (centralCurve D)))

/-- Global finite generation for the actual central coefficients is already supplied by the Tate limit. -/
theorem centralGlobalIntegralCohomology_finite (D : GenuineKummerData K E₀ hZ)
    (hglob : MilneGlobalFiniteness)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S) (n : ℤ) :
    Module.Finite ℤ_[2] ((globalCx ℤ_[2] (GKS K D.S)
      (TateS K D.S (centralCurve D))).toCC.homology n) :=
  moduleFinite_globalTateCohomology K D.S (centralCurve D) hglob D.hSfin h2 n

/-- Local finite generation uses the same actual Tate coefficients restricted by the genuine map. -/
theorem centralLocalIntegralCohomology_finite (D : GenuineKummerData K E₀ hZ)
    (hloc : MilneLocalFiniteness) (v : Places K D.S) (n : ℤ) :
    Module.Finite ℤ_[2] ((localCx ℤ_[2] (GKS K D.S) (fun v : Places K D.S => Gloc K v.1)
      (fun v => locMap K D.S v.1) (TateS K D.S (centralCurve D)) v).toCC.homology n) :=
  moduleFinite_localTateCohomology K D.S (centralCurve D) hloc v.1 n

/-- The literal compact-support cochain complex has finitely generated cohomology in all degrees. -/
theorem centralCompactIntegralCohomology_finite (D : GenuineKummerData K E₀ hZ)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S) (n : ℤ) :
    Module.Finite ℤ_[2] ((compactCx (centralStrictIntegralSelData D)).toCC.homology n) := by
  let : Finite (Places K D.S) := D.hSfin.to_subtype
  let G := (centralStrictIntegralSelData D).G
  let L := (centralStrictIntegralSelData D).L
  have hG : Module.Finite ℤ_[2] (G.toCC.homology n) :=
    centralGlobalIntegralCohomology_finite D hglob h2 n
  have hL : Module.Finite ℤ_[2] (L.toCC.homology (n - 1)) :=
    moduleFinite_homology_piCx _ (n - 1) (fun v =>
      centralLocalIntegralCohomology_finite D hloc v (n - 1))
  exact moduleFinite_of_exact
    ((coneSES_shortExact (centralStrictIntegralSelData D).res).homology_exact₂ n)
    (moduleFinite_homology_shiftDown L n hL) hG

/-- Global support zero through two does not require vanishing or finiteness of rational point torsion. -/
theorem centralGlobalIntegralCohomology_outside (D : GenuineKummerData K E₀ hZ)
    (hglob : MilneGlobalFiniteness) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (n : ℤ) (hn : n < 0 ∨ 2 < n) :
    Subsingleton ((globalCx ℤ_[2] (GKS K D.S)
      (TateS K D.S (centralCurve D))).toCC.homology n) := by
  rcases hn with hn | hn
  · exact homology_subsingleton_of_term _ n (natCx_negative_term _ n hn)
  · exact globalTate_homology_high (centralCurve D) (centralFullTorsion D)
      hglob hglobal hK D.hSfin h2 n hn

/-- Compact-support cohomology is supported in zero through three, by the actual cone exact sequence. -/
theorem centralCompactIntegralCohomology_outside (D : GenuineKummerData K E₀ hZ)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (n : ℤ) (hn : n < 0 ∨ 3 < n) :
    Subsingleton ((compactCx (centralStrictIntegralSelData D)).toCC.homology n) := by
  let A := centralStrictIntegralSelData D
  rcases hn with hn | hn
  · have hg : Subsingleton (A.G.X n) := natCx_negative_term _ n hn
    have hl : ∀ v : Places K D.S, Subsingleton
        ((localCx ℤ_[2] (GKS K D.S) (fun v : Places K D.S => Gloc K v.1)
          (fun v => locMap K D.S v.1) (TateS K D.S (centralCurve D)) v).X (n - 1)) :=
      fun v => natCx_negative_term _ (n - 1) (by omega)
    let := hg
    let := hl
    have hz : Subsingleton ((compactCx A).X n) := by
      change Subsingleton (A.G.X n ×
        (∀ v : Places K D.S,
          (localCx ℤ_[2] (GKS K D.S) (fun v : Places K D.S => Gloc K v.1)
            (fun v => locMap K D.S v.1) (TateS K D.S (centralCurve D)) v).X (n - 1)))
      infer_instance
    exact homology_subsingleton_of_term _ n hz
  · have hg : Subsingleton (A.G.toCC.homology n) :=
      centralGlobalIntegralCohomology_outside D hglob hglobal hK h2 n (Or.inr (by omega))
    have hl : Subsingleton (A.L.toCC.homology (n - 1)) :=
      pi_homology_subsingleton _ (n - 1) (fun v =>
        localTate_homology_high (centralCurve D) (centralFullTorsion D) hloc hlocal
          v.1 (n - 1) (by omega))
    exact subsingleton_of_exact ((coneSES_shortExact A.res).homology_exact₂ n)
      (shiftDown_homology_subsingleton A.L n hl) hg

/-- The actual perfect determinant pairing is also perfect in the flipped direction. -/
theorem centralIntegralBeta_flip_bijective (D : GenuineKummerData K E₀ hZ) :
    Function.Bijective (centralIntegralBeta D).flip := by
  have hflip : (centralIntegralBeta D).flip = -(centralIntegralBeta D) := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    apply (ContinuousCharacterLine.equiv ℤ_[2] (cyc2 K D.S)).injective
    change ContinuousCharacterLine.equiv ℤ_[2] (cyc2 K D.S) (integralBeta y x) =
      ContinuousCharacterLine.equiv ℤ_[2] (cyc2 K D.S) (-(integralBeta x y))
    rw [map_neg, integralBeta_underlying, integralBeta_underlying]
    exact detT_swap x y
  rw [hflip]
  constructor
  · intro x y h
    apply integralBeta_bijective.1
    simpa using congrArg Neg.neg h
  · intro y
    obtain ⟨x, hx⟩ := integralBeta_bijective.2 (-y)
    exact ⟨x, by rw [LinearMap.neg_apply, hx, neg_neg]⟩

end ZInQ.Contrib.RC53Assist.IntegralDuality
