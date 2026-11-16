import ZInQKernel.Contrib.CloudB3W17Hodge.Bridge
import ZInQKernel.Contrib.CloudB3W17Uniformization.NativeAnalytic

/-!
# Transport native analytic facts through the genuine complex-point comparison

Only composition/naturality adapters are proved here. Native regular-section
holomorphy, Γ coordinates and scheme-morphism analyticity are the already
compiled `NativeAnalytic` theorems; the carrier/evaluation/topology comparison
is the immutable Hodge `Bridge`. A genuine `C^ω` comparison diffeomorphism is
an explicit argument of these intermediate adapters, to be supplied by the
canonical charted-space comparison helper in the final H103 assembly.
There is no new open leaf, purpose-built structure or closing claim here.
-/

open scoped Manifold ContDiff Topology
open CategoryTheory AlgebraicGeometry Set Function

namespace CloudB3W17Uniformization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CloudB3W17Hodge
local instance (X : Over (Spec ↧ℂ)) : TopologicalSpace (CPt X) :=
  CloudB3W17Hodge.classicalTopology X

noncomputable section

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance : ChartedSpace (Fin d → ℂ) (CPt X) := CloudB3W17Hodge.chartedSpace X d

/-- Composition naturality of the actual carrier comparison is category associativity. -/
theorem cptEquiv_map {Y : Over (Spec ↧ℂ)} (α : X ⟶ Y) (P : CPt X) :
    cptEquiv Y (P ≫ α) = AlgebraicGeometry.Point.map α (cptEquiv X P) := by
  simp only [cptEquiv, AlgebraicGeometry.Point.map, Equiv.coe_fn_mk, Category.assoc]

variable (e : CPt X ≃ₘ^ω⟮𝓘(ℂ, Fin d → ℂ), 𝓘(ℂ, Fin d → ℂ)⟯ ComplexPoint X)
  (he : ∀ P : CPt X, e P = cptEquiv X P)

/-- Zariski point opens are open for the actual classical topology. -/
theorem isOpen_cptIn (U : X.left.Opens) : IsOpen {P : CPt X | XPtIn X P U} := by
  have h := (AlgebraicGeometry.Point.isOpen_overOpen (X := X) U).preimage
    (cptHomeomorph X).continuous
  have hset : (cptHomeomorph X) ⁻¹' AlgebraicGeometry.Point.overOpen U =
      {P : CPt X | XPtIn X P U} := by
    ext P
    exact (ptIn_iff X P U).symm
  rwa [hset] at h

include e he in
/-- The native regular-section analytic theorem transports to the actual CPt evaluation. -/
theorem contMDiffOn_cptEvaluate (U : X.left.Opens) (s : Γ(X.left, U)) :
    ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω (XevalAt X U s) {P : CPt X | XPtIn X P U} := by
  have hm : MapsTo e {P : CPt X | XPtIn X P U} (AlgebraicGeometry.Point.overOpen U) := by
    intro P hP
    change e P ∈ AlgebraicGeometry.Point.overOpen U
    rw [he P]
    exact (ptIn_iff X P U).mp hP
  have h := (contMDiffOn_nativeEvaluate X d U s).comp e.contMDiff.contMDiffOn hm
  apply h.congr
  intro P _
  exact (xevalAt_eq_evaluate X U s P).trans (congrArg (AlgebraicGeometry.Point.evaluate U s) (he P).symm)

include e he in
/-- Native Γ local coordinates transport to actual CPt local analytic coordinates. -/
theorem cpt_regularCoordinates (P : CPt X) :
    ∃ (U : X.left.Opens) (f : Fin d → Γ(X.left, U)), XPtIn X P U ∧
      IsLocalDiffeomorphAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
        (fun Q i => XevalAt X U (f i) Q) P := by
  obtain ⟨U, f, hU, hcoords⟩ := native_regularCoordinates X d (e P)
  have hP : XPtIn X P U := (ptIn_iff X P U).mpr (by rwa [← he P])
  have h := (e.isLocalDiffeomorph P).comp (K := 𝓘(ℂ, Fin d → ℂ))
    (P := Fin d → ℂ) hcoords
  have hfun : (fun Q i => XevalAt X U (f i) Q) =
      (fun q i => AlgebraicGeometry.Point.evaluate U (f i) q) ∘ e := by
    funext Q i
    rw [xevalAt_eq_evaluate]
    simp only [Function.comp_apply, he]
  exact ⟨U, f, hP, hfun.symm ▸ h⟩

include e he in
/-- Native scheme-morphism analyticity transports through the genuine comparison. -/
theorem contMDiff_cptMap {Y : Over (Spec ↧ℂ)} (m : ℕ) [SmoothOfRelativeDimension m Y.hom]
    (eY : let _ : ChartedSpace (Fin m → ℂ) (CPt Y) := CloudB3W17Hodge.chartedSpace Y m;
      CPt Y ≃ₘ^ω⟮𝓘(ℂ, Fin m → ℂ), 𝓘(ℂ, Fin m → ℂ)⟯ ComplexPoint Y)
    (heY : ∀ Q : CPt Y, eY Q = cptEquiv Y Q) (α : X ⟶ Y) :
    let _ : ChartedSpace (Fin m → ℂ) (CPt Y) := CloudB3W17Hodge.chartedSpace Y m
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin m → ℂ) ω (fun P : CPt X => P ≫ α) := by
  let : ChartedSpace (Fin m → ℂ) (CPt Y) := CloudB3W17Hodge.chartedSpace Y m
  have h := eY.symm.contMDiff.comp ((contMDiff_nativeMap X d m α).comp e.contMDiff)
  apply h.congr
  intro P
  apply eY.injective
  change eY (P ≫ α) = eY (eY.symm (AlgebraicGeometry.Point.map α (e P)))
  rw [eY.apply_symm_apply, heY, he]
  exact cptEquiv_map X α P

end
end CloudB3W17Uniformization
