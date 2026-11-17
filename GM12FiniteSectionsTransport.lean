/-
H5 Lane5 GM12, universe-u finite-section transport. SOURCE ONLY, UNCOMPILED.

NO-LINE ANALYSIS: HasGoodReduction A O has no line-bundle premise. Its result
is an abelian-scheme GROUP over the ORIGINAL O with generic GROUP fibre ≅ the
SAME A/K. M/L0, a section presentation and psi/cocycle are intermediate,
existentially constructed descent witnesses. The fixed I3 below is an output
of C4, not a new final NOS hypothesis. Its native power is transported to the
literal Source power on the SAME H, and amplification is used forward only.

Blueprint attribution: frenzymath/FLT6e837e75..., Apache-2.0, Anthropic, PBC,
ProjPresentation.exists_of_iso / its PresIso transport. The transport below
is newly written at universe u using actual restriction and Γ-linear maps;
no P2M Type0 solution, provider closure, tactic budget or native run is used.
The original Source definitions are separately recovered/frozen. Their
conformance copies and remaining imports are NOT a native admission.
-/
import GM12SourceNativePowerMaps
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.FiniteProjAmplify
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Sections

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace H5OriginalDVR.Lane5.GM12.FiniteSections

local notation "SrcPresentation" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation
local notation "SrcFinite" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
local notation "SrcClosed" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections
local notation "SPow" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {M N : X.Modules}

/-- Module-map naturality on the ACTUAL ordinary presheaf of sections. -/
theorem restrict_app (phi : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
    N.presheaf.map i.op (phi.app U s) = phi.app V (M.presheaf.map i.op s) := by
  have h := phi.mapPresheaf.naturality i.op
  have h' := congrArg (fun g => (ConcreteCategory.hom g) s) h
  simpa using h'.symm

/-- Change only the coefficient line along an actual isomorphism. The SAME
sections are sent by e.hom, while the scheme map, base equation, frame opens
and scalar ratio equations remain literal. -/
def transportPresentation {d : ℕ} (P : SrcPresentation M f d) (e : M ≅ N) :
    SrcPresentation N f d where
  σ i := e.hom.app ⊤ (P.σ i)
  toProj := P.toProj
  toProj_π := P.toProj_π
  frame i V hV := by
    have hfun :
        (fun g : Γ(X, V) =>
          g • N.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (e.hom.app ⊤ (P.σ i))) =
        (e.hom.app V) ∘ (fun g : Γ(X, V) =>
          g • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (P.σ i)) := by
      funext g
      simp only [Function.comp_apply, restrict_app, Scheme.Modules.Hom.app_smul]
    rw [hfun]
    exact (Scheme.Modules.appLinearEquivOfIso e V).bijective.comp (P.frame i V hV)
  app_ratio_smul i j := by
    rw [restrict_app, restrict_app, ← Scheme.Modules.Hom.app_smul, P.app_ratio_smul i j]

/-- Literal map preservation; finite is not turned into closed. -/
theorem transportPresentation_map {d : ℕ} (P : SrcPresentation M f d) (e : M ≅ N) :
    (transportPresentation P e).toProj = P.toProj := rfl

/-- Actual global sections are transported by the original module iso. -/
theorem transportPresentation_section {d : ℕ} (P : SrcPresentation M f d)
    (e : M ≅ N) (i : Fin (d + 1)) :
    (transportPresentation P e).σ i = e.hom.app ⊤ (P.σ i) := rfl

/-- Finite-by-sections transports along the actual iso and the SAME toProj. -/
theorem finite_of_iso (e : M ≅ N) (h : SrcFinite M f) : SrcFinite N f := by
  obtain ⟨d, P, hP⟩ := h
  exact ⟨d, transportPresentation P e, hP⟩

/-- The exact fixed I3 conclusion implies the original literal Source-power
finite conclusion. No exponent multiple/section-compatibility input is added. -/
theorem source_finite_power_of_native (M : X.Modules) (a : ℕ) (ha : 0 < a)
    (hI3 : SrcFinite (_root_.AlgebraicGeometry.Scheme.Modules.tensorPow M a) f) :
    0 < a ∧ SrcFinite (SPow M a) f :=
  ⟨ha, finite_of_iso (SourcePower.iso M a).symm hI3⟩

/-- Forward-only finite-to-closed amplification after the actual power iso.
The new positive n and the closed map are CONSTRUCTED by the retained C1
source theorem; there is no finite=closed or reverse-Serre step. -/
theorem exists_closed_source_power_of_I3 (M : X.Modules)
    (hI3 : ∃ a : ℕ, 0 < a ∧
      SrcFinite (_root_.AlgebraicGeometry.Scheme.Modules.tensorPow M a) f) :
    ∃ n : ℕ, 0 < n ∧ SrcClosed (SPow M n) f := by
  obtain ⟨a, ha, hfinite⟩ := hI3
  have hsource := (source_finite_power_of_native M a ha hfinite).2
  exact ZInQ.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower.
    exists_closedImmersionBySections_tensorPow_of_finiteBySections_tensorPow a ha hsource

end H5OriginalDVR.Lane5.GM12.FiniteSections
