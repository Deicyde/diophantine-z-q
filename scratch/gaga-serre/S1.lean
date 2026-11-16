import ZInQKernel.Contrib.OneProof.SGA1Printed
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.QuasiProjective

open scoped Topology
open Filter Set CategoryTheory AlgebraicGeometry

set_option linter.style.haveILetI false

noncomputable section

namespace SerreGAGA

open UnifPrinted UnifTopology SGA1Printed SGA1Etale
open PkgI3 (AbVar)

/-- **Projective variety over `ℂ`** in Serre's sense (FAC, GAGA): a reduced closed subscheme of a
projective space `ℙ^N_ℂ` (`N` finite), as a `ℂ`-scheme. -/
def IsProjVar (X : Over (Spec (CommRingCat.of ℂ))) : Prop :=
  IsReduced X.left ∧
    ∃ (N : Type) (_ : Finite N) (i : X.left ⟶ ℙ(N; Spec (CommRingCat.of ℂ))),
      IsClosedImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of ℂ)) ↘ Spec (CommRingCat.of ℂ) = X.hom

/-- LEAF: Serre's GAGA for holomorphic maps of projective varieties. -/
def SerreGAGAMorphism : Prop :=
  ∀ (X Y : Over (Spec (CommRingCat.of ℂ))), IsProjVar X → IsProjVar Y →
    ∀ F : CPt X → CPt Y, IsAnMorphism X Y F → ∃ f : X ⟶ Y, ∀ P, F P = P ≫ f

/-- Abelian varieties are projective varieties. -/
theorem isProjVar (A : AbVar ℂ) : IsProjVar A.X := by
  have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  refine ⟨inferInstance, ?_⟩
  obtain ⟨N, hN, i, hi, hover⟩ :=
    GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral A.X
  have : IsProper (i ≫ ℙ(N; Spec (CommRingCat.of ℂ)) ↘ Spec (CommRingCat.of ℂ)) := by
    rw [hover]; infer_instance
  have : IsProper i := IsProper.of_comp i (ℙ(N; Spec (CommRingCat.of ℂ)) ↘ Spec (CommRingCat.of ℂ))
  exact ⟨N, hN, i, .of_isPreimmersion i i.isClosedMap.isClosed_range, hover⟩

theorem sga1_XII_4_4_of_serre (h : SerreGAGAMorphism) : SGA1_XII_4_4 :=
  fun A B F hF => h A.X B.X (isProjVar A) (isProjVar B) F hF

theorem gagaMorphism_of_serre (hM : MumfordComplexTorus) (hL : SGA1_XII_3_3a)
    (hPC : ProperCompactAn) (hC : SGA1_XII_2_4) (hS : SerreGAGAMorphism) :
    ZInQ.HomLattice.GAGAMorphism :=
  gagaMorphism_of_printed hM hL hPC hC (sga1_XII_4_4_of_serre hS)

/-! Germ form -/

variable {X Y : Over (Spec (CommRingCat.of ℂ))}

theorem anFunAt_eventually [LocallyOfFiniteType X.hom] {F : CPt X → ℂ} {P : CPt X}
    (h : AnFunAt X F P) : ∀ᶠ Q in @nhds _ (analyticTopology X) P, AnFunAt X F Q := by
  letI := analyticTopology X
  obtain ⟨U, k, g, H, hPU, hH, hev⟩ := h
  have hcont : ContinuousAt (fun Q i => XevalAt X U (g i) Q) P :=
    continuousAt_pi.mpr fun i => continuousAt_xevalAt_an U (g i) hPU
  have hH' := hcont.eventually hH.eventually_analyticAt
  filter_upwards [(isOpen_ptIn_an U).mem_nhds hPU, hH', hev.eventually_nhds] with Q hQU hQH hQe
  exact ⟨U, k, g, H, hQU, hQH, hQe⟩

theorem isAnMorphism_iff_germ [LocallyOfFiniteType Y.hom] (F : CPt X → CPt Y) :
    IsAnMorphism X Y F ↔ @Continuous _ _ (analyticTopology X) (analyticTopology Y) F ∧
      ∀ (P : CPt X) (s : CPt Y → ℂ), AnFunAt Y s (F P) → AnFunAt X (s ∘ F) P := by
  letI := analyticTopology X
  letI := analyticTopology Y
  constructor
  · rintro ⟨hc, hF⟩
    refine ⟨hc, fun P s hs => ?_⟩
    have hmem : F P ∈ interior {Q | AnFunAt Y s Q} :=
      mem_interior_iff_mem_nhds.mpr (anFunAt_eventually hs)
    exact hF _ s isOpen_interior (fun Q hQ => (interior_subset (s := {Q | AnFunAt Y s Q}) hQ : AnFunAt Y s Q)) P hmem
  · rintro ⟨hc, hF⟩
    exact ⟨hc, fun W s _ hs P hP => hF P s (hs _ hP)⟩

#print axioms gagaMorphism_of_serre
#print axioms isAnMorphism_iff_germ

end SerreGAGA
