/-
H5 lane3 Step 1: GM1 v3, the NATIVE route (Parent decision (B)). GM1 `SeesawPulledBack` is PROVED
from H72's native seesaw core and ONE native bridge. 2026-11-17. New file. SOURCE-ONLY,
UNCOMPILED. Universe u, any characteristic.

Single producer, by exact path/SHA:
* Lemma: `ZInQ.Contrib.CloudR2Poincare.L1.normalizedPicardClass_eq_one_of_residueFibres_reduced`,
  in swarm/h72/src/ZInQKernel/Contrib/CloudR2Poincare/L1/ReducedGlobalSeesaw.lean, sha256
  4ac58f79e1cc113ef1db1e28b5911e8bf5606763ff033e7198e341de6f2245a8.
* Hypotheses: `{k} [Field k]` (any field, no CharZero, no dimension restriction); `π` proper and
  geometrically integral with a section; `T` locally Noetherian and reduced; the class normalized
  along W07 `sectionBaseChange`; ALL residue fibres trivial. Conclusion: the class is `1`.
* W07 `sectionBaseChange π σ hσ T = pullback.lift (T.hom ≫ σ) (𝟙)` is definitionally
  `baseSection`. The Picard API is W07 `Scheme.Pic` (`mk`, `map_mk`, `mk_eq_mk_iff`,
  `one_eq_mk_unit`).

The proof:
* Normalize as in Seesaw.lean: `L' := L ⊗ (pr₂^*b^*L)ᵛ`. The base section is trivial
  (`normalized_base`), and so are all rational slices (`normalized_slices`, via C2's field-line
  triviality).
* Use the bridge to pass from rational slices to all residue fibres.
* H72 gives `[L'] = 1`, hence `L' ≅ O` and `L ≅ pr₂^*b^*L`.
This supersedes the SeesawOpenness/SeesawGlue/SeesawDensity route of Seesaw.lean, which stays as
history of the decomposition. No Stacks import is used.

ONE native obligation (TRUE), `AllResidueFibresOfRationalSlices`: over an algebraically closed
`K`, with `X` proper and geometrically integral and `T` locally of finite type, if all rational
slices are trivial then all residue fibres are trivial.
* Closed points: the residue fibre at `t` matches the rational slice at Mathlib
  `pointOfClosedPoint t`, through `Spec (κ(t) ≅ K)` and actual pullback pasting.
* Other points: H72 `isClosed_fibrePicardClass_trivial` (L1/NativeTrivialityLocus.lean fd0f9728…)
  on affine opens, with `fX` flat over the field (Mathlib), plus Jacobson.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.SeesawShear
import ZInQKernel.Contrib.CloudR2Poincare.L1.ReducedGlobalSeesaw

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- The native bridge (TRUE; see header). -/
def AllResidueFibresOfRationalSlices : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] {X T : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fT : T ⟶ Spec (CommRingCat.of K)) [IsProper fX] [GeometricallyIntegral fX]
    [LocallyOfFiniteType fT] (L : (Limits.pullback fX fT).Modules) [L.IsInvertible],
    (∀ (t : Spec (CommRingCat.of K) ⟶ T) (ht : t ≫ fT = 𝟙 _),
      Nonempty ((Scheme.Modules.pullback (sliceAt fX fT t ht)).obj L ≅ 𝟙_ X.Modules)) →
    ∀ τ : T, Scheme.Pic.map (pullback.fst (pullback.snd fX fT) (T.fromSpecResidueField τ))
      (Scheme.Pic.mk L) = 1

section Normalized

variable {K : Type u} [Field K] {X T : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
  (fT : T ⟶ Spec (CommRingCat.of K)) (x₀ : Spec (CommRingCat.of K) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
  (L : (Limits.pullback fX fT).Modules) [L.IsInvertible]

/-- The normalizing factor `pr₂^* b^*L`. -/
abbrev normFactor : (Limits.pullback fX fT).Modules :=
  (Scheme.Modules.pullback (pullback.snd fX fT)).obj
    ((Scheme.Modules.pullback (baseSection fX fT x₀ hx₀)).obj L)

/-- PROVED: the normalized line is trivial along the base section. -/
theorem normalized_base :
    Iso' ((Scheme.Modules.pullback (baseSection fX fT x₀ hx₀)).obj
      (L ⊗ Scheme.Modules.dual (normFactor fX fT x₀ hx₀ L))) (𝟙_ T.Modules) := by
  have hbsnd : baseSection fX fT x₀ hx₀ ≫ pullback.snd fX fT = 𝟙 T := pullback.lift_snd _ _ _
  refine (iso'_pb_tensor _ _ _).trans ?_
  refine ((iso'_refl _).tensor ((iso'_pb_dual _ _).trans ?_)).trans (iso'_dual _)
  exact ((iso'_pb_comp _ _ _).trans ((iso'_pb_congr hbsnd _).trans (iso'_pb_id _))).dual

/-- PROVED: if all rational slices of `L` are trivial, so are those of the normalized line. -/
theorem normalized_slices (hF : LineOnSpecFieldTrivial.{u})
    (hslice : ∀ (t : Spec (CommRingCat.of K) ⟶ T) (ht : t ≫ fT = 𝟙 _),
      Nonempty ((Scheme.Modules.pullback (sliceAt fX fT t ht)).obj L ≅ 𝟙_ X.Modules))
    (t : Spec (CommRingCat.of K) ⟶ T) (ht : t ≫ fT = 𝟙 _) :
    Nonempty ((Scheme.Modules.pullback (sliceAt fX fT t ht)).obj
      (L ⊗ Scheme.Modules.dual (normFactor fX fT x₀ hx₀ L)) ≅ 𝟙_ X.Modules) := by
  have hssnd : sliceAt fX fT t ht ≫ pullback.snd fX fT = fX ≫ t := pullback.lift_snd _ _ _
  have hN : Iso' ((Scheme.Modules.pullback (sliceAt fX fT t ht)).obj (normFactor fX fT x₀ hx₀ L))
      (𝟙_ X.Modules) :=
    (iso'_pb_comp _ _ _).trans <|
      (iso'_pb_congr hssnd _).trans <|
        (iso'_pb_comp _ _ _).symm.trans <|
          (Iso'.pb fX (hF _)).trans (iso'_pb_unit fX)
  refine (iso'_pb_tensor _ _ _).trans ?_
  refine ((hslice t ht).tensor ((iso'_pb_dual _ _).trans hN.dual)).trans ?_
  exact (iso'_unit_left _).trans (iso'_dual_unit X)

end Normalized

/-- GM1 v3, PROVED from H72's native normalized seesaw and the native bridge. -/
theorem seesawPulledBack_v3 (hB : AllResidueFibresOfRationalSlices.{u}) :
    SeesawPulledBack.{u} := by
  intro K _ _ X T fX fT _ _ _ _ x₀ hx₀ L _ hslice
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian fT
  have hb := normalized_base fX fT x₀ hx₀ L
  have hs := normalized_slices fX fT x₀ hx₀ L lineOnSpecFieldTrivial hslice
  have hNorm : Scheme.Pic.map (sectionBaseChange fX x₀ hx₀ (Over.mk fT))
      (Scheme.Pic.mk (L ⊗ Scheme.Modules.dual (normFactor fX fT x₀ hx₀ L))) = 1 := by
    rw [Scheme.Pic.map_mk, Scheme.Pic.one_eq_mk_unit]
    exact (Scheme.Pic.mk_eq_mk_iff _ _).mpr hb
  have h1 := ZInQ.Contrib.CloudR2Poincare.L1.normalizedPicardClass_eq_one_of_residueFibres_reduced
    fX x₀ hx₀ (Over.mk fT) _ hNorm (hB fX fT _ hs)
  have hL' : Iso' (L ⊗ Scheme.Modules.dual (normFactor fX fT x₀ hx₀ L)) (𝟙_ _) := by
    rw [Scheme.Pic.one_eq_mk_unit] at h1
    exact (Scheme.Pic.mk_eq_mk_iff _ _).mp h1
  exact Iso'.of_tensor_dual_unit hL'

end ZInQ.Contrib.CloudR2NOS.Step1
