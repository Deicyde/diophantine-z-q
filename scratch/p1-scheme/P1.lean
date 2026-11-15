import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveLine.RelativeCoordinates
import ZInQKernel.HDecomp.QM.Pairs

noncomputable section

namespace GapGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV
open TopologicalSpace Opposite

/-- Copied verbatim from `scratch/mcr-quot/MCRQuot.lean` L3989 (namespace `MCRGlue` there). -/
def baseToSectionsOver (R : CommRingCat.{0}) (𝒵 : Over (Spec R)) (W : 𝒵.left.Opens) :
    R →+* Γ(𝒵.left, W) :=
  (𝒵.left.presheaf.map (homOfLE le_top).op).hom.comp
    ((𝒵.hom.appTop).hom.comp (Scheme.ΓSpecIso R).inv.hom)

/-- Copied verbatim from `scratch/mcr-quot/MCRQuot.lean` L3995 (namespace `MCRGlue` there). -/
def IsP1CoordinateQ (𝒵 : Over (Spec (CommRingCat.of ℚ))) (σ : ToP1 𝒵.left) : Prop :=
  IsAffineOpen σ.U ∧ IsAffineOpen σ.V ∧
    Function.Bijective (eval₂RingHom (baseToSectionsOver _ 𝒵 σ.U) σ.f) ∧
    Function.Bijective (eval₂RingHom (baseToSectionsOver _ 𝒵 σ.V) σ.g)

/-- Copied verbatim from `scratch/mcr-quot/MCRQuot.lean` L8549 (namespace `MCRQuot` there). -/
def P1SchemeQ : Prop :=
  ∃ (P : Over (Spec (CommRingCat.of ℚ))) (τ : ToP1 P.left),
    IsProper P.hom ∧ SmoothOfRelativeDimension 1 P.hom ∧ IsP1CoordinateQ P τ ∧
    ∀ (Z : Over (Spec (CommRingCat.of ℚ))) (σ : ToP1 Z.left),
      ∃ (m : Z ⟶ P) (eU : m.left ⁻¹ᵁ τ.U = σ.U) (eV : m.left ⁻¹ᵁ τ.V = σ.V),
        m.left.app τ.U τ.f = Z.left.presheaf.map (eqToHom eU).op σ.f ∧
        m.left.app τ.V τ.g = Z.left.presheaf.map (eqToHom eV).op σ.g

/-! ## Restriction lemmas -/

section Restrict

variable {X : Scheme.{0}}

lemma presheaf_map_map {A B C D : X.Opens} (i : op A ⟶ op B) (j : op B ⟶ op D)
    (i' : op A ⟶ op C) (j' : op C ⟶ op D) (s : Γ(X, A)) :
    X.presheaf.map j (X.presheaf.map i s) = X.presheaf.map j' (X.presheaf.map i' s) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  rfl

lemma homOfLE_appTop_topIso_inv {W U : X.Opens} (h : W ≤ U) (s : Γ(X, U)) :
    (X.homOfLE h).appTop (U.topIso.inv s) =
      W.topIso.inv (X.presheaf.map (homOfLE h).op s) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  exact presheaf_map_map _ _ _ _ s

lemma image_basicOpen_topIso_inv (V : X.Opens) (s : Γ(X, V)) :
    V.ι ''ᵁ V.toScheme.basicOpen (V.topIso.inv s) = X.basicOpen s := by
  rw [Scheme.image_basicOpen, Scheme.Opens.ι_appIso]
  simp only [Iso.refl_inv, Scheme.Opens.topIso_inv]
  erw [Scheme.basicOpen_res]
  rw [Scheme.Opens.ι_image_top]
  exact inf_eq_right.mpr (X.basicOpen_le s)

lemma mem_basicOpen_topIso_inv (V : X.Opens) (s : Γ(X, V)) (p : V.toScheme) :
    p ∈ V.toScheme.basicOpen (V.topIso.inv s) ↔ p.1 ∈ X.basicOpen s := by
  rw [← image_basicOpen_topIso_inv V s]
  exact (Scheme.Opens.mem_ι_image_iff V).symm

end Restrict

/-! ## The relative line over `ℚ` -/

open ProjectiveSpace ProjectiveLine

local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "L" => ProjectiveLine.relativeLine (Spec (CommRingCat.of ℚ))

abbrev std (c : ULift.{0} (Fin 2)) : (L).Opens := standardOpen (ULift.{0} (Fin 2)) Q c

/-- The affine coordinate on the chart `c`, as a section of `P¹` over the chart. -/
def tcoord (c : ULift.{0} (Fin 2)) : Γ(L, std c) :=
  (std c).topIso.hom (relativeChartCoordinate Q c)

lemma topIso_inv_tcoord (c : ULift.{0} (Fin 2)) :
    (std c).topIso.inv (tcoord c) = relativeChartCoordinate Q c := by
  simp only [tcoord, Iso.hom_inv_id_apply]

lemma std_sup : std ⟨0⟩ ⊔ std ⟨1⟩ = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← iSup_standardOpen (ULift.{0} (Fin 2)) Q]
  refine iSup_le fun ⟨c⟩ => ?_
  fin_cases c
  · exact le_sup_left
  · exact le_sup_right

lemma chart_preimage (c d : ULift.{0} (Fin 2)) (hcd : c ≠ d) :
    (std c).ι ⁻¹ᵁ std d = (std c).toScheme.basicOpen (relativeChartCoordinate Q c) := by
  conv_lhs => rw [relativeChart_ι_eq_normalized Q c]
  rw [normalized, homOfSections_preimage_standardOpen]
  simp [normalizedSections, hcd.symm]

lemma basicOpen_tcoord (c d : ULift.{0} (Fin 2)) (hcd : c ≠ d) :
    (L).basicOpen (tcoord c) = std c ⊓ std d := by
  rw [← image_basicOpen_topIso_inv, topIso_inv_tcoord, ← chart_preimage c d hcd,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

lemma tcoord_mul (c d : ULift.{0} (Fin 2)) (hcd : c ≠ d) (h₁ : std c ⊓ std d ≤ std c)
    (h₂ : std c ⊓ std d ≤ std d) :
    (L).presheaf.map (homOfLE h₁).op (tcoord c) *
      (L).presheaf.map (homOfLE h₂).op (tcoord d) = 1 := by
  have key := relativeChartCoordinate_mul (base := Q) c d hcd ((L).homOfLE h₁) ((L).homOfLE h₂)
    (by rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι])
  rw [← topIso_inv_tcoord c, ← topIso_inv_tcoord d, homOfLE_appTop_topIso_inv,
    homOfLE_appTop_topIso_inv, ← map_mul] at key
  have := congrArg (std c ⊓ std d).topIso.hom key
  rwa [Iso.inv_hom_id_apply, map_one] at this

/-- The tautological map `P¹_ℚ → P¹` by charts. -/
def tau : ToP1 L where
  U := std ⟨0⟩
  V := std ⟨1⟩
  cover := std_sup
  f := tcoord ⟨0⟩
  g := tcoord ⟨1⟩
  inv := tcoord_mul _ _ (by decide) _ _
  basicOpen_f := basicOpen_tcoord _ _ (by decide)
  basicOpen_g := by rw [basicOpen_tcoord _ ⟨0⟩ (by decide), inf_comm]

end GapGlue
