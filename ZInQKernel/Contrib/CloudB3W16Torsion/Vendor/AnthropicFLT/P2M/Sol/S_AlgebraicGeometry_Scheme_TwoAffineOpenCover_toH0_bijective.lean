/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_toH0_bijective. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_toH0_bijective

set_option autoImplicit false

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Spec Scheme Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Γ Opens Cover TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom)
namespace TwoAffineOpenCover
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (algebraOfHom cover structureSheafSections toH0 toH0_apply_coe U1 U0 sup_eq_top)
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SheafCondition

variable (X : Scheme.{u}) (U V : X.Opens)

private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.SheafCondition.eqLocus : Subring (Γ(X, U) × Γ(X, V)) :=
  RingHom.eqLocus
    ((X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom.comp (RingHom.fst Γ(X, U) Γ(X, V)))
    ((X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom.comp (RingHom.snd Γ(X, U) Γ(X, V)))
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.SheafCondition (eqLocus)
theorem mem_eqLocus_iff (s : Γ(X, U) × Γ(X, V)) :
    s ∈ eqLocus X U V ↔
      (X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom s.1
        = (X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom s.2 :=
  Iff.rfl

def gammaEquiv (h : U ⊔ V = ⊤) : Γ(X, ⊤) ≃+* eqLocus X U V :=
  ((X.presheaf.mapIso (eqToIso h).op).trans (X.sheaf.objSupIsoProdEqLocus U V)).commRingCatIsoToRingEquiv

private theorem map_comp_apply {W₁ W₂ W₃ : X.Opens} (f : W₁ ⟶ W₂) (g : W₂ ⟶ W₃) (a : Γ(X, W₃)) :
    (X.presheaf.map f.op).hom ((X.presheaf.map g.op).hom a) = (X.presheaf.map (f ≫ g).op).hom a := by
  rw [op_comp, Functor.map_comp, CommRingCat.comp_apply]

theorem gammaEquiv_apply_fst (h : U ⊔ V = ⊤) (a : Γ(X, ⊤)) :
    (gammaEquiv X U V h a).1.1 = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom a := by
  have h0 : (gammaEquiv X U V h a).1.1
      = ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.1 := rfl
  have h1 : ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.1
      = (X.presheaf.map (homOfLE le_sup_left).op).hom ((X.presheaf.map (eqToHom h).op).hom a) :=
    X.sheaf.objSupIsoProdEqLocus_hom_fst U V _
  rw [h0, h1, map_comp_apply X (homOfLE le_sup_left) (eqToHom h) a,
    Subsingleton.elim ((homOfLE le_sup_left : U ⟶ U ⊔ V) ≫ eqToHom h) (homOfLE (le_top : U ≤ ⊤))]

theorem gammaEquiv_apply_snd (h : U ⊔ V = ⊤) (a : Γ(X, ⊤)) :
    (gammaEquiv X U V h a).1.2 = (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a := by
  have h0 : (gammaEquiv X U V h a).1.2
      = ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.2 := rfl
  have h1 : ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.2
      = (X.presheaf.map (homOfLE le_sup_right).op).hom ((X.presheaf.map (eqToHom h).op).hom a) :=
    X.sheaf.objSupIsoProdEqLocus_hom_snd U V _
  rw [h0, h1, map_comp_apply X (homOfLE le_sup_right) (eqToHom h) a,
    Subsingleton.elim ((homOfLE le_sup_right : V ⟶ U ⊔ V) ≫ eqToHom h) (homOfLE (le_top : V ≤ ⊤))]

end SheafCondition

open SheafCondition

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

theorem toH0_bijective' : letI := algebraOfHom c ⊤; Function.Bijective (𝒱.toH0 c) := by
  letI := algebraOfHom c ⊤
  have hpair : ∀ s : Γ(X, ⊤),
      ((𝒱.toH0 c s : (𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1))
        = (gammaEquiv X 𝒱.U0 𝒱.U1 𝒱.sup_eq_top s).1 := fun s => by
    rw [toH0_apply_coe]
    exact Prod.ext (gammaEquiv_apply_fst X _ _ _ s).symm (gammaEquiv_apply_snd X _ _ _ s).symm
  constructor
  · intro s s' hss'
    apply (gammaEquiv X 𝒱.U0 𝒱.U1 𝒱.sup_eq_top).injective
    apply Subtype.ext
    rw [← hpair, ← hpair, hss']
  · rintro ⟨p, hp⟩
    have hp' : p ∈ eqLocus X 𝒱.U0 𝒱.U1 :=
      (mem_eqLocus_iff X 𝒱.U0 𝒱.U1 p).mpr ((TwoChartCech.Cover.mem_H0_structureSheaf_iff _ p).mp hp)
    refine ⟨(gammaEquiv X 𝒱.U0 𝒱.U1 𝒱.sup_eq_top).symm ⟨p, hp'⟩, Subtype.ext ?_⟩
    rw [hpair, RingEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem solution {R : Type u} [CommRing R] {X : AlgebraicGeometry.Scheme.{u}}
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ AlgebraicGeometry.Spec (.of R)) :
    letI := AlgebraicGeometry.Scheme.TwoAffineOpenCover.algebraOfHom c ⊤
    Function.Bijective (𝒱.toH0 c) :=
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.toH0_bijective' 𝒱 c

end
