/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_exists_isUniversal. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Sites.Representability
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isRepresentable_supportedIn
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_of_forall_finset
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_isUniversal

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

open AlgebraicGeometry _root_.AlgebraicGeometry.RelEffCartierDiv in
theorem solution
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (hcov : ∀ (V : S.affineOpens) (F : Finset 𝒞), (∀ x ∈ F, f x ∈ (V : S.Opens)) →
      ∃ U : 𝒞.Opens, IsAffineOpen U ∧ U ≤ f ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ U)
    (r : ℕ) :
    ∃ (Y : Scheme.{u}) (y : Y ⟶ S) (Duniv : RelEffCartierDiv f r y), Duniv.IsUniversal := by
  classical

  let F : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
    ⟨RelEffCartierDiv.functor f r, (isSheaf_iff_isSheaf_of_type _ _).2 (RelEffCartierDiv.isSheaf_functor f r)⟩

  let ι : Type u := Σ V : S.affineOpens, {U : 𝒞.affineOpens // (U : 𝒞.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)}
  have hrep : ∀ i : ι, ∃ X : Scheme.{u},
      Nonempty ((RelEffCartierDiv.supportedIn f r (i.2.1 : 𝒞.Opens)).toFunctor.RepresentableBy X) :=
    fun i => by
      obtain ⟨X, -, hX⟩ := RelEffCartierDiv.isRepresentable_supportedIn f r i.1 i.2.1 i.2.2
      exact ⟨X, hX⟩
  choose X hX using hrep
  let e : ∀ i : ι, yoneda.obj (X i) ≅ (RelEffCartierDiv.supportedIn f r (i.2.1 : 𝒞.Opens)).toFunctor :=
    fun i => Functor.representableByEquiv (hX i).some
  let fam : ∀ i : ι, yoneda.obj (X i) ⟶ F.1 :=
    fun i => (e i).hom ≫ (RelEffCartierDiv.supportedIn f r (i.2.1 : 𝒞.Opens)).ι

  have hfam : ∀ i, IsOpenImmersion.presheaf (fam i) := fun i =>
    (MorphismProperty.cancel_left_of_respectsIso _ _ _).2
      (RelEffCartierDiv.isOpenImmersion_presheaf_supportedIn_incl f r _)

  haveI : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc fam) := by
    constructor
    rintro T ⟨g, D⟩
    rw [Scheme.mem_grothendieckTopology_iff]
    choose W hW V U hUV hsupp using
      fun t : T => RelEffCartierDiv.exists_supportedIn_of_forall_finset f hcov r D t
    refine ⟨Scheme.Cover.mkOfCovers T (fun t => (W t : Scheme.{u})) (fun t => (W t).ι)
      (fun t => ⟨t, ⟨t, hW t⟩, rfl⟩) (fun t => inferInstance), ?_⟩
    rintro Y q ⟨t⟩

    let i : ι := ⟨V t, ⟨U t, hUV t⟩⟩
    let sec : (RelEffCartierDiv.supportedIn f r (i.2.1 : 𝒞.Opens)).toFunctor.obj (op (W t : Scheme.{u})) :=
      ⟨(RelEffCartierDiv.functor f r).map (W t).ι.op ⟨g, D⟩, hsupp t⟩
    refine ⟨(Limits.Sigma.ι (fun i => yoneda.obj (X i)) i).app _ ((e i).inv.app _ sec), ?_⟩
    have h1 : (Limits.Sigma.desc fam).app (op (W t : Scheme.{u}))
        ((Limits.Sigma.ι (fun i => yoneda.obj (X i)) i).app _ ((e i).inv.app _ sec)) =
        (fam i).app _ ((e i).inv.app _ sec) := by
      rw [← types_comp_apply ((Limits.Sigma.ι (fun i => yoneda.obj (X i)) i).app _)
          ((Limits.Sigma.desc fam).app _),
        ← NatTrans.comp_app, Limits.Sigma.ι_desc]
    change (Limits.Sigma.desc fam).app (op (W t : Scheme.{u}))
        ((Limits.Sigma.ι (fun i => yoneda.obj (X i)) i).app _ ((e i).inv.app _ sec)) =
      (RelEffCartierDiv.functor f r).map (W t).ι.op ⟨g, D⟩
    rw [h1]
    change ((e i).inv.app _ ≫ (e i).hom.app _ ≫ (RelEffCartierDiv.supportedIn f r _).ι.app _) sec = _
    rw [Iso.inv_hom_id_app_assoc]
    rfl

  have hR : (RelEffCartierDiv.functor f r).IsRepresentable :=
    Scheme.LocalRepresentability.isRepresentable hfam
  exact (RelEffCartierDiv.isRepresentable_functor_iff f r).1 hR
