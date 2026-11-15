import ZInQKernel.Contrib.OneProof.QuotientP1.P1ModelA
import ZInQKernel.Contrib.OneProof.QuotientP1.P1Scheme
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk

/-!
# p1-quot3, helper (L4 part B): extending sections over points of codimension `≥ 2`

Generated from `scratch/p1-quot3/L4B.lean`: `extend_top`, `extend_open` (from the vendored extension theorem for
morphisms to affine schemes). No `sorry`, no `axiom`.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Polynomial Opposite

namespace HDec.MCRGlue.P1Model

/-- **Global sections extend over points of codimension `≥ 2`** on a locally noetherian scheme with normal domain
stalks (from the vendored extension theorem for morphisms to affine schemes, with target `Spec ℤ[X]`). -/
theorem extend_top {T : Scheme.{0}} [IsLocallyNoetherian T]
    (hT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x))
    (W : T.Opens) (hW : ∀ x : T, ringKrullDim (T.presheaf.stalk x) ≤ 1 → x ∈ W) (s : Γ(T, W)) :
    ∃ f : Γ(T, ⊤), T.presheaf.map (homOfLE le_top : W ⟶ ⊤).op f = s := by
  set s' : Γ(W.toScheme, ⊤) := W.topIso.inv s
  set ψ : CommRingCat.of ℤ[X] ⟶ Γ(W.toScheme, ⊤) :=
    CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) s')
  let v : W.toScheme ⟶ Spec (CommRingCat.of ℤ[X]) := W.toScheme.toSpecΓ ≫ Spec.map ψ
  obtain ⟨φ, hφ, -⟩ :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk
      hT W hW v
  refine ⟨φ.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv Polynomial.X), ?_⟩
  have h1 : W.ι.appTop (φ.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv Polynomial.X)) = s' := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hφ]
    simp only [v, Scheme.Hom.comp_appTop]
    rw [ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply _ (Spec.map ψ).appTop,
      ← Scheme.ΓSpecIso_inv_naturality, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      Scheme.toSpecΓ_appTop, Iso.inv_hom_id, CommRingCat.id_apply]
    exact Polynomial.eval₂_X _ _
  rw [← QuotientP1Proof.topIso_hom_ι_appTop, h1]
  exact Iso.inv_hom_id_apply _ _

/-- **Sections over an open `V ⊆ U` containing the points of `U` of codimension `≤ 1` extend to `U`.** -/
theorem extend_open {X : Scheme.{0}} [IsLocallyNoetherian X]
    (hN : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (U V : X.Opens) (hVU : V ≤ U)
    (hV : ∀ x : X, x ∈ U → ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V) (s : Γ(X, V)) :
    ∃ f : Γ(X, U), X.presheaf.map (homOfLE hVU).op f = s := by
  haveI : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have hT : ∀ x : U.toScheme, IsDomain (U.toScheme.presheaf.stalk x) ∧
      IsIntegrallyClosed (U.toScheme.presheaf.stalk x) := by
    intro x
    let e := (U.stalkIso x).commRingCatIsoToRingEquiv
    obtain ⟨h1, h2⟩ := hN x.1
    exact ⟨Function.Injective.isDomain e.toRingHom e.injective, IsIntegrallyClosed.of_equiv e.symm⟩
  set W : U.toScheme.Opens := U.ι ⁻¹ᵁ V
  have hW : ∀ x : U.toScheme, ringKrullDim (U.toScheme.presheaf.stalk x) ≤ 1 → x ∈ W := by
    intro x hx
    rw [ringKrullDim_eq_of_ringEquiv (U.stalkIso x).commRingCatIsoToRingEquiv] at hx
    exact hV x.1 x.2 hx
  obtain ⟨fT, hfT⟩ := extend_top hT W hW (U.ι.app V s)
  have hUtop : U ≤ U.ι ''ᵁ ⊤ := fun x hx => ⟨⟨x, hx⟩, trivial, rfl⟩
  have hWsub : U.ι ''ᵁ W ≤ U.ι ''ᵁ ⊤ := U.ι.image_mono le_top
  have hWV : U.ι ''ᵁ W ≤ V := by
    rintro _ ⟨y, hy, rfl⟩; exact hy
  have hVW : V ≤ U.ι ''ᵁ W := fun x hx => ⟨⟨x, hVU hx⟩, hx, rfl⟩
  let f0 : Γ(X, U.ι ''ᵁ ⊤) := fT
  have hfT' : X.presheaf.map (homOfLE hWsub).op f0 = X.presheaf.map (homOfLE hWV).op s := hfT
  refine ⟨X.presheaf.map (homOfLE hUtop).op f0, ?_⟩
  rw [Scheme.presheaf_map_map, ← Scheme.presheaf_map_map hWsub hVW, hfT', Scheme.presheaf_map_map]
  simp

end HDec.MCRGlue.P1Model
