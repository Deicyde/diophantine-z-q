import ZInQKernel.Contrib.OneProof.QuotientP1.P1ModelA
import ZInQKernel.Contrib.OneProof.QuotientP1.P1Scheme
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk

/-!
# p1-quot3, L4 part B: extending sections over points of codimension `≥ 2` (scratch)
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

end HDec.MCRGlue.P1Model
