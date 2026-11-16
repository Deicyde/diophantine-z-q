/-
Source port from openai/math, revision 4eaee87548250b2682affda7d05d947c05554bae.
Upstream: lean/OAI/AlgebraicGeometry/FormalGeometry/Completion/Finite/GroupAnnihilator.lean
Git blob SHA-1: 260714323bd22e89689b30e59b7df503659490ad
Upstream SHA-256: 28100a234b0415307dc09c4a6d97152f307058ce3b7f744ac50f44d7228f1612
License: Apache-2.0; see the contribution root LICENSE and NOTICE.md.
Adaptations: external imports relocated under the contribution Vendor directory;
namespace relocation to MilneQuasiInverse.Vendor.OAI. Proof bodies are otherwise preserved.
Source-only port; elaboration at the target pins has not been run.
-/

import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Vendor.OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RankAnnihilation
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Vendor.OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation

/-! # Group Annihilator -/

namespace MilneQuasiInverse.Vendor.OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupAnnihilator

noncomputable section

/-! A positive integer annihilates an actual finite commutative group
scheme over a field. The Hopf algebra norm calculation retains all
infinitesimal points; reducedness is not required. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u

theorem group_power_of_iso {S : Scheme.{u}} {G H : Grp (Over S)}
    (e : G ≅ H) (n : ℕ) (hG : (𝟙 G.X) ^ n = 1) : (𝟙 H.X) ^ n = 1 := by
  let a : H.X ⟶ G.X := e.inv.hom.hom
  let b : G.X ⟶ H.X := e.hom.hom.hom
  have : IsMonHom b := inferInstanceAs (IsMonHom e.hom.hom.hom)
  have he : a ≫ b = 𝟙 H.X := congrArg (fun f : H ⟶ H => f.hom.hom) e.inv_hom_id
  have ha : a ^ n = 1 :=
    (congrArg (fun f => f ^ n) (Category.comp_id a)).symm.trans
      ((MonObj.comp_pow (𝟙 G.X) n a).symm.trans
        ((congrArg (fun f => a ≫ f) hG).trans (MonObj.comp_one a)))
  exact (congrArg (fun f => f ^ n) he).symm.trans
    ((MonObj.pow_comp a n b).symm.trans
      ((congrArg (fun f => f ≫ b) ha).trans (MonObj.one_comp b)))

theorem finiteGroup_exists_annihilator (k : Type u) [Field k]
    (G : Grp (Over (Spec (CommRingCat.of k)))) [IsCommMonObj G.X] [IsFinite G.X.hom] :
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X), x ^ n = 1 := by
  obtain ⟨R, hR, hc, ⟨e⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k G
  have : Module.Finite k R := hR
  have : Coalgebra.IsCocomm k R := hc
  have : Nontrivial R := (Bialgebra.counitAlgHom k R).toRingHom.domain_nontrivial
  have hp : (𝟙 ((hopfSpec (CommRingCat.of k)).obj (.op R)).X) ^ Module.finrank k R = 1 := by
    have h := AbelianScheme.CartierDuality.RankAnnihilation.Construction.NormCharacters.affineGroup_power_card k R (Module.finBasis k R)
    simp only [Fintype.card_fin] at h
    change (𝟙 ((hopfSpec (CommRingCat.of k)).obj (.op R)).X) ^ Module.finrank k R = 1 at h
    exact h
  have hG := group_power_of_iso e (Module.finrank k R) hp
  refine ⟨Module.finrank k R, Module.finrank_pos, fun T x => ?_⟩
  have h := congrArg (fun a : G.X ⟶ G.X => x ≫ a) hG
  simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using h

end Construction

end

end MilneQuasiInverse.Vendor.OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupAnnihilator
