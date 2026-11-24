import ZInQKernel.Contrib.OneProof.NeronDVR.RelativePicard
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.AffineSpaceRigidity

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open NeronDVR.GenericFrame

namespace ZInQ.ToricOrthogonality

variable {X Y Q : Scheme.{0}} {p : Y ⟶ X} {s : X ⟶ Y}
  (hs : s ≫ p = 𝟙 X) {M : Y.Modules}

include hs in
private theorem section_le_preimage (U : X.Opens) : U ≤ s ⁻¹ᵁ (p ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, hs, Scheme.Hom.id_preimage]

/-- Pull a frame over a saturated open back along a section of the projection. -/
def frameAt {U : X.Opens} (m : Γ(M, p ⁻¹ᵁ U)) :
    Γ((pullback s).obj M, U) :=
  ((pullback s).obj M).presheaf.map (homOfLE (section_le_preimage hs U)).op
    (pullbackSection s m)

private theorem frameAt_restrict {U V : X.Opens} (h : V ≤ U) (m : Γ(M, p ⁻¹ᵁ U)) :
    frameAt hs (M.presheaf.map (homOfLE (p.preimage_mono h)).op m) =
      ((pullback s).obj M).presheaf.map (homOfLE h).op (frameAt hs m) := by
  simp only [frameAt, pullbackSection_map, presheaf_map_homOfLE_map_homOfLE]

private theorem frameAt_smul {U : X.Opens} (a : Γ(Y, p ⁻¹ᵁ U)) (m : Γ(M, p ⁻¹ᵁ U)) :
    frameAt hs (a • m) = s.appLE _ _ (section_le_preimage hs U) a • frameAt hs m := by
  rw [frameAt, pullbackSection_smul, map_smul, Scheme.Hom.app_eq_appLE,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  rfl

private theorem frameAt_free {U : X.Opens} {m : Γ(M, p ⁻¹ᵁ U)} (hm : IsFreeGenerator m) :
    IsFreeGenerator (frameAt hs m) :=
  (hm.pullbackSection s).map _

theorem section_appLE_projection {U : X.Opens} (v : Γ(X, U)) :
    s.appLE _ _ (section_le_preimage hs U) (p.app U v) = v := by
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE s p U (p ⁻¹ᵁ U) U le_rfl (section_le_preimage hs U)]
  have step {f g : X ⟶ X} (h : f = g) (hf : U ≤ f ⁻¹ᵁ U) (hg : U ≤ g ⁻¹ᵁ U) :
      f.appLE U U hf = g.appLE U U hg := by subst h; rfl
  rw [step hs _ (by rw [Scheme.Hom.id_preimage])]
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  change (X.presheaf.map (homOfLE (le_rfl : U ≤ U)).op) v = v
  rw [show (homOfLE (le_rfl : U ≤ U)) = 𝟙 U from rfl, op_id]
  rw [X.presheaf.map_id]
  rfl

/-- A frame over a saturated open can be normalized to a given frame on the section. -/
theorem exists_normalized_frame {U : X.Opens} {m : Γ(M, p ⁻¹ᵁ U)}
    (hm : IsFreeGenerator m) {v : Γ((pullback s).obj M, U)} (hv : IsFreeGenerator v) :
    ∃ m' : Γ(M, p ⁻¹ᵁ U), IsFreeGenerator m' ∧ frameAt hs m' = v := by
  obtain ⟨u, hu⟩ := (frameAt_free hs hm).exists_unit_smul_eq hv
  let w := Units.map (p.app U).hom.toMonoidHom u
  refine ⟨w.val • m, hm.units_smul w, ?_⟩
  rw [frameAt_smul]
  change s.appLE _ _ (section_le_preimage hs U) (p.app U u.val) • frameAt hs m = v
  rw [section_appLE_projection hs]
  exact hu.symm

/-- Frames of a line bundle that are locally trivial over saturated opens glue
when units normalized at the section come from the auxiliary factor. -/
theorem exists_frame_of_normalized_units [IsIntegral X] [IsIntegral Y]
    (q : Y ⟶ Q)
    (v : Γ((pullback s).obj M, ⊤))
    (hloc : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ m : Γ(M, p ⁻¹ᵁ U),
      IsFreeGenerator m ∧ frameAt hs m = ((pullback s).obj M).presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op v)
    (hsplit : ∀ (W : X.Opens), IsAffineOpen W → (W : Set X).Nonempty →
      ∀ u : Γ(Y, p ⁻¹ᵁ W)ˣ, s.appLE _ _ (section_le_preimage hs W) u.val = 1 →
        ∃ w : Γ(Q, ⊤)ˣ, u.val = q.appLE ⊤ (p ⁻¹ᵁ W) le_top w.val) :
    ∃ m : Γ(M, ⊤), IsFreeGenerator m := by
  classical
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨V, hx₀, m₀, hm₀, he₀⟩ := hloc x₀
  have hD : ((p ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty := by
    refine ⟨s x₀, ?_⟩
    exact section_le_preimage hs V hx₀
  refine (exists_isFreeGenerator_of_locally_extends _ hD m₀ ?_).imp fun _ hm => hm.1
  intro y
  obtain ⟨U, hy, m, hm, he⟩ := hloc (p y)
  obtain ⟨z, hzU, hzV⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen
    ⟨p y, hy⟩ ⟨x₀, hx₀⟩
  obtain ⟨W, hW, hzW, hWle⟩ := exists_isAffineOpen_mem_and_subset (x := z) (U := U ⊓ V) ⟨hzU, hzV⟩
  have hWU : W ≤ U := hWle.trans inf_le_left
  have hWV : W ≤ V := hWle.trans inf_le_right
  obtain ⟨u, hu⟩ := ((hm.map (p.preimage_mono hWU))).exists_unit_smul_eq
    (hm₀.map (p.preimage_mono hWV))
  have hu₁ : s.appLE _ _ (section_le_preimage hs W) u.val = 1 := by
    apply (frameAt_free hs (hm.map (p.preimage_mono hWU))).smul_left_injective
    have heq := congrArg (frameAt hs) hu
    rw [frameAt_smul, frameAt_restrict hs hWV m₀, frameAt_restrict hs hWU m, he, he₀,
      presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE] at heq
    rw [frameAt_restrict hs hWU m, he, presheaf_map_homOfLE_map_homOfLE]
    simpa only [one_smul] using heq.symm
  obtain ⟨w, hw⟩ := hsplit W hW ⟨z, hzW⟩ u hu₁
  let a := Units.map (q.appLE ⊤ (p ⁻¹ᵁ U) le_top).hom.toMonoidHom w
  refine ⟨p ⁻¹ᵁ U, hy, a.val • m, hm.units_smul a, ?_⟩
  have hwV : Nonempty (p ⁻¹ᵁ W : Y.Opens) := ⟨⟨s z, section_le_preimage hs W hzW⟩⟩
  let hsmall : p ⁻¹ᵁ W ≤ (p ⁻¹ᵁ U : Y.Opens) ⊓ p ⁻¹ᵁ V :=
    le_inf (p.preimage_mono hWU) (p.preimage_mono hWV)
  apply restriction_injective_of_isFreeGenerator hsmall (hm.map inf_le_left)
  simp only [Scheme.Modules.map_smul, presheaf_map_homOfLE_map_homOfLE]
  have hr : Y.presheaf.map (homOfLE hsmall).op
      (Y.presheaf.map (homOfLE (inf_le_left : (p ⁻¹ᵁ U : Y.Opens) ⊓ p ⁻¹ᵁ V ≤ _)).op a.val) =
        Y.presheaf.map (homOfLE (p.preimage_mono hWU)).op a.val := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl
  rw [hr]
  change Y.presheaf.map (homOfLE (p.preimage_mono hWU)).op
      (q.appLE ⊤ (p ⁻¹ᵁ U) le_top w.val) •
    M.presheaf.map (homOfLE (p.preimage_mono hWU)).op m =
    M.presheaf.map (homOfLE (p.preimage_mono hWV)).op m₀
  rw [← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_map q le_top (homOfLE (p.preimage_mono hWU)).op, ← hw]
  exact hu.symm

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.exists_frame_of_normalized_units
