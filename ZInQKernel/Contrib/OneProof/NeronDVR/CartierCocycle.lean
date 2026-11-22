import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.CanonicalSection
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Hilbert.SectionPencil.Divisor
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.HomSection
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.Tensor
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorPower
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.Multiplication

/-!
# Descent cocycles from Cartier divisors

A section with Cartier zero scheme determines morphisms between invertible
modules. Pulling back the section along the two overlap projections gives
a unique compatible comparison when the zero ideals agree. Uniqueness
forces the cocycle on the triple overlap.
-/


open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {L M : X.Modules} [L.IsInvertible] [M.IsInvertible]

omit [M.IsInvertible] in
/-- On an affine chart trivializing both line bundles, cancellation of a
Cartier section reduces to cancellation of a regular element. -/
private theorem app_eq_of_cartierSection_comp_eq
    (s : unit X ⟶ L) (hD : s.zeroLocus.IsInvertible)
    (f g : L ⟶ M) (h : s ≫ f = s ≫ g)
    (V : X.affineOpens) {e : Γ(L, V.1)} {e' : Γ(M, V.1)}
    (he : IsFreeGenerator e) (he' : IsFreeGenerator e') (m : Γ(L, V.1)) :
    f.app V.1 m = g.app V.1 m := by
  obtain ⟨a, ha⟩ := he.exists_smul_eq (s.app V.1 (1 : Γ(X, V.1)))
  have hI : s.zeroLocus.ideal V = Ideal.span {a} :=
    s.ideal_zeroLocus V (isFreeGenerator_one V.1) he ha.symm
  have hr : a ∈ nonZeroDivisors Γ(X, V.1) := hD.mem_nonZeroDivisors hI
  obtain ⟨b, hb⟩ := he'.exists_smul_eq (f.app V.1 e)
  obtain ⟨c, hc⟩ := he'.exists_smul_eq (g.app V.1 e)
  have hab : a * b = a * c := by
    apply he'.smul_left_injective
    change (a * b) • e' = (a * c) • e'
    rw [mul_smul, mul_smul, hb, hc, ← Hom.app_smul, ← Hom.app_smul, ha]
    exact congrArg (fun F : unit X ⟶ M => F.app V.1 (1 : Γ(X, V.1))) h
  have hbc : b = c := (mul_cancel_left_mem_nonZeroDivisors hr).mp hab
  have heg : f.app V.1 e = g.app V.1 e := hb.symm.trans (hbc ▸ hc)
  obtain ⟨r, rfl⟩ := he.exists_smul_eq m
  rw [Hom.app_smul, Hom.app_smul, heg]

set_option backward.isDefEq.respectTransparency false in
/-- A morphism between invertible modules is determined by its value on a
section with effective Cartier zero locus. -/
theorem hom_eq_of_cartierSection_comp_eq
    (s : unit X ⟶ L) (hD : s.zeroLocus.IsInvertible)
    (f g : L ⟶ M) (h : s ≫ f = s ≫ g) : f = g := by
  refine hom_ext _ _ fun U => ?_
  ext m
  have key (x : U) : ∃ V : X.affineOpens, x.1 ∈ V.1 ∧ V.1 ≤ U ∧
      (∃ e : Γ(L, V.1), IsFreeGenerator e) ∧ ∃ e' : Γ(M, V.1), IsFreeGenerator e' := by
    obtain ⟨V, hxV, hVU, hL, e', he'⟩ := exists_isFreeGenerator₂ L M x.2
    exact ⟨V, hxV, hVU, hL, e', he'⟩
  choose V hxV hVU hL hM using key
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    (fun x => (V x).1) U (fun x => homOfLE (hVU x))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV _⟩) _ _ fun x => ?_
  rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
  obtain ⟨_, he⟩ := hL x
  obtain ⟨_, he'⟩ := hM x
  exact app_eq_of_cartierSection_comp_eq s hD f g h (V x) he he' _

private def sectionToDual (s : unit X ⟶ L) : Lᵛ ⟶ unit X :=
  (λ_ Lᵛ).inv ≫ (s ▷ Lᵛ) ≫ dualEvaluation L

private theorem zeroLocus_sectionToDual (s : unit X ⟶ L) :
    (sectionToDual s).zeroLocus = s.zeroLocus := by
  rw [← s.zeroLocus_whiskerRight Lᵛ]
  exact Hom.zeroLocus_eq_of_arrowIso _ _
    (Arrow.isoMk' _ _ (λ_ Lᵛ).symm (asIso (dualEvaluation L)).symm
      (by simp [sectionToDual]))

private theorem iso_comp_comparison {C : Type*} [Category C] {A B I U : C}
    (e : A ≅ I) (f : B ≅ I) (q : I ⟶ U) (a : A ⟶ U) (b : B ⟶ U)
    (he : e.hom ≫ q = a) (hf : f.hom ≫ q = b) :
    (e ≪≫ f.symm).hom ≫ b = a := by
  rw [← hf, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, he]

omit [M.IsInvertible] in
private theorem exists_iso_toModules_of_zeroLocus_eq
    (a : L ⟶ unit X) (I : X.IdealSheafData) (h : a.zeroLocus = I) (hI : I.IsInvertible) :
    ∃ i : L ≅ I.toModules, i.hom ≫ I.toModulesι = a := by
  subst I
  exact a.exists_iso_toModules_zeroLocus hI

private theorem exists_sameIdeal_comparison
    (a : L ⟶ unit X) (b : M ⟶ unit X)
    (hab : a.zeroLocus = b.zeroLocus) (ha : a.zeroLocus.IsInvertible) :
    ∃ e : L ≅ M, e.hom ≫ b = a := by
  obtain ⟨i, hi⟩ := a.exists_iso_toModules_zeroLocus ha
  obtain ⟨j, hj⟩ := exists_iso_toModules_of_zeroLocus_eq b a.zeroLocus hab.symm ha
  exact ⟨i ≪≫ j.symm, iso_comp_comparison i j _ a b hi hj⟩

private theorem exists_sectionToDual_comparison
    (s : unit X ⟶ L) (t : unit X ⟶ M)
    (h : s.zeroLocus = t.zeroLocus) (hD : s.zeroLocus.IsInvertible) :
    ∃ e : Lᵛ ≅ Mᵛ, e.hom ≫ sectionToDual t = sectionToDual s :=
  exists_sameIdeal_comparison (sectionToDual s) (sectionToDual t)
    ((zeroLocus_sectionToDual s).trans (h.trans (zeroLocus_sectionToDual t).symm))
    ((zeroLocus_sectionToDual s).symm ▸ hD)

/-- Tensoring on the right by an invertible module is an equivalence. -/
private def tensorRightEquiv (P : X.Modules) [P.IsInvertible] : X.Modules ≌ X.Modules := by
  let F := tensoringRight X.Modules
  let cancel (A B : X.Modules) (e : A ⊗ B ≅ 𝟙_ X.Modules) :
      F.obj A ⋙ F.obj B ≅ 𝟭 X.Modules :=
    NatIso.ofComponents (fun T => (α_ T A B) ≪≫ whiskerLeftIso T e ≪≫ ρ_ T)
      (fun f => by
        change ((f ▷ A) ▷ B) ≫ _ = _ ≫ f
        simp only [Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
        rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
          rightUnitor_naturality])
  exact CategoryTheory.Equivalence.mk (F.obj P) (F.obj Pᵛ) (cancel P Pᵛ (tensorObjDualIsoUnit P)).symm
    (cancel Pᵛ P ((β_ _ _) ≪≫ tensorObjDualIsoUnit P))

set_option backward.isDefEq.respectTransparency false in
/-- Sections with the same effective Cartier zero scheme determine a
section-preserving isomorphism between their invertible modules. -/
theorem exists_iso_of_cartierSection_zeroLocus_eq
    (s : unit X ⟶ L) (t : unit X ⟶ M)
    (h : s.zeroLocus = t.zeroLocus) (hD : s.zeroLocus.IsInvertible) :
    ∃ e : L ≅ M, s ≫ e.hom = t := by
  obtain ⟨e, he⟩ := exists_sectionToDual_comparison s t h hD
  let cL := tensorObjDualIsoUnit L
  let cM : M ⊗ Lᵛ ≅ 𝟙_ X.Modules := whiskerLeftIso M e ≪≫ tensorObjDualIsoUnit M
  let F := (tensorRightEquiv Lᵛ).functor
  let f : F.obj L ≅ F.obj M := cL ≪≫ cM.symm
  let g := F.preimageIso f
  refine ⟨g, F.map_injective ?_⟩
  rw [Functor.map_comp]
  have hg : F.map g.hom = f.hom := F.map_preimage f.hom
  rw [hg]
  change (s ▷ Lᵛ) ≫ cL.hom ≫ cM.inv = t ▷ Lᵛ
  apply (cancel_mono cM.hom).mp
  rw [Category.assoc, Category.assoc, cM.inv_hom_id, Category.comp_id]
  apply (cancel_epi (λ_ Lᵛ).inv).mp
  exact he.symm.trans (by
    dsimp [sectionToDual, cM]
    rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
    rfl)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.SectionPencil

open Scheme.Modules

variable {X Y Z : Scheme.{u}} {L M : X.Modules}

@[reassoc]
private theorem pullbackSectionHom_map_comp (f : Y ⟶ X)
    (s : unit X ⟶ L) (t : L ⟶ M) :
    pullbackSectionHom f s ≫ (Scheme.Modules.pullback f).map t =
      pullbackSectionHom f (s ≫ t) := by
  simp only [pullbackSectionHom, Category.assoc]
  exact congrArg (fun g => (pullbackObjUnitIso f).inv ≫ g)
    ((Scheme.Modules.pullback f).map_comp s t).symm

private theorem pullbackSectionHom_app_one (f : Y ⟶ X) (s : unit X ⟶ L) :
    (pullbackSectionHom f s).app ⊤ (1 : Γ(Y, ⊤)) =
      pullbackSection f (U := ⊤) (s.app ⊤ (1 : Γ(X, ⊤))) :=
  (pullbackSection_app_one f s).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem pullbackSectionHom_comp_hom (b : Z ⟶ Y) (a : Y ⟶ X) (s : unit X ⟶ L) :
    pullbackSectionHom b (pullbackSectionHom a s) ≫ (pullbackComp b a).hom.app L =
      pullbackSectionHom (b ≫ a) s := by
  apply unit_hom_ext
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, pullbackSectionHom_app_one,
    pullbackSection_pullbackSection]
  have eq := (pullbackComp b a).inv_hom_id_app L
  exact congrArg (fun h => (Hom.app h ⊤) (pullbackSection (b ≫ a) (U := ⊤)
    (s.app ⊤ (1 : Γ(X, ⊤))))) eq

@[reassoc]
theorem pullbackSectionHom_comp_inv (b : Z ⟶ Y) (a : Y ⟶ X) (s : unit X ⟶ L) :
    pullbackSectionHom (b ≫ a) s ≫ (pullbackComp b a).inv.app L =
      pullbackSectionHom b (pullbackSectionHom a s) := by
  rw [← pullbackSectionHom_comp_hom b a s, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

@[reassoc]
theorem pullbackSectionHom_congr_hom {a₁ a₂ : Y ⟶ X} (h : a₁ = a₂) (s : unit X ⟶ L) :
    pullbackSectionHom a₁ s ≫ (pullbackCongr h).hom.app L = pullbackSectionHom a₂ s := by
  subst a₂
  simp [pullbackCongr]

@[reassoc]
theorem pullbackSectionHom_congr_inv {a₁ a₂ : Y ⟶ X} (h : a₁ = a₂) (s : unit X ⟶ L) :
    pullbackSectionHom a₂ s ≫ (pullbackCongr h).inv.app L = pullbackSectionHom a₁ s := by
  subst a₂
  simp [pullbackCongr]

variable [L.IsInvertible]

/-- Compatibility with a Cartier section determines the cocycle on every
triple overlap. -/
theorem cocycle_of_cartierSection (s : unit X ⟶ L) (hD : s.zeroLocus.IsInvertible)
    (a₁ a₂ : Y ⟶ X) (b₁₂ b₁₃ b₂₃ : Z ⟶ Y) [Flat (b₁₃ ≫ a₁)]
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁)
    (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁)
    (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (ψ : (Scheme.Modules.pullback a₁).obj L ≅ (Scheme.Modules.pullback a₂).obj L)
    (hs : pullbackSectionHom a₁ s ≫ ψ.hom = pullbackSectionHom a₂ s) :
    ((pullbackCongr h₁).app L).symm ≪≫
      ((pullbackComp b₁₂ a₁).app L).symm ≪≫
      (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((pullbackComp b₁₂ a₂).app L) ≪≫
      ((pullbackCongr h₂).app L) ≪≫ ((pullbackComp b₂₃ a₁).app L).symm ≪≫
      (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((pullbackComp b₂₃ a₂).app L) ≪≫
      ((pullbackCongr h₃).app L).symm
    = ((pullbackComp b₁₃ a₁).app L).symm ≪≫
      (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((pullbackComp b₁₃ a₂).app L) := by
  have hD' : (pullbackSectionHom (b₁₃ ≫ a₁) s).zeroLocus.IsInvertible := by
    rw [pullbackSectionHom_zeroLocus]
    exact hD.comap_of_flat _
  apply Iso.ext
  apply hom_eq_of_cartierSection_comp_eq _ hD'
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  rw [pullbackSectionHom_congr_inv_assoc h₁ s,
    pullbackSectionHom_comp_inv_assoc b₁₂ a₁ s,
    pullbackSectionHom_map_comp_assoc, hs, pullbackSectionHom_comp_hom_assoc,
    pullbackSectionHom_congr_hom_assoc h₂ s, pullbackSectionHom_comp_inv_assoc,
    pullbackSectionHom_map_comp_assoc, hs, pullbackSectionHom_comp_hom_assoc,
    pullbackSectionHom_congr_inv h₃ s, pullbackSectionHom_comp_inv_assoc,
    pullbackSectionHom_map_comp_assoc, hs, pullbackSectionHom_comp_hom]

/-- Equal Cartier zero ideals under two flat pullbacks give a comparison of
their divisor line bundles preserving the canonical section. -/
theorem exists_pullback_comparison_of_cartierSection (s : unit X ⟶ L)
    (hD : s.zeroLocus.IsInvertible) (a₁ a₂ : Y ⟶ X) [Flat a₁]
    (hI : s.zeroLocus.comap a₁ = s.zeroLocus.comap a₂) :
    ∃ ψ : (Scheme.Modules.pullback a₁).obj L ≅ (Scheme.Modules.pullback a₂).obj L,
      pullbackSectionHom a₁ s ≫ ψ.hom = pullbackSectionHom a₂ s := by
  apply exists_iso_of_cartierSection_zeroLocus_eq
  · simpa only [pullbackSectionHom_zeroLocus] using hI
  · rw [pullbackSectionHom_zeroLocus]
    exact hD.comap_of_flat _

end AlgebraicGeometry.SectionPencil

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The square of the divisor line bundle has a section with zero ideal the
product of two copies of the original Cartier ideal. -/
theorem IsInvertible.exists_zeroLocus_tensorSquare {X : Scheme.{u}} {D : X.IdealSheafData}
    (hD : D.IsInvertible) :
    letI := hD.isInvertible_dual_toModules
    ∃ s : 𝟙_ X.Modules ⟶ D.toModulesᵛ.tensorPow 2, s.zeroLocus = D * D := by
  let hD₂ := hD.mul_effectiveCartier hD
  have := hD.isInvertible_toModules
  have := hD₂.isInvertible_toModules
  have := hD.isInvertible_dual_toModules
  have := hD₂.isInvertible_dual_toModules
  have hpow : Scheme.Pic.mk (D.toModulesᵛ.tensorPow 2) = (Scheme.Pic.mk D.toModulesᵛ) ^ 2 := by
    rw [pow_two, ← Scheme.Pic.mk_tensorObj]
    exact (Scheme.Pic.mk_eq_mk_iff _ _).mpr ⟨Iso.refl _ ⊗ᵢ ρ_ _⟩
  have heq : Scheme.Pic.mk (D * D).toModulesᵛ = Scheme.Pic.mk (D.toModulesᵛ.tensorPow 2) := by
    rw [Scheme.Pic.mk_dual, Scheme.Pic.mk_toModules_mul hD hD, mul_inv,
      ← Scheme.Pic.mk_dual, hpow, pow_two]
  obtain ⟨e⟩ := (Scheme.Pic.mk_eq_mk_iff _ _).mp heq
  exact hD₂.exists_zeroLocus_eq_of_iso e

end AlgebraicGeometry.Scheme.IdealSheafData
