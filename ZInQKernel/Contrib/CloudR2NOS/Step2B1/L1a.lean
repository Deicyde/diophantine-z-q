/-
H5 lane3 Step 2, B1 KEY (L1.a) `StalkIdealIndependent` (L1Plan.lean 8272a66b) PROVED from Mathlib.
2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

Proof. Let `x` be the common point and `S := O_x`.
* Mathlib `IsAffineOpen.isLocalization_stalk'` makes `S` a localization of `Γ(U)` at `p` (via
  the germ) and of `Γ(V)` at `q`. `IsLocalization.algEquiv` gives
  `τ_U : Γ(U)_p ≃ S` and `τ_V : Γ(V)_q ≃ S`; set `τ := τ_U ≫ τ_V⁻¹`.
* `τ_U (loc_p (I U)) = germ_U (I U)` and `τ_V (loc_q (I V)) = germ_V (I V)`
  (`AlgEquiv.commutes`, `Ideal.map_map`).
* `germ_U (I U) = germ_V (I V)`: choose an affine `W ∋ x` with `W ≤ U ⊓ V` (affine basis). Then
  `germ_U = res ≫ germ_W` (`germ_res`), and Mathlib `IdealSheafData.map_ideal` gives
  `res (I U) = I W`, and likewise for `V`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.L1Plan

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2NOS.Step2B1

/-- The stalk ideal computed on any affine chart is the same. -/
theorem germ_ideal_eq {X : Scheme.{u}} (I : X.IdealSheafData) (U V : X.affineOpens) (x : X)
    (hxU : x ∈ U.1) (hxV : x ∈ V.1) :
    Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U) =
      Ideal.map (X.presheaf.germ V.1 x hxV).hom (I.ideal V) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (U.1 ⊓ V.1 : X.Opens) from
      ⟨hxU, hxV⟩) (U.1 ⊓ V.1).isOpen
  let W' : X.affineOpens := ⟨W, hW⟩
  have hWU : W' ≤ U := fun _ h => (hWUV h).1
  have hWV : W' ≤ V := fun _ h => (hWUV h).2
  have hU : Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U) =
      Ideal.map (X.presheaf.germ W x hxW).hom (I.ideal W') := by
    rw [← Scheme.IdealSheafData.map_ideal I hWU, Ideal.map_map, ← CommRingCat.hom_comp,
      TopCat.Presheaf.germ_res]
  have hV : Ideal.map (X.presheaf.germ V.1 x hxV).hom (I.ideal V) =
      Ideal.map (X.presheaf.germ W x hxW).hom (I.ideal W') := by
    rw [← Scheme.IdealSheafData.map_ideal I hWV, Ideal.map_map, ← CommRingCat.hom_comp,
      TopCat.Presheaf.germ_res]
  rw [hU, hV]

theorem stalkIdealIndependent : StalkIdealIndependent.{u} := by
  intro X I U V p q hpq
  set x := U.2.fromSpec p with hx
  have hxU : x ∈ U.1 := by rw [← U.2.range_fromSpec]; exact ⟨p, rfl⟩
  have hxV : x ∈ V.1 := by rw [hx, hpq, ← V.2.range_fromSpec]; exact ⟨q, rfl⟩
  -- the stalk as a localization of both charts
  letI algU : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  haveI locU : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    U.2.isLocalization_stalk' p hxU
  let τU : Localization.AtPrime p.asIdeal ≃ₐ[Γ(X, U.1)] X.presheaf.stalk x :=
    IsLocalization.algEquiv p.asIdeal.primeCompl _ _
  have hτU : ∀ J : Ideal Γ(X, U.1),
      Ideal.map τU (Ideal.map (algebraMap Γ(X, U.1) (Localization.AtPrime p.asIdeal)) J) =
        Ideal.map (X.presheaf.germ U.1 x hxU).hom J := by
    intro J
    rw [Ideal.map_map]
    congr 1
    ext r
    exact τU.commutes r
  -- the same for `V` (the stalk at `V.fromSpec q = x`)
  have hxq : V.2.fromSpec q = x := hpq.symm
  letI algV : Algebra Γ(X, V.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  haveI locV : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal := by
    have h := V.2.isLocalization_stalk' q (hxq ▸ hxV)
    rw [hxq] at h
    exact h
  let τV : Localization.AtPrime q.asIdeal ≃ₐ[Γ(X, V.1)] X.presheaf.stalk x :=
    IsLocalization.algEquiv q.asIdeal.primeCompl _ _
  have hτV : ∀ J : Ideal Γ(X, V.1),
      Ideal.map τV (Ideal.map (algebraMap Γ(X, V.1) (Localization.AtPrime q.asIdeal)) J) =
        Ideal.map (X.presheaf.germ V.1 x hxV).hom J := by
    intro J
    rw [Ideal.map_map]
    congr 1
    ext r
    exact τV.commutes r
  refine ⟨τU.toRingEquiv.trans τV.symm.toRingEquiv, ?_⟩
  have hsymm : ∀ J : Ideal (Localization.AtPrime q.asIdeal),
      Ideal.map τV.symm.toRingEquiv (Ideal.map τV J) = J := by
    intro J
    rw [Ideal.map_map]
    convert Ideal.map_id J
    ext a
    simp
  calc Ideal.map (τU.toRingEquiv.trans τV.symm.toRingEquiv)
        (Ideal.map (algebraMap Γ(X, U.1) (Localization.AtPrime p.asIdeal)) (I.ideal U))
      = Ideal.map τV.symm.toRingEquiv (Ideal.map τU
          (Ideal.map (algebraMap Γ(X, U.1) (Localization.AtPrime p.asIdeal)) (I.ideal U))) := by
        rw [Ideal.map_map]
        rfl
    _ = Ideal.map τV.symm.toRingEquiv (Ideal.map (X.presheaf.germ V.1 x hxV).hom (I.ideal V)) := by
        rw [hτU, germ_ideal_eq I U V x hxU hxV]
    _ = Ideal.map (algebraMap Γ(X, V.1) (Localization.AtPrime q.asIdeal)) (I.ideal V) := by
        rw [← hτV, hsymm]

end ZInQ.Contrib.CloudR2NOS.Step2B1
