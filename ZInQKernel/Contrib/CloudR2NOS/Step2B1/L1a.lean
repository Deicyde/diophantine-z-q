/-
H5 lane C3 STEP-F9 fix edition (2026-11-17). Source only. The change relative to its base is recorded in the C3 fix ledger.
-/
/-
H5 lane3 Step 2, B1 KEY (L1.a) `StalkIdealIndependent` (L1Plan.lean) PROVED from Mathlib.
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
  -- STEP-F9: the germ/restriction identity is used as a term (the restriction morphism is formed
  -- in `X.Opens`, where `TopCat.Presheaf.germ_res` lives), not found by `rw`.
  have hgU : X.presheaf.map (homOfLE (show W ≤ U.1 from hWU)).op ≫ X.presheaf.germ W x hxW =
      X.presheaf.germ U.1 x hxU := X.presheaf.germ_res _ x hxW
  have hgV : X.presheaf.map (homOfLE (show W ≤ V.1 from hWV)).op ≫ X.presheaf.germ W x hxW =
      X.presheaf.germ V.1 x hxV := X.presheaf.germ_res _ x hxW
  have hU : Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U) =
      Ideal.map (X.presheaf.germ W x hxW).hom (I.ideal W') := by
    rw [← Scheme.IdealSheafData.map_ideal I hWU, Ideal.map_map, ← CommRingCat.hom_comp]
    exact congrArg (fun φ => Ideal.map (CommRingCat.Hom.hom φ) (I.ideal U)) hgU.symm
  have hV : Ideal.map (X.presheaf.germ V.1 x hxV).hom (I.ideal V) =
      Ideal.map (X.presheaf.germ W x hxW).hom (I.ideal W') := by
    rw [← Scheme.IdealSheafData.map_ideal I hWV, Ideal.map_map, ← CommRingCat.hom_comp]
    exact congrArg (fun φ => Ideal.map (CommRingCat.Hom.hom φ) (I.ideal V)) hgV.symm
  rw [hU, hV]

/-- STEP-F9 helper: the stalk is the localization at `y`, for any point `x` equal to `fromSpec y`
(stated for a variable point, so the equation can be substituted). -/
private theorem isLocalization_stalk_at_L1a {X : Scheme.{u}} (U : X.affineOpens)
    (y : PrimeSpectrum Γ(X, U.1)) (x : X) (hxy : U.2.fromSpec y = x) (hxU : x ∈ U.1) :
    @IsLocalization.AtPrime Γ(X, U.1) _ (X.presheaf.stalk x) _
      (TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩) y.asIdeal _ := by
  subst hxy
  exact U.2.isLocalization_stalk' y hxU

/-- STEP-F9 helper: transport and transport back along a ring equivalence. -/
private theorem ideal_map_symm_map_eq_L1a {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (I : Ideal R) : Ideal.map e.symm (Ideal.map e I) = I := by
  rw [Ideal.map_symm]
  exact Ideal.comap_map_of_bijective e e.bijective

/-- STEP-F9 helper: mapping along `e₁.trans e₂.symm` is mapping along `e₁`, then `e₂.symm`. -/
private theorem ideal_map_trans_symm_eq_L1a {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (e₁ : R ≃+* S) (e₂ : T ≃+* S) (I : Ideal R) :
    Ideal.map (e₁.trans e₂.symm) I = Ideal.map e₂.symm (Ideal.map e₁ I) := by
  rw [← Ideal.map_coe (f := e₁.trans e₂.symm), ← Ideal.map_coe (f := e₂.symm),
    ← Ideal.map_coe (f := e₁), Ideal.map_map]
  congr 1
  all_goals exact RingHom.ext fun _ => rfl

theorem stalkIdealIndependent : StalkIdealIndependent.{u} := by
  intro X I U V p q hpq
  -- STEP-F9: the common point as a plain variable, with both chart equations.
  obtain ⟨x, hxp⟩ : ∃ x : X, U.2.fromSpec p = x := ⟨_, rfl⟩
  have hxq : V.2.fromSpec q = x := hpq.symm.trans hxp
  have hxU : x ∈ U.1 := by
    rw [← hxp]
    show U.2.fromSpec p ∈ (U.1 : Set X)
    rw [← U.2.range_fromSpec]
    exact ⟨p, rfl⟩
  have hxV : x ∈ V.1 := by
    rw [← hxq]
    show V.2.fromSpec q ∈ (V.1 : Set X)
    rw [← V.2.range_fromSpec]
    exact ⟨q, rfl⟩
  -- the stalk as a localization of both charts
  letI algU : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  haveI locU : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    isLocalization_stalk_at_L1a U p x hxp hxU
  let τU : Localization.AtPrime p.asIdeal ≃ₐ[Γ(X, U.1)] X.presheaf.stalk x :=
    IsLocalization.algEquiv p.asIdeal.primeCompl _ _
  let eU : Localization.AtPrime p.asIdeal ≃+* X.presheaf.stalk x := τU.toRingEquiv
  have hτU : ∀ J : Ideal Γ(X, U.1),
      Ideal.map eU (Ideal.map (algebraMap Γ(X, U.1) (Localization.AtPrime p.asIdeal)) J) =
        Ideal.map (X.presheaf.germ U.1 x hxU).hom J := by
    intro J
    rw [← Ideal.map_coe (f := eU), Ideal.map_map]
    congr 1
    all_goals exact RingHom.ext fun r => τU.commutes r
  letI algV : Algebra Γ(X, V.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  haveI locV : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal :=
    isLocalization_stalk_at_L1a V q x hxq hxV
  let τV : Localization.AtPrime q.asIdeal ≃ₐ[Γ(X, V.1)] X.presheaf.stalk x :=
    IsLocalization.algEquiv q.asIdeal.primeCompl _ _
  let eV : Localization.AtPrime q.asIdeal ≃+* X.presheaf.stalk x := τV.toRingEquiv
  have hτV : ∀ J : Ideal Γ(X, V.1),
      Ideal.map eV (Ideal.map (algebraMap Γ(X, V.1) (Localization.AtPrime q.asIdeal)) J) =
        Ideal.map (X.presheaf.germ V.1 x hxV).hom J := by
    intro J
    rw [← Ideal.map_coe (f := eV), Ideal.map_map]
    congr 1
    all_goals exact RingHom.ext fun r => τV.commutes r
  refine ⟨eU.trans eV.symm, ?_⟩
  rw [ideal_map_trans_symm_eq_L1a eU eV, hτU, germ_ideal_eq I U V x hxU hxV, ← hτV,
    ideal_map_symm_map_eq_L1a eV]

end ZInQ.Contrib.CloudR2NOS.Step2B1
