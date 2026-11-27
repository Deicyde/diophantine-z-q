import ZInQKernel.Contrib.OneProof.ColmezTiltIso.Cp

/-!
# Colmez's `B_dR^+` and `B_dR`, as printed, are the tree's

Colmez, Math. Ann. 292 (1992), §2, p. 632: "Notons encore θ l'homomorphisme de W(R)[p^{-1}] dans
C_p et soit B⁺_dR = lim← W(R)[p^{-1}]/(Ker θ)^n." and "Notons B_dR le corps des fractions de B⁺_dR".
Also: "B⁺_dR est un anneau de valuation discrète, d'idéal maximal Ker θ et de corps résiduel C_p."

* `colmezThetaInvertP : W(R)[1/p] → O[1/p]`, Colmez's `θ` with `p` inverted, and
  `ColmezBdRPlus O p = lim← W(R)[1/p]/(Ker θ)^n` (an `AdicCompletion`), as printed.
* `colmezBdRPlusEquiv : ColmezBdRPlus O p ≃+* BDeRhamPlus O p`: **Colmez's `B_dR^+` is
  Mathlib's**, through `W(colmezEquiv)`; it sends the class of `w ∈ W(R)` to the class of
  `wittEquiv w` (`colmezBdRPlusEquiv_of`).
* For `O = 𝓞_ℂ_[p]`: `ColmezBdRPlus` is a discrete valuation ring
  (`isDiscreteValuationRing_colmezBdRPlus`, from the tree's `isDiscreteValuationRing_BDeRhamPlus`),
  `colmezThetaPlus` (the tree's `thetaPlusCp` transported) extends Colmez's `θ`
  (`colmezThetaPlus_of`), is surjective onto `ℂ_p`, and its kernel is the maximal ideal
  (`ker_colmezThetaPlus`, from `ker_thetaPlusCp` and `maximalIdeal_BDeRhamPlus`).
* `colmezBdREquiv : FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p) ≃+* BdrKer.BdR 𝓞_ℂ_[p] p`: **Colmez's
  `B_dR` (the fraction field) is the tree's `B_dR`** (Mathlib's `BDeRham`), from the tree's
  `isFractionRing_BDeRham`.
-/

namespace ZInQ.Contrib.ColmezTiltIso

set_option linter.unusedSectionVars false

open Ideal WittVector ZInQ.Contrib.G9

section AdicEquiv

variable {A B : Type*} [CommRing A] [CommRing B]

/-- `PkgI4.DR.adicMap` of mutually inverse maps are mutually inverse. -/
theorem adicMap_adicMap (e : A ≃+* B) (J : Ideal A) (J' : Ideal B) (h : J ≤ J'.comap e.toRingHom)
    (h' : J' ≤ J.comap e.symm.toRingHom) (x : AdicCompletion J A) :
    PkgI4.DR.adicMap J' J e.symm.toRingHom h' (PkgI4.DR.adicMap J J' e.toRingHom h x) = x := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [PkgI4.DR.adicMap_evalₐ]
  simp only [PkgI4.DR.adicMapAux, RingHom.comp_apply]
  erw [PkgI4.DR.adicMap_evalₐ]
  simp only [PkgI4.DR.adicMapAux, RingHom.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := J ^ n) (AdicCompletion.evalₐ J n x)
  erw [← ha]
  simp only [Ideal.quotientMap_mk]
  simp

/-- A ring isomorphism `e` with `J = e⁻¹(J')` induces `Â_J ≃ B̂_{J'}`. -/
noncomputable def adicEquiv (e : A ≃+* B) (J : Ideal A) (J' : Ideal B)
    (h : J = J'.comap e.toRingHom) : AdicCompletion J A ≃+* AdicCompletion J' B :=
  have h1 : J ≤ J'.comap e.toRingHom := h.le
  have h2 : J' ≤ J.comap e.symm.toRingHom := fun x hx => by
    rw [Ideal.mem_comap, h, Ideal.mem_comap]
    simpa using hx
  { toFun := PkgI4.DR.adicMap J J' e.toRingHom h1
    invFun := PkgI4.DR.adicMap J' J e.symm.toRingHom h2
    left_inv := adicMap_adicMap e J J' h1 h2
    right_inv := by
      have h3 : J' ≤ J.comap e.symm.symm.symm.toRingHom := h2
      have h4 : J ≤ J'.comap e.symm.symm.toRingHom := h1
      exact adicMap_adicMap e.symm J' J h2 h4
    map_add' := map_add _
    map_mul' := map_mul _ }

theorem adicEquiv_of (e : A ≃+* B) (J : Ideal A) (J' : Ideal B) (h : J = J'.comap e.toRingHom)
    (a : A) : adicEquiv e J J' h (AdicCompletion.of J A a) = AdicCompletion.of J' B (e a) :=
  PkgI4.DR.adicMap_of _ _ _ _ a

end AdicEquiv

variable (O : Type*) [CommRing O] (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

/-- Colmez's `θ` on `W(R)[p^{-1}]`, with values in `O[1/p]` (`= C_p` for `O = O_{C_p}`). -/
noncomputable def colmezThetaInvertP :
    Localization.Away (p : WittVector p (ColmezR O p)) →+* Localization.Away (p : O) :=
  Localization.awayLift ((algebraMap O _).comp (colmezTheta O p)) _ (by
    rw [RingHom.comp_apply, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit _)

/-- **Colmez's `B_dR^+`** (p. 632): `lim← W(R)[p^{-1}]/(Ker θ)^n`. -/
abbrev ColmezBdRPlus :=
  AdicCompletion (RingHom.ker (colmezThetaInvertP O p)) (Localization.Away (p : WittVector p
    (ColmezR O p)))

variable {O p}

/-- `W(R)[1/p] ≅ W(O♭)[1/p]`, induced by `wittEquiv`. -/
noncomputable def locEquiv : Localization.Away (p : WittVector p (ColmezR O p)) ≃+*
    Localization.Away (p : WittVector p (PreTilt O p)) :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (p : WittVector p (ColmezR O p)))
    (T := Submonoid.powers (p : WittVector p (PreTilt O p))) _ _ (wittEquiv (O := O) (p := p)) (by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (map_natCast (wittEquiv (O := O) (p := p)) p))

theorem locEquiv_algebraMap (w : WittVector p (ColmezR O p)) :
    locEquiv (algebraMap _ (Localization.Away (p : WittVector p (ColmezR O p))) w) =
      algebraMap _ _ (wittEquiv w) :=
  IsLocalization.ringEquivOfRingEquiv_eq (M := Submonoid.powers (p : WittVector p (ColmezR O p)))
    (T := Submonoid.powers (p : WittVector p (PreTilt O p)))
    (S := Localization.Away (p : WittVector p (ColmezR O p)))
    (Q := Localization.Away (p : WittVector p (PreTilt O p))) _ w

/-- `θ[1/p]` commutes with the isomorphism: Mathlib's `fontaineThetaInvertP ∘ locEquiv` is
Colmez's `θ` on `W(R)[1/p]`. -/
theorem fontaineThetaInvertP_comp_locEquiv :
    (fontaineThetaInvertP O p).comp locEquiv.toRingHom = colmezThetaInvertP O p := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (ColmezR O p)))
  ext w
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    locEquiv_algebraMap, colmezThetaInvertP, fontaineThetaInvertP, Localization.awayLift,
    IsLocalization.Away.lift, IsLocalization.lift_eq]
  rfl

theorem ker_colmezThetaInvertP :
    RingHom.ker (colmezThetaInvertP O p) =
      (RingHom.ker (fontaineThetaInvertP O p)).comap locEquiv.toRingHom := by
  rw [← fontaineThetaInvertP_comp_locEquiv]
  rfl

/-- **Colmez's `B_dR^+` is Mathlib's `BDeRhamPlus`** (the ring the tree's `B_dR^+` is). -/
noncomputable def colmezBdRPlusEquiv : ColmezBdRPlus O p ≃+* BDeRhamPlus O p :=
  adicEquiv locEquiv _ _ ker_colmezThetaInvertP

theorem colmezBdRPlusEquiv_of (w : WittVector p (ColmezR O p)) :
    colmezBdRPlusEquiv (AdicCompletion.of _ _ (algebraMap _ _ w)) =
      BdrKer.ofPlus O p (algebraMap _ _ (wittEquiv w)) := by
  have h := adicEquiv_of (locEquiv (O := O) (p := p)) _ _ ker_colmezThetaInvertP (algebraMap _ _ w)
  rw [locEquiv_algebraMap] at h
  exact h

/-! ### Over `O_{C_p}` -/

variable (p)

instance isDomain_colmezBdRPlus : IsDomain (ColmezBdRPlus 𝓞_ℂ_[p] p) :=
  MulEquiv.isDomain (BDeRhamPlus 𝓞_ℂ_[p] p) colmezBdRPlusEquiv.toMulEquiv

instance isLocalRing_colmezBdRPlus : IsLocalRing (ColmezBdRPlus 𝓞_ℂ_[p] p) :=
  colmezBdRPlusEquiv.symm.isLocalRing

/-- **Colmez's `B_dR^+` is a discrete valuation ring** (p. 632), from the tree's
`isDiscreteValuationRing_BDeRhamPlus`. -/
theorem isDiscreteValuationRing_colmezBdRPlus :
    IsDiscreteValuationRing (ColmezBdRPlus 𝓞_ℂ_[p] p) := by
  have hD := BdrKer.Cp.isDiscreteValuationRing_BDeRhamPlus p
  have : IsPrincipalIdealRing (ColmezBdRPlus 𝓞_ℂ_[p] p) :=
    IsPrincipalIdealRing.of_surjective colmezBdRPlusEquiv.symm colmezBdRPlusEquiv.symm.surjective
  refine IsDiscreteValuationRing.mk fun h => ?_
  exact hD.not_a_field' (IsLocalRing.isField_iff_maximalIdeal_eq.mp
    (MulEquiv.isField (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
      colmezBdRPlusEquiv.symm.toMulEquiv))

/-- `θ` on Colmez's `B_dR^+`: the tree's `thetaPlusCp` through `colmezBdRPlusEquiv`. -/
noncomputable def colmezThetaPlus : ColmezBdRPlus 𝓞_ℂ_[p] p →+* ℂ_[p] :=
  (BdrKer.Cp.thetaPlusCp p).comp colmezBdRPlusEquiv.toRingHom

/-- `colmezThetaPlus` **extends Colmez's `θ`** on `W(R)`. -/
theorem colmezThetaPlus_of (w : WittVector p (ColmezR 𝓞_ℂ_[p] p)) :
    colmezThetaPlus p (AdicCompletion.of _ _ (algebraMap _ _ w)) =
      (colmezTheta 𝓞_ℂ_[p] p w : ℂ_[p]) := by
  change BdrKer.Cp.thetaPlusCp p (colmezBdRPlusEquiv _) = _
  rw [colmezBdRPlusEquiv_of, thetaPlusCp_ofPlus_wittEquiv]

theorem colmezThetaPlus_surjective : Function.Surjective (colmezThetaPlus p) :=
  (BdrKer.Cp.thetaPlusCp_surjective p).comp colmezBdRPlusEquiv.surjective

/-- **`Ker θ` is the maximal ideal of Colmez's `B_dR^+`** (p. 632; residue field `ℂ_p` by
`colmezThetaPlus_surjective`), from the tree's `ker_thetaPlusCp` and `maximalIdeal_BDeRhamPlus`. -/
theorem ker_colmezThetaPlus :
    RingHom.ker (colmezThetaPlus p) = IsLocalRing.maximalIdeal (ColmezBdRPlus 𝓞_ℂ_[p] p) := by
  have h1 : RingHom.ker (colmezThetaPlus p) =
      (RingHom.ker (BdrKer.Cp.thetaPlusCp p)).comap colmezBdRPlusEquiv.toRingHom := rfl
  rw [h1, BdrKer.Cp.ker_thetaPlusCp, ← BdrKer.Cp.maximalIdeal_BDeRhamPlus]
  ext x
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, not_iff_not]
  exact isUnit_map_iff (colmezBdRPlusEquiv (O := 𝓞_ℂ_[p]) (p := p)) x

/-- **Colmez's `B_dR` is the tree's `B_dR`**: the fraction field of Colmez's `B_dR^+` is
isomorphic to Mathlib's `BDeRham 𝓞_ℂ_[p] p`, compatibly with `colmezBdRPlusEquiv`. -/
noncomputable def colmezBdREquiv :
    FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p) ≃+* BdrKer.BdR 𝓞_ℂ_[p] p :=
  haveI := BdrKer.Cp.isFractionRing_BDeRham p
  IsFractionRing.ringEquivOfRingEquiv (colmezBdRPlusEquiv (O := 𝓞_ℂ_[p]) (p := p))

theorem colmezBdREquiv_algebraMap (x : ColmezBdRPlus 𝓞_ℂ_[p] p) :
    colmezBdREquiv p (algebraMap _ _ x) = algebraMap _ _ (colmezBdRPlusEquiv x) :=
  have := BdrKer.Cp.isFractionRing_BDeRham p
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (colmezBdRPlusEquiv (O := 𝓞_ℂ_[p]) (p := p)) x

end ZInQ.Contrib.ColmezTiltIso
