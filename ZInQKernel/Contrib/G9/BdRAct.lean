import ZInQKernel.Contrib.G9.I4Layer

/-!
# G9: pkg-I4's actions of `G_{ℚ_p}` on `ℂ_p` and on `B_dR` are group actions

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

pkg-I4 (`I4Layer.lean`, verbatim) defines `cpAct p σ` on `ℂ_p` and `bdrAct p σ` on `B_dR` for each
`σ ∈ G_{ℚ_p}` separately. Here: `cpAct (σ τ) = cpAct σ ∘ cpAct τ`, `cpAct 1 = id`, the same for
`bdrAct` (functoriality of Mathlib's `B_dR` construction: mod `p`, tilt, Witt vectors,
localization, adic completion, localization), and the cyclotomic twists `cycPow` are
multiplicative. Packaged as monoid homomorphisms `htAct p i : G_{ℚ_p} →* End_{ℚ_p}(ℂ_p)`
(`c ↦ χ(σ)^i σ(c)`) and `drAct p : G_{ℚ_p} →* End_{ℚ_p}(B_dR)`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open PkgI4 Ideal

noncomputable section

namespace PkgI4.DR

variable (p : ℕ) [Fact p.Prime] {O : Type*} [CommRing O]

theorem modPMap_comp (f g : O →+* O) :
    modPMap p (g.comp f) = (modPMap p g).comp (modPMap p f) := by
  ext x
  rfl

theorem modPMap_id : modPMap p (RingHom.id O) = RingHom.id _ := by
  ext x
  rfl

variable [Fact ¬IsUnit (p : O)]

theorem preTiltMap_comp (f g : O →+* O) :
    preTiltMap p (g.comp f) = (preTiltMap p g).comp (preTiltMap p f) := by
  ext x
  refine Perfection.ext fun n => ?_
  rw [RingHom.comp_apply, coeff_preTiltMap, coeff_preTiltMap, coeff_preTiltMap, modPMap_comp]
  rfl

theorem preTiltMap_id : preTiltMap p (RingHom.id O) = RingHom.id _ := by
  ext x
  refine Perfection.ext fun n => ?_
  rw [coeff_preTiltMap, modPMap_id]
  rfl

theorem locMap_comp (f g : O →+* O) :
    locMap p (g.comp f) = (locMap p g).comp (locMap p f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt O p)))
  ext w
  simp only [RingHom.comp_apply, locMap, Localization.awayLift, IsLocalization.Away.lift,
    IsLocalization.lift_eq]
  congr 1
  ext n
  simp only [WittVector.map_coeff, preTiltMap_comp, RingHom.comp_apply]

theorem locMap_id : locMap p (RingHom.id O) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt O p)))
  ext w
  simp only [RingHom.comp_apply, RingHom.id_apply, locMap, Localization.awayLift,
    IsLocalization.Away.lift, IsLocalization.lift_eq]
  congr 1
  ext n
  simp only [WittVector.map_coeff, preTiltMap_id, RingHom.id_apply]

section AdicComp

variable {A : Type*} [CommRing A] (J : Ideal A)

theorem adicMap_comp' (g0 g : A →+* A) (h0 : J ≤ J.comap g0) (h : J ≤ J.comap g)
    (g' : A →+* A) (h' : J ≤ J.comap g') (hg' : g' = g.comp g0) :
    adicMap J J g' h' = (adicMap J J g h).comp (adicMap J J g0 h0) := by
  subst hg'
  refine RingHom.ext fun x => ?_
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [RingHom.comp_apply, adicMap_evalₐ, adicMap_evalₐ, adicMapAux, adicMapAux,
    RingHom.comp_apply, RingHom.comp_apply]
  erw [adicMap_evalₐ]
  rw [adicMapAux, RingHom.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

theorem adicMap_id' (g' : A →+* A) (h' : J ≤ J.comap g') (hg' : g' = RingHom.id A) :
    adicMap J J g' h' = RingHom.id _ := by
  subst hg'
  refine RingHom.ext fun x => ?_
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [adicMap_evalₐ, adicMapAux, RingHom.comp_apply, RingHom.id_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

end AdicComp

variable [IsAdicComplete (span {(p : O)}) O]

theorem bdrPlusMap_comp (f g : O →+* O) :
    bdrPlusMap p (g.comp f) = (bdrPlusMap p g).comp (bdrPlusMap p f) :=
  adicMap_comp' _ (locMap p f) (locMap p g) (ker_le_comap_locMap p f) (ker_le_comap_locMap p g)
    _ _ (locMap_comp p f g)

theorem bdrPlusMap_id : bdrPlusMap p (RingHom.id O) = RingHom.id _ :=
  adicMap_id' _ _ _ (locMap_id p)

theorem bdrMap_comp (f g f' g' : O →+* O) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y)
    (hgf' : ∀ x, g' (f' x) = x) (hfg' : ∀ y, f' (g' y) = y)
    (h : O →+* O) (k : O →+* O) (hkh : ∀ x, k (h x) = x) (hhk : ∀ y, h (k y) = y)
    (hh : h = f'.comp f) :
    bdrMap p h k hkh hhk = (bdrMap p f' g' hgf' hfg').comp (bdrMap p f g hgf hfg) := by
  subst hh
  unfold bdrMap
  rw [IsLocalization.map_comp_map]
  apply IsLocalization.ringHom_ext (genMonoid p O)
  ext x
  simp only [RingHom.comp_apply, IsLocalization.map_eq, bdrPlusMap_comp]
  erw [IsLocalization.map_eq]
  rfl

theorem bdrMap_id (h : O →+* O) (k : O →+* O) (hkh : ∀ x, k (h x) = x) (hhk : ∀ y, h (k y) = y)
    (hh : h = RingHom.id O) :
    bdrMap p h k hkh hhk = RingHom.id _ := by
  subst hh
  unfold bdrMap
  apply IsLocalization.ringHom_ext (genMonoid p O)
  ext x
  simp only [RingHom.comp_apply, IsLocalization.map_eq, bdrPlusMap_id, RingHom.id_apply]

end PkgI4.DR

namespace PkgI4

variable (p : ℕ) [Fact p.Prime]

theorem cpAct_mul_apply (σ τ : GQp p) (x : ℂ_[p]) :
    cpAct p (σ * τ) x = cpAct p σ (cpAct p τ x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_cpAct p _) ((continuous_cpAct p σ).comp (continuous_cpAct p τ))
  | ih a => rw [cpAct_coe, cpAct_coe, cpAct_coe]; rfl

theorem cpAct_one_apply (x : ℂ_[p]) : cpAct p 1 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_cpAct p _) continuous_id
  | ih a => rw [cpAct_coe]; rfl

theorem oAct_mul (σ τ : GQp p) : oAct p (σ * τ) = (oAct p σ).comp (oAct p τ) := by
  ext x
  exact congrArg Subtype.val (Subtype.ext (cpAct_mul_apply p σ τ x) :
    oAct p (σ * τ) x = oAct p σ (oAct p τ x))

theorem oAct_one : oAct p 1 = RingHom.id _ := by
  ext x
  exact congrArg Subtype.val (Subtype.ext (cpAct_one_apply p x) : oAct p 1 x = x)

theorem bdrAct_mul (σ τ : GQp p) : bdrAct p (σ * τ) = (bdrAct p σ).comp (bdrAct p τ) :=
  DR.bdrMap_comp p _ _ _ _ _ _ _ _ _ _ _ _ (oAct_mul p σ τ)

theorem bdrAct_one : bdrAct p 1 = RingHom.id _ :=
  DR.bdrMap_id p _ _ _ _ (oAct_one p)

theorem cycPow_mul (σ τ : GQp p) (i : ℤ) : cycPow p (σ * τ) i = cycPow p σ i * cycPow p τ i := by
  have h : cyc p (σ * τ) = cyc p σ * cyc p τ := by
    simp only [cyc]
    rw [← map_mul]
    rfl
  simp only [cycPow, h, mul_zpow, Units.val_mul, PadicInt.coe_mul]

theorem cycPow_one (i : ℤ) : cycPow p 1 i = 1 := by
  have h : cyc p 1 = 1 := by
    simp only [cyc]
    rw [← map_one (cyclotomicCharacter (PadicAlgCl p) p)]
    rfl
  simp [cycPow, h]

/-- `σ ↦ (c ↦ χ(σ)^i σ(c))`, the action of `G_{ℚ_p}` on `ℂ_p(i)`, as a monoid homomorphism. -/
def htAct (i : ℤ) : GQp p →* (ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p]) where
  toFun σ :=
    { toFun := fun c => cycPow p σ i • cpAct p σ c
      map_add' := fun a b => by rw [map_add, smul_add]
      map_smul' := fun c a => by
        rw [Algebra.smul_def c a, map_mul, cpAct_algebraMap, ← Algebra.smul_def, smul_comm]
        rfl }
  map_one' := by
    ext c
    simp [cycPow_one, cpAct_one_apply]
  map_mul' σ τ := by
    ext c
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, cycPow_mul,
      cpAct_mul_apply, mul_smul]
    rw [Algebra.smul_def (cycPow p τ i) (cpAct p τ c), map_mul, cpAct_algebraMap,
      ← Algebra.smul_def, smul_comm]

theorem htAct_apply (i : ℤ) (σ : GQp p) (c : ℂ_[p]) :
    htAct p i σ c = cycPow p σ i • cpAct p σ c := rfl

/-- `σ ↦ bdrAct σ`, the action of `G_{ℚ_p}` on `B_dR`, as a monoid homomorphism to
`ℚ_p`-linear endomorphisms. -/
def drAct : GQp p →* (BdR p →ₗ[ℚ_[p]] BdR p) where
  toFun σ :=
    { toFun := bdrAct p σ
      map_add' := map_add _
      map_smul' := bdrAct_smul p σ }
  map_one' := LinearMap.ext fun c => by
    change bdrAct p 1 c = c
    rw [bdrAct_one]
    rfl
  map_mul' σ τ := LinearMap.ext fun c => by
    change bdrAct p (σ * τ) c = bdrAct p σ (bdrAct p τ c)
    rw [bdrAct_mul]
    rfl

theorem drAct_apply (σ : GQp p) (c : BdR p) : drAct p σ c = bdrAct p σ c := rfl

end PkgI4

end

end ZInQ.Contrib.G9
