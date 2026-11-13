import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Sheaves.SheafCondition.Sites

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite

namespace ZariskiConn

/-- A ring map between localizations `A_a → B_{φ a}` compatible with a bijection `φ : A → B` is
bijective. -/
theorem bijective_of_isLocalization_away {A B S T : Type*} [CommRing A] [CommRing B]
    [CommRing S] [CommRing T] [Algebra A S] [Algebra B T] (φ : A →+* B)
    (hφ : Function.Bijective φ) (a : A) [IsLocalization.Away a S]
    [IsLocalization.Away (φ a) T] (ψ : S →+* T)
    (hψ : ψ.comp (algebraMap A S) = (algebraMap B T).comp φ) : Function.Bijective ψ := by
  let e : A ≃+* B := RingEquiv.ofBijective φ hφ
  have H : (Submonoid.powers a).map e.toMonoidHom = Submonoid.powers (φ a) :=
    Submonoid.map_powers _ _
  let e' : S ≃+* T := IsLocalization.ringEquivOfRingEquiv S T e H
  have : ψ = e'.toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers a) ?_
    ext x
    rw [hψ]
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e']
    rw [IsLocalization.ringEquivOfRingEquiv_eq]
    rfl
  rw [this]
  exact e'.bijective

/-- The qcqs lemma for an open written as a basic open. -/
theorem isLocalization_of_eq_basicOpen {X : Scheme} [CompactSpace X] [QuasiSeparatedSpace X]
    (s : Γ(X, ⊤)) (V : X.Opens) (hV : X.basicOpen s = V) :
    letI := (X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op).hom.toAlgebra
    IsLocalization.Away s Γ(X, V) := by
  subst hV
  exact isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ s

/-- `f.app` is bijective on basic opens of an affine target when `f` is qcqs and bijective on
global sections. -/
theorem app_basicOpen_bijective {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] [QuasiCompact f]
    [QuasiSeparated f] (hf : Function.Bijective f.appTop) (r : Γ(Y, ⊤)) :
    Function.Bijective (f.app (Y.basicOpen r)) := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
  have hS : IsLocalization.Away r Γ(Y, Y.basicOpen r) :=
    (isAffineOpen_top Y).isLocalization_basicOpen r
  let _ : Algebra Γ(X, ⊤) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE le_top : f ⁻¹ᵁ Y.basicOpen r ⟶ ⊤).op).hom.toAlgebra
  have hT : IsLocalization.Away (f.appTop.hom r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    isLocalization_of_eq_basicOpen _ _ (f.preimage_basicOpen_top r).symm
  refine bijective_of_isLocalization_away f.appTop.hom hf r (f.app (Y.basicOpen r)).hom ?_
  have := f.naturality (homOfLE (le_top : Y.basicOpen r ≤ ⊤)).op
  ext x
  exact congrArg (fun g => g.hom x) this

/-- **`f_*𝒪_X = 𝒪_Y` from global sections.** For `f : X ⟶ Y` qcqs with `Y` affine, if `f` is
bijective on global sections then it is bijective on the sections over every open of `Y`. -/
theorem app_bijective_of_appTop_bijective {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y]
    [QuasiCompact f] [QuasiSeparated f] (hf : Function.Bijective f.appTop) (U : Y.Opens) :
    Function.Bijective (f.app U) := by
  let φ : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf := ⟨f.c⟩
  have hφ : IsIso φ := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis (B := Y.basicOpen) (isBasis_basicOpen Y) ?_
    intro r
    exact (ConcreteCategory.isIso_iff_bijective _).2 (app_basicOpen_bijective f hf r)
  have : IsIso ((TopCat.Sheaf.forget CommRingCat Y).map φ) := inferInstance
  have : IsIso (((TopCat.Sheaf.forget CommRingCat Y).map φ).app (op U)) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective (f.app U)).1 this

end ZariskiConn
