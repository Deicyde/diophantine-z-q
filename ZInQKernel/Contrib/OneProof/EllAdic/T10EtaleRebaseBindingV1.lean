import ZInQKernel.HDecomp.Textbook.T10Etale
import ZInQKernel.Contrib.OneProof.EllAdic.EllAdicHOneRebaseV1

/-!
# The Galois transport of `T10Etale` is the integral pro-étale pullback

`T10Etale.transport ℓ e n` moves pro-étale `ℓ`-adic cohomology along a scheme isomorphism
`e : X ≅ Y` through the sheaf equivalence `T10Etale.sheafEquiv e`, the comparison of constant
sheaves `T10Etale.constIso e` (uniqueness of left adjoints of global sections) and the
identity-on-sections coefficient isomorphism `T10Etale.ellIso ℓ e`. This file proves that in
degree one it is the pullback `ellAdicHOne_rebase e.symm ℓ` along `e⁻¹`:

* `constIso_inv_eq`: the two constant-sheaf comparisons agree;
* `transport_eq_ellAdicHOne_rebase`: `transport ℓ e 1 = ellAdicHOne_rebase e.symm ℓ`;
* `galH_eq_ellAdicHOne_rebase`: the Galois action `T10Etale.galH A ℓ σ` is the pullback along
  `(galIso A σ⁻¹).symm`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace RC53.EllAdic.T10Binding

universe u

variable {X Y : Scheme.{u}}

local instance bindingProEtForward {S T : Scheme.{u}} (σ : S ≅ T) :
    (smallProEtRebaseEquivalence σ).functor.IsContinuous (Scheme.ProEt.topology S)
      (Scheme.ProEt.topology T) :=
  smallProEtRebaseIso_isContinuous σ

local instance bindingProEtInverse {S T : Scheme.{u}} (σ : S ≅ T) :
    (smallProEtRebaseEquivalence σ).inverse.IsContinuous (Scheme.ProEt.topology T)
      (Scheme.ProEt.topology S) :=
  smallProEtRebaseIso_isContinuous σ.symm

/-- `adjR e` sends a map out of the constant sheaf to the value of `toSheafify ≫ f` at the image
of the terminal object. -/
theorem adjR_homEquiv (e : X ≅ Y) {P : Sheaf (Scheme.ProEt.topology Y) Ab.{u+1}}
    (f : (constantSheaf (Scheme.ProEt.topology Y) Ab.{u+1}).obj FiniteAbDictionary.zCoeff ⟶ P) :
    (T10Etale.adjR e).homEquiv _ _ f =
      (toSheafify (Scheme.ProEt.topology Y) ((Functor.const _).obj FiniteAbDictionary.zCoeff) ≫
        f.hom).app (op ((T10Etale.proEtEquiv e).functor.obj (T10Etale.terminalProEt X))) := by
  rw [Adjunction.homEquiv_unit]
  simp only [T10Etale.adjR, constantSheafAdj]
  rw [Adjunction.comp_unit_app]
  simp
  rfl

/-- The unit of `adjL e` at `ℤ` is the sheafification unit at the image of the terminal object. -/
theorem adjL_unit_app (e : X ≅ Y) :
    (T10Etale.adjL e).unit.app FiniteAbDictionary.zCoeff =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const _).obj FiniteAbDictionary.zCoeff)).app
        (op ((T10Etale.proEtEquiv e).inverse.obj
          ((T10Etale.proEtEquiv e).functor.obj (T10Etale.terminalProEt X)))) := by
  rw [← Adjunction.homEquiv_id, T10Etale.adjL, Adjunction.homEquiv_ofNatIsoRight_apply]
  erw [Adjunction.homEquiv_id]
  rw [Adjunction.comp_unit_app]
  simp only [constantSheafAdj]
  rw [Adjunction.comp_unit_app]
  show ((𝟙 _ ≫ (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const _).obj FiniteAbDictionary.zCoeff)).app _) ≫
      ((T10Etale.sheafEquiv e).unit.app _).hom.app _) ≫ 𝟙 _ = _
  rw [Category.comp_id, Category.id_comp]
  show _ ≫ (sheafify (Scheme.ProEt.topology X)
      ((Functor.const _).obj FiniteAbDictionary.zCoeff)).map
      ((T10Etale.proEtEquiv e).op.unitIso.hom.app _) = _
  rw [← NatTrans.naturality]
  exact Category.id_comp _

/-- **The two constant-sheaf comparisons agree.** `T10Etale.constIso e ℤ` is defined by
uniqueness of left adjoints; `proEtConstantRebaseIso e.symm` by the sheafification unit. -/
theorem constIso_inv_eq (e : X ≅ Y) :
    (T10Etale.constIso e FiniteAbDictionary.zCoeff).inv =
      (proEtConstantRebaseIso e.symm).hom.app FiniteAbDictionary.zCoeff := by
  apply ((T10Etale.adjR e).homEquiv _ _).injective
  have h1 : (T10Etale.adjR e).homEquiv _ _ (T10Etale.constIso e FiniteAbDictionary.zCoeff).inv =
      (T10Etale.adjL e).unit.app FiniteAbDictionary.zCoeff :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app (T10Etale.adjR e) (T10Etale.adjL e) _
  have hk := congrArg
    (fun φ => NatTrans.app φ (op ((T10Etale.proEtEquiv e).functor.obj (T10Etale.terminalProEt X))))
    (ConstantSheafTransport.k_toSheafify (smallProEtRebaseEquivalence e.symm)
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) Ab.{u+1} FiniteAbDictionary.zCoeff)
  have h2 := adjR_homEquiv e ((proEtConstantRebaseIso e.symm).hom.app FiniteAbDictionary.zCoeff)
  exact h1.trans ((adjL_unit_app e).trans (hk.symm.trans h2.symm))

/-- **T10's transport is the integral pullback.** In degree one, transport along `e` is the
pullback `ellAdicHOne_rebase e.symm ℓ` along `e⁻¹`. -/
theorem transport_eq_ellAdicHOne_rebase (ℓ : ℕ) [Fact ℓ.Prime] (e : X ≅ Y)
    (x : X.EllAdicCohomology ℓ 1) :
    T10Etale.transport ℓ e 1 x = ellAdicHOne_rebase e.symm ℓ x := by
  have h0 : T10Etale.transport ℓ e 1 x =
      extOneTransport (T10Etale.sheafEquiv e).functor
        (T10Etale.constIso e FiniteAbDictionary.zCoeff).inv (T10Etale.ellIso ℓ e).hom x :=
    (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add 1)).symm
  rw [h0, constIso_inv_eq]
  rfl

/-- **The Galois action of `T10Etale` is a pullback.** `galH A ℓ σ` is the integral pullback
along `(galIso A σ⁻¹).symm`. -/
theorem galH_eq_ellAdicHOne_rebase {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup K)
    (x : (A.baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1) :
    T10Etale.galH A ℓ σ x =
      ellAdicHOne_rebase (T10Etale.galIso A (σ⁻¹ : Field.absoluteGaloisGroup K)).symm ℓ x :=
  transport_eq_ellAdicHOne_rebase ℓ _ x

end RC53.EllAdic.T10Binding
