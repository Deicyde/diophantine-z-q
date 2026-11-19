import ZInQKernel.Contrib.OneProof.JDescent5Sections
import ZInQKernel.Contrib.OneProof.JDescent5Parity

/-! The inversion of the group scheme acts on the generic stalk and preserves the identity place. -/

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TauCeti TopologicalSpace

noncomputable section
attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra
set_option maxHeartbeats 1000000

def fixedStalkMap {X : Scheme} (f : X ⟶ X) (p : X) (hp : f p = p) :
    X.presheaf.stalk p ⟶ X.presheaf.stalk p :=
  X.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes ≫ f.stalkMap p

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem fixedStalkMap_involutive {X : Scheme} (f : X ⟶ X) (p : X) (hp : f p = p)
    (hf : f ≫ f = 𝟙 X) : Function.Involutive (fixedStalkMap f p hp) := by
  let s : f p ⤳ p := (Inseparable.of_eq hp).specializes
  have hh : fixedStalkMap f p hp ≫ fixedStalkMap f p hp = 𝟙 _ := by
    change (X.presheaf.stalkSpecializes s ≫ f.stalkMap p) ≫
      (X.presheaf.stalkSpecializes s ≫ f.stalkMap p) = _
    simp only [Category.assoc]
    rw [← f.stalkSpecializes_stalkMap_assoc (f p) p s,
      TopCat.Presheaf.stalkSpecializes_comp_assoc, ← Scheme.Hom.stalkMap_comp,
      Scheme.Hom.stalkMap_congr_hom _ _ hf]
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hU
    simp [TopCat.Presheaf.stalkCongr]
  intro a
  exact congrArg (fun g : X.presheaf.stalk p ⟶ X.presheaf.stalk p => g a) hh

private theorem fixedStalkMap_germ {X : Scheme} (f : X ⟶ X) (p : X) (hp : f p = p)
    (U : X.Opens) (hpU : p ∈ U) (hU : U ≤ f ⁻¹ᵁ U) (u : Γ(X, U)) :
    fixedStalkMap f p hp (X.presheaf.germ U p hpU u) =
      X.presheaf.germ U p hpU (f.appLE U U hU u) := by
  let h : f p ⤳ p := (Inseparable.of_eq hp).specializes
  let hp' : f p ∈ U := h.mem_open U.isOpen hpU
  change f.stalkMap p (X.presheaf.stalkSpecializes h (X.presheaf.germ U p hpU u)) = _
  have h₁ := congrArg (fun g : Γ(X, U) ⟶ X.presheaf.stalk (f p) => g u)
    (X.presheaf.germ_stalkSpecializes hpU h)
  change X.presheaf.stalkSpecializes h (X.presheaf.germ U p hpU u) =
    X.presheaf.germ U (f p) hp' u at h₁
  rw [h₁, f.germ_stalkMap_apply U p hp']
  exact (X.presheaf.germ_res_apply (homOfLE hU) p hpU (f.app U u)).symm

private theorem fixedStalkMap_specializes {X : Scheme} (f : X ⟶ X) {p q : X}
    (hp : f p = p) (hq : f q = q) (h : p ⤳ q) :
    X.presheaf.stalkSpecializes h ≫ fixedStalkMap f p hp =
      fixedStalkMap f q hq ≫ X.presheaf.stalkSpecializes h := by
  simp only [fixedStalkMap, Category.assoc]
  rw [← f.stalkSpecializes_stalkMap p q h]
  simp only [TopCat.Presheaf.stalkSpecializes_comp_assoc]

def abVarInv {L : Type} [Field L] (A : PkgI3.AbVar L) : A.X.left ⟶ A.X.left :=
  ι[A.X].left

private theorem abVarInv_sq {L : Type} [Field L] (A : PkgI3.AbVar L) :
    abVarInv A ≫ abVarInv A = 𝟙 _ :=
  congrArg Over.Hom.left (GrpObj.inv_comp_inv A.X)

private theorem abVarInv_fix_identity {L : Type} [Field L] (A : PkgI3.AbVar L) :
    abVarInv A (abVarIdentity A) = abVarIdentity A := by
  have h : (η[A.X] : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ A.X) ≫ ι[A.X] = η[A.X] := by
    rw [MonObj.one_eq_one]
    change (1 : (𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ A.X))⁻¹ = 1
    exact inv_one
  exact congrArg (fun g : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ A.X =>
    g.left (IsLocalRing.closedPoint L)) h

private theorem abVarInv_fix_generic {L : Type} [Field L] (A : PkgI3.AbVar L) :
    abVarInv A (genericPoint A.X.left) = genericPoint A.X.left := by
  have : IsIso (abVarInv A) := ⟨abVarInv A, abVarInv_sq A, abVarInv_sq A⟩
  exact genericPoint_eq_of_isOpenImmersion (abVarInv A)

def abVarInvFunctionField {L : Type} [Field L] (A : PkgI3.AbVar L) :
    AbVarFunctionField A ≃ₐ[L] AbVarFunctionField A := by
  let X := A.X.left
  let eta :=  genericPoint X
  let w := fixedStalkMap (abVarInv A) eta (abVarInv_fix_generic A)
  have hinv := fixedStalkMap_involutive _ _ (abVarInv_fix_generic A) (abVarInv_sq A)
  let g : AbVarFunctionField A →ₐ[L] AbVarFunctionField A :=
    { toRingHom := w.hom
      commutes' := fun a => by
        let c := (Scheme.ΓSpecIso (CommRingCat.of L)).inv a
        change w (X.presheaf.germ ⊤ eta trivial (A.X.hom.appTop c)) =
          X.presheaf.germ ⊤ eta trivial (A.X.hom.appTop c)
        dsimp only [w]
        rw [fixedStalkMap_germ (abVarInv A) eta (abVarInv_fix_generic A) ⊤ trivial (by simp)]
        have h := congrArg Scheme.Hom.appTop (Over.w (ι[A.X]))
        rw [Scheme.Hom.comp_appTop] at h
        have hconst : (abVarInv A).appTop (A.X.hom.appTop c) = A.X.hom.appTop c :=
          congrArg (fun f : Γ(Spec (CommRingCat.of L), ⊤) ⟶ Γ(X, ⊤) => f c) h
        have htop : (abVarInv A).appLE ⊤ ⊤ (by simp) = (abVarInv A).appTop :=
          (abVarInv A).appLE_eq_app
        rw [htop, hconst] }
  exact AlgEquiv.ofBijective g hinv.bijective

private theorem abVarInvFunctionField_involutive {L : Type} [Field L] (A : PkgI3.AbVar L) :
    Function.Involutive (abVarInvFunctionField A) :=
  fixedStalkMap_involutive _ _ (abVarInv_fix_generic A) (abVarInv_sq A)

private theorem abVarInvFunctionField_map_place {L : Type} [Field L] (A : PkgI3.AbVar L)
    (P : Place L (AbVarFunctionField A))
    (hP : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
      P.integers.toSubring) : P.map (abVarInvFunctionField A) = P := by
  let X := A.X.left
  let eta :=  genericPoint X
  let O := abVarIdentity A
  let w := fixedStalkMap (abVarInv A) O (abVarInv_fix_identity A)
  let α := abVarInvFunctionField A
  let β : X.presheaf.stalk O →+* AbVarFunctionField A := algebraMap (X.presheaf.stalk O) _
  have hcomp (s : X.presheaf.stalk O) : α (β s) = β (w s) :=
    congrArg (fun f : X.presheaf.stalk O ⟶ X.functionField => f s)
      (fixedStalkMap_specializes _ (abVarInv_fix_generic A) (abVarInv_fix_identity A)
        ((genericPoint_spec X).specializes (Set.mem_univ O)))
  have hm {z : AbVarFunctionField A} (hz : z ∈ P.integers.toSubring) :
      α z ∈ P.integers.toSubring := by
    obtain ⟨s, rfl⟩ : z ∈ β.range := hP.symm ▸ hz
    exact hP ▸ ⟨w s, (hcomp s).symm⟩
  apply Place.integers_injective
  ext z
  rw [Place.mem_integers_map_iff]
  have he : α.symm z = α z := α.injective ((α.apply_symm_apply z).trans
    (abVarInvFunctionField_involutive A z).symm)
  rw [he]
  exact ⟨fun hz => (abVarInvFunctionField_involutive A z) ▸ hm hz, hm⟩

theorem abVarInv_stable_punctured {L : Type} [Field L] (A : PkgI3.AbVar L) :
    abVarPunctured A ≤ abVarInv A ⁻¹ᵁ abVarPunctured A := by
  intro z hz
  change abVarInv A z ≠ abVarIdentity A
  intro h
  have h₂ : abVarInv A (abVarInv A z) = z :=
    congrArg (fun f : A.X.left ⟶ A.X.left => f z) (abVarInv_sq A)
  exact hz (h₂.symm.trans ((congrArg (abVarInv A) h).trans (abVarInv_fix_identity A)))

theorem abVarInvFunctionField_section {L : Type} [Field L] (A : PkgI3.AbVar L)
    (U : A.X.left.Opens) [Nonempty U] (hU : U ≤ abVarInv A ⁻¹ᵁ U) (s : Γ(A.X.left, U)) :
    abVarInvFunctionField A (A.X.left.germToFunctionField U s) =
      A.X.left.germToFunctionField U ((abVarInv A).appLE U U hU s) :=
  fixedStalkMap_germ _ _ (abVarInv_fix_generic A) U _ hU s

set_option backward.isDefEq.respectTransparency.types false in
/-- If inversion fixes the generic stalk pointwise it fixes the whole separated scheme. -/
theorem abVarInv_eq_id_of_germInversion_trivial {L : Type} [Field L] (A : PkgI3.AbVar L)
    (h : ∀ z, abVarInvFunctionField A z = z) : abVarInv A = 𝟙 _ := by
  let X := A.X.left
  let eta := genericPoint X
  let f := abVarInv A
  let j := X.fromSpecStalk eta
  have : IsDominant j := ⟨(dense_iff_closure_eq.mpr (genericPoint_closure X)).mono
    (Set.singleton_subset_iff.mpr ⟨_, Scheme.fromSpecStalk_closedPoint⟩)⟩
  have hi : fixedStalkMap f eta (abVarInv_fix_generic A) = 𝟙 _ := by
    apply CommRingCat.hom_ext
    exact RingHom.ext h
  have he : Spec.map (fixedStalkMap f eta (abVarInv_fix_generic A)) ≫ j = j ≫ f := by
    change Spec.map (fixedStalkMap f eta _) ≫ X.fromSpecStalk eta = _
    rw [fixedStalkMap, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  apply AlgebraicGeometry.ext_of_isDominant_of_isSeparated A.X.hom ?_ j
  · rw [← he, hi, Spec.map_id, Category.id_comp, Category.comp_id]
  · exact (Over.w ι[A.X]).trans (Category.id_comp _).symm

theorem abVarInv_abscissa_of_genusOne {L : Type} [Field L] [NumberField L]
    (hgenus : AbVarFunctionFieldGenusOne) (A : PkgI3.AbVar L) (hdim : A.dim = 1)
    (P : Place L (AbVarFunctionField A))
    (hP : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
      P.integers.toSubring) {x y : AbVarFunctionField A} {a b : L}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxo : P.ord x = -2) (hyo : P.ord y = -3)
    (hreg : ∀ Q, Q ≠ P → 0 ≤ Q.ord x ∧ 0 ≤ Q.ord y)
    (heq : y ^ 2 = x ^ 3 + algebraMap L (AbVarFunctionField A) a * x +
      algebraMap L (AbVarFunctionField A) b) :
    abVarInvFunctionField A x = x := by
  obtain ⟨Q, _, hq, hdim', _⟩ := abVar_identityPoleSpaces_of_genusOne hgenus A hdim
  have hQP : Q = P := Place.integers_injective
    (ValuationSubring.toSubring_injective (hq.symm.trans hP))
  subst Q
  have d2 := hdim' 2 (by decide)
  have d3 := hdim' 3 (by decide)
  simp only [TauCeti.AlgebraicGeometry.WeilDivisor.single_eq_zsmul_ofPoint, Divisor.dim_def] at d2 d3
  exact (shortCubic_parity_of_place_involution P d2 d3 _ (abVarInvFunctionField_involutive A)
    (abVarInvFunctionField_map_place A P hP) hx hy hxo hyo hreg heq).1

#print axioms fixedStalkMap_involutive
#print axioms fixedStalkMap_germ
#print axioms fixedStalkMap_specializes
#print axioms abVarInv_sq
#print axioms abVarInv_fix_identity
#print axioms abVarInv_fix_generic
#print axioms abVarInvFunctionField_involutive
#print axioms abVarInvFunctionField_map_place
#print axioms abVarInv_stable_punctured
#print axioms abVarInvFunctionField_section
#print axioms abVarInv_eq_id_of_germInversion_trivial
#print axioms abVarInv_abscissa_of_genusOne

end

end HDec.CMBranch.CMjBridges
