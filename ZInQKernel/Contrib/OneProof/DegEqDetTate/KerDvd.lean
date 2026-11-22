import ZInQKernel.Contrib.OneProof.DegEqDetTate.Reduction

/-!
# deg-det, part 2: `#ker ψ(k̄) ∣ deg ψ`

Task deg-det (2026-11-16), report `docs/research/deg-det.md`.

For an endomorphism `ψ` of an abelian variety `A` over an algebraically closed field `k` with `deg ψ ≠ 0`
(`deg` = `CharPolyEll.degEnd`, the function-field degree): the kernel of `ψ` on `A(k̄)` is finite and its order
divides `deg ψ` (`kerDvdDeg`). Proof: a point `P ∈ ker ψ` gives the translation `τ_P = (A → Spec k̄ → A) · id`
(`τ`), with `τ_P ≫ ψ = ψ`, `τ_{PQ} = τ_Q ≫ τ_P`, and `τ_P = id ⇒ P = 1`; `τ_P` acts on the function field
`K(A)` (`σ`, characterized by `Spec(σ f) ≫ ι = ι ≫ f` for `ι : Spec K(A) → A`), fixing `ψ^* K(A)`
(`stalkMap_comp_σP`) and faithfully (`eq_id_of_σ_eq`, Mathlib's `ext_of_isDominant_of_isSeparated`). So
`ker ψ ↪ Aut(K(A)/ψ^*K(A))`, and Artin's theorem (`IntermediateField.finrank_fixedField_eq_card`) with the
tower law gives `#ker ψ ∣ [K(A) : ψ^*K(A)]`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace ZInQ.Contrib.OneProof.DegDet.KerDvd

open ZInQ.Contrib.OneProof.CharPolyEll

attribute [local instance] isIntegral_left

variable {k : Type} [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k)

local notation "Kb" => AlgebraicClosure k

/-- `k ≃ k̄` (`k` algebraically closed). -/
def eBar : k ≃+* AlgebraicClosure k :=
  RingEquiv.ofBijective (algebraMap k (AlgebraicClosure k))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem eBar_symm_algebraMap (x : k) : (eBar (k := k)).symm (algebraMap k Kb x) = x :=
  (eBar (k := k)).symm_apply_apply x

theorem algebraMap_eBar_symm (y : Kb) : algebraMap k Kb ((eBar (k := k)).symm y) = y :=
  (eBar (k := k)).apply_symm_apply y

/-- The structure morphism `A → Spec k → Spec k̄` (over `k`). -/
def toPt : A.X ⟶ PkgI3.AbVar.ptObj (K := k) Kb :=
  Over.homMk (A.X.hom ≫ Spec.map (CommRingCat.ofHom (eBar (k := k)).symm.toRingHom)) (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    have : ((eBar (k := k)).symm.toRingHom.comp (algebraMap k Kb)) = RingHom.id k := by
      ext x; exact eBar_symm_algebraMap x
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])

theorem pt_comp_toPt (Q : A.Pt Kb) : Q ≫ toPt A = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp only [toPt, Over.comp_left, Over.homMk_left, Over.id_left]
  erw [← Category.assoc, Over.w Q]
  simp only [PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (algebraMap k Kb).comp (eBar (k := k)).symm.toRingHom = RingHom.id Kb := by
    ext y; exact algebraMap_eBar_symm y
  rw [this, CommRingCat.ofHom_id, Spec.map_id]
  rfl

/-- Translation by a `k̄`-point. -/
def τ (P : A.Pt Kb) : A.X ⟶ A.X := (toPt A ≫ P) * 𝟙 A.X

theorem pt_comp_τ (Q P : A.Pt Kb) : Q ≫ τ A P = P * Q := by
  rw [τ, MonObj.comp_mul, ← Category.assoc, pt_comp_toPt, Category.id_comp, Category.comp_id]

theorem τ_comp_toPt (P : A.Pt Kb) : τ A P ≫ toPt A = toPt A := by
  apply Over.OverMorphism.ext
  simp only [toPt, Over.comp_left, Over.homMk_left]
  erw [← Category.assoc, Over.w (τ A P)]

theorem τ_mul (P Q : A.Pt Kb) : τ A (P * Q) = τ A Q ≫ τ A P := by
  have h1 : τ A Q ≫ τ A P = (toPt A ≫ P) * τ A Q := by
    conv_lhs => rw [show τ A P = (toPt A ≫ P) * 𝟙 A.X from rfl]
    rw [MonObj.comp_mul, ← Category.assoc, τ_comp_toPt, Category.comp_id]
  rw [h1]
  change (toPt A ≫ (P * Q)) * 𝟙 A.X = (toPt A ≫ P) * ((toPt A ≫ Q) * 𝟙 A.X)
  rw [MonObj.comp_mul, _root_.mul_assoc]

theorem τ_one : τ A 1 = 𝟙 _ := by
  rw [τ, MonObj.comp_one, _root_.one_mul]

theorem τ_comp_hom {ψ : PkgI3.AbVar.End A} (P : A.Pt Kb) (hP : P ≫ ψ.hom = 1) :
    τ A P ≫ ψ.hom = ψ.hom := by
  rw [τ, MonObj.mul_comp, Category.assoc, hP, MonObj.comp_one, Category.id_comp, _root_.one_mul]

theorem eq_one_of_τ_eq_id (P : A.Pt Kb) (h : τ A P = 𝟙 _) : P = 1 := by
  have := pt_comp_τ A 1 P
  rw [h, Category.comp_id, _root_.mul_one] at this
  exact this.symm

section Stalk

variable {X : Scheme} [IsIntegral X]

/-- The action on the function field of an endomorphism fixing the generic point. -/
def σ (f : X ⟶ X) (hf : f (genericPoint X) = genericPoint X) :
    X.presheaf.stalk (genericPoint X) ⟶ X.presheaf.stalk (genericPoint X) :=
  X.presheaf.stalkSpecializes (show f (genericPoint X) ⤳ genericPoint X by rw [hf]) ≫
    f.stalkMap (genericPoint X)

theorem Spec_σ (f : X ⟶ X) (hf : f (genericPoint X) = genericPoint X) :
    Spec.map (σ f hf) ≫ X.fromSpecStalk (genericPoint X) = X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [σ, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

omit [IsIntegral X] in
theorem eq_of_Spec_comp {R : CommRingCat} (x : X) (a b : X.presheaf.stalk x ⟶ R)
    (h : Spec.map a ≫ X.fromSpecStalk x = Spec.map b ≫ X.fromSpecStalk x) : a = b :=
  Spec.map_injective ((cancel_mono _).mp h)

theorem σ_comp (f g : X ⟶ X) (hf : f (genericPoint X) = genericPoint X)
    (hg : g (genericPoint X) = genericPoint X) (hfg : (f ≫ g) (genericPoint X) = genericPoint X) :
    σ (f ≫ g) hfg = σ g hg ≫ σ f hf := by
  apply eq_of_Spec_comp
  rw [Spec_σ, Spec.map_comp, Category.assoc, Spec_σ]
  conv_rhs => rw [← Category.assoc, Spec_σ]
  rw [Category.assoc]

theorem σ_id (h : (𝟙 X : X ⟶ X) (genericPoint X) = genericPoint X) : σ (𝟙 X) h = 𝟙 _ := by
  apply eq_of_Spec_comp
  rw [Spec_σ, Spec.map_id, Category.id_comp, Category.comp_id]

instance isDominant_fromSpecStalk_genericPoint :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  refine Dense.mono ?_ (dense_iff_closure_eq.mpr (genericPoint_spec X))
  rintro _ rfl
  rw [Scheme.range_fromSpecStalk]
  exact specializes_rfl

/-- Faithfulness: an endomorphism (over a separated base) acting trivially on the function field is `𝟙`. -/
theorem eq_id_of_σ_eq {S : Scheme} (s : X ⟶ S) [IsSeparated s] (f : X ⟶ X) (hfs : f ≫ s = s)
    (hf : f (genericPoint X) = genericPoint X) (h : σ f hf = 𝟙 _) : f = 𝟙 X := by
  refine ext_of_isDominant_of_isSeparated s (by rw [hfs, Category.id_comp])
    (X.fromSpecStalk (genericPoint X)) ?_
  rw [← Spec_σ f hf, h, Spec.map_id, Category.id_comp, Category.comp_id]

end Stalk

section Kernel

open PkgI3.AbVar

theorem σ_congr {X : Scheme} [IsIntegral X] (f g : X ⟶ X) (h : f = g)
    (hf : f (genericPoint X) = genericPoint X) (hg : g (genericPoint X) = genericPoint X) :
    σ f hf = σ g hg := by
  subst h; rfl

variable {A}

theorem τ_left_genericPoint (P : A.Pt Kb) :
    (τ A P).left (genericPoint A.X.left) = genericPoint A.X.left := by
  apply ZInQ.Contrib.OneProof.DegDet.map_genericPoint
  intro y
  refine ⟨(τ A P⁻¹).left y, ?_⟩
  have h : (τ A P⁻¹ ≫ τ A P) = 𝟙 _ := by rw [← τ_mul, _root_.mul_inv_cancel, τ_one]
  have h2 := congrArg (fun t => t.left) h
  simp only [Over.comp_left, Over.id_left] at h2
  rw [← Scheme.Hom.comp_apply, h2]
  rfl

/-- The action of a `k̄`-point on the function field. -/
def σP (P : A.Pt Kb) :
    A.X.left.presheaf.stalk (genericPoint A.X.left) ⟶ A.X.left.presheaf.stalk (genericPoint A.X.left) :=
  σ (τ A P).left (τ_left_genericPoint P)

theorem σP_mul (P Q : A.Pt Kb) : σP (P * Q) = σP P ≫ σP Q := by
  have h := σ_comp (τ A Q).left (τ A P).left (τ_left_genericPoint Q) (τ_left_genericPoint P)
    (by rw [Scheme.Hom.comp_apply, τ_left_genericPoint, τ_left_genericPoint])
  rw [σP, σ_congr (τ A (P * Q)).left ((τ A Q).left ≫ (τ A P).left)
    (by rw [τ_mul]; rfl) _ (by rw [Scheme.Hom.comp_apply, τ_left_genericPoint, τ_left_genericPoint]), h]
  rfl

theorem σP_one : σP (1 : A.Pt Kb) = 𝟙 _ := by
  have h1 : (𝟙 A.X.left : A.X.left ⟶ A.X.left) (genericPoint A.X.left) = genericPoint A.X.left := rfl
  rw [σP, σ_congr (τ A 1).left (𝟙 _) (by rw [τ_one]; rfl) _ h1, σ_id h1]

theorem stalkMap_comp_σP (ψ : End A) (P : A.Pt Kb) (hP : P ≫ ψ.hom = 1) :
    ψ.hom.left.stalkMap (genericPoint A.X.left) ≫ σP P = ψ.hom.left.stalkMap (genericPoint A.X.left) := by
  apply eq_of_Spec_comp
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, σP,
    Spec_σ, Category.assoc]
  congr 1
  have := congrArg (fun t => t.left) (τ_comp_hom A P hP)
  simpa only [Over.comp_left] using this

theorem eq_one_of_σP_eq (P : A.Pt Kb) (h : σP P = 𝟙 _) : P = 1 := by
  apply eq_one_of_τ_eq_id A P
  apply Over.OverMorphism.ext
  exact eq_id_of_σ_eq A.X.hom (τ A P).left (Over.w (τ A P)) _ h

end Kernel

section Artin

open PkgI3.AbVar

variable {A}

theorem σP_apply_mul (P Q : A.Pt Kb) (x) : (σP (P * Q)).hom x = (σP Q).hom ((σP P).hom x) := by
  rw [σP_mul]; rfl

theorem σP_apply_one (x) : (σP (1 : A.Pt Kb)).hom x = x := by
  rw [σP_one]; rfl

/-- **`#ker ψ(k̄)` divides `deg ψ`** (when `deg ψ ≠ 0`; then the kernel is finite): the kernel acts
faithfully on `K(A)` by translations, fixing `ψ^* K(A)`; Artin's theorem. -/
theorem kerDvdDeg (ψ : End A) (hdeg : degEnd ψ ≠ 0) :
    Finite (ptMap (L := Kb) ψ).ker ∧ Nat.card (ptMap (L := Kb) ψ).ker ∣ degEnd ψ := by
  classical
  have hiso := ZInQ.Contrib.OneProof.DegDet.isIsogenyMor_of_degEnd_ne_zero hdeg
  have hψe : ψ.hom.left (genericPoint A.X.left) = genericPoint A.X.left :=
    ZInQ.Contrib.OneProof.DegDet.map_genericPoint _ hiso.2.surj
  let fB : Field (A.X.left.presheaf.stalk (ψ.hom.left (genericPoint A.X.left))) :=
    (ZInQ.Contrib.OneProof.DegDet.isField_stalk _ hψe).toField
  let fK : Field (A.X.left.presheaf.stalk (genericPoint A.X.left)) :=
    (ZInQ.Contrib.OneProof.DegDet.isField_stalk _ rfl).toField
  let alg : Algebra (A.X.left.presheaf.stalk (ψ.hom.left (genericPoint A.X.left)))
      (A.X.left.presheaf.stalk (genericPoint A.X.left)) :=
    (ψ.hom.left.stalkMap (genericPoint A.X.left)).hom.toAlgebra
  have hfr : degEnd ψ = Module.finrank (A.X.left.presheaf.stalk (ψ.hom.left (genericPoint A.X.left)))
      (A.X.left.presheaf.stalk (genericPoint A.X.left)) := by
    unfold degEnd; rw [if_pos hiso]
  set G := (ptMap (L := Kb) ψ).ker
  have hmemG : ∀ P : G, P.1 ≫ ψ.hom = 1 := fun P => P.2
  let ρ0 : G → (A.X.left.presheaf.stalk (genericPoint A.X.left) ≃ₐ[A.X.left.presheaf.stalk (ψ.hom.left (genericPoint A.X.left))] A.X.left.presheaf.stalk (genericPoint A.X.left)) := fun P =>
    { toFun := (σP P.1).hom
      invFun := (σP P.1⁻¹).hom
      left_inv := fun x => by
        change (σP P.1⁻¹).hom ((σP P.1).hom x) = x
        rw [← σP_apply_mul, _root_.mul_inv_cancel, σP_apply_one]
      right_inv := fun x => by
        change (σP P.1).hom ((σP P.1⁻¹).hom x) = x
        rw [← σP_apply_mul, _root_.inv_mul_cancel, σP_apply_one]
      map_mul' := map_mul _
      map_add' := map_add _
      commutes' := fun b => by
        change (σP P.1).hom ((ψ.hom.left.stalkMap (genericPoint A.X.left)).hom b) =
          (ψ.hom.left.stalkMap (genericPoint A.X.left)).hom b
        rw [← CommRingCat.comp_apply, stalkMap_comp_σP ψ P.1 (hmemG P)] }
  let ρ : G →* (A.X.left.presheaf.stalk (genericPoint A.X.left) ≃ₐ[A.X.left.presheaf.stalk (ψ.hom.left (genericPoint A.X.left))] A.X.left.presheaf.stalk (genericPoint A.X.left)) :=
    { toFun := ρ0
      map_one' := by
        ext x
        exact σP_apply_one x
      map_mul' := fun P Q => by
        ext x
        change (σP (P.1 * Q.1)).hom x = (σP P.1).hom ((σP Q.1).hom x)
        rw [_root_.mul_comm, σP_apply_mul] }
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro P hP
    rw [MonoidHom.mem_ker] at hP
    have h1 : σP P.1 = 𝟙 _ := by
      ext x
      have := congrArg (fun e : A.X.left.presheaf.stalk (genericPoint A.X.left) ≃ₐ[A.X.left.presheaf.stalk (ψ.hom.left (genericPoint A.X.left))] A.X.left.presheaf.stalk (genericPoint A.X.left) => e x) hP
      exact this
    exact (Subgroup.mem_bot).mpr (Subtype.ext (eq_one_of_σP_eq P.1 h1))
  have hfd : FiniteDimensional (A.X.left.presheaf.stalk (ψ.hom.left (genericPoint A.X.left))) (A.X.left.presheaf.stalk (genericPoint A.X.left)) := Module.finite_of_finrank_pos (by rw [← hfr]; omega)
  haveI : Finite G := Finite.of_injective ρ hinj
  refine ⟨inferInstance, ?_⟩
  set H := ρ.range
  have hH : Nat.card H = Nat.card G := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h1 := IntermediateField.finrank_fixedField_eq_card H
  have h2 := Module.finrank_mul_finrank (A.X.left.presheaf.stalk (ψ.hom.left (genericPoint A.X.left))) (IntermediateField.fixedField H) (A.X.left.presheaf.stalk (genericPoint A.X.left))
  rw [hfr, ← h2, h1, hH]
  exact Dvd.intro_left _ rfl

end Artin

end ZInQ.Contrib.OneProof.DegDet.KerDvd
