import ZInQKernel.HDecomp.Faltings.Leaves

/-! # height-bc: the natural map of a base change of group models (construction) -/

namespace ZInQ.HeightBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

/-- `Spec 𝓞_{L'} → Spec 𝓞_L`. -/
noncomputable abbrev bO (L L' : Type) [Field L] [Field L'] [Algebra L L'] :
    Spec (CommRingCat.of (𝓞 L')) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))

section Construction

variable {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']

theorem bO_genericPt : bO L L' (genericPt L') = genericPt L := by
  change PrimeSpectrum.comap (algebraMap (𝓞 L) (𝓞 L')) (genericPt L') = _
  refine PrimeSpectrum.ext ?_
  show Ideal.comap (algebraMap (𝓞 L) (𝓞 L')) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 L'))

theorem bO_appTop (r : 𝓞 L) :
    (bO L L').appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r) =
      (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).inv (algebraMap (𝓞 L) (𝓞 L') r) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).hom
      ((bO L L').appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) =
        algebraMap (𝓞 L) (𝓞 L') r := by
    rw [← CommRingCat.comp_apply, h, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    rfl
  rw [← h3, Iso.hom_inv_id_apply]

variable (𝒢 : GroupModel A L) (𝒢' : GroupModel A L')
  (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)

/-- `e` is an isomorphism of group schemes (the content of `IsBaseChangeOf`). -/
def IsMonBC : Prop :=
  letI : GrpObj ((Over.pullback (bO L L')).obj 𝒢.G) := Functor.grpObjObj
  IsMonHom e.hom

/-- The projection `π : 𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'} → 𝒢`. -/
noncomputable def bcProj : 𝒢'.G.left ⟶ 𝒢.G.left := e.hom.left ≫ pullback.fst _ _

theorem bcProj_w : bcProj 𝒢 𝒢' e ≫ 𝒢.G.hom = 𝒢'.G.hom ≫ bO L L' := by
  unfold bcProj
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  congr 1
  exact Over.w e.hom

variable {𝒢 𝒢' e} in
theorem bcProj_unit (he : IsMonBC 𝒢 𝒢' e) :
    𝒢'.unitSection ≫ bcProj 𝒢 𝒢' e = bO L L' ≫ 𝒢.unitSection := by
  let _ : GrpObj ((Over.pullback (bO L L')).obj 𝒢.G) := Functor.grpObjObj
  have : IsMonHom e.hom := he
  have h1 : (η[𝒢'.G] ≫ e.hom).left = (η[(Over.pullback (bO L L')).obj 𝒢.G]).left :=
    congrArg Over.Hom.left (IsMonHom.one_hom (f := e.hom))
  have hε : (Functor.LaxMonoidal.ε (Over.pullback (bO L L'))).left ≫ pullback.fst _ _ =
      bO L L' := by
    have hw := Over.w (Functor.LaxMonoidal.ε (Over.pullback (bO L L')))
    have hc := pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom)
      (g := bO L L')
    calc _ = (Functor.LaxMonoidal.ε (Over.pullback (bO L L'))).left ≫
          (pullback.fst _ _ ≫ (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom) := by
            exact congrArg (fun k => _ ≫ k) (Category.comp_id _).symm
      _ = (Functor.LaxMonoidal.ε (Over.pullback (bO L L'))).left ≫ pullback.snd _ _ ≫ bO L L' := by
            rw [hc]
      _ = bO L L' := by
            rw [← Category.assoc]
            erw [hw]
            exact Category.id_comp _
  unfold GroupModel.unitSection bcProj
  rw [← Category.assoc, ← Over.comp_left]
  erw [h1]
  show (Functor.LaxMonoidal.ε _ ≫ (Over.pullback (bO L L')).map η[𝒢.G]).left ≫ pullback.fst _ _ = _
  have hmap : ((Over.pullback (bO L L')).map η[𝒢.G]).left ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ η[𝒢.G].left := pullback.lift_fst _ _ _
  rw [Over.comp_left, Category.assoc]
  erw [hmap]
  rw [← Category.assoc]
  erw [hε]

variable {𝒢 𝒢' e} in
theorem bcProj_genericUnit (he : IsMonBC 𝒢 𝒢' e) :
    bcProj 𝒢 𝒢' e 𝒢'.genericUnit = 𝒢.genericUnit := by
  have h2 := congrArg (fun φ => φ (genericPt L')) (bcProj_unit he)
  unfold GroupModel.genericUnit
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  simp only
  rw [bO_genericPt]

variable {𝒢 𝒢' e}

/-- The comparison `𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}` along `π` (`π(ξ') = ξ`). -/
noncomputable def bcMap (he : IsMonBC 𝒢 𝒢' e) : 𝒢.genStalk ⟶ 𝒢'.genStalk :=
  𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq (bcProj_genericUnit he)).specializes ≫
    (bcProj 𝒢 𝒢' e).stalkMap 𝒢'.genericUnit

/-- `bcMap` is `π^*` on germs. -/
theorem bcMap_germ (he : IsMonBC 𝒢 𝒢' e) (U : 𝒢.G.left.Opens) (hx : 𝒢.genericUnit ∈ U)
    (hx' : 𝒢'.genericUnit ∈ (bcProj 𝒢 𝒢' e) ⁻¹ᵁ U) (s : Γ(𝒢.G.left, U)) :
    (bcMap he) (𝒢.G.left.presheaf.germ U 𝒢.genericUnit hx s) =
      𝒢'.G.left.presheaf.germ ((bcProj 𝒢 𝒢' e) ⁻¹ᵁ U) 𝒢'.genericUnit hx'
        ((bcProj 𝒢 𝒢' e).app U s) := by
  unfold bcMap
  rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

theorem isIso_stalkSpecializes_bcMap (he : IsMonBC 𝒢 𝒢' e) :
    IsIso (𝒢.G.left.presheaf.stalkSpecializes
      (Inseparable.of_eq (bcProj_genericUnit he)).specializes) :=
  Iso.isIso_hom (𝒢.G.left.presheaf.stalkCongr (Inseparable.of_eq (bcProj_genericUnit he)).symm)

theorem bcMap_mem_maximalIdeal (he : IsMonBC 𝒢 𝒢' e) (t : 𝒢.genStalk)
    (ht : t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    bcMap he t ∈ IsLocalRing.maximalIdeal 𝒢'.genStalk := by
  haveI := isIso_stalkSpecializes_bcMap he
  set e' := 𝒢.G.left.presheaf.stalkSpecializes
    (Inseparable.of_eq (bcProj_genericUnit he)).specializes
  have h1 : e' t ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ht ⊢
    intro hu
    apply ht
    have := hu.map (inv e').hom
    rwa [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply] at this
  exact map_nonunit ((bcProj 𝒢 𝒢' e).stalkMap 𝒢'.genericUnit).hom _ h1

/-- `bcMap` is compatible with the structure maps `𝓞_L → 𝓞_{L'}`. -/
theorem bcMap_structMap (he : IsMonBC 𝒢 𝒢' e) (r : 𝓞 L) :
    bcMap he (𝒢.structMap r) = 𝒢'.structMap (algebraMap (𝓞 L) (𝓞 L') r) := by
  have e1 : 𝒢.structMap r = 𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) := rfl
  have e2 : 𝒢'.structMap (algebraMap (𝓞 L) (𝓞 L') r) =
      𝒢'.G.left.presheaf.germ ⊤ 𝒢'.genericUnit trivial
      (𝒢'.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).inv
        (algebraMap (𝓞 L) (𝓞 L') r))) := rfl
  rw [e1, e2, bcMap_germ he ⊤ (show 𝒢.genericUnit ∈ (⊤ : 𝒢.G.left.Opens) from trivial)
    (show 𝒢'.genericUnit ∈ (bcProj 𝒢 𝒢' e) ⁻¹ᵁ (⊤ : 𝒢.G.left.Opens) from trivial)]
  have hw := bcProj_w 𝒢 𝒢' e
  have : 𝒢.G.hom.appTop ≫ (bcProj 𝒢 𝒢' e).appTop = (bO L L').appTop ≫ 𝒢'.G.hom.appTop := by
    rw [← Scheme.Hom.comp_appTop, hw, Scheme.Hom.comp_appTop]
  rw [← bO_appTop, ← CommRingCat.comp_apply (bO L L').appTop, ← this, CommRingCat.comp_apply]
  rfl

/-- The `𝓞_L`-module structure on `ω_{A_{L'}}` by restriction along `𝓞_L → 𝓞_{L'}`. -/
noncomputable abbrev cotRes (𝒢' : GroupModel A L') : Module (𝓞 L) 𝒢'.cotangent :=
  Module.compHom _ (algebraMap (𝓞 L) (𝓞 L'))

/-- **The induced map `ω_{A_L} → ω_{A_{L'}}` on cotangent spaces at the origin** (`π^*`),
semilinear over `𝓞_L → 𝓞_{L'}`. -/
noncomputable def bcCot (he : IsMonBC 𝒢 𝒢' e) :
    𝒢.cotangent →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] 𝒢'.cotangent where
  toFun x := Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒢.genStalk)
    (IsLocalRing.maximalIdeal 𝒢'.genStalk) (bcMap he).hom.toIntAlgHom
    (fun t ht => bcMap_mem_maximalIdeal he t ht) x
  map_add' x y := map_add _ x y
  map_smul' r x := by
    obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ x
    let ψ := (bcMap he).hom.toIntAlgHom
    have h : IsLocalRing.maximalIdeal 𝒢.genStalk ≤
        (IsLocalRing.maximalIdeal 𝒢'.genStalk).comap ψ :=
      fun t ht => bcMap_mem_maximalIdeal he t ht
    change Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒢.genStalk)
        (IsLocalRing.maximalIdeal 𝒢'.genStalk) ψ h (𝒢.structMap r • Ideal.toCotangent _ m) =
      𝒢'.structMap (algebraMap (𝓞 L) (𝓞 L') r) • Ideal.mapCotangent
        (IsLocalRing.maximalIdeal 𝒢.genStalk) (IsLocalRing.maximalIdeal 𝒢'.genStalk) ψ h
        (Ideal.toCotangent _ m)
    rw [← (Ideal.toCotangent _).map_smul, Ideal.mapCotangent_toCotangent,
      Ideal.mapCotangent_toCotangent, ← (Ideal.toCotangent _).map_smul]
    congr 1
    apply Subtype.ext
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, ψ, RingHom.toIntAlgHom_apply]
    rw [bcMap_structMap]

theorem bcCot_dCls (he : IsMonBC 𝒢 𝒢' e) (t : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    bcCot he (𝒢.dCls t) = 𝒢'.dCls ⟨bcMap he t, bcMap_mem_maximalIdeal he t t.2⟩ := rfl

/-! ### The map of Hodge lines `ψ : ⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` -/

open scoped TensorProduct
open ExteriorAlgebra

/-- The `𝓞_L`-module structure on `⋀^g_{𝓞_{L'}} ω_{A_{L'}}` by restriction of scalars. -/
noncomputable abbrev extRes (𝒢' : GroupModel A L') (g : ℕ) :
    Module (𝓞 L) (exteriorPower (𝓞 L') g 𝒢'.cotangent) :=
  Module.compHom _ (algebraMap (𝓞 L) (𝓞 L'))

theorem bcCot_update (he : IsMonBC 𝒢 𝒢' e) {g : ℕ} [DecidableEq (Fin g)]
    (m : Fin g → 𝒢.cotangent) (i : Fin g) (z : 𝒢.cotangent) :
    (fun j => bcCot he (Function.update m i z j)) =
      Function.update (fun j => bcCot he (m j)) i (bcCot he z) := by
  funext j
  exact Function.apply_update (fun _ => bcCot he) m i z j

/-- `v ↦ π^*v₁ ∧ ⋯ ∧ π^*v_g`, alternating over `𝓞_L`. -/
noncomputable def bcAlt (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    letI := extRes (L := L) 𝒢' g
    𝒢.cotangent [⋀^Fin g]→ₗ[𝓞 L] exteriorPower (𝓞 L') g 𝒢'.cotangent :=
  letI := extRes (L := L) 𝒢' g
  { toFun := fun v => exteriorPower.ιMulti (𝓞 L') g (fun i => bcCot he (v i))
    map_update_add' := by
      intro _ m i x y
      simp only [bcCot_update he, map_add]
      exact (exteriorPower.ιMulti (𝓞 L') g).map_update_add _ i _ _
    map_update_smul' := by
      intro _ m i r x
      simp only [bcCot_update he, map_smulₛₗ]
      exact (exteriorPower.ιMulti (𝓞 L') g).map_update_smul _ i _ _
    map_eq_zero_of_eq' := by
      intro v i j hv hij
      exact (exteriorPower.ιMulti (𝓞 L') g).map_eq_zero_of_eq _ (by simp only [hv]) hij }

/-- `⋀^g π^* : ⋀^g_{𝓞_L} ω_{A_L} → ⋀^g_{𝓞_{L'}} ω_{A_{L'}}`, additive and semilinear. -/
noncomputable def bcExt (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    exteriorPower (𝓞 L) g 𝒢.cotangent →+ exteriorPower (𝓞 L') g 𝒢'.cotangent :=
  letI := extRes (L := L) 𝒢' g
  (exteriorPower.alternatingMapLinearEquiv (bcAlt he g)).toAddMonoidHom

theorem bcExt_ιMulti (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (v : Fin g → 𝒢.cotangent) :
    bcExt he g (exteriorPower.ιMulti (𝓞 L) g v) =
      exteriorPower.ιMulti (𝓞 L') g (fun i => bcCot he (v i)) := by
  letI := extRes (L := L) 𝒢' g
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (bcAlt he g) v

theorem bcExt_smul (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (r : 𝓞 L)
    (x : exteriorPower (𝓞 L) g 𝒢.cotangent) :
    bcExt he g (r • x) = algebraMap (𝓞 L) (𝓞 L') r • bcExt he g x := by
  letI := extRes (L := L) 𝒢' g
  exact (exteriorPower.alternatingMapLinearEquiv (bcAlt he g)).map_smul r x

/-- **The natural map of Hodge spaces** `ψ = L' ⊗ ⋀^g π^* : hodgeSpace g → hodgeSpace' g`. -/
noncomputable def bcHodge (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun a : L => AddMonoidHom.mk'
      (fun x => algebraMap L L' a ⊗ₜ[𝓞 L'] bcExt he g x)
      (fun x y => by rw [map_add, TensorProduct.tmul_add]))
      (fun a b => by
        ext x
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add,
          TensorProduct.add_tmul]))
    (fun r a x => by
      simp only [AddMonoidHom.mk'_apply]
      rw [bcExt_smul, ← TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def, map_mul]
      rfl)

theorem bcHodge_tmul (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (a : L)
    (x : exteriorPower (𝓞 L) g 𝒢.cotangent) :
    bcHodge he g (a ⊗ₜ[𝓞 L] x) = algebraMap L L' a ⊗ₜ[𝓞 L'] bcExt he g x := rfl

theorem bcHodge_smul (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (c : L) (v : 𝒢.hodgeSpace g) :
    bcHodge he g (c • v) = algebraMap L L' c • bcHodge he g v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [TensorProduct.smul_tmul', bcHodge_tmul, bcHodge_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- `ψ(1 ⊗ df₁ ∧ ⋯ ∧ df_g) = 1 ⊗ d(π^*f₁) ∧ ⋯ ∧ d(π^*f_g)`. -/
theorem bcHodge_wedge (he : IsMonBC 𝒢 𝒢' e) {g : ℕ}
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    bcHodge he g (𝒢.wedge f) =
      𝒢'.wedge (fun i => ⟨bcMap he (f i), bcMap_mem_maximalIdeal he _ (f i).2⟩) := by
  unfold GroupModel.wedge
  rw [bcHodge_tmul, map_one, bcExt_ιMulti]
  rfl

end Construction

end ZInQ.HeightBC
