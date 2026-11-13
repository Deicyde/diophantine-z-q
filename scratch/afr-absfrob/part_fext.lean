
/-! # afr-absfrob, part 2: `FExtendGen` from the Néron mapping property (leaf I2-NMP)

Appended by `build.sh` after alg-frob-red's `AlgFrobRed.lean` (verbatim copy) and the
absolute-Frobenius part. -/

noncomputable section

namespace AlgFrobRedRed

open CategoryTheory AlgebraicGeometry Limits
open ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

/-- **Galois rigidity of embeddings (proved).** For a normal extension `L/ℚ`, a domain `R` and two
ring maps `ψ₁, ψ₂ : L → R` which agree after some ring map `χ : R → Q` to a nontrivial ring,
`ψ₁ = ψ₂`. (`ψ₂ ℓ` is a root of the minimal polynomial of `ℓ`, which splits in `L`; so
`ψ₂ ℓ = ψ₁ r` for a conjugate `r`, and `χ ∘ ψ₁` is injective.) -/
theorem ringHom_eq_of_normal {L R Q : Type*} [Field L] [Algebra ℚ L] [Normal ℚ L]
    [CommRing R] [IsDomain R] [CommRing Q] [Nontrivial Q]
    (ψ₁ ψ₂ : L →+* R) (χ : R →+* Q) (h : χ.comp ψ₁ = χ.comp ψ₂) : ψ₁ = ψ₂ := by
  ext ℓ
  have hint : IsIntegral ℚ ℓ := Normal.isIntegral inferInstance ℓ
  have hsp := Normal.splits (inferInstance : Normal ℚ L) ℓ
  have hc : ψ₁.comp (algebraMap ℚ L) = ψ₂.comp (algebraMap ℚ L) := RingHom.ext_rat _ _
  have hne : ((minpoly ℚ ℓ).map (algebraMap ℚ L)).map ψ₁ ≠ 0 :=
    Polynomial.map_ne_zero (Polynomial.map_ne_zero (minpoly.ne_zero hint))
  have hroot : ψ₂ ℓ ∈ (((minpoly ℚ ℓ).map (algebraMap ℚ L)).map ψ₁).roots := by
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.map_map, hc,
      ← Polynomial.map_map, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]
  rw [hsp.roots_map ψ₁, Multiset.mem_map] at hroot
  obtain ⟨r, -, hr⟩ := hroot
  have hrl : r = ℓ := (χ.comp ψ₁).injective (by
    show χ (ψ₁ r) = χ (ψ₁ ℓ)
    rw [hr]
    exact (RingHom.congr_fun h ℓ).symm)
  rw [← hr, hrl]

/-- **Morphisms from an integral scheme to `Spec L`, `L/ℚ` normal, agreeing at one field-valued
point, are equal (proved).** Via `Γ(X, ⊤)` (a domain) and `ringHom_eq_of_normal`. -/
theorem hom_spec_eq_of_point {L : Type} [Field L] [Algebra ℚ L] [Normal ℚ L] {X : Scheme.{0}}
    [IsIntegral X] {K : Type} [Field K] (g₁ g₂ : X ⟶ Spec (.of L)) (x : Spec (.of K) ⟶ X)
    (h : x ≫ g₁ = x ≫ g₂) : g₁ = g₂ := by
  apply ext_of_isAffine
  have h' := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h'
  have key := ringHom_eq_of_normal ((Scheme.ΓSpecIso (.of L)).inv ≫ g₁.appTop).hom
    ((Scheme.ΓSpecIso (.of L)).inv ≫ g₂.appTop).hom (x.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
    (by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
      congr 1
      simp only [Category.assoc]
      rw [reassoc_of% h'])
  rw [← cancel_epi (Scheme.ΓSpecIso (.of L)).inv]
  exact CommRingCat.hom_ext key

/-- `Spec` of an injective ring map is dominant (proved; the kernel is `0 ≤ nilradical`). -/
theorem isDominant_Spec_map_of_injective {R S : CommRingCat.{0}} (φ : R ⟶ S)
    (h : Function.Injective φ.hom) : IsDominant (Spec.map φ) := by
  refine ⟨?_⟩
  show DenseRange (PrimeSpectrum.comap φ.hom)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [h (hx.trans (map_zero _).symm)]
  exact zero_mem _

/-- Cancelling `Spec(s)` for an automorphism `s` of `ℚ̄` (proved). -/
theorem spec_aut_cancel (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {X : Scheme.{0}}
    {a b : Spec (.of (AlgebraicClosure ℚ)) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ a =
      Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ b) :
    a = b := by
  have hi : Spec.map (CommRingCat.ofHom (s.symm : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
      Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (s.symm : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp
          (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) = RingHom.id _ from
        RingHom.ext fun x => s.symm_apply_apply x,
      CommRingCat.ofHom_id, Spec.map_id]
  calc a = (Spec.map (CommRingCat.ofHom (s.symm : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
        Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))) ≫ a := by
          rw [hi, Category.id_comp]
    _ = b := by rw [Category.assoc, h, ← Category.assoc, hi, Category.id_comp]

set_option synthInstance.maxHeartbeats 400000 in
/-- The unit section of a base change `(Over.pullback g').mapGrp.obj 𝒜`, followed by the first
projection, is `g'` followed by the unit section of `𝒜` (proved; `sf_eta_fst` for any `g'`). -/
theorem pb_eta_fst {S S' : Scheme.{0}} (g' : S' ⟶ S) (𝒜 : Grp (Over S)) :
    (η[((Over.pullback g').mapGrp.obj 𝒜).X]).left ≫ pullback.fst 𝒜.X.hom g' =
      g' ≫ (η[𝒜.X]).left := by
  let F := Over.pullback g'
  have hε : (Functor.LaxMonoidal.ε F).left ≫ pullback.snd (𝟙 S) g' = 𝟙 _ :=
    Over.w (Functor.LaxMonoidal.ε F)
  have hε2 : (Functor.LaxMonoidal.ε F).left ≫ pullback.fst (𝟙 S) g' = g' := by
    have hc : pullback.fst (𝟙 S) g' = pullback.snd (𝟙 S) g' ≫ g' := by
      rw [← pullback.condition, Category.comp_id]
    rw [hc, ← Category.assoc, hε, Category.id_comp]
  have hmap : (F.map η[𝒜.X]).left ≫ pullback.fst 𝒜.X.hom g' =
      pullback.fst (𝟙 S) g' ≫ (η[𝒜.X]).left := pullback.lift_fst _ _ _
  show ((Functor.LaxMonoidal.ε F) ≫ F.map η[𝒜.X]).left ≫ pullback.fst 𝒜.X.hom g' = _
  rw [Over.comp_left, Category.assoc, hmap, ← Category.assoc, hε2]

/-- `Spec(O_w → L)`. -/
abbrev jSpec (L : IF) (v : ValuationSubring PkgI4.Qbar) :
    Spec (.of L) ⟶ Spec (.of (Ow L v)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))

/-- `Spec(t)`, `t = σ⁻¹|_{O_w}`. -/
abbrev tSpec {L : IF} [IsGalois ℚ L] {v : ValuationSubring PkgI4.Qbar} (σ : PkgI4.GQ)
    (hσ : σ ∈ v.decompositionSubgroup ℚ) : Spec (.of (Ow L v)) ⟶ Spec (.of (Ow L v)) :=
  Spec.map (CommRingCat.ofHom (tSig σ hσ))

/-- `τ = σ⁻¹|_L`. -/
abbrev tauL (L : IF) [IsGalois ℚ L] (σ : PkgI4.GQ) : L →+* L :=
  (((σ⁻¹).restrictNormal L : L ≃ₐ[ℚ] L) : L →+* L)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **`FExtendGen` from the leaf I2-NMP (proved).**
1. `F` lies over `Spec τ`, `τ = σ⁻¹|_L`: both `F ≫ A → Spec L` and `A → Spec L → Spec L` agree at
   the `ℚ̄`-point `0` (from `f 0 = 0`), and `A` is integral (`hom_spec_eq_of_point`).
2. `ℬ = 𝒜 ×_{Spec t} Spec O_w` (the conjugate model) is an abelian scheme (base change).
3. `φ = (e ≫ F ≫ e⁻¹ ≫ pr₁, pr₂) : 𝒜_L → ℬ_L` is an `L`-morphism; I2-NMP gives `G : 𝒜 → ℬ`
   over `O_w` with `G_L = φ`; `F̃ = G ≫ pr₁` lies over `Spec t` and restricts to `F`.
4. `F̃` fixes the unit section: both sides agree on `Spec L` (because `F(0) = 0` twisted, by
   separatedness of `A` and dominance of `Spec ℚ̄ → Spec L`), hence on `Spec O_w`
   (separatedness of `𝒜`, dominance of `Spec L → Spec O_w`). -/
theorem fExtendGen_of_nmp (hN : PkgI2.NeronMappingAbelianScheme.{0}) : FExtendGen := by
  intro L _ _ A F _ _ p hp v σ hv hσ 𝒜 h𝒜 e f hf
  generalize hσ.1 = hσ1
  haveI : IsDiscreteValuationRing (Ow L v) := owDVR L v p hp hv
  haveI : IsProper 𝒜.X.hom := h𝒜.proper
  haveI : Smooth 𝒜.X.hom := h𝒜.smooth
  haveI : GeometricallyConnected 𝒜.X.hom := h𝒜.geomConnected
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  -- ring identities
  have hR1 : Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫ Spec.map (CommRingCat.ofHom (tauL L σ)) =
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    show σ (algebraMap L PkgI4.Qbar ((σ⁻¹).restrictNormal L a)) = algebraMap L PkgI4.Qbar a
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  have hR2 : jSpec L v ≫ tSpec σ hσ1 = Spec.map (CommRingCat.ofHom (tauL L σ)) ≫ jSpec L v := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  -- the zero point
  let x0 : Spec (.of Qbar) ⟶ A.X.left := (Additive.toMul (0 : PtQ L A)).left
  have hu : (CartesianMonoidalCategory.toUnit (PkgI3.AbVar.ptObj (K := L) Qbar)).left =
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) :=
    (Category.comp_id _).symm.trans
      (Over.w (CartesianMonoidalCategory.toUnit (PkgI3.AbVar.ptObj (K := L) Qbar)))
  have hx0 : x0 = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫ (η[A.X]).left := by
    show (CartesianMonoidalCategory.toUnit (PkgI3.AbVar.ptObj (K := L) Qbar)).left ≫
      (η[A.X]).left = _
    rw [hu]
    rfl
  have hx0w : x0 ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) :=
    Over.w (Additive.toMul (0 : PtQ L A))
  have hηw : (η[A.X]).left ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]
  have hf0 : Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
      x0 ≫ F = x0 := by
    have := hf 0
    rw [map_zero] at this
    exact this.symm
  have hpt : x0 ≫ F = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫
      Spec.map (CommRingCat.ofHom (tauL L σ)) ≫ (η[A.X]).left := by
    apply spec_aut_cancel (act σ)
    rw [hf0, reassoc_of% hR1]
    exact hx0
  -- Step 1: `F` lies over `Spec τ`
  have hFover : F ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (tauL L σ)) := by
    apply hom_spec_eq_of_point _ _ x0
    rw [reassoc_of% hpt, hηw, reassoc_of% hx0w]
    erw [Category.comp_id]
  -- `F(0) = 0`, twisted
  have hF0 : (η[A.X]).left ≫ F = Spec.map (CommRingCat.ofHom (tauL L σ)) ≫ (η[A.X]).left := by
    haveI := isDominant_Spec_map_of_injective (CommRingCat.ofHom (algebraMap L Qbar))
      (algebraMap L Qbar).injective
    refine ext_of_isDominant_of_isSeparated (X := Spec (.of L)) A.X.hom ?_
      (Spec.map (CommRingCat.ofHom (algebraMap L Qbar))) ?_
    · simp only [Category.assoc]
      rw [hFover, reassoc_of% hηw, hηw]
      erw [Category.comp_id]
    · calc _ = x0 ≫ F := by rw [hx0, Category.assoc]
        _ = _ := hpt
  -- Step 2: the conjugate model
  let ℬ := (Over.pullback (tSpec σ hσ1)).mapGrp.obj 𝒜
  haveI hℬ : PkgI2.IsAbelianScheme ℬ :=
    ⟨show IsProper (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) from inferInstance,
      show Smooth (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) from inferInstance,
      show GeometricallyConnected (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) from inferInstance⟩
  -- Step 3: the generic morphism and I2-NMP
  let E : pullback 𝒜.X.hom (jSpec L v) ⟶ A.X.left := e.hom.hom.hom.left
  let Ei : A.X.left ⟶ pullback 𝒜.X.hom (jSpec L v) := e.inv.hom.hom.left
  have hEi : Ei ≫ E = 𝟙 _ := congrArg (fun m => m.hom.hom.left) e.inv_hom_id
  have hEw : E ≫ A.X.hom = pullback.snd 𝒜.X.hom (jSpec L v) := Over.w e.hom.hom.hom
  have hEiw : Ei ≫ pullback.snd 𝒜.X.hom (jSpec L v) = A.X.hom := Over.w e.inv.hom.hom
  have c1 : (E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v)) ≫ 𝒜.X.hom =
      (pullback.snd 𝒜.X.hom (jSpec L v) ≫ jSpec L v) ≫ tSpec σ hσ1 := by
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% hEiw, reassoc_of% hFover, reassoc_of% hEw, hR2]
  let inner : pullback 𝒜.X.hom (jSpec L v) ⟶ pullback 𝒜.X.hom (tSpec σ hσ1) :=
    pullback.lift (E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v))
      (pullback.snd 𝒜.X.hom (jSpec L v) ≫ jSpec L v) c1
  let φl : pullback 𝒜.X.hom (jSpec L v) ⟶
      pullback (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) (jSpec L v) :=
    pullback.lift inner (pullback.snd 𝒜.X.hom (jSpec L v)) (pullback.lift_snd _ _ _)
  let φ : (Over.pullback (jSpec L v)).obj 𝒜.X ⟶ (Over.pullback (jSpec L v)).obj ℬ.X :=
    Over.homMk φl (pullback.lift_snd _ _ _)
  obtain ⟨G, hG⟩ := (hN L (Ow L v) 𝒜 ℬ).2 φ
  have hG' : (Over.pullback (jSpec L v)).map G = φ := hG
  let Gl : 𝒜.X.left ⟶ pullback 𝒜.X.hom (tSpec σ hσ1) := G.left
  let Ft : 𝒜.X.left ⟶ 𝒜.X.left := Gl ≫ pullback.fst 𝒜.X.hom (tSpec σ hσ1)
  have hGl : pullback.fst 𝒜.X.hom (jSpec L v) ≫ Gl =
      φl ≫ pullback.fst (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) (jSpec L v) := by
    have h1 : ((Over.pullback (jSpec L v)).map G).left ≫
        pullback.fst (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) (jSpec L v) =
        pullback.fst 𝒜.X.hom (jSpec L v) ≫ G.left := pullback.lift_fst _ _ _
    have h2 : ((Over.pullback (jSpec L v)).map G).left = φl := congrArg (fun m => m.left) hG'
    rw [← h2]
    exact h1.symm
  have hfst : pullback.fst 𝒜.X.hom (jSpec L v) ≫ Ft =
      E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) := by
    show pullback.fst 𝒜.X.hom (jSpec L v) ≫ Gl ≫ pullback.fst 𝒜.X.hom (tSpec σ hσ1) = _
    rw [← Category.assoc (pullback.fst 𝒜.X.hom (jSpec L v)), hGl, Category.assoc φl]
    simp only [φl, inner, pullback.lift_fst_assoc, pullback.lift_fst]
  have hC3 : Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) ≫ Ft =
      F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) := by
    rw [hfst, ← Category.assoc Ei E, hEi, Category.id_comp]
  have hGw : Gl ≫ pullback.snd 𝒜.X.hom (tSpec σ hσ1) = 𝒜.X.hom := Over.w G
  have hC1 : Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ tSpec σ hσ1 := by
    show (Gl ≫ pullback.fst 𝒜.X.hom (tSpec σ hσ1)) ≫ 𝒜.X.hom = _
    rw [Category.assoc, pullback.condition, reassoc_of% hGw]
  refine ⟨Ft, hC1, ?_, hC3⟩
  -- Step 4: the unit section
  have hηO : (η[𝒜.X]).left ≫ 𝒜.X.hom = 𝟙 _ := Over.w η[𝒜.X]
  have hηL : jSpec L v ≫ (η[𝒜.X]).left =
      (η[A.X]).left ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) := by
    rw [← pb_eta_fst (jSpec L v) 𝒜, ← Category.assoc]
    congr 1
    have h1 : η[A.X] ≫ e.inv.hom.hom = η[((Over.pullback (jSpec L v)).mapGrp.obj 𝒜).X] :=
      IsMonHom.one_hom _
    exact (congrArg (fun m => m.left) h1).symm
  haveI := isDominant_Spec_map_of_injective (CommRingCat.ofHom (algebraMap (Ow L v) L))
    (Subtype.val_injective)
  refine ext_of_isDominant_of_isSeparated (X := Spec (.of (Ow L v))) 𝒜.X.hom ?_ (jSpec L v) ?_
  · simp only [Category.assoc]
    rw [hC1, reassoc_of% hηO, hηO]
    erw [Category.comp_id]
  · rw [reassoc_of% hηL, hC3, reassoc_of% hF0, reassoc_of% hR2, hηL]

/-- **`FExtendCore` from I2-NMP (proved).** -/
theorem fExtendCore_of_nmp (hN : PkgI2.NeronMappingAbelianScheme.{0}) : FExtendCore :=
  fExtendCore_of_gen (fExtendGen_of_nmp hN)

/-- **Main result: `FrobTrace.AlgFrobRed` from the leaf candidates `GoodRedCofinite`,
`SmoothGeomConnIntegral` and the kernel leaves I2-Red, I2-NMP (proved).** alg-frob-red's two glue
Props are discharged: `AbsFrob` (`absFrob`, Mathlib only) and `FExtendGen` (`fExtendGen_of_nmp`). -/
theorem algFrobRed_of_nmp (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen hG hS hRed (fExtendGen_of_nmp hN) absFrob

/-- **`TateBridge35` from I3.M0, the two leaf candidates and I2-Red, I2-NMP (proved).** -/
theorem tateBridge35_of_nmp (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hN : PkgI2.NeronMappingAbelianScheme.{0}) : G14Bridge.TateBridge35 :=
  tateBridge35_of_gen hT hG hS hRed (fExtendGen_of_nmp hN) absFrob

end AlgFrobRedRed

#print axioms AlgFrobRedRed.absFrob
#print axioms AlgFrobRedRed.fExtendCore_of_nmp
#print axioms AlgFrobRedRed.algFrobRed_of_nmp
#print axioms AlgFrobRedRed.tateBridge35_of_nmp
#print axioms AlgFrobRedRed.ringHom_eq_of_normal
#print axioms AlgFrobRedRed.hom_spec_eq_of_point
#print axioms AlgFrobRedRed.fExtendGen_of_nmp
