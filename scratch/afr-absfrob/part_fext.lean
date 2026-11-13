
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
  haveI : IsDiscreteValuationRing (Ow L v) := owDVR L v p hp hv
  haveI : IsProper 𝒜.X.hom := h𝒜.proper
  haveI : Smooth 𝒜.X.hom := h𝒜.smooth
  haveI : GeometricallyConnected 𝒜.X.hom := h𝒜.geomConnected
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  -- `τ = σ⁻¹|_L`
  let τ : L →+* L := (((σ⁻¹).restrictNormal L : L ≃ₐ[ℚ] L) : L →+* L)
  -- ring identities
  have hR1 : Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫ Spec.map (CommRingCat.ofHom τ) =
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    show σ (algebraMap L PkgI4.Qbar ((σ⁻¹).restrictNormal L a)) = algebraMap L PkgI4.Qbar a
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  have hR2 : Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) ≫
      Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) =
      Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  -- the zero point
  let x0 : Spec (.of Qbar) ⟶ A.X.left := (Additive.toMul (0 : PtQ L A)).left
  have hx0 : x0 = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫ (η[A.X]).left := by
    have hu := Over.w (CartesianMonoidalCategory.toUnit (PkgI3.AbVar.ptObj (K := L) Qbar))
    exact (congrArg (· ≫ (η[A.X]).left) (hu.symm.trans (Category.comp_id _) |>.symm)).symm
  have hx0w : x0 ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) :=
    Over.w (Additive.toMul (0 : PtQ L A))
  have hηw : (η[A.X]).left ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]
  have hf0 : Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
      x0 ≫ F = x0 := by
    have := hf 0
    rw [map_zero] at this
    exact this.symm
  have hpt : x0 ≫ F = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫
      Spec.map (CommRingCat.ofHom τ) ≫ (η[A.X]).left := by
    apply spec_aut_cancel (act σ)
    rw [hf0, ← Category.assoc, ← Category.assoc, Category.assoc _ _ (Spec.map _), hR1, hx0]
  -- Step 1: `F` lies over `Spec τ`
  have hFover : F ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom τ) := by
    apply hom_spec_eq_of_point _ _ x0
    rw [← Category.assoc, hpt, Category.assoc, Category.assoc, hηw, Category.comp_id,
      ← Category.assoc, hx0w]
  -- `F(0) = 0`, twisted
  have hF0 : (η[A.X]).left ≫ F = Spec.map (CommRingCat.ofHom τ) ≫ (η[A.X]).left := by
    haveI := isDominant_Spec_map_of_injective (CommRingCat.ofHom (algebraMap L Qbar))
      (algebraMap L Qbar).injective
    refine ext_of_isDominant_of_isSeparated A.X.hom ?_
      (Spec.map (CommRingCat.ofHom (algebraMap L Qbar))) ?_
    · rw [Category.assoc, hFover, ← Category.assoc, hηw, Category.id_comp, Category.assoc, hηw,
        Category.comp_id]
    · rw [← Category.assoc, ← hx0, hpt]
  -- Step 2: the conjugate model
  let ℬ := (Over.pullback (Spec.map (CommRingCat.ofHom (tSig σ hσ.1)))).mapGrp.obj 𝒜
  haveI hℬ : PkgI2.IsAbelianScheme ℬ :=
    ⟨show IsProper (pullback.snd 𝒜.X.hom (Spec.map (CommRingCat.ofHom (tSig σ hσ.1)))) from
        inferInstance,
      show Smooth (pullback.snd 𝒜.X.hom (Spec.map (CommRingCat.ofHom (tSig σ hσ.1)))) from
        inferInstance,
      show GeometricallyConnected
        (pullback.snd 𝒜.X.hom (Spec.map (CommRingCat.ofHom (tSig σ hσ.1)))) from inferInstance⟩
  -- Step 3: the generic morphism and I2-NMP
  let jS := Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))
  let tS := Spec.map (CommRingCat.ofHom (tSig σ hσ.1))
  let E : pullback 𝒜.X.hom jS ⟶ A.X.left := e.hom.hom.hom.left
  let Ei : A.X.left ⟶ pullback 𝒜.X.hom jS := e.inv.hom.hom.left
  have hEi : Ei ≫ E = 𝟙 _ := congrArg (fun m => m.hom.hom.left) e.inv_hom_id
  have hEw : E ≫ A.X.hom = pullback.snd 𝒜.X.hom jS := Over.w e.hom.hom.hom
  have hEiw : Ei ≫ pullback.snd 𝒜.X.hom jS = A.X.hom := Over.w e.inv.hom.hom
  have c1 : (E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom jS) ≫ 𝒜.X.hom =
      (pullback.snd 𝒜.X.hom jS ≫ jS) ≫ tS := by
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc Ei, hEiw, ← Category.assoc F, hFover,
      Category.assoc, ← Category.assoc E, hEw]
    exact congrArg (pullback.snd 𝒜.X.hom jS ≫ ·) hR2.symm
  let inner : pullback 𝒜.X.hom jS ⟶ pullback 𝒜.X.hom tS :=
    pullback.lift (E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom jS) (pullback.snd 𝒜.X.hom jS ≫ jS) c1
  let φl : pullback 𝒜.X.hom jS ⟶ pullback (pullback.snd 𝒜.X.hom tS) jS :=
    pullback.lift inner (pullback.snd 𝒜.X.hom jS) (pullback.lift_snd _ _ _)
  let φ : (Over.pullback jS).obj 𝒜.X ⟶ (Over.pullback jS).obj ℬ.X :=
    Over.homMk φl (pullback.lift_snd _ _ _)
  obtain ⟨G, hG⟩ := (hN L (Ow L v) 𝒜 ℬ).2 φ
  let Ft : 𝒜.X.left ⟶ 𝒜.X.left := G.left ≫ pullback.fst 𝒜.X.hom tS
  have hGl : pullback.fst 𝒜.X.hom jS ≫ G.left = φl ≫ pullback.fst (pullback.snd 𝒜.X.hom tS) jS := by
    have h1 : ((Over.pullback jS).map G).left ≫ pullback.fst (pullback.snd 𝒜.X.hom tS) jS =
        pullback.fst 𝒜.X.hom jS ≫ G.left := pullback.lift_fst _ _ _
    rw [← h1, hG]
    rfl
  have hfst : pullback.fst 𝒜.X.hom jS ≫ Ft = E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom jS := by
    show pullback.fst 𝒜.X.hom jS ≫ G.left ≫ pullback.fst 𝒜.X.hom tS = _
    rw [← Category.assoc, hGl, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst]
  have hC3 : Ei ≫ pullback.fst 𝒜.X.hom jS ≫ Ft = F ≫ Ei ≫ pullback.fst 𝒜.X.hom jS := by
    rw [hfst, ← Category.assoc Ei E, hEi, Category.id_comp]
  have hGw : G.left ≫ pullback.snd 𝒜.X.hom tS = 𝒜.X.hom := Over.w G
  have hC1 : Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ tS := by
    show (G.left ≫ pullback.fst 𝒜.X.hom tS) ≫ 𝒜.X.hom = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, hGw]
  refine ⟨Ft, hC1, ?_, hC3⟩
  -- Step 4: the unit section
  have hηO : (η[𝒜.X]).left ≫ 𝒜.X.hom = 𝟙 _ := Over.w η[𝒜.X]
  have hηL : jS ≫ (η[𝒜.X]).left = (η[A.X]).left ≫ Ei ≫ pullback.fst 𝒜.X.hom jS := by
    rw [← pb_eta_fst jS 𝒜, ← Category.assoc]
    congr 1
    have h1 : η[A.X] ≫ e.inv.hom.hom = η[((Over.pullback jS).mapGrp.obj 𝒜).X] :=
      IsMonHom.one_hom
    exact (congrArg Over.Hom.left h1).symm
  haveI := isDominant_Spec_map_of_injective (CommRingCat.ofHom (algebraMap (Ow L v) L))
    (Subtype.val_injective)
  refine ext_of_isDominant_of_isSeparated 𝒜.X.hom ?_ jS ?_
  · rw [Category.assoc, hC1, ← Category.assoc, hηO, Category.id_comp, Category.assoc, hηO,
      Category.comp_id]
  · rw [← Category.assoc, hηL, Category.assoc, Category.assoc, hC3, ← Category.assoc, hF0,
      ← Category.assoc jS, hR2, Category.assoc, hηL, Category.assoc]

/-- **`FExtendCore` from I2-NMP (proved).** -/
theorem fExtendCore_of_nmp (hN : PkgI2.NeronMappingAbelianScheme.{0}) : FExtendCore :=
  fExtendCore_of_gen (fExtendGen_of_nmp hN)

end AlgFrobRedRed

#print axioms AlgFrobRedRed.ringHom_eq_of_normal
#print axioms AlgFrobRedRed.hom_spec_eq_of_point
#print axioms AlgFrobRedRed.fExtendGen_of_nmp
