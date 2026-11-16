theorem isPrimitiveType_of_finrank_two (Φ : Fin 1 → E →+* ℂ) (h2 : Module.finrank ℚ E = 2)
    (hinj : Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i))) : IsPrimitiveType Φ

theorem not_isPrimitiveType_PhiE {K : Type} [Field K] [NumberField K] [Fact (Irreducible (X ^ 2 - C (2 : K)))]
    (κ : K →+* ℂ) : ¬ IsPrimitiveType (PhiE κ)

theorem polMaxPrim_of_polMax (h : MainTheoremCMPolMax) : MainTheoremCMPolMaxPrim

theorem polPrim_of_pol (h : MainTheoremCMPol) : MainTheoremCMPolPrim

theorem polPrim_of_polMaxPrim (h : MainTheoremCMPolMaxPrim) : MainTheoremCMPolPrim

theorem polQuad_of_polPrim (h : MainTheoremCMPolPrim) : MainTheoremCMPolQuad

theorem polMaxQuad_of_polMaxPrim (h : MainTheoremCMPolMaxPrim) : MainTheoremCMPolMaxQuad

theorem signPrim_of_sign {ε : ℤˣ} (h : HcmPrinted.MainTheoremCMSign ε) : MainTheoremCMSignPrim ε

theorem signQuad_of_signPrim {ε : ℤˣ} (h : MainTheoremCMSignPrim ε) : MainTheoremCMSignQuad ε

theorem ek_of_sign {ε : ℤˣ} (h : HcmPrinted.MainTheoremCMSign ε) : MainTheoremCMEK ε

theorem mainTheoremCMSignOn_of_polar (P : CMTypeClass) (ε : ℤˣ) (hP : MainTheoremCMPolOn P ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MainTheoremCMSignOn P ε

theorem mainTheoremCMSignPrim_of_polar (ε : ℤˣ) (hP : MainTheoremCMPolPrimSign ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MainTheoremCMSignPrim ε

theorem mainTheoremCMSignQuad_of_polar (ε : ℤˣ) (hP : MainTheoremCMPolQuadSign ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MainTheoremCMSignQuad ε

theorem reflexNorm_rhoK_eq (K : Type) [Field K] [NumberField K] [Fact (Irreducible (X ^ 2 - C (2 : K)))]
    (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (reflexNorm rhoK u : AQ ⊗[ℚ] EK K) = inclA (reflexNorm rho1 u : AQ ⊗[ℚ] K)

theorem exists_isogeny_EK (hX : CMAbVarExists) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) [Fact (Irreducible (X ^ 2 - C (2 : K)))] (κ : K →+* ℂ)
    (A : PkgI3.AbVar ℂ) (hdimA : A.dim = ((2 : ℕ) : WithBot ℕ∞)) (𝔞 : AddSubgroup (EK K))
    (θ : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)) (hθ : IsUniformization (RingHom.id ℂ) (cmLat (PhiE κ) 𝔞) θ) :
    ∃ (B : PkgI3.AbVar ℂ) (θB : (Fin 1 → ℂ) → CPts B (RingHom.id ℂ)) (𝔟 : AddSubgroup K)
      (f₁ f₂ : PkgI3.AbVar.Hom B A) (m : ℕ),
      B.dim = ((1 : ℕ) : WithBot ℕ∞) ∧ IsOLattice 𝔟 ∧
      IsUniformization (RingHom.id ℂ) (cmLat (fun _ : Fin 1 => κ) 𝔟) θB ∧ 0 < m ∧
      (∀ w₁ w₂ : Fin 1 → ℂ, θ (w₁ 0 • cmVec (PhiE κ) 1 + w₂ 0 • cmVec (PhiE κ) (AdjoinRoot.root _)) =
        θB w₁ ≫ f₁.hom * θB w₂ ≫ f₂.hom) ∧
      (∀ P : CPts A (RingHom.id ℂ), ∃ Q₁ Q₂ : CPts B (RingHom.id ℂ), P = Q₁ ≫ f₁.hom * Q₂ ≫ f₂.hom) ∧
      (∀ Q₁ Q₂ : CPts B (RingHom.id ℂ), Q₁ ≫ f₁.hom * Q₂ ≫ f₂.hom = 1 → Q₁ ^ m = 1 ∧ Q₂ ^ m = 1)

theorem mainTheoremCMEK_of_quad (ε : ℤˣ) (hP : MainTheoremCMSignQuad ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MainTheoremCMEK ε

theorem mainTheoremCMEK_of_prim (ε : ℤˣ) (hP : MainTheoremCMSignPrim ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MainTheoremCMEK ε

theorem mainTheoremCMEK_of_polQuad (hP : MainTheoremCMPolQuad) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ∃ ε : ℤˣ, MainTheoremCMEK ε

theorem mainTheoremCMEK_of_polPrim (hP : MainTheoremCMPolPrim) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ∃ ε : ℤˣ, MainTheoremCMEK ε

theorem mainTheoremCMPrim_of_polPrim (hP : MainTheoremCMPolPrim) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ∃ ε : ℤˣ, MainTheoremCMSignPrim ε

theorem qmReciprocityL3_of_ek (hM : ∃ ε : ℤˣ, MainTheoremCMEK ε) (hC : ZInQ.HomUnify.HomLatticeCorr) :
    QMReciprocityL3

theorem qmReciprocityL3_of_polPrim (hP : MainTheoremCMPolPrim) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ShimuraSplit2.QMReciprocityL3

theorem qmReciprocityL3_of_polQuad (hP : MainTheoremCMPolQuad) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ShimuraSplit2.QMReciprocityL3

theorem rayClassCMAb_of_polPrim (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hP : MainTheoremCMPolPrim)
    (hX : CMAbVarExists) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hMum : AvSplit.MumfordTorsionAlgClosed) :
    ShimuraGlue.Ray.RayClassCMAb

theorem rayClassCMAb_of_polQuad (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hP : MainTheoremCMPolQuad)
    (hX : CMAbVarExists) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hMum : AvSplit.MumfordTorsionAlgClosed) :
    ShimuraGlue.Ray.RayClassCMAb

theorem shimuraMainCM_of_arithQuad (hM : MainTheoremCMSignQuad 1) (hWU : WeierstrassUniformization)
    (hWP : WeierstrassParam) (hWA : WeierstrassAbVar) (hH : ZInQ.HomUnify.HomLatticeCorr) :
    T5Glue.ShimuraMainCM

theorem shimuraMainCM_of_arithPrim (hM : MainTheoremCMSignPrim 1) (hWU : WeierstrassUniformization)
    (hWP : WeierstrassParam) (hWA : WeierstrassAbVar) (hH : ZInQ.HomUnify.HomLatticeCorr) :
    T5Glue.ShimuraMainCM

theorem shimuraMainCM_of_polMaxPrim (hP : MainTheoremCMPolMaxPrim) (hX : CMAbVarExists)
    (hWU : HcmPrinted.WeierstrassUniformization) (hWP : HcmPrinted.WeierstrassParam)
    (hWA : HcmPrinted.WeierstrassAbVar) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) : T5Glue.ShimuraMainCM

theorem shimuraMainCM_of_polMaxQuad (hP : MainTheoremCMPolMaxQuad) (hX : CMAbVarExists)
    (hWU : HcmPrinted.WeierstrassUniformization) (hWP : HcmPrinted.WeierstrassParam)
    (hWA : HcmPrinted.WeierstrassAbVar) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) : T5Glue.ShimuraMainCM

theorem exists_liftHom (σ : ℂ ≃+* ℂ) {A A' B : PkgI3.AbVar ℂ} (h : A'.X.left ⟶ A.X.left)
    (hpb : IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))))
    (hone : (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left)
    (f : B.X ⟶ A.X) [IsMonHom f] :
    ∃ F : (bcC B (σ : ℂ →+* ℂ)).X ⟶ A'.X, IsMonHom F ∧
      ∀ P : CPts (bcC B (σ : ℂ →+* ℂ)) (RingHom.id ℂ),
        pl (P ≫ F) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (dd σ B P ≫ f)

theorem exists_bcHom (σ : ℂ ≃+* ℂ) {A B : PkgI3.AbVar ℂ} (f : B.X ⟶ A.X) [IsMonHom f] :
    ∃ F : (bcC B (σ : ℂ →+* ℂ)).X ⟶ (bcC A (σ : ℂ →+* ℂ)).X, IsMonHom F ∧
      ∀ P : CPts (bcC B (σ : ℂ →+* ℂ)) (RingHom.id ℂ), dd σ A (P ≫ F) = dd σ B P ≫ f

theorem exists_unif_of_bc (σ : ℂ ≃+* ℂ) {A A' : PkgI3.AbVar ℂ} (h : A'.X.left ⟶ A.X.left)
    (hpb : IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))))
    (hone : (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left)
    {g : ℕ} {L : Submodule ℤ (Fin g → ℂ)}
    {θ0 : (Fin g → ℂ) → CPts (bcC A (σ : ℂ →+* ℂ)) (RingHom.id ℂ)}
    (hθ0 : IsUniformization (RingHom.id ℂ) L θ0) :
    ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ), IsUniformization (RingHom.id ℂ) L θ' ∧
      ∀ z, pl (θ' z) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (dd σ A (θ0 z))
