/-! # twist-descent, part MAIN: `TwistDescent` (kf-glue) proved

For `σ ∈ G_ℚ` with restriction `ρ = σ|_L`: the hypothesis gives a twisted isomorphism
`φ : B_{e₀} ≅ B_{σ⁻¹e₀}` over `ℚ̄` (`e₀ : K ↪ ℚ̄`); it is `G_L`-invariant (`L` is a Hom field,
`td_hom_inv`), so it descends to `φ_L : B_L → B ×_{K,τ∘(K↪L)} L` (`hfd`, `τ = σ⁻¹|_L`); then
`E = φ_L ≫ c_τ`, with `c_τ` the comparison over `Spec τ`. `φ_L` is a homomorphism by rigidity
(`G0FibreSimple.rigidityHom`, proved in kf-glue). `E` and `α` are chosen as functions of `σ|_L`,
with `E = 𝟙`, `α = id` on the trivial class (`twistDescent`). -/

section TwistDescentMain

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open TwistDescentXC TwistDescentHFD

namespace G0ModField.KernelField

open G0ModField

/-- **`G_L` fixes homomorphisms between conjugates** (from the Hom-field hypothesis of
`TwistDescent`): `k ∘ φ = φ ∘ k` for `k ∈ G_L` and `φ : B_{e₁} → B_{e₂}`. -/
theorem td_hom_inv {K : IF} [IsGalois ℚ K] (B : PkgI3.AbVar K) {L : IF} (hKL : K ≤ L)
    (hHF : ∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K B σ = 1)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₁) ((G4WeilRes.conjData K B).A e₂))
    (k : Qbar ≃ₐ[ℚ] Qbar) (hk : k ∈ L.fixingSubgroup)
    (k₁ : sp (e₁ : K →+* Qbar) = sp (k : Qbar →+* Qbar) ≫ sp (e₁ : K →+* Qbar))
    (k₂ : sp (e₂ : K →+* Qbar) = sp (k : Qbar →+* Qbar) ≫ sp (e₂ : K →+* Qbar)) :
    xc B.X (sp (k : Qbar →+* Qbar)) k₁ ≫ φ.hom.left =
      φ.hom.left ≫ xc B.X (sp (k : Qbar →+* Qbar)) k₂ := by
  classical
  have hs : ∀ e : K →ₐ[ℚ] Qbar, (G4WeilRes.embAct K k).symm e = e := by
    intro e
    ext x
    have hx : e x ∈ L :=
      hKL ((SetLike.ext_iff.mp (AlgHom.fieldRange_of_normal e) (e x)).mp ⟨x, rfl⟩)
    exact (IntermediateField.mem_fixingSubgroup_iff L _).mp (inv_mem hk) _ hx
  let m : G4WeilRes.HomLattice (G4WeilRes.conjData K B).A := Pi.single (e₁, e₂) φ
  have hm : G4WeilRes.conjAct K B k m = m := LinearEquiv.congr_fun (hHF k hk) m
  have h0 := G4WeilRes.conjAct_isConjAction K B k m e₁ e₂
  dsimp only at h0
  rw [hm] at h0
  have hme : m (e₁, e₂) = φ := Pi.single_eq_same _ _
  rw [hme] at h0
  have gen : ∀ (x y : K →ₐ[ℚ] Qbar) (hx : x = e₁) (hy : y = e₂)
      (p₁ : G4WeilRes.specEmb K e₁ = G4WeilRes.specGal k ≫ G4WeilRes.specEmb K x)
      (p₂ : G4WeilRes.specEmb K e₂ = G4WeilRes.specGal k ≫ G4WeilRes.specEmb K y),
      φ.hom.left ≫ G4Conj.cmp B.X (G4WeilRes.specGal k) p₂ =
        G4Conj.cmp B.X (G4WeilRes.specGal k) p₁ ≫ (m (x, y)).hom.left →
      xc B.X (sp (k : Qbar →+* Qbar)) k₁ ≫ φ.hom.left =
        φ.hom.left ≫ xc B.X (sp (k : Qbar →+* Qbar)) k₂ := by
    intro x y hx hy p₁ p₂ h
    subst hx hy
    rw [hme] at h
    exact h.symm
  exact gen _ _ (hs e₁) (hs e₂) (G4WeilRes.specEmb_symm K k e₁) (G4WeilRes.specEmb_symm K k e₂) h0

/-- The clauses of `SemilinearTwistAt` at one `σ`, in terms of `ρ = σ|_L`. -/
def TwistClause (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A) (ρ : L ≃ₐ[ℚ] L)
    (E : A.X.left ⟶ A.X.left) (α : O ≃+* O) : Prop :=
  IsIso E ∧
    (∃ τ : L ≃+* L, (∀ x : L, τ x = ρ⁻¹ x) ∧
      ∃ hτ : E ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)),
        μ[A.X].left ≫ E =
          pullback.map A.X.hom A.X.hom A.X.hom A.X.hom E E
            (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hτ.symm hτ.symm ≫ μ[A.X].left ∧
        η[A.X].left ≫ E = Spec.map (CommRingCat.ofHom (τ : L →+* L)) ≫ η[A.X].left) ∧
    (∀ a : O, (ι' a).hom.left ≫ E = E ≫ (ι' (α a)).hom.left)

/-- `Spec ℚ̄ → Spec L` is an epimorphism. -/
theorem specQbar_epi (L : IF) : Epi (sp (algebraMap L Qbar)) := by
  obtain ⟨h1, h2, h3⟩ := TwistDescentGD.spec_field_props L Qbar
  infer_instance

/-- The trivial class: `E = 𝟙`, `α = id`. -/
theorem twistClause_one (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A) :
    TwistClause L A ι' 1 (𝟙 _) (RingEquiv.refl O) := by
  have hid : Spec.map (CommRingCat.ofHom ((RingEquiv.refl L : L ≃+* L) : L →+* L)) = 𝟙 _ := by
    rw [← Spec.map_id]; rfl
  refine ⟨inferInstance, ⟨RingEquiv.refl _, fun x => rfl, ?_, ?_, ?_⟩, fun a => ?_⟩
  · rw [hid, Category.id_comp, Category.comp_id]
  · rw [Category.comp_id]
    symm
    refine Eq.trans (congrArg (fun m => m ≫ μ[A.X].left) ?_) (Category.id_comp _)
    apply pullback.hom_ext <;> simp
  · rw [hid, Category.id_comp, Category.comp_id]
  · simp

set_option maxHeartbeats 1000000 in
/-- **The construction at one `σ`** (`E = φ_L ≫ c_τ`, `α = α_φ⁻¹`). -/
theorem td_construct {K : IF} [FiniteDimensional ℚ K] [IsGalois ℚ K] (B : PkgI3.AbVar K)
    (ιB : O →+* PkgI3.AbVar.End B) {L : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L)
    (hHF : ∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K B σ = 1)
    (hTw : ∀ e₁ e₂ : K →ₐ[ℚ] Qbar, ∃ (α : O ≃+* O)
        (φ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₁) ((G4WeilRes.conjData K B).A e₂))
        (ψ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₂) ((G4WeilRes.conjData K B).A e₁)),
        φ.hom ≫ ψ.hom = 𝟙 _ ∧ ψ.hom ≫ φ.hom = 𝟙 _ ∧
        ∀ a : O, (bcEnd K B e₁ (ιB (α a))).hom ≫ φ.hom = φ.hom ≫ (bcEnd K B e₂ (ιB a)).hom)
    (σ : Qbar ≃ₐ[ℚ] Qbar) :
    ∃ (E : (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left ⟶
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left) (α : O ≃+* O),
      TwistClause L (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL))
        ((@endBC K _ B L _ (incAlg hKL)).comp ιB) (AlgEquiv.restrictNormalHom L σ) E α := by
  letI : Algebra K L := incAlg hKL
  let e₀ : K →ₐ[ℚ] Qbar := K.val
  let e₂ : K →ₐ[ℚ] Qbar := G4WeilRes.embAct K σ⁻¹ e₀
  obtain ⟨α, φ, ψ, hφψ, hψφ, htw⟩ := hTw e₀ e₂
  let τ : L ≃+* L := (AlgEquiv.restrictNormalHom L σ⁻¹ : L ≃ₐ[ℚ] L).toRingEquiv
  have hτx : ∀ x : L, (τ x : Qbar) = σ⁻¹ x := fun x => AlgEquiv.restrictNormalHom_apply L σ⁻¹ x
  let e₁L : K →+* L := algebraMap K L
  let e₂L : K →+* L := (τ : L →+* L).comp e₁L
  have he₁ : ∀ x, (e₁L x : Qbar) = (e₀ : K →+* Qbar) x := fun x => rfl
  have he₂ : ∀ x, (e₂L x : Qbar) = (e₂ : K →+* Qbar) x := fun x => hτx _
  have h₁ : sp (e₀ : K →+* Qbar) = sp (algebraMap L Qbar) ≫ sp e₁L := sp_eq _ _ _ he₁
  have h₂ : sp (e₂ : K →+* Qbar) = sp (algebraMap L Qbar) ≫ sp e₂L := sp_eq _ _ _ he₂
  let φ₀ : pullback B.X.hom (sp (e₀ : K →+* Qbar)) ⟶ pullback B.X.hom (sp (e₂ : K →+* Qbar)) :=
    φ.hom.left
  let ψ₀ : pullback B.X.hom (sp (e₂ : K →+* Qbar)) ⟶ pullback B.X.hom (sp (e₀ : K →+* Qbar)) :=
    ψ.hom.left
  have hφs : φ₀ ≫ pullback.snd B.X.hom (sp (e₂ : K →+* Qbar)) =
      pullback.snd B.X.hom (sp (e₀ : K →+* Qbar)) := Over.w φ.hom
  have hψs : ψ₀ ≫ pullback.snd B.X.hom (sp (e₀ : K →+* Qbar)) =
      pullback.snd B.X.hom (sp (e₂ : K →+* Qbar)) := Over.w ψ.hom
  obtain ⟨φL, hφL⟩ := hfd B e₁L e₂L _ _ h₁ h₂ he₁ he₂ φ₀ hφs
    (fun k hk k₁ k₂ => td_hom_inv B hKL hHF e₀ e₂ φ k hk k₁ k₂)
  obtain ⟨ψL, hψL⟩ := hfd B e₂L e₁L _ _ h₂ h₁ he₂ he₁ ψ₀ hψs
    (fun k hk k₁ k₂ => td_hom_inv B hKL hHF e₂ e₀ ψ k hk k₁ k₂)
  have ep₁ := xc_epi B e₁L _ h₁
  have ep₂ := xc_epi B e₂L _ h₂
  have hφψ' : φ₀ ≫ ψ₀ = 𝟙 _ := congrArg Over.Hom.left hφψ
  have hψφ' : ψ₀ ≫ φ₀ = 𝟙 _ := congrArg Over.Hom.left hψφ
  have hφψL : φL ≫ ψL = 𝟙 _ := by
    rw [← cancel_epi (xc B.X (sp (algebraMap L Qbar)) h₁), ← Category.assoc, hφL,
      Category.assoc, hψL, ← Category.assoc, hφψ', Category.id_comp, Category.comp_id]
  have hψφL : ψL ≫ φL = 𝟙 _ := by
    rw [← cancel_epi (xc B.X (sp (algebraMap L Qbar)) h₂), ← Category.assoc, hψL,
      Category.assoc, hφL, ← Category.assoc, hψφ', Category.id_comp, Category.comp_id]
  have hφLs : φL ≫ pullback.snd B.X.hom (sp e₂L) = pullback.snd B.X.hom (sp e₁L) := by
    rw [← cancel_epi (xc B.X (sp (algebraMap L Qbar)) h₁), ← Category.assoc, hφL,
      Category.assoc, xc_snd, ← Category.assoc, hφs, xc_snd]
  have hc : sp e₂L = sp (τ : L →+* L) ≫ sp e₁L := sp_eq _ _ _ fun _ => rfl
  have hci : sp e₁L = sp (τ.symm : L →+* L) ≫ sp e₂L :=
    sp_eq _ _ _ fun x => τ.symm_apply_apply _
  let c := xc B.X (sp (τ : L →+* L)) hc
  let cinv := xc B.X (sp (τ.symm : L →+* L)) hci
  have hcc : c ≫ cinv = 𝟙 _ := by
    rw [xc_comp_eq B.X _ _ _ _ (sp (RingHom.id L)) (sp_eq _ _ _ fun _ => rfl)
      (sp_comp_eq _ _ _ fun x => τ.apply_symm_apply x)]
    exact xc_self B.X _ (sp_id_eq _ fun _ => rfl) _
  have hcc' : cinv ≫ c = 𝟙 _ := by
    rw [xc_comp_eq B.X _ _ _ _ (sp (RingHom.id L)) (sp_eq _ _ _ fun _ => rfl)
      (sp_comp_eq _ _ _ fun x => τ.symm_apply_apply x)]
    exact xc_self B.X _ (sp_id_eq _ fun _ => rfl) _
  -- `φ_L` is a homomorphism (rigidity)
  let A₂ : PkgI3.AbVar L := G4WeilRes.bcAlong B e₂L
  let φL' : (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X ⟶ A₂.X := Over.homMk φL hφLs
  haveI := specQbar_epi L
  have o1 := xc_one B.X (sp (algebraMap L Qbar)) h₁
  have o2 := xc_one B.X (sp (algebraMap L Qbar)) h₂
  have o3 : η[((G4WeilRes.conjData K B).A e₀).X].left ≫ φ₀ =
      η[((G4WeilRes.conjData K B).A e₂).X].left := by
    show (η[((G4WeilRes.conjData K B).A e₀).X] ≫ φ.hom).left = _
    rw [IsMonHom.one_hom]
  have hηL : η[(@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X].left ≫ φL =
      η[A₂.X].left := by
    have eq : sp (algebraMap L Qbar) ≫
        η[(@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X].left ≫ φL =
        sp (algebraMap L Qbar) ≫ η[A₂.X].left :=
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ φL) o1.symm).trans <|
          (Category.assoc _ _ _).trans <|
            (congrArg (η[((G4WeilRes.conjData K B).A e₀).X].left ≫ ·) hφL).trans <|
              (Category.assoc _ _ _).symm.trans <|
                (congrArg (· ≫ xc B.X (sp (algebraMap L Qbar)) h₂) o3).trans o2
    exact (cancel_epi (sp (algebraMap L Qbar))).mp eq
  have hη : η[(@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X] ≫ φL' = η[A₂.X] :=
    Over.OverMorphism.ext hηL
  have hmon : IsMonHom φL' := G0FibreSimple.rigidityHom L _ _ φL' hη
  have hiso : IsIso (φL ≫ c) :=
    ⟨⟨cinv ≫ ψL, by rw [Category.assoc, reassoc_of% hcc, hφψL],
      by rw [Category.assoc, reassoc_of% hψφL, hcc']⟩⟩
  have hτ : (φL ≫ c) ≫ pullback.snd B.X.hom (sp e₁L) =
      pullback.snd B.X.hom (sp e₁L) ≫ sp (τ : L →+* L) := by
    rw [Category.assoc, xc_snd, reassoc_of% hφLs]
  have m1 : μ[(@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X].left ≫ φL =
      (φL' ⊗ₘ φL').left ≫ μ[A₂.X].left :=
    congrArg Over.Hom.left (IsMonHom.mul_hom (f := φL'))
  have m2 := xc_mul B.X (sp (τ : L →+* L)) hc
  have m3 : (φL' ⊗ₘ φL').left ≫ xc2 B.X (sp (τ : L →+* L)) hc =
      pullback.map (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.hom
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.hom
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.hom
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.hom (φL ≫ c) (φL ≫ c)
        (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hτ.symm hτ.symm := by
    have f1 := xc2_fst B.X (sp (τ : L →+* L)) hc
    have f2 := Over.tensorHom_left_fst (pullback.snd B.X.hom (sp e₂L)) (pullback.snd B.X.hom (sp e₂L)) φL' φL'
    have g1 := xc2_snd B.X (sp (τ : L →+* L)) hc
    have g2 := Over.tensorHom_left_snd (pullback.snd B.X.hom (sp e₂L)) (pullback.snd B.X.hom (sp e₂L)) φL' φL'
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans <| (congrArg _ f1).trans <|
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ c) f2).trans <|
          (Category.assoc _ _ _).trans (pullback.lift_fst _ _ _).symm
    · exact (Category.assoc _ _ _).trans <| (congrArg _ g1).trans <|
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ c) g2).trans <|
          (Category.assoc _ _ _).trans (pullback.lift_snd _ _ _).symm
  refine ⟨φL ≫ c, α.symm, hiso, ⟨τ, fun x => ?_, hτ, ?_, ?_⟩, fun a => ?_⟩
  · rw [← map_inv]; rfl
  · exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ c) m1).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg ((φL' ⊗ₘ φL').left ≫ ·) m2).trans <|
            (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) m3)
  · exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ c) hηL).trans (xc_one B.X (sp (τ : L →+* L)) hc)
  · have hmap : ∀ f₁ f₂ : B.X ⟶ B.X,
        ((Over.pullback (sp (e₀ : K →+* Qbar))).map f₁).left ≫ φ₀ =
          φ₀ ≫ ((Over.pullback (sp (e₂ : K →+* Qbar))).map f₂).left →
        ((Over.pullback (sp e₁L)).map f₁).left ≫ φL =
          φL ≫ ((Over.pullback (sp e₂L)).map f₂).left := by
      intro f₁ f₂ h
      rw [← cancel_epi (xc B.X (sp (algebraMap L Qbar)) h₁)]
      calc xc B.X (sp (algebraMap L Qbar)) h₁ ≫ ((Over.pullback (sp e₁L)).map f₁).left ≫ φL
          = ((Over.pullback (sp (e₀ : K →+* Qbar))).map f₁).left ≫ φ₀ ≫
              xc B.X (sp (algebraMap L Qbar)) h₂ := by
            rw [← Category.assoc, ← xc_map B.X _ h₁ f₁, Category.assoc, hφL]
        _ = φ₀ ≫ xc B.X (sp (algebraMap L Qbar)) h₂ ≫
              ((Over.pullback (sp e₂L)).map f₂).left := by
            rw [← Category.assoc, h, Category.assoc, xc_map B.X _ h₂ f₂]
        _ = _ := by rw [← Category.assoc, ← hφL, Category.assoc]
    have ht := htw (α.symm a)
    rw [RingEquiv.apply_symm_apply] at ht
    have ht' := congrArg Over.Hom.left ht
    rw [Over.comp_left, Over.comp_left] at ht'
    have key := hmap (ιB a).hom (ιB (α.symm a)).hom ht'
    change ((Over.pullback (sp e₁L)).map (ιB a).hom).left ≫ φL ≫ c =
      (φL ≫ c) ≫ ((Over.pullback (sp e₁L)).map (ιB (α.symm a)).hom).left
    rw [← Category.assoc, key, Category.assoc, xc_map B.X _ hc, Category.assoc]

/-- **`TwistDescent` holds** (kf-glue's glue Prop, statement verbatim; no hypotheses). -/
theorem twistDescent : TwistDescent := by
  intro K _ _ B ιB L _ _ hKL hHF hTw
  classical
  have key : ∀ ρ : L ≃ₐ[ℚ] L, ∃ (E : (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left ⟶
      (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left) (α : O ≃+* O),
      TwistClause L (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL))
        ((@endBC K _ B L _ (incAlg hKL)).comp ιB) ρ E α := by
    intro ρ
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := L) (E := Qbar) ρ
    exact td_construct B ιB hKL hHF hTw σ
  let G : (L ≃ₐ[ℚ] L) → ((@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left ⟶
      (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left) :=
    fun ρ => if ρ = 1 then 𝟙 _ else (key ρ).choose
  let Gα : (L ≃ₐ[ℚ] L) → (O ≃+* O) :=
    fun ρ => if ρ = 1 then RingEquiv.refl O else (key ρ).choose_spec.choose
  have hG : ∀ ρ, TwistClause L (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL))
      ((@endBC K _ B L _ (incAlg hKL)).comp ιB) ρ (G ρ) (Gα ρ) := by
    intro ρ
    by_cases h : ρ = 1
    · subst h
      simp only [G, Gα, if_pos rfl]
      exact twistClause_one L _ _
    · simp only [G, Gα, if_neg h]
      exact (key ρ).choose_spec.choose_spec
  let r : GQ → (L ≃ₐ[ℚ] L) := fun σ => AlgEquiv.restrictNormalHom L (act σ)
  have hr : ∀ k ∈ GQL L, r k = 1 := by
    intro k hk
    ext x
    show ((AlgEquiv.restrictNormalHom L (act k) x : L) : Qbar) = (x : Qbar)
    rw [AlgEquiv.restrictNormalHom_apply]
    exact mem_GQL.mp hk x x.2
  refine ⟨fun σ => G (r σ), fun σ => Gα (r σ), fun σ => ?_⟩
  obtain ⟨h1, ⟨τ, hτ, hrest⟩, h3⟩ := hG (r σ)
  refine ⟨h1, ⟨τ, fun x => ?_, hrest⟩, h3, fun k hk => ?_⟩
  · rw [hτ x, ← map_inv, AlgEquiv.restrictNormalHom_apply]
    rfl
  · have e1 : r (σ * k) = r σ := by
      show AlgEquiv.restrictNormalHom L (act σ * act k) = _
      rw [map_mul]
      exact (congrArg (r σ * ·) (hr k hk)).trans (mul_one _)
    have e2 : r (k * σ) = r σ := by
      show AlgEquiv.restrictNormalHom L (act k * act σ) = _
      rw [map_mul]
      exact (congrArg (· * r σ) (hr k hk)).trans (one_mul _)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show G (r k) = 𝟙 _
      rw [hr k hk]; exact if_pos rfl
    · show Gα (r k) = RingEquiv.refl O
      rw [hr k hk]; exact if_pos rfl
    · show G (r (σ * k)) = G (r σ); rw [e1]
    · show G (r (k * σ)) = G (r σ); rw [e2]
    · show Gα (r (σ * k)) = Gα (r σ); rw [e1]
    · show Gα (r (k * σ)) = Gα (r σ); rw [e2]

end G0ModField.KernelField

end TwistDescentMain
