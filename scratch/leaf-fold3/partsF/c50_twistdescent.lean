-- (leaf-fold3) scratch/twist-descent/Part{XC,HFD,Main,GDM,Final}.lean verbatim
/-! # twist-descent, part XC: comparison maps between base changes along different bases

Generic category theory (any `C` with pullbacks), generalizing `G4Conj.cmp` (one base `T`) to two
bases: for `f₂ = s ≫ f₁` with `s : T₂ ⟶ T₁`, the comparison `X ×_{S,f₂} T₂ → X ×_{S,f₁} T₁`
(`xc`), its pullback square, composition, and compatibility with base-changed endomorphisms,
units and multiplications. -/

section TwistDescentXC

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Obj

namespace TwistDescentXC

variable {C : Type*} [Category C] [HasPullbacks C] {S : C} (X : Over S)

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

/-- `X ×_{f₂} T₂ → X ×_{f₁} T₁` over `s`, for `f₂ = s ≫ f₁`. -/
noncomputable def xc {T₁ T₂ : C} {f₁ : T₁ ⟶ S} {f₂ : T₂ ⟶ S} (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    pullback X.hom f₂ ⟶ pullback X.hom f₁ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s)
    (by rw [pullback.condition, h, Category.assoc])

variable {T₁ T₂ T₃ : C} {f₁ : T₁ ⟶ S} {f₂ : T₂ ⟶ S} {f₃ : T₃ ⟶ S}

@[reassoc (attr := simp)]
theorem xc_fst (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc X s h ≫ pullback.fst X.hom f₁ = pullback.fst X.hom f₂ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem xc_snd (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc X s h ≫ pullback.snd X.hom f₁ = pullback.snd X.hom f₂ ≫ s := pullback.lift_snd _ _ _

/-- The comparison square over `s` is a pullback. -/
theorem xc_isPullback (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    IsPullback (xc X s h) (pullback.snd X.hom f₂) (pullback.snd X.hom f₁) s := by
  have sq : IsPullback (pullback.fst X.hom f₂) (pullback.snd X.hom f₂) X.hom (s ≫ f₁) := by
    rw [← h]; exact IsPullback.of_hasPullback _ _
  have e : xc X s h = (IsPullback.of_hasPullback X.hom f₁).lift (pullback.fst X.hom f₂)
      (pullback.snd X.hom f₂ ≫ s) (by rw [sq.w, Category.assoc]) := by
    apply pullback.hom_ext
    · rw [xc_fst]; exact (IsPullback.lift_fst _ _ _ _).symm
    · rw [xc_snd]; exact (IsPullback.lift_snd _ _ _ _).symm
  rw [e]
  exact IsPullback.of_right' sq (IsPullback.of_hasPullback X.hom f₁)

theorem xc_comp (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) (s' : T₃ ⟶ T₂) (h' : f₃ = s' ≫ f₂)
    (h'' : f₃ = (s' ≫ s) ≫ f₁) : xc X s' h' ≫ xc X s h = xc X (s' ≫ s) h'' := by
  apply pullback.hom_ext <;> simp

theorem xc_comp_eq (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) (s' : T₃ ⟶ T₂) (h' : f₃ = s' ≫ f₂)
    (t : T₃ ⟶ T₁) (ht : f₃ = t ≫ f₁) (hst : s' ≫ s = t) :
    xc X s' h' ≫ xc X s h = xc X t ht := by
  subst hst; exact xc_comp X s h s' h' ht

theorem xc_congr {s s' : T₂ ⟶ T₁} (hs : s = s') (h : f₂ = s ≫ f₁) (h' : f₂ = s' ≫ f₁) :
    xc X s h = xc X s' h' := by
  subst hs; rfl

theorem xc_self (s : T₁ ⟶ T₁) (hs : s = 𝟙 T₁) (h : f₁ = s ≫ f₁) : xc X s h = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · rw [xc_snd, hs, Category.comp_id, Category.id_comp]

/-- `xc` intertwines base-changed endomorphisms. -/
theorem xc_map (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) (f : X ⟶ X) :
    ((Over.pullback f₂).map f).left ≫ xc X s h = xc X s h ≫ ((Over.pullback f₁).map f).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, xc_fst, Over.pullback_map_left, pullback.lift_fst, xc_fst_assoc]
  · simp only [Category.assoc, xc_snd, Over.pullback_map_left, pullback.lift_snd,
      pullback.lift_snd_assoc]

/-- `xc` on the self-products. -/
noncomputable def xc2 (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    ((Over.pullback f₂).obj X ⊗ (Over.pullback f₂).obj X).left ⟶
      ((Over.pullback f₁).obj X ⊗ (Over.pullback f₁).obj X).left :=
  pullback.lift (pullback.fst _ _ ≫ xc X s h) (pullback.snd _ _ ≫ xc X s h) (by
    show (pullback.fst _ _ ≫ xc X s h) ≫ pullback.snd X.hom f₁ =
      (pullback.snd _ _ ≫ xc X s h) ≫ pullback.snd X.hom f₁
    simp only [Category.assoc, xc_snd]
    exact pullback.condition_assoc s)

@[reassoc (attr := simp)]
theorem xc2_fst (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc2 X s h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ xc X s h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem xc2_snd (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc2 X s h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ xc X s h :=
  pullback.lift_snd _ _ _

/-- **`xc` respects the multiplications.** -/
theorem xc_mul [MonObj X] (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    (μ[(Over.pullback f₂).obj X]).left ≫ xc X s h =
      xc2 X s h ≫ (μ[(Over.pullback f₁).obj X]).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, xc_fst, Category.assoc, G4Conj.mul_left_fst, G4Conj.mul_left_fst,
      ← Category.assoc (xc2 X s h)]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, xc2_fst_assoc, xc_fst]
    · simp only [Category.assoc, pullback.lift_snd, xc2_snd_assoc, xc_fst]
  · rw [Category.assoc, xc_snd, Category.assoc]
    have h2 := Over.w (μ[(Over.pullback f₂).obj X])
    have h1 := Over.w (μ[(Over.pullback f₁).obj X])
    erw [← Category.assoc, h2, h1]
    show (pullback.fst _ _ ≫ pullback.snd X.hom f₂) ≫ s =
      xc2 X s h ≫ (pullback.fst _ _ ≫ pullback.snd X.hom f₁)
    rw [xc2_fst_assoc, xc_snd, Category.assoc]

/-- **`xc` respects the units.** -/
theorem xc_one [MonObj X] (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    (η[(Over.pullback f₂).obj X]).left ≫ xc X s h = s ≫ (η[(Over.pullback f₁).obj X]).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, xc_fst, G4Conj.one_left_fst, Category.assoc, G4Conj.one_left_fst, h,
      Category.assoc]
  · rw [Category.assoc, xc_snd, Category.assoc]
    have h2 := Over.w (η[(Over.pullback f₂).obj X])
    have h1 := Over.w (η[(Over.pullback f₁).obj X])
    erw [← Category.assoc, h2, h1]
    simp

end TwistDescentXC

end TwistDescentXC


/-! # twist-descent, part HFD: descent of `G_L`-invariant morphisms between conjugates

For a field `K ⊆ ℚ̄`, `K`-schemes `X` (quasi-compact, quasi-separated) and `Y` (locally of finite
presentation), a number field `L ⊆ ℚ̄` and two embeddings `e₁L, e₂L : K → L`, a `ℚ̄`-morphism
`φ : X ×_{K,e₁} ℚ̄ → Y ×_{K,e₂} ℚ̄` (`eᵢ = (L ↪ ℚ̄) ∘ eᵢL`) that commutes with the Galois translates
by `G_L` is the base change of a morphism `X ×_{K,e₁L} L → Y ×_{K,e₂L} L` (`hfd`). Proof: EGA IV₃ 8.8.2 (`MorphDescend.exists_descend`,
proved) descends `φ` to a finite `L₁ ⊇ L`; pass to the normal closure `L'` of `L₁`; the descended
morphism is `Gal(L'/L)`-invariant (checked after the epimorphism `B_{ℚ̄} → B_{L'}`), so it descends
to `L` by `TwistDescentGD.descend` (Galois descent along `L'/L`, from Mathlib's fpqc descent). -/

section TwistDescentHFD

open CategoryTheory AlgebraicGeometry Limits
open TwistDescentXC

namespace TwistDescentHFD

/-- `Spec` of a ring map. -/
noncomputable abbrev sp {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom f)

theorem sp_comp_eq {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (s : R₁ →+* R₂)
    (t : R₂ →+* R₃) (u : R₁ →+* R₃) (h : ∀ x, t (s x) = u x) : sp t ≫ sp s = sp u := by
  rw [sp, sp, sp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact h x

theorem sp_eq {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (s : R₁ →+* R₂)
    (t : R₂ →+* R₃) (u : R₁ →+* R₃) (h : ∀ x, t (s x) = u x) : sp u = sp t ≫ sp s :=
  (sp_comp_eq s t u h).symm

theorem sp_id_eq {R : Type} [CommRing R] (t : R →+* R) (h : ∀ x, t x = x) : sp t = 𝟙 _ := by
  rw [sp, ← Spec.map_id]
  congr 1
  ext x
  exact h x

abbrev Qb : Type := AlgebraicClosure ℚ

variable {K : IntermediateField ℚ Qb} (X Y : Over (Spec (CommRingCat.of K)))

/-- `ℚ̄ → B_{L'}` comparisons are epimorphisms (flat surjective quasi-compact base change). -/
theorem xc_epi {L : IntermediateField ℚ Qb} (eL : K →+* L) (e : K →+* Qb)
    (h : sp e = sp (algebraMap L Qb) ≫ sp eL) : Epi (xc X (sp (algebraMap L Qb)) h) :=
  TwistDescentGD.epi_of_isPullback_field (xc_isPullback X _ h)

/-- **Hom-field descent.** -/
theorem hfd [QuasiCompact X.hom] [QuasiSeparated X.hom] [LocallyOfFinitePresentation Y.hom]
    {L : IntermediateField ℚ Qb} [FiniteDimensional ℚ L]
    (e₁L e₂L : K →+* L) (e₁ e₂ : K →+* Qb)
    (h₁ : sp e₁ = sp (algebraMap L Qb) ≫ sp e₁L) (h₂ : sp e₂ = sp (algebraMap L Qb) ≫ sp e₂L)
    (he₁ : ∀ x, (e₁L x : Qb) = e₁ x) (he₂ : ∀ x, (e₂L x : Qb) = e₂ x)
    (φ : pullback X.hom (sp e₁) ⟶ pullback Y.hom (sp e₂))
    (hφ : φ ≫ pullback.snd _ _ = pullback.snd _ _)
    (hinv : ∀ k : Qb ≃ₐ[ℚ] Qb, k ∈ L.fixingSubgroup →
      ∀ (k₁ : sp e₁ = sp (k : Qb →+* Qb) ≫ sp e₁) (k₂ : sp e₂ = sp (k : Qb →+* Qb) ≫ sp e₂),
        xc X (sp (k : Qb →+* Qb)) k₁ ≫ φ = φ ≫ xc Y (sp (k : Qb →+* Qb)) k₂) :
    ∃ φL : pullback X.hom (sp e₁L) ⟶ pullback Y.hom (sp e₂L),
      xc X (sp (algebraMap L Qb)) h₁ ≫ φL = φ ≫ xc Y (sp (algebraMap L Qb)) h₂ := by
  have hm₁ : ∀ x, e₁ x ∈ L := fun x => he₁ x ▸ (e₁L x).2
  have hm₂ : ∀ x, e₂ x ∈ L := fun x => he₂ x ▸ (e₂L x).2
  obtain ⟨L₁, ψ, hψ⟩ := MorphDescend.exists_descend L X Y e₁ e₂ hm₁ hm₂ φ hφ
  obtain ⟨L₁, hfin₁, hLL₁⟩ := L₁
  let L' : IntermediateField ℚ Qb := IntermediateField.normalClosure ℚ L₁ Qb
  have hL₁L' : L₁ ≤ L' := IntermediateField.le_normalClosure L₁
  have hLL' : L ≤ L' := hLL₁.trans hL₁L'
  let _ : Algebra L L' := G0ModField.incAlg hLL'
  have : IsScalarTower ℚ L L' := IsScalarTower.of_algebraMap_eq fun x => rfl
  have : FiniteDimensional ℚ L₁ := hfin₁
  have : FiniteDimensional ℚ L' := inferInstance
  have : IsGalois ℚ L' := inferInstance
  have : FiniteDimensional L L' := FiniteDimensional.right ℚ L L'
  have : IsGalois L L' := IsGalois.tower_top_of_isGalois ℚ L L'
  -- the maps at level `L'`
  let e₁' : K →+* L' := (algebraMap L L').comp e₁L
  have hq : sp e₁' = sp (algebraMap L L') ≫ sp e₁L := sp_eq _ _ _ fun _ => rfl
  let q : pullback X.hom (sp e₁') ⟶ pullback X.hom (sp e₁L) := xc X (sp (algebraMap L L')) hq
  have hpb := xc_isPullback X (sp (algebraMap L L')) hq
  let r₁ := MorphDescend.restrL L e₁ hm₁ ⟨L₁, hfin₁, hLL₁⟩
  let r₂ := MorphDescend.restrL L e₂ hm₂ ⟨L₁, hfin₁, hLL₁⟩
  have ha : sp e₁' = sp (IntermediateField.inclusion hL₁L' : L₁ →+* L') ≫ sp r₁ :=
    sp_eq _ _ _ fun x => Subtype.ext (he₁ x).symm
  have hb : sp r₂ = sp (IntermediateField.inclusion hLL₁ : L →+* L₁) ≫ sp e₂L :=
    sp_eq _ _ _ fun x => Subtype.ext (he₂ x)
  let f : pullback X.hom (sp e₁') ⟶ pullback Y.hom (sp e₂L) :=
    xc X (sp (IntermediateField.inclusion hL₁L' : L₁ →+* L')) ha ≫ ψ ≫
      xc Y (sp (IntermediateField.inclusion hLL₁ : L →+* L₁)) hb
  have hQ' : sp e₁ = sp (algebraMap L' Qb) ≫ sp e₁' := sp_eq _ _ _ fun x => (he₁ x)
  have hepi : Epi (xc X (sp (algebraMap L' Qb)) hQ') := xc_epi X e₁' e₁ hQ'
  -- `f` after `ℚ̄ → L'` is `φ ≫ (ℚ̄ → L)`
  have hfQ : xc X (sp (algebraMap L' Qb)) hQ' ≫ f = φ ≫ xc Y (sp (algebraMap L Qb)) h₂ := by
    have c1 : xc X (sp (algebraMap L' Qb)) hQ' ≫
        xc X (sp (IntermediateField.inclusion hL₁L' : L₁ →+* L')) ha =
        MorphDescend.cmp L X e₁ hm₁ ⟨L₁, hfin₁, hLL₁⟩ :=
      xc_comp_eq X _ _ _ _ (sp (algebraMap L₁ Qb)) (sp_eq _ _ _ fun _ => rfl)
        (sp_comp_eq _ _ _ fun _ => rfl)
    have c2 : MorphDescend.cmp L Y e₂ hm₂ ⟨L₁, hfin₁, hLL₁⟩ ≫
        xc Y (sp (IntermediateField.inclusion hLL₁ : L →+* L₁)) hb =
        xc Y (sp (algebraMap L Qb)) h₂ :=
      xc_comp_eq Y _ _ (sp (algebraMap L₁ Qb)) (sp_eq _ _ _ fun _ => rfl) _ _
        (sp_comp_eq _ _ _ fun _ => rfl)
    simp only [f]
    rw [← Category.assoc, c1, ← reassoc_of% hψ, c2]
  obtain ⟨φL, hφL⟩ := TwistDescentGD.descend hpb f (fun g => by
    have hc : sp e₁' = sp (g : L' →+* L') ≫ sp e₁' :=
      sp_eq _ _ _ fun x => g.commutes (e₁L x)
    refine ⟨xc X (sp (g : L' →+* L')) hc, ?_, xc_snd _ _ _, ?_⟩
    · exact xc_comp_eq X _ _ _ _ _ _ (sp_comp_eq _ _ _ fun y => g.commutes y)
    · -- lift `g` to `k ∈ G_ℚ`
      obtain ⟨k, hk⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := L') (E := Qb)
        (g.restrictScalars ℚ)
      have hkx : ∀ x : L', k (x : Qb) = (g x : Qb) := fun x => by
        rw [← AlgEquiv.restrictNormalHom_apply L' k x, hk]; rfl
      have hkL : k ∈ L.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        have := hkx (algebraMap L L' ⟨y, hy⟩)
        rw [g.commutes] at this
        exact this
      have hkL' : ∀ y : L, k (y : Qb) = y := fun y =>
        (IntermediateField.mem_fixingSubgroup_iff L k).mp hkL y y.2
      have k₁ : sp e₁ = sp (k : Qb →+* Qb) ≫ sp e₁ :=
        sp_eq _ _ _ fun x => by rw [← he₁ x]; exact hkL' _
      have k₂ : sp e₂ = sp (k : Qb →+* Qb) ≫ sp e₂ :=
        sp_eq _ _ _ fun x => by rw [← he₂ x]; exact hkL' _
      have hu : sp e₁ = sp ((algebraMap L' Qb).comp (g : L' →+* L')) ≫ sp e₁' :=
        sp_eq _ _ _ fun x => by
          show ((g (algebraMap L L' (e₁L x)) : L') : Qb) = e₁ x
          rw [g.commutes]; exact he₁ x
      have c4 : xc X (sp (algebraMap L' Qb)) hQ' ≫ xc X (sp (g : L' →+* L')) hc =
          xc X (sp (k : Qb →+* Qb)) k₁ ≫ xc X (sp (algebraMap L' Qb)) hQ' :=
        (xc_comp_eq X _ _ _ _ _ hu (sp_comp_eq _ _ _ fun _ => rfl)).trans
          (xc_comp_eq X _ _ _ _ _ hu (sp_comp_eq _ _ _ fun x => hkx x)).symm
      have c5 : xc Y (sp (k : Qb →+* Qb)) k₂ ≫ xc Y (sp (algebraMap L Qb)) h₂ =
          xc Y (sp (algebraMap L Qb)) h₂ :=
        xc_comp_eq Y _ _ _ _ _ _ (sp_comp_eq _ _ _ fun y => hkL' y)
      rw [← cancel_epi (xc X (sp (algebraMap L' Qb)) hQ'), ← Category.assoc, c4,
        Category.assoc, hfQ, ← Category.assoc, hinv k hkL k₁ k₂, Category.assoc, c5])
  refine ⟨φL, ?_⟩
  have c3 : xc X (sp (algebraMap L Qb)) h₁ = xc X (sp (algebraMap L' Qb)) hQ' ≫ q :=
    (xc_comp_eq X _ _ _ _ _ _ (sp_comp_eq _ _ _ fun _ => rfl)).symm
  rw [c3, Category.assoc, hφL, hfQ]

end TwistDescentHFD

end TwistDescentHFD


/-! # twist-descent, part MAIN: `TwistDescent` (kf-glue) proved

For `σ ∈ G_ℚ` with restriction `ρ = σ|_L`: the hypothesis gives a twisted isomorphism
`φ : B_{e₀} ≅ B_{σ⁻¹e₀}` over `ℚ̄` (`e₀ : K ↪ ℚ̄`); it is `G_L`-invariant (`L` is a Hom field,
`td_hom_inv`), so it descends to `φ_L : B_L → B ×_{K,τ∘(K↪L)} L` (`hfd`, `τ = σ⁻¹|_L`); then
`E = φ_L ≫ c_τ`, with `c_τ` the comparison over `Spec τ`. `φ_L` is a homomorphism by rigidity
(`G0FibreSimple.rigidityHom`, proved in kf-glue). `E` and `α` are chosen as functions of `σ|_L`,
with `E = 𝟙`, `α = id` on the trivial class (`twistDescent`). -/

section TwistDescentMain

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
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
  obtain ⟨φL, hφL⟩ := hfd B.X B.X e₁L e₂L _ _ h₁ h₂ he₁ he₂ φ₀ hφs
    (fun k hk k₁ k₂ => td_hom_inv B hKL hHF e₀ e₂ φ k hk k₁ k₂)
  obtain ⟨ψL, hψL⟩ := hfd B.X B.X e₂L e₁L _ _ h₂ h₁ he₂ he₁ ψ₀ hψs
    (fun k hk k₁ k₂ => td_hom_inv B hKL hHF e₂ e₀ ψ k hk k₁ k₂)
  have ep₁ := xc_epi B.X e₁L _ h₁
  have ep₂ := xc_epi B.X e₂L _ h₂
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


/-! # twist-descent, part GDM: kf-glue's `GaloisDescentMor` proved

kf-glue stated (unused) the standard Galois descent of morphisms along `ℚ̄/L` as
`GaloisDescentMor`. It follows from `TwistDescentHFD.hfd` with `K = L`, `e₁L = e₂L = id`, and
`X ×_{L,id} L ≅ X`; uniqueness because `X_{ℚ̄} → X` is an epimorphism. -/

section TwistDescentGDM

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open TwistDescentXC TwistDescentHFD

namespace G0ModField.KernelField

open G0ModField

/-- **`GaloisDescentMor` holds** (kf-glue's statement, verbatim; no hypotheses). -/
theorem galoisDescentMor : GaloisDescentMor := by
  intro L _ X Y _ _ _ φ hφ
  have h₀ : sp (algebraMap L Qbar) = sp (algebraMap L Qbar) ≫ sp (RingHom.id L) :=
    sp_eq _ _ _ fun _ => rfl
  have hφs : φ.left ≫ pullback.snd Y.hom (sp (algebraMap L Qbar)) =
      pullback.snd X.hom (sp (algebraMap L Qbar)) := Over.w φ
  have hinv : ∀ k : Qbar ≃ₐ[ℚ] Qbar, k ∈ L.fixingSubgroup →
      ∀ (k₁ : sp (algebraMap L Qbar) = sp (k : Qbar →+* Qbar) ≫ sp (algebraMap L Qbar))
        (k₂ : sp (algebraMap L Qbar) = sp (k : Qbar →+* Qbar) ≫ sp (algebraMap L Qbar)),
        xc X (sp (k : Qbar →+* Qbar)) k₁ ≫ φ.left = φ.left ≫ xc Y (sp (k : Qbar →+* Qbar)) k₂ := by
    intro k hk k₁ k₂
    have := G4Conj.conj_cmp X Y (G4WeilRes.specGal k) k₁ k₁ φ
    rw [hφ k hk k₁] at this
    exact this.symm
  obtain ⟨φL, hφL⟩ := hfd X Y (RingHom.id L) (RingHom.id L) (algebraMap L Qbar)
    (algebraMap L Qbar) h₀ h₀ (fun _ => rfl) (fun _ => rfl) φ.left hφs hinv
  have hepi : Epi (xc X (sp (algebraMap L Qbar)) h₀) := xc_epi X (RingHom.id L) _ h₀
  have hφLs : φL ≫ pullback.snd Y.hom (sp (RingHom.id L)) =
      pullback.snd X.hom (sp (RingHom.id L)) := by
    rw [← cancel_epi (xc X (sp (algebraMap L Qbar)) h₀), ← Category.assoc, hφL,
      Category.assoc, xc_snd, ← Category.assoc, hφs, xc_snd]
  have hid : sp (RingHom.id L) = 𝟙 _ := sp_id_eq _ fun _ => rfl
  let j : X.left ⟶ pullback X.hom (sp (RingHom.id L)) :=
    pullback.lift (𝟙 _) X.hom (by rw [Category.id_comp, hid, Category.comp_id])
  let ψ0 : X.left ⟶ Y.left := j ≫ φL ≫ pullback.fst _ _
  have hψw : ψ0 ≫ Y.hom = X.hom := by
    simp only [ψ0, Category.assoc]
    rw [pullback.condition, reassoc_of% hφLs]
    simp only [j, pullback.lift_snd_assoc]
    rw [hid, Category.comp_id]
  have hj : pullback.fst X.hom (sp (algebraMap L Qbar)) ≫ j = xc X (sp (algebraMap L Qbar)) h₀ := by
    apply pullback.hom_ext
    · simp [j]
    · simp only [j, Category.assoc, pullback.lift_snd, xc_snd]
      rw [pullback.condition]
  have hex : (Over.pullback (G4WeilRes.specIncl L)).map (Over.homMk ψ0 hψw) = φ := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.lift_fst, Over.homMk_left]
      show pullback.fst _ _ ≫ j ≫ φL ≫ pullback.fst _ _ = φ.left ≫ pullback.fst _ _
      rw [← Category.assoc, hj, ← Category.assoc, hφL, Category.assoc, xc_fst]
    · simp only [Over.pullback_map_left, pullback.lift_snd]
      exact hφs.symm
  refine ⟨Over.homMk ψ0 hψw, hex, fun ψ' hψ' => ?_⟩
  have hfe : Epi (pullback.fst X.hom (sp (algebraMap L Qbar))) :=
    TwistDescentGD.epi_of_isPullback_field (IsPullback.of_hasPullback X.hom _)
  apply Over.OverMorphism.ext
  apply (cancel_epi (pullback.fst X.hom (sp (algebraMap L Qbar)))).mp
  have e1 := congrArg (fun f => f.left ≫ pullback.fst Y.hom (sp (algebraMap L Qbar)))
    (hψ'.trans hex.symm)
  simp only [Over.pullback_map_left, pullback.lift_fst] at e1
  exact e1

end G0ModField.KernelField

end TwistDescentGDM



/-! # twist-descent, part FINAL: consequences (kf-glue's reductions with `TwistDescent` discharged) -/

section TwistDescentFinal

namespace G0ModField.KernelField

/-- **`ConjIsogMaps` from `MulIsogeny` alone** (kf-glue's `conjIsogMaps_of_descent` with
`twistDescent`). -/
theorem conjIsogMaps_of_mulIsogeny (hMul : G0FibreSimple.MulIsogeny) : ConjIsogMaps :=
  conjIsogMaps_of_descent hMul twistDescent

/-- **`ConjIsogMaps` from mul-rigidity's leaf `KerUnitOpen` alone.** -/
theorem conjIsogMaps_of_kerUnitOpen' (hK : MulRigidity.KerUnitOpen) : ConjIsogMaps :=
  conjIsogMaps_of_kerUnitOpen hK twistDescent

/-- **`ConjIsogMaps` from mul-rigidity's two cotangent glue statements alone.** -/
theorem conjIsogMaps_of_cotangent' (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) : ConjIsogMaps :=
  conjIsogMaps_of_cotangent h1 h2 twistDescent

/-- **`KernelFieldExists` without `TwistDescent`.** Leaves: T6, NOS, Raynaud, TorsionStructure,
T27, `KerUnitOpen`; glue: FS5 `FibreComTrivial`. -/
theorem kernelFieldExists_of_kerUnitOpen' (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hK : MulRigidity.KerUnitOpen) :
    KernelFieldExists :=
  kernelFieldExists_of_kerUnitOpen hHFF hNOS hRay hTors t27 h5 hK twistDescent

/-- **`KernelFieldExists` without `TwistDescent`**, with `MulIsogeny`. -/
theorem kernelFieldExists_of_mulIsogeny (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hMul : G0FibreSimple.MulIsogeny) :
    KernelFieldExists :=
  kernelFieldExists_of_descent hHFF hNOS hRay hTors t27 h5 hMul twistDescent

end G0ModField.KernelField

end TwistDescentFinal


