import KfGlue
import ZInQKernel.Contrib.TwistDescent.GaloisDescent
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

For a number field `K ⊆ ℚ̄`, an abelian variety `B/K`, a finite Galois `L ⊆ ℚ̄` and two embeddings
`e₁L, e₂L : K → L`, a `ℚ̄`-morphism `φ : B ×_{K,e₁} ℚ̄ → B ×_{K,e₂} ℚ̄` (`eᵢ = (L ↪ ℚ̄) ∘ eᵢL`) that
commutes with the Galois translates by `G_L` is the base change of a morphism
`B ×_{K,e₁L} L → B ×_{K,e₂L} L` (`hfd`). Proof: EGA IV₃ 8.8.2 (`MorphDescend.exists_descend`,
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

variable {K : IntermediateField ℚ Qb} (B : PkgI3.AbVar K)

/-- `ℚ̄ → B_{L'}` comparisons are epimorphisms (flat surjective quasi-compact base change). -/
theorem xc_epi {L : IntermediateField ℚ Qb} (eL : K →+* L) (e : K →+* Qb)
    (h : sp e = sp (algebraMap L Qb) ≫ sp eL) : Epi (xc B.X (sp (algebraMap L Qb)) h) :=
  TwistDescentGD.epi_of_isPullback_field (xc_isPullback B.X _ h)

/-- **Hom-field descent.** -/
theorem hfd {L : IntermediateField ℚ Qb} [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (e₁L e₂L : K →+* L) (e₁ e₂ : K →+* Qb)
    (h₁ : sp e₁ = sp (algebraMap L Qb) ≫ sp e₁L) (h₂ : sp e₂ = sp (algebraMap L Qb) ≫ sp e₂L)
    (he₁ : ∀ x, (e₁L x : Qb) = e₁ x) (he₂ : ∀ x, (e₂L x : Qb) = e₂ x)
    (φ : pullback B.X.hom (sp e₁) ⟶ pullback B.X.hom (sp e₂))
    (hφ : φ ≫ pullback.snd _ _ = pullback.snd _ _)
    (hinv : ∀ k : Qb ≃ₐ[ℚ] Qb, k ∈ L.fixingSubgroup →
      ∀ (k₁ : sp e₁ = sp (k : Qb →+* Qb) ≫ sp e₁) (k₂ : sp e₂ = sp (k : Qb →+* Qb) ≫ sp e₂),
        xc B.X (sp (k : Qb →+* Qb)) k₁ ≫ φ = φ ≫ xc B.X (sp (k : Qb →+* Qb)) k₂) :
    ∃ φL : pullback B.X.hom (sp e₁L) ⟶ pullback B.X.hom (sp e₂L),
      xc B.X (sp (algebraMap L Qb)) h₁ ≫ φL = φ ≫ xc B.X (sp (algebraMap L Qb)) h₂ := by
  have hm₁ : ∀ x, e₁ x ∈ L := fun x => he₁ x ▸ (e₁L x).2
  have hm₂ : ∀ x, e₂ x ∈ L := fun x => he₂ x ▸ (e₂L x).2
  obtain ⟨L₁, ψ, hψ⟩ := MorphDescend.exists_descend L B.X B.X e₁ e₂ hm₁ hm₂ φ hφ
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
  let q : pullback B.X.hom (sp e₁') ⟶ pullback B.X.hom (sp e₁L) := xc B.X (sp (algebraMap L L')) hq
  have hpb := xc_isPullback B.X (sp (algebraMap L L')) hq
  let r₁ := MorphDescend.restrL L e₁ hm₁ ⟨L₁, hfin₁, hLL₁⟩
  let r₂ := MorphDescend.restrL L e₂ hm₂ ⟨L₁, hfin₁, hLL₁⟩
  have ha : sp e₁' = sp (IntermediateField.inclusion hL₁L' : L₁ →+* L') ≫ sp r₁ :=
    sp_eq _ _ _ fun x => Subtype.ext (he₁ x).symm
  have hb : sp r₂ = sp (IntermediateField.inclusion hLL₁ : L →+* L₁) ≫ sp e₂L :=
    sp_eq _ _ _ fun x => Subtype.ext (he₂ x)
  let f : pullback B.X.hom (sp e₁') ⟶ pullback B.X.hom (sp e₂L) :=
    xc B.X (sp (IntermediateField.inclusion hL₁L' : L₁ →+* L')) ha ≫ ψ ≫
      xc B.X (sp (IntermediateField.inclusion hLL₁ : L →+* L₁)) hb
  have hQ' : sp e₁ = sp (algebraMap L' Qb) ≫ sp e₁' := sp_eq _ _ _ fun x => (he₁ x)
  have hepi : Epi (xc B.X (sp (algebraMap L' Qb)) hQ') := xc_epi B e₁' e₁ hQ'
  -- `f` after `ℚ̄ → L'` is `φ ≫ (ℚ̄ → L)`
  have hfQ : xc B.X (sp (algebraMap L' Qb)) hQ' ≫ f = φ ≫ xc B.X (sp (algebraMap L Qb)) h₂ := by
    have c1 : xc B.X (sp (algebraMap L' Qb)) hQ' ≫
        xc B.X (sp (IntermediateField.inclusion hL₁L' : L₁ →+* L')) ha =
        MorphDescend.cmp L B.X e₁ hm₁ ⟨L₁, hfin₁, hLL₁⟩ :=
      xc_comp_eq B.X _ _ _ _ (sp (algebraMap L₁ Qb)) (sp_eq _ _ _ fun _ => rfl)
        (sp_comp_eq _ _ _ fun _ => rfl)
    have c2 : MorphDescend.cmp L B.X e₂ hm₂ ⟨L₁, hfin₁, hLL₁⟩ ≫
        xc B.X (sp (IntermediateField.inclusion hLL₁ : L →+* L₁)) hb =
        xc B.X (sp (algebraMap L Qb)) h₂ :=
      xc_comp_eq B.X _ _ (sp (algebraMap L₁ Qb)) (sp_eq _ _ _ fun _ => rfl) _ _
        (sp_comp_eq _ _ _ fun _ => rfl)
    simp only [f]
    rw [← Category.assoc, c1, ← reassoc_of% hψ, c2]
  obtain ⟨φL, hφL⟩ := TwistDescentGD.descend hpb f (fun g => by
    have hc : sp e₁' = sp (g : L' →+* L') ≫ sp e₁' :=
      sp_eq _ _ _ fun x => g.commutes (e₁L x)
    refine ⟨xc B.X (sp (g : L' →+* L')) hc, ?_, xc_snd _ _ _, ?_⟩
    · exact xc_comp_eq B.X _ _ _ _ _ _ (sp_comp_eq _ _ _ fun y => g.commutes y)
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
      have c4 : xc B.X (sp (algebraMap L' Qb)) hQ' ≫ xc B.X (sp (g : L' →+* L')) hc =
          xc B.X (sp (k : Qb →+* Qb)) k₁ ≫ xc B.X (sp (algebraMap L' Qb)) hQ' :=
        (xc_comp_eq B.X _ _ _ _ _ hu (sp_comp_eq _ _ _ fun _ => rfl)).trans
          (xc_comp_eq B.X _ _ _ _ _ hu (sp_comp_eq _ _ _ fun x => hkx x)).symm
      have c5 : xc B.X (sp (k : Qb →+* Qb)) k₂ ≫ xc B.X (sp (algebraMap L Qb)) h₂ =
          xc B.X (sp (algebraMap L Qb)) h₂ :=
        xc_comp_eq B.X _ _ _ _ _ _ (sp_comp_eq _ _ _ fun y => hkL' y)
      rw [← cancel_epi (xc B.X (sp (algebraMap L' Qb)) hQ'), ← Category.assoc, c4,
        Category.assoc, hfQ, ← Category.assoc, hinv k hkL k₁ k₂, Category.assoc, c5])
  refine ⟨φL, ?_⟩
  have c3 : xc B.X (sp (algebraMap L Qb)) h₁ = xc B.X (sp (algebraMap L' Qb)) hQ' ≫ q :=
    (xc_comp_eq B.X _ _ _ _ _ _ (sp_comp_eq _ _ _ fun _ => rfl)).symm
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

end G0ModField.KernelField

end TwistDescentMain
