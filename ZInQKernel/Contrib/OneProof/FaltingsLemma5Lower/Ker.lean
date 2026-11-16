import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower.Surj
import ZInQKernel.Contrib.AbVarBC.KerUnit

/-! faltings5-lower, part 7: `IsogKerCard`. The kernel of a finite homomorphism `φ` is the finite
`K`-scheme `X ×_{φ, Y, e} Spec K`; its points with values in a field `Ω` are ring maps from the finite
`K`-algebra `R = Γ(ker φ)`. A complex point lands in the algebraic closure of `K` in `ℂ`, which is the
image of `ι : K̄ → ℂ`; so every complex point of the kernel comes from a `K̄`-point, and the
`K̄`-points are finitely many (`Finite.algHom`). -/

set_option linter.style.haveILetI false

namespace GapHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Contrib.AbVarBC.Tangent Polynomial

section Ker

variable {K : Type} [Field K] {X Y : Over (Spec (CommRingCat.of K))} [MonObj X] [MonObj Y]

/-- The unit section `Spec K → Y`. -/
noncomputable def e0 (Y : Over (Spec (CommRingCat.of K))) [MonObj Y] :
    Spec (CommRingCat.of K) ⟶ Y.left := (η[Y] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y).left

theorem e0_hom : e0 Y ≫ Y.hom = 𝟙 _ := Over.w (η[Y] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y)

theorem one_left' {Ω : Type} [Field Ω] (σ : K →+* Ω) :
    (1 : ptK σ ⟶ Y).left = Spec.map (CommRingCat.ofHom σ) ≫ e0 Y := by
  rw [Hom.one_def, Over.comp_left]
  rfl

variable (φ : X ⟶ Y)

/-- The kernel scheme `X ×_{φ, Y, e} Spec K`. -/
noncomputable abbrev kerSch : Scheme := pullback φ.left (e0 Y)

/-- `Ω`-points of the kernel scheme over `σ`. -/
def kerSchPts {Ω : Type} [Field Ω] (σ : K →+* Ω) : Type :=
  {g : Spec (CommRingCat.of Ω) ⟶ kerSch φ //
    g ≫ pullback.snd φ.left (e0 Y) = Spec.map (CommRingCat.ofHom σ)}

omit [MonObj X] in
theorem kerSch_w {Ω : Type} [Field Ω] (σ : K →+* Ω) (g : kerSchPts φ σ) :
    (g.1 ≫ pullback.fst φ.left (e0 Y)) ≫ X.hom = Spec.map (CommRingCat.ofHom σ) := by
  rw [← Over.w φ, Category.assoc, ← Category.assoc (pullback.fst _ _), pullback.condition,
    Category.assoc, e0_hom, Category.comp_id]
  exact g.2

omit [MonObj X] in
theorem kerSch_cond {Ω : Type} [Field Ω] (σ : K →+* Ω) (g : kerSchPts φ σ) :
    (g.1 ≫ pullback.fst φ.left (e0 Y)) ≫ φ.left = Spec.map (CommRingCat.ofHom σ) ≫ e0 Y := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ e0 Y) g.2

/-- The kernel point of a point of the kernel scheme. -/
noncomputable def kerPtOf {Ω : Type} [Field Ω] (σ : K →+* Ω) (g : kerSchPts φ σ) :
    ptK σ ⟶ X :=
  Over.homMk (g.1 ≫ pullback.fst φ.left (e0 Y)) (kerSch_w φ σ g)

theorem kerPtOf_comp {Ω : Type} [Field Ω] (σ : K →+* Ω) (g : kerSchPts φ σ) :
    kerPtOf φ σ g ≫ φ = 1 := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, one_left']
  exact kerSch_cond φ σ g

theorem kerPt_cond {Ω : Type} [Field Ω] (σ : K →+* Ω) (P : ptK σ ⟶ X) (hP : P ≫ φ = 1) :
    (P.left : Spec (CommRingCat.of Ω) ⟶ X.left) ≫ φ.left =
      Spec.map (CommRingCat.ofHom σ) ≫ e0 Y := by
  have h := congrArg Over.Hom.left hP
  rw [Over.comp_left, one_left'] at h
  exact h

/-- Kernel points are points of the kernel scheme. -/
noncomputable def kerSchEquiv {Ω : Type} [Field Ω] (σ : K →+* Ω) :
    {P : ptK σ ⟶ X // P ≫ φ = 1} ≃ kerSchPts φ σ where
  toFun P := ⟨pullback.lift (P.1.left : Spec (CommRingCat.of Ω) ⟶ X.left)
      (Spec.map (CommRingCat.ofHom σ)) (kerPt_cond φ σ P.1 P.2), pullback.lift_snd _ _ _⟩
  invFun g := ⟨kerPtOf φ σ g, kerPtOf_comp φ σ g⟩
  left_inv P := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact pullback.lift_fst (P.1.left : Spec (CommRingCat.of Ω) ⟶ X.left)
      (Spec.map (CommRingCat.ofHom σ)) (kerPt_cond φ σ P.1 P.2)
  right_inv g := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst (g.1 ≫ pullback.fst φ.left (e0 Y))
        (Spec.map (CommRingCat.ofHom σ)) (kerSch_cond φ σ g)
    · exact (pullback.lift_snd (g.1 ≫ pullback.fst φ.left (e0 Y))
        (Spec.map (CommRingCat.ofHom σ)) (kerSch_cond φ σ g)).trans g.2.symm

variable [IsFinite φ.left]

instance : IsAffine (kerSch φ) := isAffine_of_isAffineHom (pullback.snd φ.left (e0 Y))

/-- `K → Γ(ker φ)`, a finite ring map. -/
noncomputable def kerAlg : CommRingCat.of K ⟶ Γ(kerSch φ, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (pullback.snd φ.left (e0 Y)).appTop

theorem kerAlg_finite : (kerAlg φ).hom.Finite := by
  unfold kerAlg
  rw [CommRingCat.hom_comp]
  exact RingHom.Finite.comp (Scheme.Hom.finite_appTop _) (RingHom.Finite.of_surjective _
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.surjective)

theorem mem_top {Ω : Type} [Field Ω] (g : Spec (CommRingCat.of Ω) ⟶ kerSch φ) :
    g (IsLocalRing.closedPoint (CommRingCat.of Ω)) ∈ (⊤ : (kerSch φ).Opens) := trivial

/-- The ring map of a point of the kernel scheme. -/
noncomputable def kRing {Ω : Type} [Field Ω] (g : Spec (CommRingCat.of Ω) ⟶ kerSch φ) :
    Γ(kerSch φ, ⊤) ⟶ CommRingCat.of Ω :=
  ptRing (Λ := CommRingCat.of Ω) g (mem_top φ g)

omit [MonObj X] [MonObj Y] [IsFinite φ.left] in
theorem appLE_top_eq {S T : Scheme.{0}} (f : S ⟶ T) (h : (⊤ : S.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ h = f.appTop := by
  rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]
  rfl

omit [MonObj X] [MonObj Y] [IsFinite φ.left] in
/-- The ring map of `Spec ρ : Spec Ω → Spec K`. -/
theorem ptRing_specMap {Ω : Type} [Field Ω] (ρ : CommRingCat.of K ⟶ CommRingCat.of Ω) :
    ptRing (Λ := CommRingCat.of Ω) (U := (⊤ : (Spec (CommRingCat.of K)).Opens)) (Spec.map ρ)
      trivial = (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ ρ := by
  have h2 := ptRing_specMap_comp (Λ := CommRingCat.of K) (Λ' := CommRingCat.of Ω)
    (isAffineOpen_top (Spec (CommRingCat.of K))) ρ (𝟙 (Spec (CommRingCat.of K))) trivial trivial
  rw [ptRing_id_top] at h2
  rw [← h2]
  exact ptRing_congr (Category.comp_id _).symm _ _

theorem ptRing_comp_snd {Ω : Type} [Field Ω] (g : Spec (CommRingCat.of Ω) ⟶ kerSch φ) :
    ptRing (Λ := CommRingCat.of Ω) (U := (⊤ : (Spec (CommRingCat.of K)).Opens))
      (g ≫ pullback.snd φ.left (e0 Y)) trivial =
      (pullback.snd φ.left (e0 Y)).appTop ≫ kRing φ g :=
  (ptRing_comp (Λ := CommRingCat.of Ω) (isAffineOpen_top (kerSch φ))
    (pullback.snd φ.left (e0 Y)) (isAffineOpen_top _) le_top g (mem_top φ g) trivial).trans
    (congrArg (· ≫ ptRing (Λ := CommRingCat.of Ω) g (mem_top φ g)) (appLE_top_eq _ le_top))

theorem snd_kRing {Ω : Type} [Field Ω] (σ : K →+* Ω) (g : kerSchPts φ σ) :
    (pullback.snd φ.left (e0 Y)).appTop ≫ kRing φ g.1 =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom σ := by
  rw [← ptRing_comp_snd, ← ptRing_specMap]
  exact ptRing_congr g.2 _ _

/-- The ring map of a point over `σ` restricts to `σ` on `K`. -/
theorem kRing_comp {Ω : Type} [Field Ω] (σ : K →+* Ω) (g : kerSchPts φ σ) :
    kerAlg φ ≫ kRing φ g.1 = CommRingCat.ofHom σ := by
  unfold kerAlg
  rw [Category.assoc, snd_kRing, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- A point of the kernel scheme is determined by its ring map. -/
theorem kRing_injective {Ω : Type} [Field Ω] {g g' : Spec (CommRingCat.of Ω) ⟶ kerSch φ}
    (h : kRing φ g = kRing φ g') : g = g' :=
  ptRing_ext (isAffineOpen_top _) (mem_top φ g) (mem_top φ g') h

/-- The `K̄`-points of the kernel scheme are finitely many. -/
theorem finite_kerSchPts {Ω : Type} [Field Ω] (σ : K →+* Ω) : Finite (kerSchPts φ σ) := by
  letI : Algebra K Γ(kerSch φ, ⊤) := (kerAlg φ).hom.toAlgebra
  letI : Algebra K Ω := σ.toAlgebra
  haveI : Module.Finite K Γ(kerSch φ, ⊤) := kerAlg_finite φ
  let F : kerSchPts φ σ → (Γ(kerSch φ, ⊤) →ₐ[K] Ω) := fun g =>
    { toRingHom := (kRing φ g.1).hom
      commutes' := fun c => by
        have := congrArg (fun f => f.hom c) (kRing_comp φ σ g)
        exact this }
  refine Finite.of_injective F fun g g' h => Subtype.ext (kRing_injective φ ?_)
  ext x
  exact congrArg (fun f => f x) (congrArg AlgHom.toRingHom h)

end Ker

section Alg

variable {K : Type} [Field K]

/-- An element of `ℂ` integral over `K` (through `τ`) lies in the image of `ιK : K̄ → ℂ`. -/
theorem mem_range_of_monic (τ : K →+* ℂ) (ιK : AlgebraicClosure K →+* ℂ)
    (hι : ιK.comp (algebraMap K (AlgebraicClosure K)) = τ) (x : ℂ) (p : K[X]) (hp : p.Monic)
    (hx : p.eval₂ τ x = 0) : x ∈ ιK.range := by
  letI : Algebra (AlgebraicClosure K) ℂ := ιK.toAlgebra
  have hi : IsIntegral (AlgebraicClosure K) x := by
    refine ⟨p.map (algebraMap K (AlgebraicClosure K)), hp.map _, ?_⟩
    rw [eval₂_map]
    have : (algebraMap (AlgebraicClosure K) ℂ).comp (algebraMap K (AlgebraicClosure K)) = τ := hι
    rw [this, hx]
  have hd := IsAlgClosed.degree_eq_one_of_irreducible (AlgebraicClosure K) (minpoly.irreducible hi)
  exact minpoly.mem_range_of_degree_eq_one _ _ hd

end Alg

section Card

variable {K : Type} [Field K] {X Y : Over (Spec (CommRingCat.of K))} [MonObj X] [MonObj Y]
  (φ : X ⟶ Y) [IsFinite φ.left]

/-- **Every complex point of the kernel comes from a `K̄`-point.** -/
theorem kerSchPts_surj (τ : K →+* ℂ) (ιK : AlgebraicClosure K →+* ℂ)
    (hι : ιK.comp (algebraMap K (AlgebraicClosure K)) = τ) (g : kerSchPts φ τ) :
    ∃ g' : kerSchPts φ (algebraMap K (AlgebraicClosure K)),
      Spec.map (CommRingCat.ofHom ιK) ≫ g'.1 = g.1 := by
  set ρ := (kRing φ g.1).hom
  have hρ : ∀ r, ρ r ∈ ιK.range := by
    intro r
    letI : Algebra K Γ(kerSch φ, ⊤) := (kerAlg φ).hom.toAlgebra
    obtain ⟨p, hp, hpr⟩ := (kerAlg_finite φ).to_isIntegral r
    refine mem_range_of_monic τ ιK hι (ρ r) p hp ?_
    have hc : ρ.comp (kerAlg φ).hom = τ := by
      have := congrArg CommRingCat.Hom.hom (kRing_comp φ τ g)
      rwa [CommRingCat.hom_comp] at this
    rw [← hc, ← Polynomial.hom_eval₂, hpr, map_zero]
  let e := RingEquiv.ofBijective ιK.rangeRestrict ⟨fun a b h => ιK.injective
    (congrArg Subtype.val h), ιK.rangeRestrict_surjective⟩
  let ρ' : Γ(kerSch φ, ⊤) →+* AlgebraicClosure K := e.symm.toRingHom.comp (ρ.codRestrict ιK.range hρ)
  have hρ' : ιK.comp ρ' = ρ := by
    ext r
    show ιK (e.symm ⟨ρ r, hρ r⟩) = ρ r
    have : ιK.rangeRestrict (e.symm ⟨ρ r, hρ r⟩) = ⟨ρ r, hρ r⟩ := e.apply_symm_apply _
    exact congrArg Subtype.val this
  let g' : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ kerSch φ :=
    ofRing (isAffineOpen_top (kerSch φ)) (CommRingCat.ofHom ρ')
  have hg' : Spec.map (CommRingCat.ofHom ιK) ≫ g' = g.1 := by
    rw [eq_ofRing_ptRing (isAffineOpen_top (kerSch φ)) g.1 (mem_top φ g.1)]
    simp only [g', ofRing, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext r
    exact congrArg (fun f => f r) hρ'
  refine ⟨⟨g', ?_⟩, hg'⟩
  -- `g' ≫ snd = Spec (K → K̄)`: compare ring maps after composing with the injective `ιK`
  apply ptRing_ext (Λ := CommRingCat.of (AlgebraicClosure K))
    (isAffineOpen_top (Spec (CommRingCat.of K))) (U := ⊤) trivial trivial
  rw [ptRing_comp_snd, ptRing_specMap]
  have hk : kRing φ g' = CommRingCat.ofHom ρ' := ptRing_ofRing _ _
  rw [hk]
  have h1 := snd_kRing φ τ g
  ext x
  apply ιK.injective
  have := congrArg (fun f => f.hom x) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this ⊢
  rw [← RingHom.comp_apply ιK ρ', hρ', ← RingHom.comp_apply ιK (algebraMap K _), hι]
  exact this

end Card

end GapHeight

namespace GapHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

section Final

variable {K : Type} [Field K] {X Y : Over (Spec (CommRingCat.of K))} [MonObj X] [MonObj Y]
  (φ : X ⟶ Y) [IsFinite φ.left]

/-- **The complex kernel is finite, of order at most the `K̄`-kernel.** -/
theorem kerPts_card (τ : K →+* ℂ) :
    Finite {P : ptK τ ⟶ X // P ≫ φ = 1} ∧
      Nat.card {P : ptK τ ⟶ X // P ≫ φ = 1} ≤
        Nat.card {P : ptK (algebraMap K (AlgebraicClosure K)) ⟶ X // P ≫ φ = 1} := by
  letI : Algebra K ℂ := τ.toAlgebra
  let ιA : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  let ιK : AlgebraicClosure K →+* ℂ := ιA.toRingHom
  have hι : ιK.comp (algebraMap K (AlgebraicClosure K)) = τ := by
    ext c
    exact ιA.commutes c
  let F : kerSchPts φ (algebraMap K (AlgebraicClosure K)) → kerSchPts φ τ := fun g' =>
    ⟨Spec.map (CommRingCat.ofHom ιK) ≫ g'.1, by
      rw [Category.assoc, g'.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hι]⟩
  have hF : Function.Surjective F := by
    intro g
    obtain ⟨g', hg'⟩ := kerSchPts_surj φ τ ιK hι g
    exact ⟨g', Subtype.ext hg'⟩
  haveI := finite_kerSchPts φ (algebraMap K (AlgebraicClosure K))
  haveI : Finite (kerSchPts φ τ) := Finite.of_surjective F hF
  refine ⟨Finite.of_equiv _ (kerSchEquiv φ τ).symm, ?_⟩
  rw [Nat.card_congr (kerSchEquiv φ τ),
    Nat.card_congr (kerSchEquiv φ (algebraMap K (AlgebraicClosure K)))]
  exact Nat.card_le_card_of_surjective F hF

end Final

/-- **`IsogKerCard`, proved.** -/
theorem isogKerCard : IsogKerCard := by
  intro K _ _ A B φ hφ 𝒩A 𝒩B f _ he τ
  haveI := hφ.2.1
  obtain ⟨h1, h2⟩ := kerPts_card φ τ
  have e := kerEquiv 𝒩A 𝒩B φ f he τ
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e]
  exact h2

end GapHeight
