import ZInQKernel.Contrib.HomUnify.Corr
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# homlattice: `HomLatticeCorr` reduced to two narrow analytic statements

`HomLatticeCorr` (hom-unify, `ZInQKernel/Contrib/HomUnify/Corr.lean`) is
`HomLinearLift ∧ HomRealize` (`ZInQ.HomUnify.corr_iff_lift_realize`). This file separates, in
each half, the elementary scheme/lattice content (proved here) from the analytic content (stated
as narrow hypotheses):

* `IsAnalyticHom σ ψ`: the clauses of `IsUniformization` other than kernel and surjectivity
  (a homomorphism `ℂ^n → A(ℂ)_σ`, open preimages of charts, holomorphic regular functions).
* **Glue (proved).** `isAnalyticHom_comp`: an algebraic homomorphism `f` preserves analyticity
  (`Φ_A ≫ f` is analytic); `isAnalyticHom_lin`: `Φ_B ∘ M` is analytic for `ℂ`-linear `M`.
* **Lifting half.** `AnalyticHomLift` (every analytic homomorphism `ℂ^g → B(ℂ)_σ` factors as
  `Φ_B ∘ M`, `M` linear) implies `HomLinearLift`. `AnalyticHomLift` is itself proved from the
  one-variety statement `UnifLocalInverse` (a uniformization has a holomorphic local inverse at
  `0` whose image is a neighbourhood of the identity) by pure analysis
  (`eq_fderiv_of_locally_additive`: a locally additive map differentiable at `0` is linear on a
  ball).
* **Realization half.** `AnalyticHomAlgebraic` (GAGA + rigidity, for homomorphisms: an analytic
  homomorphism `ℂ^g → B(ℂ)` killing the lattice of a uniformization of `A` comes from an
  algebraic homomorphism `A → B`) implies `HomRealize`.
-/

/-! ### Copy: rigidity (scratch/alg-frob-red/src_Rigidity.lean, lines 18-183, verbatim; task
mul-rigidity). A pointed morphism of abelian varieties is a homomorphism (Mumford §4 Cor. 1),
proved from Mathlib. -/

noncomputable section

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

variable {K : Type u} [Field K]

theorem isClosedImmersion_point (G : Over (Spec (.of K))) (x : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    IsClosedImmersion x.left :=
  isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) G.hom x.left (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Rigidity lemma (two-sided form), over an algebraically closed field.** Let `G` be proper
over `K` with `G ×_K G` integral, `Z` separated of finite type, and `c : G × G → Z` with
`c(e, y) = z` and `c(x, e) = z` (as morphisms, for all `T`-points). Then `c` is constant. -/
theorem rigidity_algClosed [IsAlgClosed K]
    (G Z : Over (Spec (.of K))) [IsProper G.hom] [IsIntegral (G ⊗ G).left]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ G) (z : 𝟙_ (Over (Spec (.of K))) ⟶ Z) (c : G ⊗ G ⟶ Z)
    (h1 : ∀ (T : Over (Spec (.of K))) (y : T ⟶ G), lift (toUnit T ≫ e) y ≫ c = toUnit T ≫ z)
    (h2 : ∀ (T : Over (Spec (.of K))) (x : T ⟶ G), lift x (toUnit T ≫ e) ≫ c = toUnit T ≫ z) :
    c = toUnit _ ≫ z := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : IsClosedImmersion e.left := isClosedImmersion_point G e
  have : Nonempty G.left := ⟨e.left point⟩
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : JacobsonSpace (G ⊗ G).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (G ⊗ G).hom
  have : Surjective G.hom := ⟨Function.surjective_to_subsingleton (α := G.left) (β := Spec _) _⟩
  have : IsProper (fst G G).left := by dsimp; infer_instance
  have : Surjective (fst G G).left := by dsimp; infer_instance
  have : IsSeparated (fst G Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (fst G Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (c.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  have : IsClosedImmersion ((lift e z).left ≫ (fst G Z).left) := by
    simpa using inferInstanceAs (IsClosedImmersion e.left)
  have : IsClosedImmersion (lift e z).left := .of_comp _ (g := (fst G Z).left)
  let gm : G ⊗ G ⟶ G ⊗ Z := lift (fst _ _) c
  have : IsProper (gm.left ≫ (fst G Z).left) := by simpa [gm]
  have : IsProper gm.left := .of_comp _ (fst G Z).left
  ext1
  have H : gm.left '' ((fst G G).left ⁻¹' {e.left point}) ⊆ {(lift e z).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro H
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints H <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton];
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift e z).left.isClosedMap _ hpoint).preimage gm.left.continuous).isOpen_compl
      · exact (e.left.isClosedMap _ hpoint).preimage (fst G G).left.continuous
    obtain ⟨⟨p, hp⟩, hpe⟩ := (pointEquivClosedPoint (G ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : p point = c₀ := congr(($hpe).1)
    let pt : 𝟙_ (Over S) ⟶ G ⊗ G := Over.homMk p hp
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G := lift (𝟙 _) (pt ≫ snd G G)
    have : p ≫ pullback.fst G.hom G.hom = e.left :=
      ext_of_apply_closedPoint_eq G.hom (by simpa) (by simp) (by simpa)
    have H₁ : p = fc.left ≫ (e ▷ G).left := by dsimp; ext <;> simp [fc, pt, S, this]
    have H₂ : fc ≫ e ▷ G ≫ gm = lift e z := by
      have h1' := h1 _ (pt ≫ snd G G)
      rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at h1'
      ext1
      · simp [fc, gm, S]
      · simpa [fc, gm, S] using h1'
    exact hc₂ <| by simp [H₁, H₂, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  obtain ⟨U, hηU, H⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    gm.left (fst G Z).left (e.left point) (by
      dsimp [-Scheme.Hom.comp_base, gm]
      simp only [pullback.lift_fst]
      exact (Set.finite_singleton _).subset H)
  have H (x : U) : ((pullback.fst G.hom Z.hom) ⁻¹' {x.1} ∩ Set.range ⇑gm.left).Finite := by
    refine ((((gm.left.imageι ≫ (fst G Z).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ gm.left.imageι)).subset ?_
    have : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst G Z).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact gm.left.isClosedMap.isClosed_range)]
  refine ext_of_apply_eq Z.hom _
    ((fst G G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst G G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst G G).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst G G).left y} := by simpa using (fst G G).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ G := Over.homMk (pointOfClosedPoint G.hom _ hx) (by simp)
    let xe : (G ⊗ Z).left := (lift (fst G G) (toUnit _ ≫ z)).left y
    have hgm : lift (fst G G) (toUnit _ ≫ e) ≫ gm = lift (fst G G) (toUnit _ ≫ z) := by
      ext1
      · simp [gm]
      · simpa [gm] using h2 _ (fst G G)
    have : gm.left y = xe := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst G G).left.continuous).isLocallyClosed ?_ gm.left.continuous
        gm.left.isClosedMap ((H ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, gm])) ?_ ?_
      · let α : G ⊗ G ⟶ G ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
              α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · refine ⟨(lift (fst G G) (toUnit _ ≫ e)).left y, subset_closure ?_, ?_⟩
        · rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, ← Over.comp_left,
            lift_fst]
        · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hgm]
    convert congr((snd G Z).left $this) using 1
    · simp [gm, ← Scheme.Hom.comp_apply]
    · simp only [xe]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
  · simp

/-- **A pointed morphism of proper group schemes is a homomorphism, over an algebraically closed
field** (rigidity, Mumford §4 Cor. 1). Apply `rigidity_algClosed` to
`c = (μ ≫ h) * ((h ⊗ h) ≫ μ)⁻¹`. -/
theorem isMonHom_of_algClosed [IsAlgClosed K]
    (G B : Over (Spec (.of K))) [GrpObj G] [GrpObj B] [IsProper G.hom] [IsIntegral (G ⊗ G).left]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (h : G ⟶ B) (h0 : η[G] ≫ h = η[B]) : IsMonHom h := by
  have hone : ∀ (T : Over (Spec (.of K))), (1 : T ⟶ G) ≫ h = 1 := fun T => by
    rw [Hom.one_def, Hom.one_def, Category.assoc, h0]
  have key := rigidity_algClosed G B η[G] η[B] ((μ ≫ h) * ((h ⊗ₘ h) ≫ μ)⁻¹)
    (fun T y => by
      rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, lift_map, ← Hom.mul_def,
        ← Hom.mul_def, ← Hom.one_def, _root_.one_mul, hone, _root_.one_mul, mul_inv_cancel,
        Hom.one_def])
    (fun T x => by
      rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, lift_map, ← Hom.mul_def,
        ← Hom.mul_def, ← Hom.one_def, _root_.mul_one, hone, _root_.mul_one, mul_inv_cancel,
        Hom.one_def])
  rw [← Hom.one_def, mul_inv_eq_one] at key
  exact ⟨h0, key⟩

/-- **Rigidity over any field** (Mumford §4 Cor. 1 / Milne Cor. 2.2): base change to `K̄` and
`isMonHom_of_algClosed`; `Over.pullback` along `Spec K̄ → Spec K` is faithful and monoidal. -/
theorem isMonHom_of_geometricallyIntegral
    (G B : Over (Spec (.of K))) [GrpObj G] [GrpObj B] [IsProper G.hom]
    [GeometricallyIntegral G.hom] [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (h : G ⟶ B) (h0 : η[G] ≫ h = η[B]) : IsMonHom h := by
  let f := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback f
  let G' := F.obj G
  let B' := F.obj B
  have : IsProper G'.hom := by dsimp [G', F]; infer_instance
  have : IsIntegral (G' ⊗ G').left := by dsimp [G', F]; infer_instance
  have : IsSeparated B'.hom := by dsimp [B', F]; infer_instance
  have : LocallyOfFiniteType B'.hom := by dsimp [B', F]; infer_instance
  let : GrpObj G' := Functor.grpObjObj
  let : GrpObj B' := Functor.grpObjObj
  have h0' : η[G'] ≫ F.map h = η[B'] := by
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, ← F.map_comp, h0]
  have := isMonHom_of_algClosed G' B' (F.map h) h0'
  refine ⟨h0, F.map_injective ?_⟩
  have hm := IsMonHom.mul_hom (F.map h)
  rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc]
    at hm
  simp only [← F.map_comp] at hm
  exact (cancel_epi _).mp hm

end MulRigidity

end

namespace ZInQ.HomLattice

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3
open ZInQ.LeafPush2 (CPts IsUniformization cEvalAt cDom)
open ZInQ.HomUnify (HomLinearLift HomRealize HomLatticeCorr T11aHom)
open Filter Topology

section Defs

variable {K : Type} [Field K]

/-- **Analytic homomorphism `ℂ^n → A(ℂ)_σ`**: the first, fourth and fifth clauses of
`IsUniformization` (homomorphism; preimages of the complex points of every open are open; every
regular function is holomorphic on that preimage). -/
def IsAnalyticHom {A : AbVar K} (σ : K →+* ℂ) {n : ℕ} (ψ : (Fin n → ℂ) → CPts A σ) : Prop :=
  (∀ z w, ψ (z + w) = ψ z * ψ w) ∧
  (∀ U, IsOpen (cDom ψ U)) ∧
  (∀ U (s : Γ(A.X.left, U)), DifferentiableOn ℂ (fun z => cEvalAt (ψ z) U s) (cDom ψ U))

/-- `IsUniformization` = analytic homomorphism + kernel `Λ` + surjective (proved). -/
theorem isUniformization_iff {A : AbVar K} (σ : K →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ) :
    IsUniformization σ Λ Φ ↔
      IsAnalyticHom σ Φ ∧ (∀ z, Φ z = 1 ↔ z ∈ Λ) ∧ Function.Surjective Φ := by
  unfold IsUniformization IsAnalyticHom
  tauto

theorem isAnalyticHom_of_unif {A : AbVar K} {σ : K →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → CPts A σ} (h : IsUniformization σ Λ Φ) :
    IsAnalyticHom σ Φ :=
  ((isUniformization_iff σ Λ Φ).1 h).1

theorem map_zero_of_hom {G : Type*} [Group G] {n : ℕ} {ψ : (Fin n → ℂ) → G}
    (h : ∀ z w, ψ (z + w) = ψ z * ψ w) : ψ 0 = 1 := by
  have h0 := h 0 0
  rw [add_zero] at h0
  exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)

theorem map_nsmul_of_hom {G : Type*} [Group G] {n : ℕ} {ψ : (Fin n → ℂ) → G}
    (h : ∀ z w, ψ (z + w) = ψ z * ψ w) (u : Fin n → ℂ) (k : ℕ) : ψ (k • u) = ψ u ^ k := by
  induction k with
  | zero => simp [map_zero_of_hom h]
  | succ k ih => rw [succ_nsmul, h, ih, pow_succ]

/-! ### Glue 1: algebraic homomorphisms preserve analyticity -/

theorem cEvalAt_comp {A B : AbVar K} {σ : K →+* ℂ} (p : CPts A σ) (f : A.X ⟶ B.X)
    (U : B.X.left.Opens) (s : Γ(B.X.left, U)) :
    cEvalAt (p ≫ f) U s = cEvalAt p (f.left ⁻¹ᵁ U) (f.left.app U s) := by
  unfold cEvalAt
  by_cases h : ⊤ ≤ p.left ⁻¹ᵁ (f.left ⁻¹ᵁ U)
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (p ≫ f).left ⁻¹ᵁ U from h)]
    congr 1
  · rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (p ≫ f).left ⁻¹ᵁ U from h)]

/-- **`Φ ≫ f` is analytic for an algebraic homomorphism `f` (proved).** This is the part
"algebraic morphisms are holomorphic" of `HomLinearLift`, at the level of the definitions. -/
theorem isAnalyticHom_comp {A B : AbVar K} {σ : K →+* ℂ} {n : ℕ}
    {ψ : (Fin n → ℂ) → CPts A σ} (hψ : IsAnalyticHom σ ψ) (f : A.X ⟶ B.X) [IsMonHom f] :
    IsAnalyticHom σ (fun z => ψ z ≫ f) := by
  refine ⟨fun z w => ?_, fun U => hψ.2.1 (f.left ⁻¹ᵁ U), fun U s => ?_⟩
  · show ψ (z + w) ≫ f = (ψ z ≫ f) * (ψ w ≫ f)
    rw [hψ.1 z w]
    exact MonObj.mul_comp _ _ _
  · have := hψ.2.2 (f.left ⁻¹ᵁ U) (f.left.app U s)
    simp only [← cEvalAt_comp] at this
    exact this

/-! ### Glue 2: lattice maps give analytic homomorphisms -/

/-- **`Φ ∘ M` is analytic for `ℂ`-linear `M` (proved).** -/
theorem isAnalyticHom_lin {B : AbVar K} {σ : K →+* ℂ} {g h : ℕ}
    {Φ : (Fin h → ℂ) → CPts B σ} (hΦ : IsAnalyticHom σ Φ) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ)) :
    IsAnalyticHom σ (fun z => Φ (M z)) := by
  have hc : Continuous M := LinearMap.continuous_of_finiteDimensional M
  have hd : Differentiable ℂ (LinearMap.toContinuousLinearMap M) :=
    (LinearMap.toContinuousLinearMap M).differentiable
  refine ⟨fun z w => by simp only [map_add, hΦ.1], fun U => (hΦ.2.1 U).preimage hc,
    fun U s => ?_⟩
  exact (hΦ.2.2 U s).comp hd.differentiableOn (fun z hz => hz)

end Defs

/-! ### The narrow analytic statements -/

/-- **Analytic lifting (BL 1.2.1 transported; analytic leaf candidate).** Every analytic
homomorphism `ψ : ℂ^g → B(ℂ)_σ` factors through a uniformization `Φ_B` (`h = dim B`) by a
`ℂ`-linear map. -/
def AnalyticHomLift : Prop :=
  ∀ (K : Type) [Field K] (B : AbVar K) (σ : K →+* ℂ) (g h : ℕ) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦB : (Fin h → ℂ) → CPts B σ), B.dim = (h : WithBot ℕ∞) → IsUniformization σ ΛB ΦB →
    ∀ ψ : (Fin g → ℂ) → CPts B σ, IsAnalyticHom σ ψ →
      ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ), ∀ z, ΦB (M z) = ψ z

/-- **A uniformization is a local analytic isomorphism at `0` (one-variety analytic leaf
candidate; Mumford §1: `Φ = exp ∘ D`, `D` a linear isomorphism, `exp` a local biholomorphism).**
For a uniformization `Φ` of `B(ℂ)_σ` with `h = dim B` there are an open `W ∋ 0` and a map
`χ : B(ℂ)_σ → ℂ^h` inverting `Φ` on `W`, such that for every analytic homomorphism `ψ` into
`B(ℂ)_σ`, `ψ` maps a neighbourhood of `0` into `Φ(W)` and `χ ∘ ψ` is holomorphic at `0`
("`Φ(W)` is a neighbourhood of the identity and `χ` is holomorphic on it", tested on analytic
homomorphisms, since `B(ℂ)_σ` carries no topology in Lean). -/
def UnifLocalInverse : Prop :=
  ∀ (K : Type) [Field K] (B : AbVar K) (σ : K →+* ℂ) (h : ℕ) (Λ : Submodule ℤ (Fin h → ℂ))
    (Φ : (Fin h → ℂ) → CPts B σ), B.dim = (h : WithBot ℕ∞) → IsUniformization σ Λ Φ →
    ∃ W : Set (Fin h → ℂ), IsOpen W ∧ (0 : Fin h → ℂ) ∈ W ∧ ∃ χ : CPts B σ → (Fin h → ℂ),
      (∀ w ∈ W, χ (Φ w) = w) ∧
      ∀ (g : ℕ) (ψ : (Fin g → ℂ) → CPts B σ), IsAnalyticHom σ ψ →
        (∀ᶠ z in 𝓝 0, ψ z ∈ Φ '' W) ∧ DifferentiableAt ℂ (fun z => χ (ψ z)) 0

/-- **GAGA for homomorphisms of complex abelian varieties (analytic leaf candidate; Serre GAGA /
Chow, with rigidity).** An analytic homomorphism `ψ : ℂ^g → B(ℂ)` that kills the lattice of a
uniformization `Φ_A` of `A(ℂ)` (`g = dim A`) is induced by an algebraic homomorphism `A → B`. -/
def AnalyticHomAlgebraic : Prop :=
  ∀ (A B : AbVar ℂ) (g : ℕ) (ΛA : Submodule ℤ (Fin g → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → IsUniformization (RingHom.id ℂ) ΛA ΦA →
    ∀ ψ : (Fin g → ℂ) → CPts B (RingHom.id ℂ), IsAnalyticHom (RingHom.id ℂ) ψ →
      (∀ z ∈ ΛA, ψ z = 1) →
      ∃ f : AbVar.Hom A B, ∀ z, ψ z = ΦA z ≫ f.hom

/-! ### Reductions -/

/-- **`HomLinearLift` from `AnalyticHomLift` (proved).** -/
theorem homLinearLift_of_analyticHomLift (H : AnalyticHomLift) : HomLinearLift := by
  intro K _ A B σ g h ΛA ΛB ΦA ΦB _ hB hUA hUB f
  exact H K B σ g h ΛB ΦB hB hUB (fun z => ΦA z ≫ f.hom)
    (isAnalyticHom_comp (isAnalyticHom_of_unif hUA) f.hom)

/-- **`HomRealize` from `AnalyticHomAlgebraic` (proved).** -/
theorem homRealize_of_analyticHomAlgebraic (H : AnalyticHomAlgebraic) : HomRealize := by
  intro A B g h ΛA ΛB ΦA ΦB hA _ hUA hUB M hM
  obtain ⟨f, hf⟩ := H A B g ΛA ΦA hA hUA (fun z => ΦB (M z))
    (isAnalyticHom_lin (isAnalyticHom_of_unif hUB) M) (fun z hz => (hUB.2.1 _).2 (hM z hz))
  exact ⟨f, hf⟩

/-- **`HomLatticeCorr` from the two analytic statements (proved).** -/
theorem homLatticeCorr_of_analytic (H1 : AnalyticHomLift) (H2 : AnalyticHomAlgebraic) :
    HomLatticeCorr :=
  ZInQ.HomUnify.corr_iff_lift_realize.2
    ⟨homLinearLift_of_analyticHomLift H1, homRealize_of_analyticHomAlgebraic H2⟩

theorem t11a_riemannEnd_of_analytic (H1 : AnalyticHomLift) (H2 : AnalyticHomAlgebraic) :
    ZInQ.LeafPush2.T11a_RiemannEnd :=
  ZInQ.HomUnify.t11a_riemannEnd_of_corr (homLatticeCorr_of_analytic H1 H2)

theorem t11aHom_of_analytic (H2 : AnalyticHomAlgebraic) : T11aHom :=
  ZInQ.HomUnify.t11aHom_of_realize (homRealize_of_analyticHomAlgebraic H2)

/-! ### Pure analysis: a locally additive map differentiable at `0` is linear on a ball -/

/-- **(proved)** If `F : ℂ^g → ℂ^h` is additive on the ball of radius `r` (`F(z + w) = F z + F w`
for `‖z‖, ‖w‖ < r`) and complex differentiable at `0`, then `F = F'(0)` on that ball. -/
theorem eq_fderiv_of_locally_additive {g h : ℕ} {F : (Fin g → ℂ) → (Fin h → ℂ)} {r : ℝ}
    (hadd : ∀ z w : Fin g → ℂ, ‖z‖ < r → ‖w‖ < r → F (z + w) = F z + F w)
    (hF : DifferentiableAt ℂ F 0) {z : Fin g → ℂ} (hz : ‖z‖ < r) : F z = fderiv ℂ F 0 z := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) hz
  have hF0 : F 0 = 0 := by
    have := hadd 0 0 (by simpa using hr) (by simpa using hr)
    rw [_root_.add_zero] at this
    exact add_left_cancel (this.symm.trans (_root_.add_zero _).symm)
  have key : ∀ n : ℕ, 0 < n → (n : ℂ) • F ((n : ℂ)⁻¹ • z) = F z := by
    intro n hn
    obtain ⟨u, hu⟩ : ∃ u, u = (n : ℂ)⁻¹ • z := ⟨_, rfl⟩
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hnorm : ∀ k : ℕ, k ≤ n → ‖(k : ℂ) • u‖ ≤ ‖z‖ := by
      intro k hk
      rw [hu, smul_smul, norm_smul]
      have h1 : ‖(k : ℂ) * (n : ℂ)⁻¹‖ ≤ 1 := by
        rw [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast, ← div_eq_mul_inv]
        exact div_le_one_of_le₀ (by exact_mod_cast hk) (by positivity)
      calc ‖(k : ℂ) * (n : ℂ)⁻¹‖ * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
        _ = ‖z‖ := _root_.one_mul _
    have hk : ∀ k : ℕ, k ≤ n → F ((k : ℂ) • u) = (k : ℂ) • F u := by
      intro k
      induction k with
      | zero => intro _; simp [hF0]
      | succ k ih =>
        intro hkn
        have h1 := hnorm k (Nat.le_of_succ_le hkn)
        have h2 := hnorm 1 (by omega)
        rw [Nat.cast_one, one_smul] at h2
        rw [Nat.cast_succ, add_smul, one_smul,
          hadd _ _ (lt_of_le_of_lt h1 hz) (lt_of_le_of_lt h2 hz), ih (Nat.le_of_succ_le hkn),
          add_smul, one_smul]
    have hzu : (n : ℂ) • u = z := by rw [hu, smul_smul, mul_inv_cancel₀ hn', one_smul]
    rw [← hu]
    conv_rhs => rw [← hzu]
    exact (hk n le_rfl).symm
  have hlim := hF.hasFDerivAt.lim z (c := fun n : ℕ => (n : ℂ)) (l := atTop) (by
    simpa [Complex.norm_natCast] using tendsto_natCast_atTop_atTop (R := ℝ))
  simp only [_root_.zero_add, hF0, sub_zero] at hlim
  have hev : (fun _ : ℕ => F z) =ᶠ[atTop] fun n : ℕ => (n : ℂ) • F ((n : ℂ)⁻¹ • z) :=
    (eventually_gt_atTop 0).mono fun n hn => (key n hn).symm
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hlim

/-- **`AnalyticHomLift` from `UnifLocalInverse` (proved).** The lifting argument of
Birkenhake–Lange 1.2.1 / Lie theory: near `0`, `F = χ ∘ ψ` lifts `ψ` through `Φ_B`; it is
additive there because `Λ_B ∩ W = 0`; so it is linear (`eq_fderiv_of_locally_additive`), and
`ψ = Φ_B ∘ F'(0)` everywhere because both sides are homomorphisms. -/
theorem analyticHomLift_of_unifLocalInverse (HL : UnifLocalInverse) : AnalyticHomLift := by
  intro K _ B σ g h ΛB ΦB hdim hU ψ hψ
  obtain ⟨W, hWo, hW0, χ, hχ, hloc⟩ := HL K B σ h ΛB ΦB hdim hU
  obtain ⟨hev, hdiff⟩ := hloc g ψ hψ
  have hΦhom := hU.1
  have hΦ0 : ΦB 0 = 1 := (hU.2.1 0).2 (zero_mem _)
  have hψ0 : ψ 0 = 1 := map_zero_of_hom hψ.1
  obtain ⟨F, hFdef⟩ : ∃ F : (Fin g → ℂ) → (Fin h → ℂ), F = fun z => χ (ψ z) := ⟨_, rfl⟩
  have hdiffF : DifferentiableAt ℂ F 0 := hFdef ▸ hdiff
  have hF0 : F 0 = 0 := by
    rw [hFdef]
    show χ (ψ 0) = 0
    rw [hψ0, ← hΦ0, hχ 0 hW0]
  have hΛW : ∀ d ∈ W, ΦB d = 1 → d = 0 := by
    intro d hd h1
    rw [← hχ d hd, h1, ← hΦ0, hχ 0 hW0]
  have hS : ∀ z, ψ z ∈ ΦB '' W → ΦB (F z) = ψ z := by
    rintro z ⟨w, hw, hwz⟩
    rw [hFdef]
    show ΦB (χ (ψ z)) = ψ z
    rw [← hwz, hχ w hw]
  have hcont : ContinuousAt F 0 := hdiffF.continuousAt
  have hP : ∀ᶠ p : (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (0, 0),
      ψ (p.1 + p.2) ∈ ΦB '' W ∧ ψ p.1 ∈ ΦB '' W ∧ ψ p.2 ∈ ΦB '' W ∧
      F (p.1 + p.2) - F p.1 - F p.2 ∈ W := by
    have t1 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.1 + p.2) (𝓝 (0, 0)) (𝓝 0) := by
      simpa using (continuous_add.tendsto ((0 : Fin g → ℂ), (0 : Fin g → ℂ)))
    have t2 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.1) (𝓝 (0, 0)) (𝓝 0) :=
      continuous_fst.tendsto _
    have t3 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.2) (𝓝 (0, 0)) (𝓝 0) :=
      continuous_snd.tendsto _
    have t4 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => F (p.1 + p.2) - F p.1 - F p.2)
        (𝓝 (0, 0)) (𝓝 0) := by
      have := ((hcont.tendsto.comp t1).sub (hcont.tendsto.comp t2)).sub
        (hcont.tendsto.comp t3)
      simpa [hF0] using this
    exact (t1.eventually hev).and ((t2.eventually hev).and ((t3.eventually hev).and
      (t4.eventually (hWo.eventually_mem hW0))))
  obtain ⟨r, hr, hrP⟩ := Metric.eventually_nhds_iff.1 hP
  have hpair : ∀ z w : Fin g → ℂ, ‖z‖ < r → ‖w‖ < r →
      ψ (z + w) ∈ ΦB '' W ∧ ψ z ∈ ΦB '' W ∧ ψ w ∈ ΦB '' W ∧ F (z + w) - F z - F w ∈ W := by
    intro z w hz hw
    have hd : dist (z, w) ((0 : Fin g → ℂ), (0 : Fin g → ℂ)) < r := by
      simp only [Prod.dist_eq, dist_zero_right]
      exact max_lt hz hw
    exact hrP hd
  have hadd : ∀ z w : Fin g → ℂ, ‖z‖ < r → ‖w‖ < r → F (z + w) = F z + F w := by
    intro z w hz hw
    obtain ⟨h1, h2, h3, h4⟩ := hpair z w hz hw
    have e : ΦB (F (z + w)) = ΦB (F z + F w) := by
      rw [hS _ h1, hΦhom, hS _ h2, hS _ h3, hψ.1]
    have hd1 : ΦB (F (z + w) - F z - F w) = 1 := by
      have := hΦhom (F (z + w) - F z - F w) (F z + F w)
      rw [show F (z + w) - F z - F w + (F z + F w) = F (z + w) by abel, e] at this
      exact mul_right_cancel (this.symm.trans (_root_.one_mul _).symm)
    have := hΛW _ h4 hd1
    rw [sub_sub, sub_eq_zero] at this
    exact this
  refine ⟨(fderiv ℂ F 0 : (Fin g → ℂ) →L[ℂ] (Fin h → ℂ)).toLinearMap, fun z => ?_⟩
  have hsmall : ∀ u : Fin g → ℂ, ‖u‖ < r → ΦB (fderiv ℂ F 0 u) = ψ u := by
    intro u hu
    rw [← eq_fderiv_of_locally_additive hadd hdiffF hu]
    exact hS u (hpair u 0 hu (by simpa using hr)).2.1
  have ht : Tendsto (fun n : ℕ => (n : ℂ)⁻¹ • z) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).smul_const z
  obtain ⟨n, hn1, hn2⟩ :=
    ((eventually_gt_atTop 0).and (ht.eventually (Metric.ball_mem_nhds 0 hr))).exists
  obtain ⟨u, hu⟩ : ∃ u, u = (n : ℂ)⁻¹ • z := ⟨_, rfl⟩
  have hur : ‖u‖ < r := by rw [hu]; simpa using hn2
  have hzu : z = n • u := by
    rw [hu, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast hn1.ne'), one_smul]
  change ΦB ((fderiv ℂ F 0) z) = ψ z
  rw [hzu, map_nsmul, map_nsmul_of_hom hΦhom, map_nsmul_of_hom hψ.1, hsmall u hur]

/-- **`HomLinearLift` from `UnifLocalInverse` (proved).** -/
theorem homLinearLift_of_unifLocalInverse (HL : UnifLocalInverse) : HomLinearLift :=
  homLinearLift_of_analyticHomLift (analyticHomLift_of_unifLocalInverse HL)

/-- **`HomLatticeCorr` from `UnifLocalInverse` and `AnalyticHomAlgebraic` (proved).** -/
theorem homLatticeCorr_of_local (HL : UnifLocalInverse) (H2 : AnalyticHomAlgebraic) :
    HomLatticeCorr :=
  homLatticeCorr_of_analytic (analyticHomLift_of_unifLocalInverse HL) H2

/-- **Converse (proved): the GAGA form `AnalyticHomAlgebraic` follows from the lattice form
`HomRealize`**, given analytic lifting, the existence of uniformizations (leaf-push2's textbook
leaf `UniformizationExists`) and finiteness of the dimension. So, beside those, the two forms of
the realization half have the same content. -/
theorem analyticHomAlgebraic_of_homRealize (HR : HomRealize) (HL : AnalyticHomLift)
    (HU : ZInQ.LeafPush2.UniformizationExists)
    (hfin : ∀ B : AbVar ℂ, ∃ h : ℕ, B.dim = (h : WithBot ℕ∞)) : AnalyticHomAlgebraic := by
  intro A B g ΛA ΦA hA hUA ψ hψ hker
  obtain ⟨h, hB⟩ := hfin B
  obtain ⟨ΛB, ΦB, _, _, hUB⟩ := HU ℂ B (RingHom.id ℂ) h hB
  obtain ⟨M, hM⟩ := HL ℂ B (RingHom.id ℂ) g h ΛB ΦB hB hUB ψ hψ
  have hMΛ : ∀ z ∈ ΛA, M z ∈ ΛB := fun z hz => (hUB.2.1 _).1 (by rw [hM]; exact hker z hz)
  obtain ⟨f, hf⟩ := HR A B g h ΛA ΛB ΦA ΦB hA hB hUA hUB M hMΛ
  exact ⟨f, fun z => by rw [← hM, hf]⟩

/-- **leaf-push2's T11(a) from `UnifLocalInverse` and `AnalyticHomAlgebraic` (proved).** -/
theorem t11a_riemannEnd_of_local (HL : UnifLocalInverse) (H2 : AnalyticHomAlgebraic) :
    ZInQ.LeafPush2.T11a_RiemannEnd :=
  ZInQ.HomUnify.t11a_riemannEnd_of_corr (homLatticeCorr_of_local HL H2)

/-- **`HomLatticeCorr` from `UnifLocalInverse` and the build's `HomRealize` (proved).** -/
theorem homLatticeCorr_of_local_realize (HL : UnifLocalInverse) (HR : HomRealize) :
    HomLatticeCorr :=
  ZInQ.HomUnify.corr_iff_lift_realize.2 ⟨homLinearLift_of_unifLocalInverse HL, HR⟩

/-! ### GAGA for morphisms: rigidity is proved, so the leaf need not assert a homomorphism -/

/-- **GAGA (analytic leaf candidate, narrowest form; Serre GAGA / SGA 1 XII, full faithfulness of
analytification on proper `ℂ`-schemes).** An analytic homomorphism `ψ : ℂ^g → B(ℂ)` killing the
lattice of a uniformization `Φ_A` of `A(ℂ)` (`g = dim A`) is induced by an algebraic **morphism**
`f : A → B` (`ψ = f ∘ Φ_A`). -/
def AnalyticMapAlgebraic : Prop :=
  ∀ (A B : AbVar ℂ) (g : ℕ) (ΛA : Submodule ℤ (Fin g → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → IsUniformization (RingHom.id ℂ) ΛA ΦA →
    ∀ ψ : (Fin g → ℂ) → CPts B (RingHom.id ℂ), IsAnalyticHom (RingHom.id ℂ) ψ →
      (∀ z ∈ ΛA, ψ z = 1) →
      ∃ f : A.X ⟶ B.X, ∀ z, ψ z = ΦA z ≫ f

/-- A morphism sending the identity `ℂ`-point to the identity sends `η` to `η` (proved). -/
theorem eta_comp_of_one_comp {A B : AbVar ℂ} (f : A.X ⟶ B.X)
    (h : (1 : CPts A (RingHom.id ℂ)) ≫ f = 1) : η[A.X] ≫ f = η[B.X] := by
  let s : 𝟙_ (Over (Spec (CommRingCat.of ℂ))) ⟶ ZInQ.LeafPush2.cptObj (RingHom.id ℂ) :=
    Over.homMk (𝟙_ (Over (Spec (CommRingCat.of ℂ)))).hom (by simp [ZInQ.LeafPush2.cptObj])
  have hs : s ≫ toUnit _ = 𝟙 _ := toUnit_unique _ _
  have hA : η[A.X] = s ≫ (1 : CPts A (RingHom.id ℂ)) := by
    rw [Hom.one_def, ← Category.assoc, hs, Category.id_comp]
  have hB : η[B.X] = s ≫ (1 : CPts B (RingHom.id ℂ)) := by
    rw [Hom.one_def, ← Category.assoc, hs, Category.id_comp]
  rw [hA, Category.assoc, h, ← hB]

/-- **`AnalyticHomAlgebraic` from `AnalyticMapAlgebraic` (proved, by rigidity).** -/
theorem analyticHomAlgebraic_of_map (H : AnalyticMapAlgebraic) : AnalyticHomAlgebraic := by
  intro A B g ΛA ΦA hA hUA ψ hψ hker
  obtain ⟨f, hf⟩ := H A B g ΛA ΦA hA hUA ψ hψ hker
  have h1 : (1 : CPts A (RingHom.id ℂ)) ≫ f = 1 := by
    rw [← (hUA.2.1 0).2 (zero_mem _), ← hf, map_zero_of_hom hψ.1]
  have : IsMonHom f :=
    MulRigidity.isMonHom_of_geometricallyIntegral A.X B.X f (eta_comp_of_one_comp f h1)
  exact ⟨AbVar.Hom.mk' f, fun z => by rw [AbVar.Hom.hom_mk']; exact hf z⟩

/-- The converse is immediate: the two GAGA forms are equivalent. -/
theorem analyticMapAlgebraic_iff : AnalyticMapAlgebraic ↔ AnalyticHomAlgebraic :=
  ⟨analyticHomAlgebraic_of_map, fun H A B g ΛA ΦA hA hUA ψ hψ hker =>
    let ⟨f, hf⟩ := H A B g ΛA ΦA hA hUA ψ hψ hker; ⟨f.hom, hf⟩⟩

/-- **Main reduction (proved): `HomLatticeCorr` from `UnifLocalInverse` and
`AnalyticMapAlgebraic`.** -/
theorem homLatticeCorr_of_local_map (HL : UnifLocalInverse) (H2 : AnalyticMapAlgebraic) :
    HomLatticeCorr :=
  homLatticeCorr_of_local HL (analyticHomAlgebraic_of_map H2)

theorem t11a_riemannEnd_of_local_map (HL : UnifLocalInverse) (H2 : AnalyticMapAlgebraic) :
    ZInQ.LeafPush2.T11a_RiemannEnd :=
  t11a_riemannEnd_of_local HL (analyticHomAlgebraic_of_map H2)

end ZInQ.HomLattice

#print axioms ZInQ.HomLattice.isUniformization_iff
#print axioms ZInQ.HomLattice.cEvalAt_comp
#print axioms ZInQ.HomLattice.isAnalyticHom_comp
#print axioms ZInQ.HomLattice.isAnalyticHom_lin
#print axioms ZInQ.HomLattice.homLinearLift_of_analyticHomLift
#print axioms ZInQ.HomLattice.homRealize_of_analyticHomAlgebraic
#print axioms ZInQ.HomLattice.homLatticeCorr_of_analytic
#print axioms ZInQ.HomLattice.t11a_riemannEnd_of_analytic
#print axioms ZInQ.HomLattice.t11aHom_of_analytic
#print axioms ZInQ.HomLattice.eq_fderiv_of_locally_additive
#print axioms ZInQ.HomLattice.analyticHomLift_of_unifLocalInverse
#print axioms ZInQ.HomLattice.homLinearLift_of_unifLocalInverse
#print axioms ZInQ.HomLattice.homLatticeCorr_of_local
#print axioms ZInQ.HomLattice.analyticHomAlgebraic_of_homRealize
#print axioms ZInQ.HomLattice.t11a_riemannEnd_of_local
#print axioms ZInQ.HomLattice.homLatticeCorr_of_local_realize
#print axioms MulRigidity.isMonHom_of_geometricallyIntegral
#print axioms ZInQ.HomLattice.eta_comp_of_one_comp
#print axioms ZInQ.HomLattice.analyticHomAlgebraic_of_map
#print axioms ZInQ.HomLattice.analyticMapAlgebraic_iff
#print axioms ZInQ.HomLattice.homLatticeCorr_of_local_map
#print axioms ZInQ.HomLattice.t11a_riemannEnd_of_local_map
