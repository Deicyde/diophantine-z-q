import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower.Gen
import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower.Lattice

/-! faltings5-lower, part 3: the assembly. For an isogeny `φ : A → B` and its Néron extension
`f : 𝒩_A → 𝒩_B`, every metrization `M` of `𝒩_A` gives a metrization `M'` of `𝒩_B`: the Hodge lattice
is `⋀^g ω_{𝒩_B}`, mapped into `⋀^g ω_{𝒩_A}` by `f^*` (`hodgeMap`, bijective on the Hodge lines when
`f^*` is bijective on cotangent spaces), the uniformization is `Φ ≫ f`, the period lattice is
`Φ⁻¹(ker f(ℂ)) ⊇ Λ_A` of index `#ker f(ℂ)`. Comparing Faltings' formula for both gives
`h(M') ≤ h(M) + ½ log d` when `#ker f(ℂ)_σ ≤ d` at every `σ`. -/

set_option linter.style.haveILetI false

namespace GapHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings MeasureTheory

section Periods

variable {K : Type} [Field K] {A B : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- Composition with a homomorphism of group models, on complex points. -/
noncomputable def ptsHom (𝒢 : GroupModel A L) (𝒩 : GroupModel B L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (τ : L →+* ℂ) : 𝒢.Pts τ →* 𝒩.Pts τ where
  toFun p := p ≫ f
  map_one' := MonObj.one_comp f
  map_mul' p q := MonObj.mul_comp p q f

/-- A uniformization as an additive homomorphism. -/
noncomputable def unifHom (𝒢 : GroupModel A L) {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) : (Fin g → ℂ) →+ Additive (𝒢.Pts τ) where
  toFun z := Additive.ofMul (Φ z)
  map_zero' := by rw [ZInQ.H5Glue.map_zero_of_hom Φ hmul]; rfl
  map_add' z w := by rw [hmul]; rfl

/-- The period lattice of `Φ ≫ f`: `Φ⁻¹(ker f(ℂ))`. -/
noncomputable def isogPeriods (𝒢 : GroupModel A L) (𝒩 : GroupModel B L) (f : 𝒢.G ⟶ 𝒩.G)
    [IsMonHom f] {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) : Submodule ℤ (Fin g → ℂ) :=
  ((MonoidHom.toAdditive (ptsHom 𝒢 𝒩 f τ)).comp (unifHom 𝒢 Φ hmul)).ker.toIntSubmodule

theorem mem_isogPeriods (𝒢 : GroupModel A L) (𝒩 : GroupModel B L) (f : 𝒢.G ⟶ 𝒩.G)
    [IsMonHom f] {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) (z : Fin g → ℂ) :
    z ∈ isogPeriods 𝒢 𝒩 f Φ hmul ↔ Φ z ≫ f = 1 := by
  show ((MonoidHom.toAdditive (ptsHom 𝒢 𝒩 f τ)).comp (unifHom 𝒢 Φ hmul)) z = 0 ↔ _
  exact Iff.rfl

theorem le_isogPeriods (𝒢 : GroupModel A L) (𝒩 : GroupModel B L) (f : 𝒢.G ⟶ 𝒩.G)
    [IsMonHom f] {τ : L →+* ℂ} {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) : Λ ≤ isogPeriods 𝒢 𝒩 f Φ hΦ.1 := by
  intro z hz
  rw [mem_isogPeriods, (hΦ.2.1 z).mpr hz]
  exact MonObj.one_comp f

/-- The index of `Λ_A` in `Φ⁻¹(ker f(ℂ))` is at most `#ker f(ℂ)` (and nonzero), if the latter
is finite. -/
theorem relIndex_isogPeriods (𝒢 : GroupModel A L) (𝒩 : GroupModel B L) (f : 𝒢.G ⟶ 𝒩.G)
    [IsMonHom f] {τ : L →+* ℂ} {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (hfin : Finite {p : 𝒢.Pts τ // p ≫ f = 1}) :
    Λ.toAddSubgroup.relIndex (isogPeriods 𝒢 𝒩 f Φ hΦ.1).toAddSubgroup ≠ 0 ∧
      Λ.toAddSubgroup.relIndex (isogPeriods 𝒢 𝒩 f Φ hΦ.1).toAddSubgroup ≤
        Nat.card {p : 𝒢.Pts τ // p ≫ f = 1} := by
  set P := isogPeriods 𝒢 𝒩 f Φ hΦ.1
  let ψ : P.toAddSubgroup →+ Additive (𝒢.Pts τ) :=
    (unifHom 𝒢 Φ hΦ.1).comp P.toAddSubgroup.subtype
  have hker : ψ.ker = Λ.toAddSubgroup.addSubgroupOf P.toAddSubgroup := by
    ext ⟨z, hz⟩
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    show Additive.ofMul (Φ z) = 0 ↔ z ∈ Λ
    exact hΦ.2.1 z
  have hidx : Λ.toAddSubgroup.relIndex P.toAddSubgroup = Nat.card (Set.range ψ) := by
    rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker]
    rfl
  let emb : Set.range ψ → {p : 𝒢.Pts τ // p ≫ f = 1} := fun x =>
    ⟨Additive.toMul (x : Additive (𝒢.Pts τ)), by
      obtain ⟨y, hy⟩ := x.2
      rw [← hy]
      exact (mem_isogPeriods 𝒢 𝒩 f Φ hΦ.1 y.1).mp y.2⟩
  have hemb : Function.Injective emb := by
    intro x y hxy
    have h1 : (emb x).1 = (emb y).1 := by rw [hxy]
    exact Subtype.ext (Additive.toMul.injective h1)
  haveI : Finite (Set.range ψ) := Finite.of_injective emb hemb
  haveI : Nonempty (Set.range ψ) := ⟨⟨0, 0, map_zero ψ⟩⟩
  rw [hidx]
  exact ⟨Nat.card_pos.ne', Nat.card_le_card_of_injective emb hemb⟩

end Periods

section Hodge

variable {L : Type} [Field L] [NumberField L]
variable {V V' : Type*} [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]
  [AddCommGroup V'] [Module L V'] [Module (𝓞 L) V'] [IsScalarTower (𝓞 L) L V']

/-- Pull back Hodge data along an injective `L`-linear map onto a new lattice, with new period
lattices containing the old ones with finite index. -/
noncomputable def isogHodge {g : ℕ} (D : HodgeData L g V) (H : V' →ₗ[L] V)
    (hH : Function.Injective H) (Λ' : Submodule (𝓞 L) V') (hfin : Module.finrank L V' = 1)
    (hlat : ∃ s ∈ Λ', s ≠ 0 ∧ secIndex Λ' s ≠ 0) (P : (L →+* ℂ) → Submodule ℤ (Fin g → ℂ))
    (hP : ∀ σ, D.periods σ ≤ P σ)
    (hPi : ∀ σ, (D.periods σ).toAddSubgroup.relIndex (P σ).toAddSubgroup ≠ 0) :
    HodgeData L g V' where
  lattice := Λ'
  finrank_eq_one := hfin
  isLattice := hlat
  periods := P
  periods_discrete σ := by
    haveI := D.periods_discrete σ
    exact discreteTopology_of_le_of_relIndex _ _ (hPi σ)
  periods_isZLattice σ := by
    haveI := D.periods_discrete σ
    haveI := D.periods_isZLattice σ
    haveI := discreteTopology_of_le_of_relIndex _ _ (hPi σ)
    exact isZLattice_of_le _ _ (hP σ)
  coeff τ := (D.coeff τ).comp H
  coeff_ne_zero τ := by
    obtain ⟨s, -, hs0, -⟩ := hlat
    intro h
    have h1 := LinearMap.congr_fun h s
    have hHs : H s ≠ 0 := fun h0 => hs0 (hH (h0.trans (map_zero H).symm))
    exact D.coeff_apply_ne_zero τ hHs h1

/-- **Faltings' formula on both sides**: `h(D') ≤ h(D) + ½ log d` if every index is `≤ d`. -/
theorem modelHeight_isogHodge_le {g : ℕ} (D : HodgeData L g V) (H : V' →ₗ[L] V)
    (hH : Function.Injective H) (Λ' : Submodule (𝓞 L) V') (hfin : Module.finrank L V' = 1)
    (hlat : ∃ s ∈ Λ', s ≠ 0 ∧ secIndex Λ' s ≠ 0) (P : (L →+* ℂ) → Submodule ℤ (Fin g → ℂ))
    (hP : ∀ σ, D.periods σ ≤ P σ)
    (hPi : ∀ σ, (D.periods σ).toAddSubgroup.relIndex (P σ).toAddSubgroup ≠ 0) (d : ℕ)
    (hd : ∀ σ, (D.periods σ).toAddSubgroup.relIndex (P σ).toAddSubgroup ≤ d)
    (hle : ∀ x ∈ Λ', H x ∈ D.lattice) :
    (isogHodge D H hH Λ' hfin hlat P hP hPi).modelHeight ≤
      D.modelHeight + (1 / 2) * Real.log d := by
  set D' := isogHodge D H hH Λ' hfin hlat P hP hPi
  obtain ⟨v₀, hv₀, hv0, -⟩ := hlat
  have hHv0 : H v₀ ≠ 0 := fun h0 => hv0 (hH (h0.trans (map_zero H).symm))
  have hne := ZInQ.H5Glue.secIndex_ne_zero_of_mem D (hle v₀ hv₀) hHv0
  obtain ⟨hpos, hle'⟩ := ZInQ.H5Glue.secIndex_le_of_map H hH Λ' D.lattice hle hv₀ hne
  rw [D'.modelHeight_eq hv₀ hv0, D.modelHeight_eq (hle v₀ hv₀) hHv0]
  have hn : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (L →+* ℂ) : ℝ) = Module.finrank ℚ L := by
    exact_mod_cast NumberField.Embeddings.card L ℂ
  have hlog : Real.log (secIndex Λ' v₀) ≤ Real.log (secIndex D.lattice (H v₀)) :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hpos) (by exact_mod_cast hle')
  -- at each place: `log ‖c‖² covol(P σ) ≥ log ‖c‖² covol(Λ_σ) - log d`
  have hσ : ∀ σ : L →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ (H v₀))) -
      Real.log d ≤ Real.log (torusMetricSq (D'.periods σ) (D'.coeff σ v₀)) := by
    intro σ
    haveI := D.periods_discrete σ
    haveI := D.periods_isZLattice σ
    haveI : DiscreteTopology (P σ) := D'.periods_discrete σ
    haveI : IsZLattice ℝ (P σ) := D'.periods_isZLattice σ
    have hc : D'.coeff σ v₀ = D.coeff σ (H v₀) := rfl
    have hc0 : D.coeff σ (H v₀) ≠ 0 := D.coeff_apply_ne_zero σ hHv0
    have hcov := covolume_eq_relIndex_mul volume (D.periods σ) (P σ) (hP σ)
    have hr0 : (0 : ℝ) < (D.periods σ).toAddSubgroup.relIndex (P σ).toAddSubgroup := by
      exact_mod_cast Nat.pos_of_ne_zero (hPi σ)
    have hrd : ((D.periods σ).toAddSubgroup.relIndex (P σ).toAddSubgroup : ℝ) ≤ d := by
      exact_mod_cast hd σ
    have hP0 : 0 < ZLattice.covolume (P σ) := ZLattice.covolume_pos _ _
    have hn0 : 0 < ‖D.coeff σ (H v₀)‖ ^ 2 := by positivity
    rw [hc]
    show Real.log (‖D.coeff σ (H v₀)‖ ^ 2 * ZLattice.covolume (D.periods σ)) - Real.log d ≤
      Real.log (‖D.coeff σ (H v₀)‖ ^ 2 * ZLattice.covolume (P σ))
    rw [hcov, sub_le_iff_le_add]
    have hd0 : (0 : ℝ) < d := lt_of_lt_of_le hr0 hrd
    rw [← Real.log_mul (by positivity) hd0.ne']
    apply Real.log_le_log (by positivity)
    have : ‖D.coeff σ (H v₀)‖ ^ 2 *
        (((D.periods σ).toAddSubgroup.relIndex (P σ).toAddSubgroup : ℝ) * ZLattice.covolume (P σ)) =
        (‖D.coeff σ (H v₀)‖ ^ 2 * ZLattice.covolume (P σ)) *
          ((D.periods σ).toAddSubgroup.relIndex (P σ).toAddSubgroup : ℝ) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hrd (by positivity)
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => hσ σ)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hsum
  have e1 : Real.log (secIndex D'.lattice v₀) = Real.log (secIndex Λ' v₀) := rfl
  rw [div_add' _ _ _ hn.ne', div_le_div_iff_of_pos_right hn]
  nlinarith

end Hodge

section Main

variable {K : Type} [Field K] {A B : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **One metrization of `𝒩_A` gives one of `𝒩_B`, at most `½ log d` higher**, for a homomorphism
`f : 𝒩_A → 𝒩_B` that is bijective on cotangent spaces at the origin, surjective on complex points,
with finite kernels on complex points of order `≤ d`. -/
theorem height_le_of_metrized {g : ℕ} (M : MetrizedModel A L g) (𝒩 : GroupModel B L)
    (f : M.model.G ⟶ 𝒩.G) [IsMonHom f] (hcot : Function.Bijective (cotMap M.model 𝒩 f))
    (hsurj : ∀ τ : L →+* ℂ, Function.Surjective fun p : M.model.Pts τ => p ≫ f) (d : ℕ)
    (hker : ∀ τ : L →+* ℂ, Finite {p : M.model.Pts τ // p ≫ f = 1} ∧
      Nat.card {p : M.model.Pts τ // p ≫ f = 1} ≤ d) :
    𝒩.height ≤ ((M.hodge.modelHeight + (1 / 2) * Real.log d : ℝ) : EReal) := by
  set H := hodgeMap M.model 𝒩 f g
  have hbij : Function.Bijective H := ZInQ.H5Glue.baseChange_map_bijective g _ hcot
  have hfin : Module.finrank L (𝒩.hodgeSpace g) = 1 :=
    (LinearEquiv.ofBijective H hbij).finrank_eq.trans M.hodge.finrank_eq_one
  obtain ⟨v₀, hv₀, hv0⟩ :=
    ZInQ.H5Glue.hodgeLatticeNonzero_of_omegaSpans ZInQ.H5Glue.omegaSpans K B L 𝒩 g hfin
  have hle : ∀ x ∈ 𝒩.detLattice g, H x ∈ M.hodge.lattice := fun x hx => by
    rw [M.lattice_eq]; exact hodgeMap_detLattice _ _ f g x hx
  have hHv0 : H v₀ ≠ 0 := fun h0 => hv0 (hbij.1 (h0.trans (map_zero H).symm))
  have hne := ZInQ.H5Glue.secIndex_ne_zero_of_mem M.hodge (hle v₀ hv₀) hHv0
  have hlat : ∃ s ∈ 𝒩.detLattice g, s ≠ 0 ∧ secIndex (𝒩.detLattice g) s ≠ 0 :=
    ⟨v₀, hv₀, hv0, (ZInQ.H5Glue.secIndex_le_of_map H hbij.1 _ _ hle hv₀ hne).1⟩
  choose Φ hΦ hc using M.arch
  let P : (L →+* ℂ) → Submodule ℤ (Fin g → ℂ) := fun σ => isogPeriods M.model 𝒩 f (Φ σ) (hΦ σ).1
  have hP : ∀ σ, M.hodge.periods σ ≤ P σ := fun σ => le_isogPeriods M.model 𝒩 f _ (Φ σ) (hΦ σ)
  have hPi : ∀ σ, (M.hodge.periods σ).toAddSubgroup.relIndex (P σ).toAddSubgroup ≠ 0 :=
    fun σ => (relIndex_isogPeriods M.model 𝒩 f _ (Φ σ) (hΦ σ) (hker σ).1).1
  have hd : ∀ σ, (M.hodge.periods σ).toAddSubgroup.relIndex (P σ).toAddSubgroup ≤ d :=
    fun σ => (relIndex_isogPeriods M.model 𝒩 f _ (Φ σ) (hΦ σ) (hker σ).1).2.trans (hker σ).2
  let D' := isogHodge M.hodge H hbij.1 (𝒩.detLattice g) hfin hlat P hP hPi
  let M' : MetrizedModel B L g :=
    { model := 𝒩
      hodge := D'
      lattice_eq := rfl
      arch := fun τ => by
        obtain ⟨hmul, -, hsurj0, hopen, hdiff⟩ := hΦ τ
        refine ⟨fun z => Φ τ z ≫ f, ⟨?_, ?_, ?_, ?_, ?_⟩, fun t => ?_⟩
        · intro z w
          simp only
          rw [hmul, MonObj.mul_comp]
        · intro z
          exact (mem_isogPeriods M.model 𝒩 f (Φ τ) (hΦ τ).1 z).symm
        · intro q
          obtain ⟨p, rfl⟩ := hsurj τ q
          obtain ⟨z, rfl⟩ := hsurj0 p
          exact ⟨z, rfl⟩
        · intro U
          rw [dom_comp]
          exact hopen _
        · intro U s
          rw [dom_comp]
          simp only [evalAt_comp]
          exact hdiff _ _
        · show M.hodge.coeff τ (H (𝒩.wedge t)) = _
          rw [hodgeMap_wedgeGerm, hc τ, jacDet_comp_genMap M.model 𝒩 f _ (Φ τ) (hΦ τ) t
            (fun i => ⟨genMap M.model 𝒩 f (t i), genMap_mem_maximalIdeal _ _ f _ (t i).2⟩)
            (fun i => rfl)] }
  calc 𝒩.height ≤ (M'.hodge.modelHeight : EReal) :=
        iInf_le_of_le g (iInf_le_of_le M' (iInf_le_of_le rfl le_rfl))
    _ ≤ _ := EReal.coe_le_coe_iff.mpr
        (modelHeight_isogHodge_le M.hodge H hbij.1 _ hfin hlat P hP hPi d hd hle)

end Main

end GapHeight
