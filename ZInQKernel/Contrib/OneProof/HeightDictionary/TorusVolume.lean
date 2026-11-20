import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex

/-! # height-dict: the volume of a uniformized compact group (Mathlib only)

The archimedean step of the dictionary between the kernel's coordinate-form Faltings metric
`torusMetricSq Λ c = |c|² covol(Λ)` and the printed metric `(i/2)^g ∫_{A(ℂ)} α ∧ ᾱ`. -/

open MeasureTheory Measure Set Filter Topology Module Metric
open scoped NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace ZInQ.HeightDict.TorusVolume

variable {g : ℕ}

/-- A small ball around `0` meets no other point of its `Λ`-orbit. -/
theorem exists_ball_sub_mem (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ x ∈ ball (0 : Fin g → ℂ) r₀, ∀ y ∈ ball (0 : Fin g → ℂ) r₀,
      x - y ∈ Λ → x = y := by
  have h0 : IsOpen ({0} : Set Λ) := isOpen_discrete _
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp h0
  have h0t : (0 : Fin g → ℂ) ∈ t := by
    have : (0 : Λ) ∈ Subtype.val ⁻¹' t := by rw [hts]; rfl
    simpa using this
  obtain ⟨ρ, hρ, hρt⟩ := Metric.isOpen_iff.mp ht 0 h0t
  refine ⟨ρ / 2, by positivity, fun x hx y hy hxy => ?_⟩
  have hd : x - y ∈ ball (0 : Fin g → ℂ) ρ := by
    rw [mem_ball_zero_iff] at hx hy ⊢
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ < ρ / 2 + ρ / 2 := add_lt_add hx hy
      _ = ρ := by ring
  have : (⟨x - y, hxy⟩ : Λ) ∈ Subtype.val ⁻¹' t := hρt hd
  rw [hts] at this
  have h' : x - y = 0 := congrArg Subtype.val this
  exact sub_eq_zero.mp h'

/-- **A fundamental domain containing a ball.** -/
theorem exists_fundamentalDomain_ball (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ D : Set (Fin g → ℂ), MeasurableSet D ∧
      IsAddFundamentalDomain Λ D volume ∧ ball 0 r₀ ⊆ D ∧
      (∀ x ∈ D, ∀ y ∈ ball (0 : Fin g → ℂ) r₀, x - y ∈ Λ → x = y) ∧ volume D < ⊤ := by
  obtain ⟨r₀, hr₀, hsep⟩ := exists_ball_sub_mem Λ
  let b := (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ
  have hb : Submodule.span ℤ (Set.range b) = Λ :=
    (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis_span ℝ Λ
  set D₀ := ZSpan.fundamentalDomain b
  have hD₀m : MeasurableSet D₀ := ZSpan.fundamentalDomain_measurableSet b
  have huniq : ∀ x : Fin g → ℂ, ∃! l : Λ, (l : Fin g → ℂ) + x ∈ D₀ := by
    intro x
    obtain ⟨v, hv, hvu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
    have hvΛ : (v : Fin g → ℂ) ∈ Λ := (SetLike.ext_iff.mp hb _).mp v.2
    refine ⟨⟨v, hvΛ⟩, hv, fun l hl => ?_⟩
    have hlS : (l : Fin g → ℂ) ∈ Submodule.span ℤ (Set.range b) := (SetLike.ext_iff.mp hb _).mpr l.2
    have := hvu ⟨l, hlS⟩ hl
    exact Subtype.ext (congrArg Subtype.val this : (l : Fin g → ℂ) = v)
  set T : Set (Fin g → ℂ) := {x | ∃ l ∈ Λ, x - l ∈ ball (0 : Fin g → ℂ) r₀}
  have hTo : IsOpen T := by
    have : T = ⋃ l : Λ, (fun x => x - (l : Fin g → ℂ)) ⁻¹' ball 0 r₀ := by
      ext x; simp [T]
    rw [this]
    exact isOpen_iUnion fun l => isOpen_ball.preimage (continuous_id.sub continuous_const)
  set D := ball (0 : Fin g → ℂ) r₀ ∪ (D₀ \ T)
  have hDm : MeasurableSet D := measurableSet_ball.union (hD₀m.diff hTo.measurableSet)
  have hBT : ∀ y ∈ ball (0 : Fin g → ℂ) r₀, ∀ l ∈ Λ, y + l ∈ T := fun y hy l hl =>
    ⟨l, hl, by simpa using hy⟩
  refine ⟨r₀, hr₀, D, hDm, ?_, subset_union_left, ?_, ?_⟩
  · refine IsAddFundamentalDomain.mk' hDm.nullMeasurableSet fun x => ?_
    simp only [Submodule.vadd_def, vadd_eq_add]
    by_cases hx : x ∈ T
    · obtain ⟨l₀, hl₀, hxl⟩ := hx
      refine ⟨⟨-l₀, Λ.neg_mem hl₀⟩, Or.inl (by simpa [neg_add_eq_sub] using hxl), ?_⟩
      rintro ⟨l', hl'⟩ (h | h)
      · have := hsep _ h _ hxl (by
          have : l' + x - (x - l₀) = l' + l₀ := by abel
          rw [this]; exact Λ.add_mem hl' hl₀)
        apply Subtype.ext
        show l' = -l₀
        have h2 : l' + x = x - l₀ := this
        linear_combination (exp := 1) h2
      · exfalso
        apply h.2
        have := hBT _ hxl (l' + l₀) (Λ.add_mem hl' hl₀)
        have e : x - l₀ + (l' + l₀) = l' + x := by abel
        rwa [e] at this
    · obtain ⟨l, hl, hlu⟩ := huniq x
      refine ⟨l, Or.inr ⟨hl, fun hT => hx ?_⟩, fun l' hl' => ?_⟩
      · obtain ⟨m, hm, hmx⟩ := hT
        exact ⟨m - l, Λ.sub_mem hm l.2, by
          have e : x - (m - (l : Fin g → ℂ)) = (l : Fin g → ℂ) + x - m := by abel
          rwa [e]⟩
      · rcases hl' with h | h
        · exfalso
          exact hx ⟨-l', Λ.neg_mem l'.2, by
            have e : x - -(l' : Fin g → ℂ) = (l' : Fin g → ℂ) + x := by abel
            rwa [e]⟩
        · exact hlu l' h.1
  · intro x hx y hy hxy
    rcases hx with h | h
    · exact hsep x h y hy hxy
    · exfalso
      apply h.2
      have := hBT y hy (x - y) hxy
      rwa [add_sub_cancel] at this
  · have hb1 : Bornology.IsBounded D :=
      Metric.isBounded_ball.union ((ZSpan.fundamentalDomain_isBounded b).subset sdiff_subset)
    exact hb1.measure_lt_top


/-! ## A group uniformized by `ℂ^g` -/

section Unif

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- `Φ : ℂ^g → G` is a continuous surjective homomorphism with kernel `Λ`. -/
structure IsUnif (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → G) : Prop where
  cont : Continuous Φ
  add : ∀ z w, Φ (z + w) = Φ z * Φ w
  ker : ∀ z, Φ z = 1 ↔ z ∈ Λ
  surj : Function.Surjective Φ

variable {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → G}

namespace IsUnif

theorem map_zero (h : IsUnif Λ Φ) : Φ 0 = 1 := (h.ker 0).2 Λ.zero_mem

theorem map_neg (h : IsUnif Λ Φ) (z : Fin g → ℂ) : Φ (-z) = (Φ z)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← h.add, neg_add_cancel, h.map_zero]

theorem map_sub (h : IsUnif Λ Φ) (a b : Fin g → ℂ) : Φ (a - b) = Φ a * (Φ b)⁻¹ := by
  rw [sub_eq_add_neg, h.add, h.map_neg]

theorem eq_iff (h : IsUnif Λ Φ) (a b : Fin g → ℂ) : Φ a = Φ b ↔ a - b ∈ Λ := by
  rw [← h.ker, h.map_sub, mul_inv_eq_one]

/-- The induced map on the torus `ℂ^g/Λ`. -/
def torusMap (h : IsUnif Λ Φ) : (Fin g → ℂ) ⧸ Λ.toAddSubgroup → G :=
  Quotient.lift (s := QuotientAddGroup.leftRel Λ.toAddSubgroup) Φ (fun a b hab => by
    rw [h.eq_iff]
    have := QuotientAddGroup.leftRel_apply.mp hab
    have e : a - b = -(-a + b) := by abel
    rw [e]
    exact Λ.neg_mem this)

theorem torusMap_mk (h : IsUnif Λ Φ) (x : Fin g → ℂ) :
    h.torusMap (QuotientAddGroup.mk x) = Φ x := rfl

theorem torusMap_continuous (h : IsUnif Λ Φ) : Continuous h.torusMap :=
  h.cont.quotient_lift _

theorem torusMap_bijective (h : IsUnif Λ Φ) : Function.Bijective h.torusMap := by
  refine ⟨fun x y hxy => ?_, fun p => ?_⟩
  · induction x using QuotientAddGroup.induction_on with | H a => ?_
    induction y using QuotientAddGroup.induction_on with | H b => ?_
    rw [h.torusMap_mk, h.torusMap_mk, h.eq_iff] at hxy
    apply QuotientAddGroup.eq.mpr
    have e : -a + b = -(a - b) := by abel
    rw [e]
    exact Λ.neg_mem hxy
  · obtain ⟨a, ha⟩ := h.surj p
    exact ⟨QuotientAddGroup.mk a, ha⟩

theorem compactSpace_torus [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    CompactSpace ((Fin g → ℂ) ⧸ Λ.toAddSubgroup) := by
  have := IsZLattice.isCompact_range_of_periodic Λ
    (QuotientAddGroup.mk : (Fin g → ℂ) → (Fin g → ℂ) ⧸ Λ.toAddSubgroup) continuous_quot_mk
    (fun z w hw => QuotientAddGroup.eq.mpr (by
      rw [neg_add_rev, add_assoc, neg_add_cancel, add_zero]; exact Λ.toAddSubgroup.neg_mem hw))
  rw [QuotientAddGroup.mk_surjective.range_eq] at this
  exact isCompact_univ_iff.mp this

/-- `ℂ^g/Λ ≃ₜ G` (compact to Hausdorff). -/
noncomputable def torusHomeo [T2Space G] [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h : IsUnif Λ Φ) :
    (Fin g → ℂ) ⧸ Λ.toAddSubgroup ≃ₜ G :=
  haveI := compactSpace_torus (Λ := Λ)
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ h.torusMap_bijective)
    h.torusMap_continuous

theorem torusHomeo_mk [T2Space G] [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h : IsUnif Λ Φ)
    (x : Fin g → ℂ) : h.torusHomeo (QuotientAddGroup.mk x) = Φ x := rfl

theorem torusHomeo_add [T2Space G] [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h : IsUnif Λ Φ)
    (x y : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) :
    h.torusHomeo (x + y) = h.torusHomeo x * h.torusHomeo y := by
  induction x using QuotientAddGroup.induction_on with | H a => ?_
  induction y using QuotientAddGroup.induction_on with | H b => ?_
  rw [← QuotientAddGroup.mk_add, h.torusHomeo_mk, h.torusHomeo_mk, h.torusHomeo_mk, h.add]

theorem torusHomeo_neg [T2Space G] [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h : IsUnif Λ Φ)
    (x : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) : h.torusHomeo (-x) = (h.torusHomeo x)⁻¹ := by
  induction x using QuotientAddGroup.induction_on with | H a => ?_
  rw [← QuotientAddGroup.mk_neg, h.torusHomeo_mk, h.torusHomeo_mk, h.map_neg]

theorem isOpenMap [T2Space G] [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h : IsUnif Λ Φ) :
    IsOpenMap Φ := by
  have : Φ = h.torusHomeo ∘ (QuotientAddGroup.mk : (Fin g → ℂ) → _) := rfl
  rw [this]
  exact h.torusHomeo.isOpenMap.comp QuotientAddGroup.isOpenMap_coe

theorem compactSpace [T2Space G] [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h : IsUnif Λ Φ) :
    CompactSpace G :=
  haveI := compactSpace_torus (Λ := Λ)
  h.torusHomeo.compactSpace

theorem secondCountable [T2Space G] [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h : IsUnif Λ Φ) :
    SecondCountableTopology G :=
  h.torusHomeo.symm.secondCountableTopology

theorem isTopologicalGroup [T2Space G] [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h : IsUnif Λ Φ) :
    IsTopologicalGroup G := by
  set e := h.torusHomeo
  have hmul : (fun p : G × G => p.1 * p.2) = fun p => e (e.symm p.1 + e.symm p.2) := by
    funext p; rw [h.torusHomeo_add, e.apply_symm_apply, e.apply_symm_apply]
  have hinv : (fun p : G => p⁻¹) = fun p => e (-e.symm p) := by
    funext p; rw [h.torusHomeo_neg, e.apply_symm_apply]
  exact
    { continuous_mul := by
        rw [hmul]
        exact e.continuous.comp ((e.symm.continuous.comp continuous_fst).add
          (e.symm.continuous.comp continuous_snd))
      continuous_inv := by
        rw [hinv]
        exact e.continuous.comp (e.symm.continuous.neg) }

end IsUnif

end Unif


/-! ## The pushed-forward Lebesgue measure -/

section PiMeasure

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
variable {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → G}

/-- `π_D = Φ_*(Lebesgue|_D)`. -/
noncomputable def piMeasure (Φ : (Fin g → ℂ) → G) (D : Set (Fin g → ℂ)) : Measure G :=
  Measure.map Φ (volume.restrict D)

namespace IsUnif

theorem piMeasure_apply (h : IsUnif Λ Φ) (D : Set (Fin g → ℂ)) {S : Set G} (hS : MeasurableSet S) :
    piMeasure Φ D S = volume (Φ ⁻¹' S ∩ D) := by
  rw [piMeasure, Measure.map_apply h.cont.measurable hS,
    Measure.restrict_apply (h.cont.measurable hS)]

theorem preimage_vadd (h : IsUnif Λ Φ) (S : Set G) (l : Λ) :
    (fun x => l +ᵥ x) ⁻¹' (Φ ⁻¹' S) = Φ ⁻¹' S := by
  ext x
  simp only [mem_preimage, Submodule.vadd_def, vadd_eq_add, h.add, (h.ker l).2 l.2, one_mul]

theorem vadd_set (h : IsUnif Λ Φ) (S : Set G) (l : Λ) : l +ᵥ (Φ ⁻¹' S) = Φ ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := congrArg (fun T => y ∈ T) (h.preimage_vadd S l)
    simp only [mem_preimage, eq_iff_iff] at this
    exact this.mpr hy
  · intro hx
    refine ⟨-(l : Fin g → ℂ) + x, ?_, ?_⟩
    · have := congrArg (fun T => (-(l : Fin g → ℂ) + x) ∈ T) (h.preimage_vadd S l)
      simp only [mem_preimage, eq_iff_iff] at this
      apply this.mp
      simpa [Submodule.vadd_def] using hx
    · simp [Submodule.vadd_def]

theorem piMeasure_eq_of_fd [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h : IsUnif Λ Φ)
    {D D' : Set (Fin g → ℂ)}
    (hD : IsAddFundamentalDomain Λ D volume) (hD' : IsAddFundamentalDomain Λ D' volume) :
    piMeasure Φ D = piMeasure Φ D' := by
  have : MeasurableVAdd Λ (Fin g → ℂ) := (inferInstance : MeasurableVAdd Λ.toAddSubgroup _)
  have : VAddInvariantMeasure Λ (Fin g → ℂ) volume :=
    (inferInstance : VAddInvariantMeasure Λ.toAddSubgroup _ volume)
  ext S hS
  rw [h.piMeasure_apply D hS, h.piMeasure_apply D' hS]
  exact hD.measure_set_eq hD' (h.cont.measurable hS) (h.preimage_vadd S)

theorem piMeasure_leftInvariant [T2Space G] [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (h : IsUnif Λ Φ) {D : Set (Fin g → ℂ)} (hD : IsAddFundamentalDomain Λ D volume) :
    (piMeasure Φ D).IsMulLeftInvariant := by
  haveI := h.isTopologicalGroup
  have : MeasurableVAdd Λ (Fin g → ℂ) := (inferInstance : MeasurableVAdd Λ.toAddSubgroup _)
  have : VAddInvariantMeasure Λ (Fin g → ℂ) volume :=
    (inferInstance : VAddInvariantMeasure Λ.toAddSubgroup _ volume)
  haveI : VAddCommClass (Fin g → ℂ) Λ (Fin g → ℂ) :=
    ⟨fun z l x => by simp only [Submodule.vadd_def, vadd_eq_add]; abel⟩
  constructor
  intro p
  obtain ⟨z, rfl⟩ := h.surj p
  ext S hS
  rw [Measure.map_apply (measurable_const_mul _) hS, h.piMeasure_apply D hS,
    h.piMeasure_apply D (measurable_const_mul _ hS)]
  have e1 : Φ ⁻¹' ((fun x => Φ z * x) ⁻¹' S) = (fun x => z + x) ⁻¹' (Φ ⁻¹' S) := by
    ext x; simp [h.add]
  have e2 : (fun x => z + x) ⁻¹' (Φ ⁻¹' S) ∩ D =
      (fun x => z + x) ⁻¹' (Φ ⁻¹' S ∩ (z +ᵥ D)) := by
    ext x
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, ⟨x, h2, rfl⟩⟩
    · rintro ⟨h1, ⟨y, hy, hyx⟩⟩
      have : y = x := by simpa [vadd_eq_add] using hyx
      exact ⟨h1, this ▸ hy⟩
  rw [e1, e2, measure_preimage_add]
  exact ((hD.vadd_of_comm z).measure_set_eq hD (h.cont.measurable hS) (h.preimage_vadd S))

theorem piMeasure_isOpenPos [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h : IsUnif Λ Φ)
    {D : Set (Fin g → ℂ)}
    (hD : IsAddFundamentalDomain Λ D volume) : (piMeasure Φ D).IsOpenPosMeasure := by
  have : MeasurableVAdd Λ (Fin g → ℂ) := (inferInstance : MeasurableVAdd Λ.toAddSubgroup _)
  have : VAddInvariantMeasure Λ (Fin g → ℂ) volume :=
    (inferInstance : VAddInvariantMeasure Λ.toAddSubgroup _ volume)
  constructor
  intro O hO hne h0
  rw [h.piMeasure_apply D hO.measurableSet] at h0
  have hz := hD.measure_zero_of_invariant (Φ ⁻¹' O) (h.vadd_set O) h0
  obtain ⟨p, hp⟩ := hne
  obtain ⟨z, rfl⟩ := h.surj p
  exact ((hO.preimage h.cont).measure_pos volume ⟨z, hp⟩).ne' hz

theorem piMeasure_univ (h : IsUnif Λ Φ) (D : Set (Fin g → ℂ)) :
    piMeasure Φ D univ = volume D := by
  rw [h.piMeasure_apply D MeasurableSet.univ, preimage_univ, univ_inter]

theorem piMeasure_image_ball (h : IsUnif Λ Φ) [T2Space G] [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {D : Set (Fin g → ℂ)} {r₀ : ℝ} (hBD : ball 0 r₀ ⊆ D)
    (hsep : ∀ x ∈ D, ∀ y ∈ ball (0 : Fin g → ℂ) r₀, x - y ∈ Λ → x = y) {r : ℝ} (hr : r ≤ r₀) :
    piMeasure Φ D (Φ '' ball 0 r) = volume (ball (0 : Fin g → ℂ) r) := by
  rw [h.piMeasure_apply D (h.isOpenMap _ isOpen_ball).measurableSet]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨y, hy, hyx⟩, hxD⟩
    have := hsep x hxD y (ball_subset_ball hr hy) ((h.eq_iff x y).mp hyx.symm)
    rwa [this]
  · intro hx
    exact ⟨⟨x, hx, rfl⟩, hBD (ball_subset_ball hr hx)⟩

end IsUnif

end PiMeasure


/-! ## The volume of a normalized invariant measure -/

section Main

/-- The real determinant of a complex-linear map of `ℂ^g` is `|det_ℂ|²`. -/
theorem det_restrictScalars_eq (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) :
    (D.restrictScalars ℝ : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ)).det =
      ‖LinearMap.det (D : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

theorem eq_of_abs_le {x y : ℝ} (K : ℝ) (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → |x - y| ≤ ε * K) : x = y := by
  have hK : 0 ≤ K := by
    have := h 1 one_pos le_rfl
    linarith [abs_nonneg (x - y)]
  refine eq_of_forall_dist_le fun e he => ?_
  rw [Real.dist_eq]
  set ε := min 1 (e / (K + 1))
  have hε : 0 < ε := lt_min one_pos (div_pos he (by linarith))
  have h1 := h ε hε (min_le_left _ _)
  have h2 : ε * K ≤ e := by
    have : ε ≤ e / (K + 1) := min_le_right _ _
    calc ε * K ≤ e / (K + 1) * K := mul_le_mul_of_nonneg_right this hK
      _ ≤ e := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
  linarith

variable {G : Type*} [Group G] [TopologicalSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
variable {Φ : (Fin g → ℂ) → G}

/-- **The volume of a normalized invariant measure.** Let `Φ : ℂ^g → G` be a continuous surjective
homomorphism with kernel the full lattice `Λ` onto a Hausdorff group, `μ` a finite left-invariant
Borel measure on `G` and `F : G → ℂ^g` a map such that `F ∘ Φ` is strictly differentiable at `0`
with `ℂ`-linear derivative `D`. If `F_* μ` has density `a` at `F(1)` relative to Lebesgue measure
(`hnorm`), then `μ(G) = a · |det D|² · covol(Λ)`. -/
theorem volume_eq_of_normalized (h : IsUnif Λ Φ) (μ : Measure G) [IsFiniteMeasure μ]
    [μ.IsMulLeftInvariant] (F : G → (Fin g → ℂ)) (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    (hψ : HasStrictFDerivAt (F ∘ Φ) (D.restrictScalars ℝ) 0) (a : ℝ)
    (hnorm : ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 (1 : G), ∀ E ⊆ W, MeasurableSet E →
      |(μ E).toReal - a * (volume (F '' E)).toReal| ≤ ε * (volume (F '' E)).toReal) :
    (μ univ).toReal =
      a * ‖LinearMap.det (D : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 * ZLattice.covolume Λ := by
  haveI := h.isTopologicalGroup
  haveI := h.compactSpace
  haveI := h.secondCountable
  obtain ⟨r₀, hr₀, DD, hDm, hfd, hB, hsep, hfin⟩ := exists_fundamentalDomain_ball Λ
  set π := piMeasure Φ DD with hπ
  haveI : IsFiniteMeasure π := ⟨by rw [h.piMeasure_univ]; exact hfin⟩
  haveI := h.piMeasure_leftInvariant hfd
  haveI := h.piMeasure_isOpenPos hfd
  haveI : IsHaarMeasure π := {}
  have hμ : μ = haarScalarFactor μ π • π := isMulLeftInvariant_eq_smul μ π
  set c : ℝ≥0 := haarScalarFactor μ π
  set d : ℝ := ‖LinearMap.det (D : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 with hd
  have hd0 : 0 ≤ d := by positivity
  set A : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ) := D.restrictScalars ℝ
  have hAd : |A.det| = d := by rw [det_restrictScalars_eq, abs_of_nonneg hd0]
  -- the scalar is `a d`
  have hc : (c : ℝ) = a * d := by
    refine eq_of_abs_le (d + 1 + |a|) fun ε hε hε1 => ?_
    -- Jacobian estimates
    have hup : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), ∀ (s : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → (Fin g → ℂ)),
        ApproximatesLinearOn f A s δ →
          volume (f '' s) ≤ ENNReal.ofReal (d + ε) * volume s :=
      addHaar_image_le_mul_of_det_lt (volume : Measure (Fin g → ℂ)) A
        (m := Real.toNNReal (d + ε)) (by
          rw [hAd]
          exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
    have hlow : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), ∀ (s : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → (Fin g → ℂ)),
        ApproximatesLinearOn f A s δ →
          ENNReal.ofReal (d - ε) * volume s ≤ volume (f '' s) := by
      by_cases hdε : ε < d
      · exact mul_le_addHaar_image_of_lt_det (volume : Measure (Fin g → ℂ)) A
          (m := Real.toNNReal (d - ε)) (by
            rw [hAd]
            exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
      · filter_upwards with δ s f _
        rw [ENNReal.ofReal_of_nonpos (by linarith), zero_mul]
        exact bot_le
    obtain ⟨δ, ⟨hδu, hδl⟩, hδpos⟩ := ((hup.and hlow).and self_mem_nhdsWithin).exists
    obtain ⟨s, hs, hsA⟩ := hψ.approximates_deriv_on_nhds (c := δ) (Or.inr hδpos)
    obtain ⟨W, hW, hWn⟩ := hnorm ε hε
    have hΦW : Φ ⁻¹' W ∈ 𝓝 (0 : Fin g → ℂ) :=
      h.cont.continuousAt.preimage_mem_nhds (by rw [h.map_zero]; exact hW)
    obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.mem_nhds_iff.mp (inter_mem hs hΦW)
    set r := min r₁ r₀
    have hr : 0 < r := lt_min hr₁ hr₀
    set B := ball (0 : Fin g → ℂ) r
    have hBs : B ⊆ s := fun x hx => (hr₁s (ball_subset_ball (min_le_left _ _) hx)).1
    have hBW : Φ '' B ⊆ W := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hr₁s (ball_subset_ball (min_le_left _ _) hx)).2
    have hEm : MeasurableSet (Φ '' B) := (h.isOpenMap _ isOpen_ball).measurableSet
    have hN := hWn (Φ '' B) hBW hEm
    rw [image_image] at hN
    have hsB : ApproximatesLinearOn (F ∘ Φ) A B δ := hsA.mono_set hBs
    have hX1 := hδu B (F ∘ Φ) hsB
    have hX2 := hδl B (F ∘ Φ) hsB
    have hπB : π (Φ '' B) = volume B := h.piMeasure_image_ball hB hsep (min_le_right _ _)
    have hμB : μ (Φ '' B) = c * volume B := by
      rw [hμ, Measure.smul_apply, hπB, ENNReal.smul_def, smul_eq_mul]
    -- real numbers
    have hV0 : 0 < volume B := measure_ball_pos _ _ hr
    have hVt : volume B ≠ ⊤ := measure_ball_lt_top.ne
    set V := (volume B).toReal
    have hVpos : 0 < V := ENNReal.toReal_pos hV0.ne' hVt
    have hXt : volume ((fun x => F (Φ x)) '' B) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt) hX1
    set X := (volume ((fun x => F (Φ x)) '' B)).toReal
    have hXu : X ≤ (d + ε) * V := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt) hX1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
    have hXl : (d - ε) * V ≤ X := by
      by_cases hdε : 0 ≤ d - ε
      · have := ENNReal.toReal_mono hXt hX2
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hdε] at this
      · have : (d - ε) * V ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hVpos.le
        exact this.trans ENNReal.toReal_nonneg
    have hμr : (μ (Φ '' B)).toReal = c * V := by
      rw [hμB, ENNReal.toReal_mul, ENNReal.coe_toReal]
    rw [hμr] at hN
    -- |c V - a X| ≤ ε X
    have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
    have h1 : |(c : ℝ) * V - a * X| ≤ ε * ((d + ε) * V) :=
      hN.trans (mul_le_mul_of_nonneg_left hXu hε.le)
    have h2 : |a * X - a * d * V| ≤ |a| * (ε * V) := by
      rw [show a * X - a * d * V = a * (X - d * V) by ring, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
      rw [abs_le]; constructor <;> nlinarith
    have h3 : |((c : ℝ) - a * d) * V| ≤ ε * ((d + ε) * V) + |a| * (ε * V) := by
      have : ((c : ℝ) - a * d) * V = ((c : ℝ) * V - a * X) + (a * X - a * d * V) := by ring
      rw [this]
      exact (abs_add_le _ _).trans (add_le_add h1 h2)
    rw [abs_mul, abs_of_pos hVpos] at h3
    have h4 : |(c : ℝ) - a * d| ≤ ε * (d + ε) + |a| * ε := by
      have : |(c : ℝ) - a * d| * V ≤ (ε * (d + ε) + |a| * ε) * V := by linarith
      exact le_of_mul_le_mul_right this hVpos
    calc |(c : ℝ) - a * d| ≤ ε * (d + ε) + |a| * ε := h4
      _ ≤ ε * (d + 1 + |a|) := by nlinarith [abs_nonneg a]
  -- conclusion
  have hcov : ZLattice.covolume Λ = (volume DD).toReal :=
    ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hfd
  rw [hμ, Measure.smul_apply, h.piMeasure_univ, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, hc, hcov]


/-- **Existence: `‖det D‖² π` has density `1` at `F(1)`** (so `a ‖det D‖² π` has density `a`), for
`π = Φ_*(Lebesgue|_D)` and a fundamental domain `D` containing a ball, when `det D ≠ 0`. -/
theorem piMeasure_normalized (h : IsUnif Λ Φ) {DD : Set (Fin g → ℂ)} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hBD : ball 0 r₀ ⊆ DD) (hsep : ∀ x ∈ DD, ∀ y ∈ ball (0 : Fin g → ℂ) r₀, x - y ∈ Λ → x = y)
    (F : G → (Fin g → ℂ)) (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    (hψ : HasStrictFDerivAt (F ∘ Φ) (D.restrictScalars ℝ) 0)
    (hD : LinearMap.det (D : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) ≠ 0) (a : ℝ) (ha : 0 ≤ a) :
    ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 (1 : G), ∀ E ⊆ W, MeasurableSet E →
      |a * ‖LinearMap.det (D : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 * (piMeasure Φ DD E).toReal -
        a * (volume (F '' E)).toReal| ≤ ε * (volume (F '' E)).toReal := by
  intro ε hε
  set d : ℝ := ‖LinearMap.det (D : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 with hd
  have hdpos : 0 < d := by positivity
  set A : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ) := D.restrictScalars ℝ
  have hAd : |A.det| = d := by rw [det_restrictScalars_eq, abs_of_nonneg hdpos.le]
  set δ' : ℝ := min (d / 2) (ε * d / (2 * (a + 1))) with hδ'
  have hδ'pos : 0 < δ' := lt_min (by positivity) (by positivity)
  have hδ'1 : δ' ≤ d / 2 := min_le_left _ _
  have hδ'2 : δ' ≤ ε * d / (2 * (a + 1)) := min_le_right _ _
  have hup : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), ∀ (s : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → (Fin g → ℂ)),
      ApproximatesLinearOn f A s δ → volume (f '' s) ≤ ENNReal.ofReal (d + δ') * volume s :=
    addHaar_image_le_mul_of_det_lt (volume : Measure (Fin g → ℂ)) A
      (m := Real.toNNReal (d + δ')) (by
        rw [hAd]; exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
  have hlow : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), ∀ (s : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → (Fin g → ℂ)),
      ApproximatesLinearOn f A s δ → ENNReal.ofReal (d - δ') * volume s ≤ volume (f '' s) :=
    mul_le_addHaar_image_of_lt_det (volume : Measure (Fin g → ℂ)) A
      (m := Real.toNNReal (d - δ')) (by
        rw [hAd]; exact (ENNReal.ofReal_lt_ofReal_iff hdpos).mpr (by linarith))
  obtain ⟨δ, ⟨hδu, hδl⟩, hδpos⟩ := ((hup.and hlow).and self_mem_nhdsWithin).exists
  obtain ⟨s₀, hs₀, hsA⟩ := hψ.approximates_deriv_on_nhds (c := δ) (Or.inr hδpos)
  obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.mem_nhds_iff.mp hs₀
  set r := min r₁ r₀
  have hr : 0 < r := lt_min hr₁ hr₀
  set B := ball (0 : Fin g → ℂ) r
  have hBs : B ⊆ s₀ := (ball_subset_ball (min_le_left _ _)).trans hr₁s
  have hBr₀ : B ⊆ ball 0 r₀ := ball_subset_ball (min_le_right _ _)
  refine ⟨Φ '' B, (h.isOpenMap _ isOpen_ball).mem_nhds ⟨0, mem_ball_self hr, h.map_zero⟩, ?_⟩
  intro E hEW hE
  set E' := Φ ⁻¹' E ∩ B
  have hE'B : E' ⊆ B := inter_subset_right
  have hΦE' : Φ '' E' = E := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx.1
    · intro p hp
      obtain ⟨y, hy, rfl⟩ := hEW hp
      exact ⟨y, ⟨hp, hy⟩, rfl⟩
  have hπE : piMeasure Φ DD E = volume E' := by
    rw [h.piMeasure_apply DD hE]
    congr 1
    ext x
    constructor
    · rintro ⟨hx, hxD⟩
      obtain ⟨y, hy, hyx⟩ := hEW hx
      have := hsep x hxD y (hBr₀ hy) ((h.eq_iff x y).mp hyx.symm)
      exact ⟨hx, this ▸ hy⟩
    · rintro ⟨hx, hxB⟩
      exact ⟨hx, hBD (hBr₀ hxB)⟩
  have hFE : F '' E = (F ∘ Φ) '' E' := by rw [← hΦE', image_comp]
  rw [hπE, hFE]
  have hsE : ApproximatesLinearOn (F ∘ Φ) A E' δ := hsA.mono_set (hE'B.trans hBs)
  have hX1 := hδu E' (F ∘ Φ) hsE
  have hX2 := hδl E' (F ∘ Φ) hsE
  have hVt : volume E' ≠ ⊤ := (measure_mono hE'B).trans_lt measure_ball_lt_top |>.ne
  have hXt : volume ((F ∘ Φ) '' E') ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt) hX1
  set V := (volume E').toReal
  set X := (volume ((F ∘ Φ) '' E')).toReal
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hXu : X ≤ (d + δ') * V := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt) hX1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hXl : (d - δ') * V ≤ X := by
    have := ENNReal.toReal_mono hXt hX2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
  have h1 : |a * d * V - a * X| ≤ a * (δ' * V) := by
    rw [show a * d * V - a * X = a * (d * V - X) by ring, abs_mul, abs_of_nonneg ha]
    refine mul_le_mul_of_nonneg_left ?_ ha
    rw [abs_le]; constructor <;> nlinarith
  have hVX : V ≤ 2 / d * X := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hdpos]
    nlinarith
  calc |a * d * V - a * X| ≤ a * (δ' * V) := h1
    _ ≤ a * (ε * d / (2 * (a + 1)) * (2 / d * X)) := by
        apply mul_le_mul_of_nonneg_left _ ha
        exact mul_le_mul hδ'2 hVX hV0 (by positivity)
    _ = ε * X * (a / (a + 1)) := by field_simp
    _ ≤ ε * X * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_one (by linarith)]; linarith
    _ = ε * X := mul_one _

end Main

end ZInQ.HeightDict.TorusVolume
