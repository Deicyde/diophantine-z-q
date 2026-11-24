import ZInQKernel.Contrib.OneProof.SphereCoveringSection
import Mathlib.Geometry.Manifold.Complex

/-! Local primitives with locally constant differences on the Riemann
sphere glue to a global primitive. -/

noncomputable section

open Set Function Filter
open scoped Topology

/-- On a space homeomorphic to the Riemann sphere, local functions whose
differences are locally constant on overlaps can be adjusted by locally
constant functions to give a single global function. -/
theorem exists_function_of_locallyConstant_differences_on_sphere
    {X A ι : Type*} [TopologicalSpace X] [AddCommGroup A]
    (e : X ≃ₜ OnePoint ℂ) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hCov : ∀ x, ∃ i, x ∈ U i) (g : ι → X → A)
    (hDiff : ∀ i j x, x ∈ U i → x ∈ U j →
      ∀ᶠ y in 𝓝 x, g i y - g j y = g i x - g j x) :
    ∃ F : X → A, ∀ i x, x ∈ U i → ∀ᶠ y in 𝓝 x, F y - g i y = F x - g i x := by
  choose indexAt hIndex using hCov
  let _ : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  let Z : FiberBundleCore ι X A :=
    { baseSet := U
      isOpen_baseSet := hU
      indexAt := indexAt
      mem_baseSet_at := hIndex
      coordChange := fun i j x a => (g i x - g j x) + a
      coordChange_self := by intros; simp
      continuousOn_coordChange := by
        intro i j z hz
        have h₁ := continuous_fst.continuousAt.eventually (hDiff i j z.1 hz.1.1 hz.1.2)
        have h₂ : ∀ᶠ w : X × A in 𝓝 z, w.2 = z.2 :=
          continuous_snd.continuousAt.eventually ((isOpen_discrete {z.2}).mem_nhds rfl)
        apply ContinuousAt.continuousWithinAt
        have hc : ContinuousAt (fun _ : X × A => (g i z.1 - g j z.1) + z.2) z :=
          continuousAt_const
        refine hc.congr_of_eventuallyEq ?_
        filter_upwards [h₁, h₂] with w hw₁ hw₂
        rw [hw₁, hw₂]
      coordChange_comp := by
        intros
        abel }
  have hp : IsCoveringMap Z.proj := FiberBundle.isCoveringMap
  have hsur : Function.Surjective Z.proj := fun x => ⟨⟨x, (0 : A)⟩, rfl⟩
  obtain ⟨σ, hσ⟩ := hp.exists_section_of_homeomorphic_onePointComplex hsur e
  let F : X → A := fun x => g (indexAt x) x + (show A from (σ x).2)
  refine ⟨F, fun i x hx => ?_⟩
  have hproj (y : X) : (σ y).1 = y := congrFun hσ y
  have hmem : σ x ∈ (Z.localTriv i).source :=
    (Z.mem_localTriv_source i _).mpr ((hproj x).symm ▸ hx)
  have ht : ContinuousAt (fun y => Z.localTriv i (σ y)) x :=
    ((Z.localTriv i).continuousOn_toFun.continuousAt
      ((Z.localTriv i).open_source.mem_nhds hmem)).comp σ.continuous.continuousAt
  have hcont : ContinuousAt (fun y => (Z.localTriv i (σ y)).2) x :=
    continuous_snd.continuousAt.comp ht
  have hx' (y : X) : (Z.localTriv i (σ y)).2 = F y - g i y := by
    change (g (indexAt (σ y).1) (σ y).1 - g i (σ y).1) + (show A from (σ y).2) = _
    rw [hproj y]
    dsimp [F]
    abel
  have hev : ∀ᶠ y in 𝓝 x, (Z.localTriv i (σ y)).2 = (Z.localTriv i (σ x)).2 :=
    hcont.eventually ((isOpen_discrete {_}).mem_nhds rfl)
  exact hev.mono fun y hy => (hx' y).symm.trans (hy.trans (hx' x))

open scoped Manifold

/-- A holomorphic local primitive on a compact complex manifold homeomorphic
to the sphere is locally constant if the primitives differ by locally
constant functions on overlaps. -/
theorem local_primitives_eventually_constant_on_complex_sphere
    {X E H ι : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H X] {I : ModelWithCorners ℂ E H}
    [I.Boundaryless] [IsManifold I 1 X]
    (e : X ≃ₜ OnePoint ℂ) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hCov : ∀ x, ∃ i, x ∈ U i) (g : ι → X → ℂ)
    (hg : ∀ i, MDifferentiableOn I 𝓘(ℂ, ℂ) (g i) (U i))
    (hDiff : ∀ i j x, x ∈ U i → x ∈ U j →
      ∀ᶠ y in 𝓝 x, g i y - g j y = g i x - g j x) :
    ∀ i x, x ∈ U i → ∀ᶠ y in 𝓝 x, g i y = g i x := by
  obtain ⟨F, hF⟩ := exists_function_of_locallyConstant_differences_on_sphere e U hU hCov g hDiff
  have hHol : MDifferentiable I 𝓘(ℂ, ℂ) F := by
    intro x
    obtain ⟨i, hx⟩ := hCov x
    have hgx := (hg i).mdifferentiableAt ((hU i).mem_nhds hx)
    have hd : MDifferentiableAt I 𝓘(ℂ, ℂ) (fun y => g i y + (F x - g i x)) x :=
      hgx.add mdifferentiableAt_const
    exact hd.congr_of_eventuallyEq ((hF i x hx).mono fun y hy => by
      change F y = g i y + (F x - g i x)
      linear_combination hy)
  have : CompactSpace X := e.symm.compactSpace
  intro i x hx
  filter_upwards [hF i x hx, hHol.isLocallyConstant.eventually_eq x] with y hy hFy
  rw [hFy] at hy
  exact sub_right_inj.mp hy

#print axioms exists_function_of_locallyConstant_differences_on_sphere
#print axioms local_primitives_eventually_constant_on_complex_sphere
