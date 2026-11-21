import ZInQKernel.Contrib.OneProof.ThetaLineBundle

/-!
# Holomorphic gluing for the theta line

The torus charts choose local lifts to the covering space. Two such lifts
differ by a period which is locally constant on the overlap. The theta
factor for that period is the holomorphic change of fibre coordinate.
-/

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

namespace BPAnalytic.ThetaLine

variable {g : ℕ} (Ω : Matrix (Fin g) (Fin g) ℂ) (h : Ω ∈ SiegelSpace g)

private abbrev liftChart (i : Torus (lattice Ω h)) := chartAt (Fin g → ℂ) i

private def coordinatesOfPeriod (v : Fin g → ℂ) : PeriodCoordinates g := by
  classical
  exact if hv : ∃ x, periodShift Ω x = v then Classical.choose hv else 0

private theorem periodShift_coordinates {v : Fin g → ℂ} (hv : v ∈ lattice Ω h) :
    periodShift Ω (coordinatesOfPeriod Ω v) = v := by
  obtain ⟨m, n, hmn⟩ := (mem_periodLattice_iff Ω _ v).mp hv
  have hx : ∃ x, periodShift Ω x = v := ⟨(m, n), hmn.symm⟩
  simpa only [coordinatesOfPeriod, dite_eq_left hx] using Classical.choose_spec hx

private theorem coordinates_zero (h : Ω ∈ SiegelSpace g) : coordinatesOfPeriod Ω 0 = 0 :=
  periodShift_injective Ω (det_im_ne_zero_of_mem_siegelSpace h)
    ((periodShift_coordinates Ω h (lattice Ω h).zero_mem).trans (map_zero (periodShift Ω)).symm)

private theorem chartDifference_mem {i j p : Torus (lattice Ω h)}
    (hi : p ∈ (liftChart Ω h i).source) (hj : p ∈ (liftChart Ω h j).source) :
    liftChart Ω h j p - liftChart Ω h i p ∈ lattice Ω h :=
  (proj_eq_iff (lattice Ω h)).mp
    ((proj_chartOf (lattice Ω h) (x := j.out) hj).trans
      (proj_chartOf (lattice Ω h) (x := i.out) hi).symm)

/-- The multiplier expressing the coordinate in chart `j` in terms of chart `i`. -/
def chartFactor (i j p : Torus (lattice Ω h)) : ℂ :=
  factor Ω (coordinatesOfPeriod Ω (liftChart Ω h j p - liftChart Ω h i p)) (liftChart Ω h i p)

/-- The changes of coordinates in the atlas identify the same point of the quotient. -/
theorem fibreAtChart_change {i j p : Torus (lattice Ω h)}
    (hi : p ∈ (liftChart Ω h i).source) (hj : p ∈ (liftChart Ω h j).source) (z : ℂ) :
    (fibreAtLift Ω h (liftChart Ω h j p) (chartFactor Ω h i j p * z)).val =
      (fibreAtLift Ω h (liftChart Ω h i p) z).val := by
  let u := liftChart Ω h i p
  let v := liftChart Ω h j p
  let a := coordinatesOfPeriod Ω (v - u)
  have ha : periodShift Ω a = v - u := periodShift_coordinates Ω h (chartDifference_mem Ω h hi hj)
  have hv : u + periodShift Ω a = v := by rw [ha]; abel
  change (fibreAtLift Ω h v (factor Ω a u * z)).val = (fibreAtLift Ω h u z).val
  rw [← hv]
  exact fibreAtLift_change Ω h u a z

private theorem chartFactor_comp {i j k p : Torus (lattice Ω h)}
    (hi : p ∈ (liftChart Ω h i).source) (hj : p ∈ (liftChart Ω h j).source)
    (hk : p ∈ (liftChart Ω h k).source) :
    chartFactor Ω h j k p * chartFactor Ω h i j p = chartFactor Ω h i k p := by
  let u := liftChart Ω h i p
  let v := liftChart Ω h j p
  let w := liftChart Ω h k p
  let a := coordinatesOfPeriod Ω (v - u)
  let b := coordinatesOfPeriod Ω (w - v)
  let c := coordinatesOfPeriod Ω (w - u)
  have ha : periodShift Ω a = v - u := periodShift_coordinates Ω h (chartDifference_mem Ω h hi hj)
  have hb : periodShift Ω b = w - v := periodShift_coordinates Ω h (chartDifference_mem Ω h hj hk)
  have hc : periodShift Ω c = w - u := periodShift_coordinates Ω h (chartDifference_mem Ω h hi hk)
  have hab : b + a = c := by
    apply periodShift_injective Ω (det_im_ne_zero_of_mem_siegelSpace h)
    rw [map_add, ha, hb, hc]
    abel
  have hv : v = u + periodShift Ω a := by rw [ha]; abel
  change factor Ω b v * factor Ω a u = factor Ω c u
  rw [hv, factor_cocycle Ω h.1, hab]

/-- On a chart overlap, the factor is holomorphic because the period difference
is locally constant and the multiplier for each fixed period is holomorphic. -/
theorem contMDiffOn_chartFactor (i j : Torus (lattice Ω h)) :
    ContMDiffOn 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, ℂ) ω (chartFactor Ω h i j)
      ((liftChart Ω h i).source ∩ (liftChart Ω h j).source) := by
  intro p hp
  let ci := liftChart Ω h i
  let cj := liftChart Ω h j
  let d : Torus (lattice Ω h) → (Fin g → ℂ) := fun q => cj q - ci q
  have hd : ContinuousAt d p :=
    (cj.continuousOn.continuousAt (cj.open_source.mem_nhds hp.2)).sub
      (ci.continuousOn.continuousAt (ci.open_source.mem_nhds hp.1))
  obtain ⟨ε, hε, hgap⟩ := exists_gap (lattice Ω h)
  have hnear : ∀ᶠ q in 𝓝 p, dist (d q) (d p) < ε :=
    hd.eventually (Metric.ball_mem_nhds _ hε)
  have heq : chartFactor Ω h i j =ᶠ[𝓝 p] fun q =>
      factor Ω (coordinatesOfPeriod Ω (d p)) (ci q) := by
    filter_upwards [hnear, (ci.open_source.inter cj.open_source).mem_nhds hp] with q hq hq'
    have hv : d q - d p ∈ lattice Ω h :=
      (lattice Ω h).sub_mem (chartDifference_mem Ω h hq'.1 hq'.2) (chartDifference_mem Ω h hp.1 hp.2)
    have hdq : d q = d p := sub_eq_zero.mp (hgap _ hv (by simpa [dist_eq_norm] using hq))
    change factor Ω (coordinatesOfPeriod Ω (d q)) (ci q) =
      factor Ω (coordinatesOfPeriod Ω (d p)) (ci q)
    rw [hdq]
  have hci : ContMDiffAt 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω ci p :=
    contMDiffOn_chart.contMDiffAt (ci.open_source.mem_nhds hp.1)
  have hf : ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, ℂ) ω
      (factor Ω (coordinatesOfPeriod Ω (d p))) :=
    contMDiff_iff_contDiff.mpr (contDiff_factor Ω _)
  exact (((hf (ci p)).comp p hci).congr_of_eventuallyEq heq).contMDiffWithinAt

private def chartLinearMap (i j p : Torus (lattice Ω h)) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.lsmul ℂ ℂ (chartFactor Ω h i j p)

private theorem contMDiffOn_chartLinearMap (i j : Torus (lattice Ω h)) :
    ContMDiffOn 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω (chartLinearMap Ω h i j)
      ((liftChart Ω h i).source ∩ (liftChart Ω h j).source) := by
  let mulMap : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ) := ContinuousLinearMap.lsmul ℂ ℂ
  have hmul : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω mulMap :=
    contMDiff_iff_contDiff.mpr mulMap.contDiff
  exact hmul.comp_contMDiffOn (contMDiffOn_chartFactor Ω h i j)

/-- The complex line bundle atlas on the Siegel torus. -/
def bundleCore : VectorBundleCore ℂ (Torus (lattice Ω h)) ℂ (Torus (lattice Ω h)) where
  baseSet i := (liftChart Ω h i).source
  isOpen_baseSet i := (liftChart Ω h i).open_source
  indexAt := id
  mem_baseSet_at p := mem_chart_source (Fin g → ℂ) p
  coordChange := chartLinearMap Ω h
  coordChange_self i p _ z := by
    change chartFactor Ω h i i p * z = z
    simp [chartFactor, coordinates_zero Ω h]
  continuousOn_coordChange i j := (contMDiffOn_chartLinearMap Ω h i j).continuousOn
  coordChange_comp i j k p hp z := by
    change chartFactor Ω h j k p * (chartFactor Ω h i j p * z) = chartFactor Ω h i k p * z
    rw [← mul_assoc, chartFactor_comp Ω h hp.1.1 hp.1.2 hp.2]

instance bundleCore_isContMDiff :
    (bundleCore Ω h).IsContMDiff 𝓘(ℂ, Fin g → ℂ) ω :=
  ⟨contMDiffOn_chartLinearMap Ω h⟩

/-- The theta section in the fibre coordinates of the bundle core. -/
def bundleThetaSection (p : Torus (lattice Ω h)) : (bundleCore Ω h).Fiber p :=
  riemannTheta Ω (liftChart Ω h p p)

/-- The section agrees with the one defined by the quotient. -/
theorem bundleThetaSection_eq_quotient (p : Torus (lattice Ω h)) :
    (fibreAtLift Ω h (liftChart Ω h p p) (bundleThetaSection Ω h p)).val =
      thetaSection Ω h p := by
  change thetaSection Ω h (proj (lattice Ω h) (liftChart Ω h p p)) = thetaSection Ω h p
  rw [proj_chartOf (lattice Ω h) (x := p.out) (mem_chart_source (Fin g → ℂ) p)]

/-- In every chart, the local expression of the section is the theta series at the chosen lift. -/
theorem localTriv_bundleThetaSection {i p : Torus (lattice Ω h)}
    (hi : p ∈ (bundleCore Ω h).baseSet i) :
    ((bundleCore Ω h).localTriv i ⟨p, bundleThetaSection Ω h p⟩).2 =
      riemannTheta Ω (liftChart Ω h i p) := by
  rw [VectorBundleCore.localTriv_apply]
  let u := liftChart Ω h p p
  let v := liftChart Ω h i p
  let a := coordinatesOfPeriod Ω (v - u)
  have hp : p ∈ (liftChart Ω h p).source := mem_chart_source (Fin g → ℂ) p
  have ha : periodShift Ω a = v - u := periodShift_coordinates Ω h (chartDifference_mem Ω h hp hi)
  have hv : u + periodShift Ω a = v := by rw [ha]; abel
  change factor Ω a u * riemannTheta Ω u = riemannTheta Ω v
  rw [← hv]
  exact (riemannTheta_add_period Ω h.1 u a.1 a.2).symm

/-- Holomorphicity of the theta series on the cover gives holomorphicity of the section. -/
theorem contMDiff_bundleThetaSection (hθ : ContDiff ℂ ω (riemannTheta Ω)) :
    ContMDiff 𝓘(ℂ, Fin g → ℂ) (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, ℂ)) ω
      (fun p => Bundle.TotalSpace.mk' ℂ p (bundleThetaSection Ω h p)) := by
  intro p
  let e := (bundleCore Ω h).localTriv p
  have hp : p ∈ e.baseSet := mem_chart_source (Fin g → ℂ) p
  refine (e.contMDiffAt_section_iff hp).mpr ?_
  have hc : ContMDiffAt 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω (liftChart Ω h p) p :=
    contMDiffOn_chart.contMDiffAt (e.open_baseSet.mem_nhds hp)
  have heq : (fun q => (e ⟨q, bundleThetaSection Ω h q⟩).2) =ᶠ[𝓝 p]
      fun q => riemannTheta Ω (liftChart Ω h p q) := by
    filter_upwards [e.open_baseSet.mem_nhds hp] with q hq
    exact localTriv_bundleThetaSection Ω h hq
  have ht : ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, ℂ) ω (riemannTheta Ω) :=
    contMDiff_iff_contDiff.mpr hθ
  exact ((ht (liftChart Ω h p p)).comp p hc).congr_of_eventuallyEq heq

end BPAnalytic.ThetaLine
