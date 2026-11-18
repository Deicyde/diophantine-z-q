import ZInQKernel.Contrib.OneProof.RC.Visibility.Inputs
import ZInQKernel.Contrib.OneProof.RC.Wiring.OddMinimum

/-!
# Lane RC23: the fixed visible witness from (O.2) and (O.7) (App F, tex 9391–9403; (3.7), tex 2460–2536)

"In particular, write `c_θ = 9 + ω(N)`, the valuation of the fixed integer `c₀ 2^{ω(N)}`. At the fixed
witness `D_w`, (O.2) and (O.7) imply `v₂ a_M(D_w) = c_θ + c_w` whenever `M > c_θ + c_w`. The phase is a
unit and the congruence error has strictly larger valuation, so this is an equality, not merely a lower
bound. Discarding the finitely many earlier stages is sufficient." (tex 9391–9400)

The wiring's leaf `WitnessLeaf W` (`RC/Wiring/OddMinimum.lean`: one admissible `D_w` whose coefficient
has one fixed valuation `c < M_θ` on a set of stages in the ultrafilter) is PROVED here from:
* (O.7) for `λ` (`Odd.ThetaComparison`, the same input as in `visibilityInputs_of_genuine`);
* (O.2) at the witness, read on `λ` (`WitnessValuation`: on a set of stages in the ultrafilter, `D_w` is
  admissible and `v₂ λ_θ(D_w) = c_w` exactly; ELLIOT + PRINT, `ex:app-detector`, tex 8225–8405: the
  cocycle value at `σ²` has `b`-value `2^{a+1}`, the specialization identifies it with `λ_M(\bar Q)`,
  tex 8392–8398, 8457–8460, and `(D_w/ℓ₀) = 1` keeps `D_w` in every stage's support, tex 2534–2536);
* the advancing stages (`M_θ → ∞` along the ultrafilter; the skeleton's `stages_advance`).
The arithmetic is lane RC12's `witness_vZ` (PROVED).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Visibility

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring Filter Topology

/-- **(O.2) at the fixed witness, read on `λ`** (ELLIOT + PRINT; tex 8225–8405, 2490–2493, 2534–2536):
on a set of stages in the ultrafilter, `D_w` is admissible and `λ_θ(D_w)` has 2-adic valuation exactly
`c_w`. -/
def WitnessValuation {ℓ : ℕ} (W : WData ℓ) (lam : ℕ → ℤ → ℤ) (Dw : ℤ) (cw : ℕ) : Prop :=
  ∀ᶠ θ in (W.stages : Filter ℕ), W.admissible θ Dw ∧ (2 : ℤ) ^ cw ∣ lam θ Dw ∧
    ¬ (2 : ℤ) ^ (cw + 1) ∣ lam θ Dw

/-- **PROVED (tex 9391–9400): the fixed visible witness** (`WitnessLeaf`, with `c = 9 + ω(N) + c_w`)
from (O.7), (O.2) at the witness and the advancing stages. -/
theorem witnessLeaf_of_O7 {ℓ : ℕ} (W : WData ℓ) (lam : ℕ → ℤ → ℤ) (ω : ℕ)
    (hO7 : Odd.ThetaComparison W.Mθ W.aθ lam W.admissible ω) {Dw : ℤ} {cw : ℕ}
    (hO2 : WitnessValuation W lam Dw cw) (hadv : Tendsto W.Mθ (W.stages : Filter ℕ) atTop) :
    WitnessLeaf W := by
  refine ⟨Dw, ((9 + ω + cw : ℕ) : ℤ), ?_⟩
  have hM : ∀ᶠ θ in (W.stages : Filter ℕ), 9 + ω + cw < W.Mθ θ :=
    hadv.eventually (eventually_gt_atTop _)
  filter_upwards [hO2, hM] with θ hθ hMθ
  obtain ⟨hadm, h1, h2⟩ := hθ
  obtain ⟨ζ, hζ, hcong⟩ := hO7 θ Dw hadm
  refine ⟨hadm, ?_, ?_⟩
  · rw [← odd_vZ_eq]
    exact Odd.witness_vZ ω (W.Mθ θ) cw hζ h1 h2 hcong hMθ
  · have : ((9 + ω + cw : ℕ) : ℤ) < ((W.Mθ θ : ℕ) : ℤ) := by exact_mod_cast hMθ
    exact_mod_cast this

/-- **PROVED: the fixed visible witness over the genuine genus points** — `witnessLeaf_of_O7` with
`λ = lamOf` (the stage maps applied to `L` times the genus points of the selected data). -/
theorem witnessLeaf_of_genuine {ℓ : ℕ} (W : WData ℓ)
    {E : WeierstrassCurve ℚ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (ZInQ.Contrib.CloudB3RC53.CST.newformLevel E) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {hstar : ℤ} {L : ℕ}
    (selG : (h : ℤ) → Option (ZInQ.Contrib.CloudB3RC53.GenusOdd.HeegnerDatum E f Lat κ
      (h * hstar) 1 hstar))
    (ev : StageKummer E f Lat κ hstar W.Mθ) (ω : ℕ)
    (hO7 : Odd.ThetaComparison W.Mθ W.aθ (lamOf W.Mθ L selG ev) W.admissible ω) {Dw : ℤ} {cw : ℕ}
    (hO2 : WitnessValuation W (lamOf W.Mθ L selG ev) Dw cw)
    (hadv : Tendsto W.Mθ (W.stages : Filter ℕ) atTop) :
    WitnessLeaf W :=
  witnessLeaf_of_O7 W _ ω hO7 hO2 hadv

end ZInQ.Manuscript.RC.Visibility
