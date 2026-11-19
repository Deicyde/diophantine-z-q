import ZInQKernel.Contrib.OneProof.RC.Wiring.GenusOdd34
import ZInQKernel.Contrib.OneProof.RC.Visibility.Models

/-!
# Theorem 5.3, Lane RC0: the odd side's genuine objects — (3.4), (O.8) and the fixed witness

`OddModels W` extends GenusOdd's instance of the genuine objects of (3.4) (`GenusOddInstance`:
the newform data of `E`, the Heegner selections, RC11's normalization of `L_*`, …) with the inputs
of lane RC23's visibility models at the **same** objects (the genus selection that defines `j_gen`
also defines `λ_θ(D) = lamOf`, tex 2512–2530, 9112–9113):

* `L`, `hL`: a fixed multiplier killing the torsion of every native lattice (ELLIOT + PRINT
  Silverman AEC VII.3.1; tex 8261–8263, 8295–8297; owner RC23);
* `ev`: the stage maps `x ↦ λ_{M_θ}(x̄)` (interface; tex 8378–8398, 8439–8456, 9283–9290; owner RC23);
* `hsign`: admissible parameters have odd sign (GLUE: the twist root-number formula; tex 9417,
  8209–8212, 8587–8588; owner RC23);
* `ω`, `O`, `T`, `hcore`: the theta side of (O.7) (`ThetaSide`, ELLIOT: the theta-form
  construction, tex 8418) and the comparison argument at every admissible `(θ, D)` (`ComparisonCore`,
  ELLIOT + PRINT Cornut–Jetchev, tex 9120–9370); owner RC23 and the theta-form construction of
  App F.

`OddInstance W` adds (O.2) at the fixed witness:

* `Dw`, `cw`, `hO2`: (O.2) at the fixed witness, read on `λ` (ELLIOT + PRINT; tex 8225–8405,
  2490–2493, 2534–2536; owner RC23).

Lane RC0's leaves no longer ask for `OddInstance` itself: they ask for `OddStagedInstance`
(`RC/Wiring/StageData.lean`), the same models with the stage data built by the Appendix F stage
construction and the specialization identity at the witness, from which `OddInstance` is PROVED
(`OddStagedInstance.toOddInstance`).

PROVED from `OddInstance`: `visibilityInputs_of_oddInstance` (RC23's `visibilityInputs_of_models`;
admissible parameters are prepared by the data specification and the instance) and
`witnessLeaf_of_oddInstance` (RC23's `witnessLeaf_of_models`).

Conclusion-shaped part: the point side is genuine (`λ = lamOf`, the stage map of `L` times the
genuine genus point, with the same selection as (3.4)), but the theta side `T` and the comparison
argument `hcore` exist for every integer `λ` and every `a_θ ≡ c₀ λ (mod 2^{M_θ})` on the admissible
set, so together they are (O.7)
itself, an ELLIOT leaf; `a_θ` is pinned only modulo `2^{M_θ}` on the admissible set. NOTE: `hO2`
needs `D_w` admissible in the final data's filter, so `k` must avoid the primes of `D_w` (the text,
tex 2596–2598, does not say so explicitly).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd Filter Topology

/-- **The odd side's genuine models** (tex 2403–2546, 8209–9445): GenusOdd's instance of (3.4)
together with lane RC23's visibility models at the same genus selection (see the module
docstring for the fields, with tex lines, kinds and owners). -/
structure OddModels {ℓ : ℕ} (W : WData ℓ) : Type 1 extends GenusOddInstance W where
  /-- the fixed multiplier -/
  L : ℕ
  /-- it kills the torsion of every native lattice -/
  hL : Visibility.MultiplierKillsNativeTorsion (Ecurve ℓ) f Lat κ W.hstar L
  /-- the stage maps -/
  ev : Visibility.StageKummer (Ecurve ℓ) f Lat κ W.hstar W.Mθ
  /-- admissible parameters have odd sign -/
  hsign : Visibility.AdmissibleOddSign W.toRCData
  /-- `ω(N)` -/
  ω : ℕ
  /-- the coefficient ring of the theta side -/
  O : Type
  [ringO : CommRing O]
  /-- the theta side of (O.7) -/
  T : Visibility.ThetaSide W.toRCData O
  /-- the comparison argument at every admissible `(θ, D)` -/
  hcore : ∀ θ Dd, W.admissible θ Dd →
    Visibility.ComparisonCore (T.S θ) (W.Mθ θ) (-W.hstar) Dd ω
      (Visibility.lamOf W.Mθ L selG ev θ Dd) (T.ζ θ Dd)

attribute [instance] OddModels.ringO

/-- **The odd side's genuine objects** (tex 2403–2546, 8209–9445): the models `OddModels` and (O.2)
at the fixed witness, read on `λ` (see the module docstring). -/
structure OddInstance {ℓ : ℕ} (W : WData ℓ) : Type 1 extends OddModels W where
  /-- the fixed witness -/
  Dw : ℤ
  /-- its valuation -/
  cw : ℕ
  /-- (O.2) at the witness, read on `λ` -/
  hO2 : Visibility.WitnessValuation W (Visibility.lamOf W.Mθ L selG ev) Dw cw

/-- **(O.8)'s inputs from the odd instance** (PROVED: lane RC23's `visibilityInputs_of_models`;
admissible parameters are prepared, `PreparedGlue`, and prepared parameters are GenusOdd's,
`GenusOddInstance.hprep`; `j_gen` is the selection's, `GenusOddInstance.hjg`). -/
theorem visibilityInputs_of_oddInstance {ℓ : ℕ} {W : WData ℓ} (P : Prints)
    (hArtin : ArtinFactorization) (I : OddInstance W) (hglue : PreparedGlue W) :
    VisibilityInputs W.toRCData := by
  have := I.hE
  exact Visibility.visibilityInputs_of_models W.toRCData P hArtin I.hf I.hLat I.hNC I.hκ I.hgp
    I.selG (fun _ Dd _ => congrFun I.hjg Dd) I.hL I.ev
    (fun θ Dd hD => I.hprep Dd (hglue θ Dd hD)) I.hsign I.ω I.T I.hcore

/-- **The fixed visible witness from the odd instance** (PROVED: lane RC23's
`witnessLeaf_of_models`, with the advancing stages). -/
theorem witnessLeaf_of_oddInstance {ℓ : ℕ} {W : WData ℓ} (I : OddInstance W)
    (hadv : Tendsto W.Mθ (W.stages : Filter ℕ) atTop) : WitnessLeaf W :=
  Visibility.witnessLeaf_of_models W I.selG I.ev I.ω I.T I.hcore I.hO2 hadv

end ZInQ.Manuscript.RC.Wiring
