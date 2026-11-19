import ZInQKernel.Contrib.RC53Assist.CalibrationModel.IntegralReplacement
import ZInQKernel.Contrib.RC53Assist.CalibrationShape.CalibrationDischarge
import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.ArithmeticCentralDuality

/-!
# Theorem 5.3, Lane RC0 round 18: the calibration leaf with its duality input from the literature

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141), its Kummer
coordinate (tex 3877–3909, 4005–4018, 4050–4064). The current leaf `CalibrationInputsH`
(`Wiring/CalibrationLeaf3.lean`) carries the Kummer valuation `hK` as a bare equation. The RC53
group's `CalibrationModelHK2` (`RC53Assist/Calibration/KummerIntegral.lean`) derives `hK` from a
Kummer block `KummerCoordinateBlockG`, whose order tie `DiskTie` (the integral central disks
compute the orders of the genuine finite-level Kummer Selmer cohomology) is GLUE. This file
derives that tie from nine cited book statements, through the RC53 group's integral central
model (`diskTie_of_finite_cohomology`, with the canonical reductions proved) and the integral
central Kummer duality `integralCentralKummerDuality_of_literature_with_finiteness`.

* `CalibrationBookProps`: the nine book statements, each a Lean proposition with its source
  (PRINT; no inhabitant is supplied):
  Milne, *Arithmetic Duality Theorems*, 2nd ed., I.3.4 (with 3.2, 3.5), I.2.3 (twice: the finite
  local duality and its higher-degree part), I.2.1 (last sentence), I.4.15, I.4.10(c) and I.2.3
  (cohomological dimension two); Nekovář, *Selmer complexes*, 5.4.1 and 5.4.3(ii).
* `DiskTie.of_valuation_eq`: an order tie depends only on the valuations of the three disks.
* `calibrationShape_of_literature`, `diskTie_of_literature`: for any genuine Kummer data `G` over a
  totally complex `K` with the places above `2` in the support, finite `2`-primary torsion of the
  central twist and integral central first cohomology of rank one, the calibration shape and the
  order tie of the constructed integral disks follow from the nine statements. This is the RC53
  group's `calibrationShape_of_arithmetic` with the rank one as an input in place of its curve
  binding, cochain comparison and Selmer corank (which bind the central twist to `E_ℓ'` with
  `ℓ' : ℕ`, available at an address exactly when `h_x > 0`).
* `KummerCoordinateBlockLit`, `CalibrationModelLit`: `KummerCoordinateBlockG` and
  `CalibrationModelHK2` with the order tie replaced by the inputs of the literature route and the
  identification of the three disk lengths with those of the constructed integral disks.
* `CalibrationInputsLit D`: the nine statements and, at every address, a `CalibrationModelLit`.
  PROVED: `CalibrationInputsLit.toHK2`, `CalibrationInputsLit.toH`, `calibrationTarget_of_Lit`;
  `CalibrationModelLit.ofHK2`, `nonempty_modelLit_iff` and `calibrationInputsLit_iff` (a
  `CalibrationModelLit` is exactly a `CalibrationModelHK2` with the named inputs for its Kummer
  data, the tie being derived);
  `calibrationInputsLit_of_noAddress` (non-vacuity in the degenerate case).

**The human-review boundary.**
* H1, the faithfulness of the nine formulations: each Lean proposition is meant to state the
  cited printed result for the objects named (finite discrete modules, elliptic curves over local
  fields, finite free two-adic coefficients); the quotations and page locators are in the
  docstrings of the definitions (`MilneLocalDualityPrint`, `MilneFiniteLocalDualityPrint`,
  `MilneFiniteDegreeBoundPrint`, `MilneLocalFiniteness`, `MilneGlobalFiniteness`,
  `MilneGlobalDimensionTwo`, `MilneLocalDimensionTwo`, `NekovarIntegralCompactLocality`,
  `NekovarIntegralGlobalDuality`). That they say what the books say is a human check.
* H2, the supporting definitions: continuous cochains, the compact Kummer complex of the central
  twist (`compactCentralComplex`, `tateKummerSelData`), the twist model `twistK`, the Kummer
  local conditions, the finite-level Kummer Selmer data `centralKummerSelData`, the retained
  integral model and its dual (`centralRetainedGCx`, `dualCx`): that they formalize the objects of
  the printed statements and of the manuscript is a human check.
* H3, the paper-level claim: that the remaining inputs of the leaf (the Knudsen–Mumford
  identification, the coordinate transfer, the free coefficients, the arithmetic orders, the
  rank one, the disk-length identification and the non-Kummer fields of the calibration) are what
  the manuscript supplies for Proposition `ex:arith-central-calibration` is a reading of the paper.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.Calibration
open WeierstrassCurve WeierstrassCurve.Affine Matrix CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Height (IsFreeGenerator QuadData)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData DiskTie DiskArith cycOrder cycOrder_eq
  KummerCoordinateBlockG CalibrationModelHK2 CalibrationInputsHK2 calibrationTarget_of_HK2)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (centralCurve compactCentralComplex)
open ZInQ.Contrib.RC53Assist.CalibrationModel (CalibrationCohomologyShape centralDiskMatrix
  centralDiskMatrix_det_ne_zero diskTie_of_finite_cohomology)
open ZInQ.Contrib.RC53Assist.CalibrationShape (IntegralCentralKummerDuality
  integralCentralDuality_ranks compactCentral_outside cohomology_finrank_degree_congr
  canonicalCentralReductionMap_quasiIso)
open ZInQ.Contrib.RC53Assist.DKLocalAdapter
  (integralCentralKummerDuality_of_literature_with_finiteness)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps

attribute [local instance] Nat.fact_prime_two

/-! **The nine book statements** -/

/-- **The nine cited book statements of the integral central Kummer duality** (PRINT; tex
3413–3498, 4005–4018, 4385–4451). Each field is a Lean proposition whose docstring at its
definition quotes the printed statement; none is given an inhabitant here (the human-review
boundary H1 of the module docstring). Kind: definition (PRINT inputs). -/
structure CalibrationBookProps : Prop where
  /-- PRINT, Milne, *Arithmetic Duality Theorems*, 2nd ed., I.3.4 (p. 43), with the diagram of
  the proof of I.3.2 (p. 42) and I.3.5 (p. 44): local Tate duality for an elliptic curve over a
  local field of characteristic zero, compatible with the Weil-cup pairings. -/
  milneLocalDuality : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneLocalDualityPrint
  /-- PRINT, Milne, I.2.3 (p. 28): finite local duality for `B[n]`, the degree-one perfect
  pairing and the degree-two isomorphism. -/
  milneFiniteLocalDuality : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneFiniteLocalDualityPrint
  /-- PRINT, Milne, I.2.3 (p. 28), its finite higher-degree part, for the two coefficient
  families used. -/
  milneFiniteDegreeBound :
    ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint
  /-- PRINT, Milne, I.2.1, last sentence (p. 27; the manuscript cites I.2.3): finiteness of local
  cohomology of finite discrete modules. -/
  milneLocalFiniteness : ZInQ.Contrib.RC53Assist.InnerLimitArith.MilneLocalFiniteness
  /-- PRINT, Milne, I.4.15 (p. 62; the manuscript cites I.4.10): finiteness of `H^n(G_{K,S}, M)`
  for finite discrete `M`. -/
  milneGlobalFiniteness : ZInQ.Contrib.RC53Assist.InnerLimitArith.MilneGlobalFiniteness
  /-- PRINT, Milne, I.4.10(c) (p. 57), without real places: no global cohomology above degree
  two. -/
  milneGlobalDimensionTwo : ZInQ.Contrib.RC53Assist.CalibrationShape.MilneGlobalDimensionTwo
  /-- PRINT, Milne, I.2.3 (p. 28): no local cohomology above degree two. -/
  milneLocalDimensionTwo : ZInQ.Contrib.RC53Assist.CalibrationShape.MilneLocalDimensionTwo
  /-- PRINT, Nekovář, *Selmer complexes*, 5.4.1: the top cohomology of the compact cochains with
  general coefficients and its finite-place localization. -/
  nekovarCompactLocality : ZInQ.Contrib.RC53Assist.IntegralDuality.NekovarIntegralCompactLocality
  /-- PRINT, Nekovář, *Selmer complexes*, 5.4.3(ii) (p. 127), global form over `ℤ₂`: the traced
  global cup adjoint is a quasi-isomorphism on bounded finite free models. -/
  nekovarGlobalDuality : ZInQ.Contrib.RC53Assist.IntegralDuality.NekovarIntegralGlobalDuality

/-! **The order tie from the literature** -/

section Tie

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- Two disks with the same valuation have the same orders at large precision (tex 4005–4018).
Kind: PROVED. -/
theorem cycOrder_congr {i : ℕ} (hi : i ≠ 0) {x y : ℤ_[2]} (hx : x ≠ 0) (hy : y ≠ 0)
    (hv : x.valuation = y.valuation) (hxi : x.valuation ≤ i) : cycOrder i x = cycOrder i y := by
  rw [cycOrder_eq hi hx hxi, cycOrder_eq hi hy (hv ▸ hxi), hv]

/-- **An order tie depends only on the valuations of the three disks** (tex 4005–4018).
Kind: PROVED. -/
theorem DiskTie.of_valuation_eq {G : GenuineKummerData K E₀ hZ} {x₁ x₂ x₃ y₁ y₂ y₃ : ℤ_[2]}
    (T : DiskTie G y₁ y₂ y₃) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₃ : x₃ ≠ 0) (hy₁ : y₁ ≠ 0)
    (hy₂ : y₂ ≠ 0) (hy₃ : y₃ ≠ 0) (h₁ : x₁.valuation = y₁.valuation)
    (h₂ : x₂.valuation = y₂.valuation) (h₃ : x₃.valuation = y₃.valuation) :
    DiskTie G x₁ x₂ x₃ where
  tie0 := by
    obtain ⟨i₀, h⟩ := T.tie0
    refine ⟨max i₀ (x₁.valuation + 1), fun i hi => ?_⟩
    rw [h i (le_of_max_le_left hi),
      cycOrder_congr (by omega) hy₁ hx₁ h₁.symm (by have := le_of_max_le_right hi; omega)]
  tie2 := by
    obtain ⟨i₀, h⟩ := T.tie2
    refine ⟨max i₀ (max x₂.valuation x₃.valuation + 1), fun i hi => ?_⟩
    have hi' := le_of_max_le_right hi
    rw [h i (le_of_max_le_left hi),
      cycOrder_congr (by omega) hy₂ hx₂ h₂.symm (by omega),
      cycOrder_congr (by omega) hy₃ hx₃ h₃.symm (by omega)]
  tie3 := by
    obtain ⟨i₀, h⟩ := T.tie3
    refine ⟨max i₀ (x₃.valuation + 1), fun i hi => ?_⟩
    rw [h i (le_of_max_le_left hi),
      cycOrder_congr (by omega) hy₃ hx₃ h₃.symm (by have := le_of_max_le_right hi; omega)]

/-- **The calibration shape from the literature** (tex 4005–4018): for genuine Kummer data `G`
over a totally complex `K` whose support contains the places above `2`, with finite `2`-primary
torsion of the central twist and integral central first cohomology of rank one, the compact
central complex has cohomology in degrees one to three with ranks `1, 1, 0`. The amplitude comes
from the finiteness and dimension statements (`compactCentral_outside`), the ranks in degrees two
and three from the integral duality of the nine statements (`integralCentralDuality_ranks`). As
the RC53 group's `calibrationShape_of_arithmetic`, with the rank one as an input.
Kind: PROVED. -/
theorem calibrationShape_of_literature (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (B : CalibrationBookProps) (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    [hpt : Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)]
    (hrank : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1) :
    CalibrationCohomologyShape (compactCentralComplex G) := by
  have hdual : IntegralCentralKummerDuality G hfinite :=
    integralCentralKummerDuality_of_literature_with_finiteness G hfinite B.milneLocalDuality
      B.milneFiniteLocalDuality B.milneFiniteDegreeBound B.nekovarCompactLocality
      B.nekovarGlobalDuality B.milneGlobalFiniteness B.milneLocalFiniteness
      B.milneGlobalDimensionTwo B.milneLocalDimensionTwo hK h2
  have hout : ∀ n : ℤ, n < 1 ∨ 3 < n → Subsingleton ((compactCentralComplex G).homology n) :=
    @compactCentral_outside K _ _ E₀ hZ G B.milneLocalFiniteness B.milneGlobalFiniteness
      B.milneLocalDimensionTwo B.milneGlobalDimensionTwo hK h2 hpt
  refine ⟨hout, hrank, ?_, ?_⟩
  · exact ((integralCentralDuality_ranks G hfinite hdual 2).trans
      (cohomology_finrank_degree_congr (compactCentralComplex G) (by decide))).trans hrank
  · have h : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 3) =
        Module.finrank ℤ_[2] ((compactCentralComplex G).homology 0) :=
      (integralCentralDuality_ranks G hfinite hdual 3).trans
        (cohomology_finrank_degree_congr (compactCentralComplex G) (by decide))
    have : Subsingleton ((compactCentralComplex G).homology 0) := hout 0 (by omega)
    exact h.trans Module.finrank_zero_of_subsingleton

/-- **The order tie of the constructed integral disks from the literature** (tex 3429–3431,
4005–4018): the RC53 group's `diskTie_of_finite_cohomology` at the calibration shape of
`calibrationShape_of_literature`, with the canonical reductions proved
(`canonicalCentralReductionMap_quasiIso`). Kind: PROVED. -/
theorem diskTie_of_literature (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (B : CalibrationBookProps) (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    [Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)]
    (hrank : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1) :
    DiskTie G (centralDiskMatrix G hfinite 1).det (centralDiskMatrix G hfinite 2).det
      (centralDiskMatrix G hfinite 3).det :=
  diskTie_of_finite_cohomology G hfinite (calibrationShape_of_literature G hfinite B hK h2 hrank)
    (fun i _ => canonicalCentralReductionMap_quasiIso G i)

end Tie

/-! **The Kummer block and the calibration model with the literature route** -/

section Block

/-- **The Kummer block with the order tie from the literature route** (tex 3877–3909, 4005–4018,
4050–4064): the fields of the RC53 group's `KummerCoordinateBlockG` except the order tie `tie`,
and in its place the inputs of `diskTie_of_literature` for the address's genuine data `G` (finite
generation, the places above `2`, no real places, finite `2`-primary torsion of the central twist,
rank one of the integral central first cohomology) and the identification of the lengths of the
three disks of the Knudsen–Mumford identification with those of the constructed integral disks
(GLUE). Kind: definition (inputs). -/
structure KummerCoordinateBlockLit (K : Type) [Field K] [NumberField K] (E₀ : WeierstrassCurve ℚ)
    (hZ : ℤ) {n : ℕ} (DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2]))
    (zK wK : Fin n → PowerSeries ℚ_[2]) (j vL m : ℤ) (tA shaA : ℕ) : Type 1 where
  /-- the finite set of places of the Selmer complex over `ℚ₂[[t]]` -/
  S : Set (HeightOneSpectrum (𝓞 K))
  /-- it is finite -/
  hSfin : S.Finite
  /-- the coefficient module over `ℚ₂[[t]]` -/
  M : Type
  [addM : AddCommGroup M]
  [modM : Module (PowerSeries ℚ_[2]) M]
  [actM : DistribMulAction (GKS K S) M]
  [commM : SMulCommClass (GKS K S) (PowerSeries ℚ_[2]) M]
  [topM : TopologicalSpace M]
  [caddM : ContinuousAdd M]
  [cconstM : ContinuousConstSMul (PowerSeries ℚ_[2]) M]
  [csmulM : ContinuousSMul (GKS K S) M]
  /-- the local conditions over `ℚ₂[[t]]` -/
  Δ : GaloisLocalConditions K S (PowerSeries ℚ_[2]) M
  /-- they are subcomplexes of the local cochains -/
  hinj : ∀ v (k : ℤ), Function.Injective ((Δ.i v).f k k rfl)
  /-- the Knudsen–Mumford identification over `ℚ₂[[t]]` -/
  I : GenuineKummerModelIdentification K S (PowerSeries ℚ_[2]) M Δ
  /-- the coordinate transfer to the leaf's two-term model -/
  link : Central.IsClassFunctionalCoord DK zK wK I.coord
  /-- the free coefficient of the point in the class -/
  aP : PowerSeries ℚ_[2]
  /-- the free coefficient of the point in the functional -/
  bP : PowerSeries ℚ_[2]
  /-- the class coefficient is `m · a_P` -/
  ha : I.a = PowerSeries.C (m : ℚ_[2]) * aP
  /-- the functional coefficient is `m · b_P` -/
  hb : I.b = PowerSeries.C (m : ℚ_[2]) * bP
  /-- `v₂ a_P(0) = j_rc + v₂L` -/
  haP : v2 (central aP) = ((j + vL : ℤ) : WithTop ℤ)
  /-- `v₂ b_P(0) = j_rc + v₂L` -/
  hbP : v2 (central bP) = ((j + vL : ℤ) : WithTop ℤ)
  /-- the core coordinate is a unit at the centre -/
  hu₀ : v2 (central I.u₀) = 0
  /-- the genuine data of the address -/
  G : GenuineKummerData K E₀ hZ
  /-- the central value of the degree-one disk -/
  x₁ : ℤ_[2]
  /-- the central value of the degree-two disk -/
  x₂ : ℤ_[2]
  /-- the central value of the degree-three disk -/
  x₃ : ℤ_[2]
  /-- the degree-one disk is integral at the centre -/
  hx₁ : central (I.δ₁ : PowerSeries ℚ_[2]) = x₁
  /-- the degree-two disk is integral at the centre -/
  hx₂ : central (I.δ₂ : PowerSeries ℚ_[2]) = x₂
  /-- the degree-three disk is integral at the centre -/
  hx₃ : central (I.δ₃ : PowerSeries ℚ_[2]) = x₃
  /-- the genuine orders are those of the actual torsion and `Ш` -/
  arith : DiskArith G tA shaA
  /-- finite generation of the integral compact central cohomology (it follows from the two
  finiteness prints, `centralCohomologyFinite`; a proposition, so its proof is irrelevant) -/
  hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n)
  /-- the support contains the places above `2` -/
  h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S
  /-- `K` has no real places -/
  hK : IsTotallyComplex K
  /-- the `2`-primary torsion of the central twist over `K` is finite (for any decidable equality
  on `K`, on which the group law depends only through its proofs) -/
  finite2 : ∀ [DecidableEq K],
    Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)
  /-- the integral central first cohomology has rank one (`s₂(E^{(h)}/K) = 1`) -/
  rank_one : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1
  /-- the degree-one disk has the length of the constructed integral disk -/
  hval₁ : x₁.valuation = (centralDiskMatrix G hfinite 1).det.valuation
  /-- the degree-two disk has the length of the constructed integral disk -/
  hval₂ : x₂.valuation = (centralDiskMatrix G hfinite 2).det.valuation
  /-- the degree-three disk has the length of the constructed integral disk -/
  hval₃ : x₃.valuation = (centralDiskMatrix G hfinite 3).det.valuation

attribute [instance] KummerCoordinateBlockLit.addM KummerCoordinateBlockLit.modM
  KummerCoordinateBlockLit.actM KummerCoordinateBlockLit.commM KummerCoordinateBlockLit.topM
  KummerCoordinateBlockLit.caddM KummerCoordinateBlockLit.cconstM KummerCoordinateBlockLit.csmulM

namespace KummerCoordinateBlockLit

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {n : ℕ}
  {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
  {j vL m : ℤ} {tA shaA : ℕ}

/-- **The order tie of the block, from the nine book statements** (tex 3429–3431, 4005–4018):
`diskTie_of_literature` for the constructed disks, transferred to the block's disks through the
length identification (`DiskTie.of_valuation_eq`). Kind: PROVED. -/
theorem tie (L : KummerCoordinateBlockLit K E₀ hZ DK zK wK j vL m tA shaA)
    (B : CalibrationBookProps) : DiskTie L.G L.x₁ L.x₂ L.x₃ := by
  classical
  have := L.finite2
  exact DiskTie.of_valuation_eq (diskTie_of_literature L.G L.hfinite B L.hK L.h2 L.rank_one)
    (ZInQ.Contrib.RC53Assist.Calibration.CentralDiskOrders.x_ne_zero L.hx₁)
    (ZInQ.Contrib.RC53Assist.Calibration.CentralDiskOrders.x_ne_zero L.hx₂)
    (ZInQ.Contrib.RC53Assist.Calibration.CentralDiskOrders.x_ne_zero L.hx₃)
    (centralDiskMatrix_det_ne_zero L.G L.hfinite 1) (centralDiskMatrix_det_ne_zero L.G L.hfinite 2)
    (centralDiskMatrix_det_ne_zero L.G L.hfinite 3) L.hval₁ L.hval₂ L.hval₃

/-- **The RC53 group's Kummer block from the literature block** (its order tie by `tie`).
Kind: definition. -/
def toG (L : KummerCoordinateBlockLit K E₀ hZ DK zK wK j vL m tA shaA)
    (B : CalibrationBookProps) : KummerCoordinateBlockG K E₀ hZ DK zK wK j vL m tA shaA :=
  { L with tie := L.tie B }

end KummerCoordinateBlockLit

/-- **The literature block from the RC53 group's block and the named inputs** (the order tie is
dropped). Kind: definition. -/
def KummerCoordinateBlockLit.ofG {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ}
    {hZ : ℤ} {n : ℕ} {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])}
    {zK wK : Fin n → PowerSeries ℚ_[2]} {j vL m : ℤ} {tA shaA : ℕ}
    (L : KummerCoordinateBlockG K E₀ hZ DK zK wK j vL m tA shaA)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex L.G).homology n))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ L.G.S)
    (hK : IsTotallyComplex K)
    (finite2 : ∀ [DecidableEq K],
      Finite (AddCommGroup.primaryComponent (centralCurve L.G).toAffine.Point 2))
    (rank_one : Module.finrank ℤ_[2] ((compactCentralComplex L.G).homology 1) = 1)
    (hval₁ : L.x₁.valuation = (centralDiskMatrix L.G hfinite 1).det.valuation)
    (hval₂ : L.x₂.valuation = (centralDiskMatrix L.G hfinite 2).det.valuation)
    (hval₃ : L.x₃.valuation = (centralDiskMatrix L.G hfinite 3).det.valuation) :
    KummerCoordinateBlockLit K E₀ hZ DK zK wK j vL m tA shaA :=
  { L with
    hfinite := hfinite
    h2 := h2
    hK := hK
    finite2 := finite2
    rank_one := rank_one
    hval₁ := hval₁
    hval₂ := hval₂
    hval₃ := hval₃ }

end Block

/-! **The calibration model and the leaf** -/

section Leaf

/-- **The inputs of (4.6) at one address, with the Kummer order tie from the literature**
(tex 3987–4141): every field of the RC53 group's `CalibrationModelHK2`, with the same names and
types, except that its Kummer block is a `KummerCoordinateBlockLit` (the order tie replaced by the
inputs of the literature route and the disk-length identification). Kind: definition (inputs). -/
structure CalibrationModelLit {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
    (x : Addr Fam.b) : Type 1 where
  /-- `|Ш(𝒜)[2^∞]|` -/
  shaA : ℕ
  /-- `|Ш(ℬ)[2^∞]|` -/
  shaB : ℕ
  /-- `|𝒜(ℚ)_tors[2^∞]|` -/
  tA : ℕ
  /-- `|ℬ(ℚ)_tors[2^∞]|` -/
  tB : ℕ
  /-- finiteness of `Ш(𝒜)` -/
  shaA_ne : shaA ≠ 0
  /-- finiteness of `Ш(ℬ)` -/
  shaB_ne : shaB ≠ 0
  /-- `𝒜` has torsion -/
  tA_ne : tA ≠ 0
  /-- `ℬ` has torsion -/
  tB_ne : tB ≠ 0
  /-- the finite set of primes carrying the component numbers -/
  Scomp : Finset ℕ
  /-- the component numbers of `𝒜` -/
  cA : ℕ → ℕ
  /-- the component numbers of `ℬ` -/
  cB : ℕ → ℕ
  /-- the companion primes are among them -/
  hTS : D.kfin.natAbs.primeFactors ⊆ Scomp
  /-- component numbers are positive -/
  hcpos : ∀ p ∈ Scomp, 0 < cA p
  /-- cancellation away from the companion primes -/
  hcancel : ∀ p ∈ Scomp, p ∉ D.kfin.natAbs.primeFactors → cA p = cB p
  /-- the Weil restriction has connected special fiber at a companion prime -/
  hA1 : ∀ p ∈ D.kfin.natAbs.primeFactors, cA p = 1
  /-- the companion primes are odd -/
  hodd : ∀ p ∈ D.kfin.natAbs.primeFactors, p ≠ 2
  /-- the companion primes exactly divide `k` -/
  hram : ∀ p ∈ D.kfin.natAbs.primeFactors, ¬ ((p : ℤ) ^ 2 ∣ D.kfin)
  /-- `E₀ = E^{(h_x)}` has good reduction at each companion prime (a good integral model up to
  isomorphism) -/
  goodModel : ∀ p ∈ D.kfin.natAbs.primeFactors, GoodModelIso (qtwist (Ecurve ℓ) (Fam.h x : ℚ)) p
  /-- **PRINT (Edixhoven, Thm 5.3 and Rem 5.4.1) as GLUE**, model-free form -/
  hEdix : EdixhovenComponentNumberIso ℓ (Fam.h x : ℚ) D.kfin cB
  /-- the field `K = ℚ(√k)` -/
  K : Type
  [fieldK : Field K]
  [nfK : NumberField K]
  [decK : DecidableEq K]
  [quadK : Algebra.IsQuadraticExtension ℚ K]
  /-- `√k ∈ K` and the nontrivial automorphism `√k ↦ −√k` -/
  quad : QuadData K (D.kfin : ℚ)
  /-- `φ^*ω_ℬ = a ω_𝒜` -/
  aPull : ℤ
  /-- `ψ^*ω_𝒜 = b ω_ℬ` -/
  bPull : ℤ
  /-- `ab = 4` -/
  hab : aPull * bPull = 4
  /-- `|coker φ_ℝ|` -/
  gam : ℕ
  /-- `|ker φ_ℝ|` -/
  kap : ℕ
  /-- both at most four -/
  hgam : 1 ≤ gam ∧ gam ≤ 4
  /-- both at most four -/
  hkap : 1 ≤ kap ∧ kap ≤ 4
  /-- the Néron period of `𝒜` -/
  OmA : ℝ
  /-- nonzero period -/
  hOmA : OmA ≠ 0
  /-- the rational period ratio `Ω_ℬ/Ω_𝒜` -/
  rhoOm : ℚ
  /-- the real change of variables -/
  hcv : (|aPull| : ℝ) * OmA = ((kap : ℝ) / gam) * ((rhoOm : ℝ) * OmA)
  /-- Cassels' isogeny invariance in Milne's form, with the canonical regulators of any free
  generators of the two rank-one lattices -/
  hmilne : ∀ (gA : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange K).toAffine.Point)
    (gB : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange ℚ).toAffine.Point ×
      ((qtwist (Ecurve ℓ) ((Fam.h x : ℚ) * (D.kfin : ℚ))).baseChange ℚ).toAffine.Point),
    IsFreeGenerator gA → IsFreeGenerator gB →
    Central.MilneIsogenyInvariance shaA shaB tA tA tB tB
      (∏ p ∈ Scomp, cA p) (∏ p ∈ Scomp, cB p) gA.canonicalHeight
      (ZInQ.Manuscript.RC.Height.heightB (Ecurve ℓ) (Fam.h x : ℚ) (D.kfin : ℚ) gB) OmA
      ((rhoOm : ℝ) * OmA)
  /-- `s_ℬ = s(h_x) + s(h_x k)` -/
  hsB : ((padicValNat 2 shaB : ℕ) : ℤ) =
    (shaLength (Etw ℓ (Fam.h x)) : ℤ) + (shaLength (Etw ℓ (Fam.h x * D.kfin)) : ℤ)
  /-- the rational torsion of `ℬ` is bounded by `G₀` -/
  hgB : ((padicValNat 2 tB : ℕ) : ℤ) ≤ G₀
  /-- the moving prime `r_i` -/
  rmov : ℕ
  /-- its trace `a_{r_i}` -/
  amov : ℤ
  /-- the quadratic sign `χ_h(r_i)` -/
  chimov : ℤ
  /-- the moving exponent `B_i` -/
  Bexp : ℕ
  /-- the constant `c_E` of the Tate image -/
  cE : ℕ
  /-- `χ = ±1` -/
  hchi : chimov = 1 ∨ chimov = -1
  /-- `r_i ≡ 1 (mod 2^{B_i})` -/
  hrmov : (2 : ℤ) ^ Bexp ∣ (rmov : ℤ) - 1
  /-- `2^{c_E + 1} ∤ a_{r_i} − 2χ` (the non-divisibility of the moving-prime construction) -/
  hnd : ¬ (2 : ℤ) ^ (cE + 1) ∣ amov - 2 * chimov
  /-- `B_i ≥ c_E + 1` -/
  hcB : cE + 1 ≤ Bexp
  /-- the size of the Kummer two-term model -/
  nK : ℕ
  /-- the index set of the quotient block -/
  κ : Type
  [fκ : Fintype κ]
  [dκ : DecidableEq κ]
  /-- the Kummer differential -/
  DK : Matrix (Fin nK) (Fin nK) (PowerSeries ℚ_[2])
  /-- the off-diagonal block of the relaxation -/
  X : Matrix (Fin nK) κ (PowerSeries ℚ_[2])
  /-- the quotient block at the moving and active places -/
  DW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the Kummer class -/
  zK : Fin nK → PowerSeries ℚ_[2]
  /-- the Kummer functional -/
  wK : Fin nK → PowerSeries ℚ_[2]
  /-- the primitive class -/
  zP : Fin nK ⊕ κ → PowerSeries ℚ_[2]
  /-- the primitive functional -/
  wP : Fin nK ⊕ κ → PowerSeries ℚ_[2]
  /-- the Kummer coordinate -/
  uK : PowerSeries ℚ_[2]
  /-- the primitive class restricts to the Kummer class -/
  hz : ∀ i, zP (Sum.inl i) = zK i
  /-- the primitive functional restricts to the Kummer functional -/
  hw : ∀ i, wP (Sum.inl i) = wK i
  /-- `u_prim` is the coordinate of the primitive model -/
  hP : CommonCoordinate.IsCoordOn (fromBlocks DK X 0 DW) zP wP (D.uPrim Fam x)
  /-- `u_K` is the coordinate of the Kummer model -/
  hKc : Central.IsClassFunctionalCoord DK zK wK uK
  /-- The Kummer differential has nonzero adjugate; this is weaker than
  saying that its generic cohomology has dimensions (1,1). -/
  hadj : DK.adjugate ≠ 0
  /-- **the Kummer block with the disk lengths from the literature route** (its order tie is
  derived from the nine book statements, `KummerCoordinateBlockLit.toG`); it replaces the field
  `hK`, which is derived -/
  kummer : KummerCoordinateBlockLit K (Ecurve ℓ) (Fam.h x) DK zK wK (D.jrc (Fam.h x) D.kfin) vL
    (amov - 2 * chimov) tA shaA
  /-- the Frobenius at the moving prime, over `ℚ₂[[t]]` -/
  Fr : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])
  /-- its central value has trace `a_{r_i}` -/
  hFtr : (Fr.map central).trace = (amov : ℚ_[2])
  /-- its central value has determinant `r_i` -/
  hFdet : (Fr.map central).det = (rmov : ℚ_[2])
  /-- the change of basis on the left -/
  PW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the change of basis on the right -/
  QW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the relabelling of the quotient block by the two moving places and the active places -/
  eW : κ ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin (4 * omega (Fam.h x))
  /-- the moving scalar at the first place above `r_i` -/
  zmov : PowerSeries ℚ_[2]
  /-- the moving scalar at the second place above `r_i` -/
  zmov' : PowerSeries ℚ_[2]
  /-- the block at the active places -/
  Bact : Matrix (Fin (4 * omega (Fam.h x))) (Fin (4 * omega (Fam.h x))) (PowerSeries ℚ_[2])
  /-- the quotient block is the direct sum of the local blocks, up to the changes of basis -/
  hDW : DW = PW * (fromBlocks (CommonCoordinate.twoPlaceBlock Fr (rmov : PowerSeries ℚ_[2]) zmov
    zmov') 0 0 Bact).submatrix eW eW * QW
  /-- the left change of basis has a unit determinant at the centre -/
  hPW : v2 (central PW.det) = 0
  /-- the right change of basis has a unit determinant at the centre -/
  hQW : v2 (central QW.det) = 0
  /-- the moving character is trivial at the centre: the first scalar is `χ_h(r_i)` -/
  hzmov : central zmov = chimov
  /-- the second scalar is `χ_h(r_i)` at the centre -/
  hzmov' : central zmov' = chimov
  /-- the active block is the minimal model `2 · 1` of `E[2]` at the centre -/
  hact : Bact.map central =
    (2 : ℚ_[2]) • (1 : Matrix (Fin (4 * omega (Fam.h x))) (Fin (4 * omega (Fam.h x))) ℚ_[2])

attribute [instance] CalibrationModelLit.fieldK CalibrationModelLit.nfK CalibrationModelLit.decK
  CalibrationModelLit.quadK CalibrationModelLit.fκ CalibrationModelLit.dκ

variable {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family} {x : Addr Fam.b}

/-- **The RC53 group's model from the literature model and the nine book statements**: the Kummer
block through `KummerCoordinateBlockLit.toG`. Kind: definition. -/
def CalibrationModelLit.toHK2 (M : CalibrationModelLit D vL G₀ Fam x) (B : CalibrationBookProps) :
    CalibrationModelHK2 D vL G₀ Fam x :=
  { M with kummer := M.kummer.toG B }

/-- **The literature model from the RC53 group's model and the named inputs** for its Kummer
data (the order tie is dropped). Kind: definition. -/
def CalibrationModelLit.ofHK2 (M : CalibrationModelHK2 D vL G₀ Fam x)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex M.kummer.G).homology n))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 M.K), (2 : 𝓞 M.K) ∈ v.asIdeal → v ∈ M.kummer.G.S)
    (hK : IsTotallyComplex M.K)
    (finite2 : ∀ [DecidableEq M.K],
      Finite (AddCommGroup.primaryComponent (centralCurve M.kummer.G).toAffine.Point 2))
    (rank_one : Module.finrank ℤ_[2] ((compactCentralComplex M.kummer.G).homology 1) = 1)
    (hval₁ : M.kummer.x₁.valuation = (centralDiskMatrix M.kummer.G hfinite 1).det.valuation)
    (hval₂ : M.kummer.x₂.valuation = (centralDiskMatrix M.kummer.G hfinite 2).det.valuation)
    (hval₃ : M.kummer.x₃.valuation = (centralDiskMatrix M.kummer.G hfinite 3).det.valuation) :
    CalibrationModelLit D vL G₀ Fam x :=
  { M with
    kummer := KummerCoordinateBlockLit.ofG M.kummer hfinite h2 hK finite2 rank_one hval₁ hval₂
      hval₃ }

/-- **A literature model is exactly an RC53 model with the named inputs for its Kummer data**
(given the nine statements): the order tie of the RC53 model is derived, and nothing else
changes. Kind: PROVED. -/
theorem nonempty_modelLit_iff (B : CalibrationBookProps) :
    Nonempty (CalibrationModelLit D vL G₀ Fam x) ↔
      ∃ M : CalibrationModelHK2 D vL G₀ Fam x,
        ∃ hfinite : (∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex M.kummer.G).homology n)),
          (∀ v : HeightOneSpectrum (𝓞 M.K), (2 : 𝓞 M.K) ∈ v.asIdeal → v ∈ M.kummer.G.S) ∧
          IsTotallyComplex M.K ∧
          (∀ [DecidableEq M.K],
            Finite (AddCommGroup.primaryComponent (centralCurve M.kummer.G).toAffine.Point 2)) ∧
          Module.finrank ℤ_[2] ((compactCentralComplex M.kummer.G).homology 1) = 1 ∧
          M.kummer.x₁.valuation = (centralDiskMatrix M.kummer.G hfinite 1).det.valuation ∧
          M.kummer.x₂.valuation = (centralDiskMatrix M.kummer.G hfinite 2).det.valuation ∧
          M.kummer.x₃.valuation = (centralDiskMatrix M.kummer.G hfinite 3).det.valuation := by
  constructor
  · rintro ⟨L⟩
    refine ⟨L.toHK2 B, L.kummer.hfinite, L.kummer.h2, L.kummer.hK, ?_, L.kummer.rank_one,
      L.kummer.hval₁, L.kummer.hval₂, L.kummer.hval₃⟩
    intro inst
    exact @KummerCoordinateBlockLit.finite2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ L.kummer inst
  · rintro ⟨M, hfinite, h2, hK, finite2, rank_one, hval₁, hval₂, hval₃⟩
    exact ⟨CalibrationModelLit.ofHK2 M hfinite h2 hK finite2 rank_one hval₁ hval₂ hval₃⟩

/-- **The calibration leaf with its duality input from the literature** ((4.6), tex 3987–4141):
the nine book statements (`CalibrationBookProps`; PRINT) and, as in `CalibrationInputsH`, constants
`vL ≥ 0`, `G₀` before the families and at every address of a final family with
`ord L(E^{(h_x)}) = 1` and `ord L(E^{(h_x k)}) = 0` a `CalibrationModelLit`. Kind: definition. -/
def CalibrationInputsLit (D : RCData ℓ) : Prop :=
  CalibrationBookProps ∧ ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family,
    D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelLit D vL G₀ F x)

/-- The RC53 group's inputs from the literature inputs. Kind: PROVED. -/
theorem CalibrationInputsLit.toHK2 (h : CalibrationInputsLit D) : CalibrationInputsHK2 D := by
  obtain ⟨B, vL, G₀, hvL, H⟩ := h
  refine ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact ⟨M.toHK2 B⟩

/-- **The current leaf from the literature inputs**: `CalibrationInputsLit → CalibrationInputsH`
(through the RC53 group's `CalibrationModelHK2.toModelH`). Kind: PROVED. -/
theorem CalibrationInputsLit.toH (h : CalibrationInputsLit D) : CalibrationInputsH D := by
  obtain ⟨vL, G₀, hvL, H⟩ := h.toHK2
  refine ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact ⟨M.toModelH⟩

/-- **`RCSteps.calibration` from the literature inputs** ((4.6), tex 3987–4141). Kind: PROVED. -/
theorem calibrationTarget_of_Lit (Pr : Prints) (hℓ : 0 < ℓ) (h : CalibrationInputsLit D) :
    CalibrationTarget D :=
  calibrationTarget_of_HK2 Pr hℓ h.toHK2

/-- **The literature leaf is the nine statements and, at every address, an RC53 model with the
named inputs for its Kummer data** (`nonempty_modelLit_iff`). Kind: PROVED. -/
theorem calibrationInputsLit_iff :
    CalibrationInputsLit D ↔ CalibrationBookProps ∧ ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ,
      ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
        AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 →
        ∃ M : CalibrationModelHK2 D vL G₀ F x,
          ∃ hfinite : (∀ n : ℤ,
              Module.Finite ℤ_[2] ((compactCentralComplex M.kummer.G).homology n)),
            (∀ v : HeightOneSpectrum (𝓞 M.K), (2 : 𝓞 M.K) ∈ v.asIdeal → v ∈ M.kummer.G.S) ∧
            IsTotallyComplex M.K ∧
            (∀ [DecidableEq M.K],
              Finite (AddCommGroup.primaryComponent (centralCurve M.kummer.G).toAffine.Point 2)) ∧
            Module.finrank ℤ_[2] ((compactCentralComplex M.kummer.G).homology 1) = 1 ∧
            M.kummer.x₁.valuation = (centralDiskMatrix M.kummer.G hfinite 1).det.valuation ∧
            M.kummer.x₂.valuation = (centralDiskMatrix M.kummer.G hfinite 2).det.valuation ∧
            M.kummer.x₃.valuation = (centralDiskMatrix M.kummer.G hfinite 3).det.valuation := by
  constructor
  · rintro ⟨B, vL, G₀, hvL, H⟩
    exact ⟨B, vL, G₀, hvL, fun Co Ce F hF x h1 h0 =>
      (nonempty_modelLit_iff B).1 (H Co Ce F hF x h1 h0)⟩
  · rintro ⟨B, vL, G₀, hvL, H⟩
    exact ⟨B, vL, G₀, hvL, fun Co Ce F hF x h1 h0 =>
      (nonempty_modelLit_iff B).2 (H Co Ce F hF x h1 h0)⟩

/-- **Non-vacuity in the degenerate case**: given the nine statements, the leaf holds when no
address of a final family has the two analytic ranks. Kind: PROVED. -/
theorem calibrationInputsLit_of_noAddress (B : CalibrationBookProps)
    (hD : ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      AnalyticRank (Etw ℓ (F.h x)) 1 → ¬ AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0) :
    CalibrationInputsLit D :=
  ⟨B, 0, 0, le_rfl, fun Co Ce F hF x h1 h0 => absurd h0 (hD Co Ce F hF x h1)⟩

end Leaf

end ZInQ.Manuscript.RC.Wiring
