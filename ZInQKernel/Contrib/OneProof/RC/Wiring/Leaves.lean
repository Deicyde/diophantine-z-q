import ZInQKernel.Contrib.OneProof.RC.Wiring.Even
import ZInQKernel.Contrib.OneProof.RC.Wiring.Odd
import ZInQKernel.Contrib.OneProof.RC.Wiring.OddMinimum
import ZInQKernel.Contrib.OneProof.RC.Wiring.EvenUpper
import ZInQKernel.Contrib.OneProof.RC.Wiring.Clearing
import ZInQKernel.Contrib.OneProof.RC.Wiring.Genuine
import ZInQKernel.Contrib.OneProof.RC.Wiring.Address
import ZInQKernel.Contrib.OneProof.RC.Wiring.Height
import ZInQKernel.Contrib.OneProof.RC.Boolean.Node
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Uses
import ZInQKernel.Contrib.CloudB3RC53.KummerCorankZero.Basic
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Node34
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenusOdd34
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate3
import ZInQKernel.Contrib.OneProof.RC.Wiring.PreSpec
import ZInQKernel.Contrib.OneProof.RC.Wiring.AuxFactor3
import ZInQKernel.Contrib.OneProof.RC.Wiring.EvenUpper3
import ZInQKernel.Contrib.OneProof.RC.Wiring.AddressDict6
import ZInQKernel.Contrib.OneProof.RC.Wiring.ClearingComplex3
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaLevel
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeaf2
import ZInQKernel.Contrib.OneProof.RC.BaseZeroAssembly.Assembly
import ZInQKernel.Contrib.OneProof.RC.Wiring.UniformSwitch

/-!
# Theorem 5.3, Lane RC0: every remaining hypothesis in one structure

`restrictedConverseGenuine_of_leaves : Prints → RCLeaves → RestrictedConverseGenuine` (PROVED,
standard axioms). `RCLeaves` collects every hypothesis that remains after the lanes' results are
wired in; each field carries its tex lines, kind and owner. The deduction, for each admissible `ℓ`
with Selmer corank one:

1. root number `−1` (the blueprint's `rootNumberNode_proof`, Dokchitser–Dokchitser);
2. a genus partner `h_*` (lane RC13's `genusPartner`, via `exists_genusPartner`; Hoffstein–Luo and
   BFH's twist sign from lane RC8's literal prints with lane RC18's proved `twistDictionary`);
3. the attained odd minimum `δ_o` (batch 3's (F.4)–(F.6), `exists_oddMinimum`, from the fixed
   visible witness);
4. the thirteen steps `RCSteps` of the skeleton, each a theorem from the leaves and the lanes'
   results (`rcSteps_of_leaves`): `lstar_ne_zero_iff` (RC11, the normalization carried by the
   GenusOdd instance), `genus_partner` (RC13), `visibility` (RC12), `companion` (from the leaf and
   RC11), `gz_comparison` and (3.4) at the companions (batch 3's GenusOdd from `Prints` and
   `ArtinFactorization`, with RC11's `L_*` as a scaled central value), `final_family` (batch 3's
   `finalFamilyField_proof`, with (F.3) from RC13's `roughCompanion`, (3.3b) from batch 3's
   EvenUpper over RC11's (3.2) with the Boolean comparison from RC1, the auxiliary factor from batch
   3's dictionary, (3.5) from RC16 with batch 3's concrete outer switching data over RC20's genuine
   `𝒪`, the stages from the data specification, and the address input from RC2's construction at the
   staged level with the K-split even restriction, constituent models over finite quotients and
   RC3's trace data), `calibration` (RC15 with RC19's regulator, the free generators from `Prints`
   and batch 3's Calibration), `common_coordinate` (batch 3's support-triangle models), `base_zero`
   (RC15 through batch 3's `baseZeroEndToEnd` over RC20's `Λ_(t)`, the height formula by RC19),
   `height_one` (RC16 with batch 3's concrete height-one switching data and (4.7)), `clearing` (RC7
   with batch 3's PairedFunctional and the repaired budget (5.7));
5. the skeleton's Branch 1 / fixed-field package (`rc_of_oddEmptyUnit`, `fixedFieldPackage_of_steps`),
   with the Kummer sequence in rank zero proved by batch 3 (`kummerCorankZero_proof`);
6. the blueprint's assembly with the missing-address node proved by lane RC1.

No field relies on batch 3's SelmerDuality statements (reviewed as GLUE), on batch 3's
`TraceModel`/`ConstituentModel` (which cannot be inhabited: `traceModel_false`), or on the
positivity versions of the budget (5.7).

**Which theorem carries the reduction.** Given `Prints`, the blueprint's `BranchPackageNode` is
equivalent to Theorem 5.3 (its coefficient data are existential and not tied to `ũ_x`). The
faithful reduction of Theorem 5.3 to Elliot's steps is `restrictedConverseGenuine_of_leaves` here
(and `RC/Assembly.lean`'s `restrictedConverseGenuine_of_steps'`): the step `RCSteps.clearing`,
discharged here from lane RC7, ties `C.u x j = [tʲ] ũ_x`. Claims about the reduction cite these.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 Filter Topology

attribute [local instance] Nat.fact_prime_two

/-! ## Choices substituted into the data -/

/-- The data with the genus partner `h_*` substituted. -/
def WData.withHstar {ℓ : ℕ} (W : WData ℓ) (h : ℤ) : WData ℓ := { W with hstar := h }

/-- The data with the genus partner `h_*` and the odd minimum `δ_o` substituted. -/
def WData.withChoices {ℓ : ℕ} (W : WData ℓ) (h δ : ℤ) : WData ℓ :=
  { W with hstar := h, δo := δ }

/-- The depth set of the odd coefficients of the data (it does not involve `h_*` or `δ_o`). -/
def WData.depthSet {ℓ : ℕ} (W : WData ℓ) : Set ℤ :=
  AppGEndpoints.DepthSet W.stages W.Mθ (fun θ Dd => vZ (W.aθ θ Dd)) W.admissible

/-! ## The final companion -/

/-- **The final companion, as a leaf** (tex 2595–2603): in Branch 2, `k < 0` squarefree,
`k ≠ −1, −3`, its primes in the fixed support, `k ≡ 1 (mod 4)`, a unit square at every prime of `2N`,
prime to `h_*`, and `L_*(k) ≠ 0`. -/
def CompanionLeaf {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ¬ W.OddEmptyUnit → W.kfin < 0 ∧ Squarefree W.kfin ∧ W.kfin ≠ -1 ∧ W.kfin ≠ -3 ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.kfin → p ∈ W.S) ∧ W.kfin % 4 = 1 ∧
    (∀ p : ℕ, p.Prime → p ∣ 2 * CST.newformLevel (Ecurve ℓ) → UnitSquareAt p W.kfin) ∧
    IsCoprime W.kfin W.hstar ∧ W.Lstar W.kfin ≠ 0

/-- **`RCSteps.companion`** from the leaf and the normalization of `L_*` (PROVED). -/
theorem companionTarget_of {ℓ : ℕ} {W : WData ℓ} (hL : LstarTarget W.toRCData)
    (h : CompanionLeaf W) : CompanionTarget W.toRCData := fun hU => by
  obtain ⟨hneg, hsf, h1, h3, hS, h4, h2N, hcop, hLk⟩ := h hU
  exact ⟨hneg, hsf, h1, h3, hS, h4, h2N, hcop, (hL _ hneg.ne).mp hLk⟩

/-! ## The leaves -/

/-- **The leaves that do not involve `δ_o`** (at an admissible `ℓ` with Selmer corank one and a
genus partner `h_*`), each with tex lines, kind and owner. -/
structure PreLeaves {ℓ : ℕ} (W : WData ℓ) : Prop where
  /-- The data are built to specification (`PreDataSpec`: the support consists of primes and
  contains `2, 3` and the primes of `ℓ`; the hyperfilter on the stages; `M_θ ≥ θ`; the stage support
  is the prepared filter cut by a stage condition holding at `D = 1`; the prepared filter contains
  one) (definitions; tex 1790–1793, 2404–2410, 2586, App F 8209–8212, 8233, 8400–8429, App G
  10190–10191; owner RC0, as batch 3's `PreFieldsSpec`). It gives the support, the stages and the
  stage support (`preFields_of_dataSpec`). -/
  data_spec : PreDataSpec W
  /-- The prepared filter is positive and prime to the support (definition; tex 2404–2410). -/
  prepared_spec : PreparedSpec W
  /-- (O.7), native index, torsion clause (lane RC12's remaining inputs of (O.8); tex 9101–9445;
  PRINT Cornut–Jetchev, CST + ELLIOT; owner RC12 / batch 3 GenusOdd). -/
  visibility : VisibilityInputs W.toRCData
  /-- The fixed visible witness `D_w` ((3.7); ELLIOT + PRINT CST; tex 2460–2546; owner batch 3
  GenusOdd / RC12). -/
  witness : WitnessLeaf W
  /-- The specification of the data behind the partitionable auxiliary factor (`AuxFactorInputs`:
  the type data, the conductor on the support, the prepared even sources per total type with
  RC2's coefficient rules, vanishing off their filter, a prepared unit seed per type, and the
  meaning of `Partitionable`; definition + ELLIOT; tex 2016–2185, App G 10055–10150; owners RC0,
  RC2, batch 3 AuxFactor / CoefficientDictionary). The auxiliary factor itself is PROVED from it
  (batch 3's `auxFactor_of_dictionary`, via `auxFactor_of_inputs`). -/
  aux_factor : AuxFactorInputs W
  /-- The remaining inputs of the even upper bound (3.3b) (`EvenUpperRC11Inputs`): (3.3a) at the units
  of the normalized even symbol, lane RC11's (3.2) (`EvenScalar32`), and the realized cubes of units
  (ELLIOT; tex 2273–2341, App G 10079–10129; owners RC11, batch 3 EvenUpper, RC2). The missing
  address on the cubes is PROVED (batch 3's Boolean comparison from lane RC1), at the single
  precision the consumer uses (`EvenUpperInputsAt`). -/
  even_upper : EvenUpperRC11Inputs W
  /-- GenusOdd's genuine objects of (3.4) for `W` (`GenusOddInstance`): lane RC11's normalization of
  `L_*` (GLUE Birch–Manin; tex 1825–1830, 7175–7177), the newform data of `E`, `L_*(h_*)` over the
  lattice's `Ω⁻` a nonzero rational (GLUE Manin–Drinfeld, tex 2403), the Heegner
  selections and the identification of the interface data (definitions), the genus partner's
  squares at the level and the final `k`'s conditions (ELLIOT; tex 2403–2416, 2595–2603); owners
  RC11, batch 3 GenusOdd, RC13. (3.4) itself is PROVED from it
  (`gz34Target_of_genusOdd`, with `Prints.cst` and the GLUE `artin`). -/
  genusOdd : Nonempty (GenusOddInstance W)
  /-- The inputs of (3.5) over the genuine `𝒪` (`Eq35InputsGenuineG`): the primitive coordinates at
  the companion pairs with the height-one switching data (`RegularityInputsS`), (4.6) at the
  companion pairs, and the concrete outer switching data over `𝒪` (`GenuineOuterSwitchData`:
  integral inner minimal models of one size, the outer model in `Frac 𝒪_∞`, integral cycles, the
  functional bound `v λ ≥ −a`, the switch data) (ELLIOT + GLUE; tex 2441–2446, 3987–4047,
  4909–5202; owners RC16, RC15, RC6, batch 3 UniformSwitch / SwitchInputs). PROVED from them:
  `pos`, the Cramer terminal step, the inner minors' link along the ultrafilter, the equal inner
  valuations, and RC16's (3.5) over RC20's genuine valuation. -/
  eq35 : Eq35InputsGenuineG W

/-- **The leaves at the chosen `h_*` and `δ_o`**, each with tex lines, kind and owner. -/
structure PostLeaves {ℓ : ℕ} (W : WData ℓ) : Prop where
  /-- The final companion `k`: a unit of the separate even symbol on negative discriminants square
  at `2N` (ELLIOT; tex 2595–2603, 2720–2721; owner RC2 / RC11 / RC13), recorded by the properties the
  deduction uses, with `L_*(k) ≠ 0` (a unit of the symbol has a nonzero coefficient). -/
  companion : CompanionLeaf W
  /-- The inputs of the address construction at `δ_o` (`AddressPackageLeaf6`): lane RC2's
  `addressInput_of_address` at the staged level, with the even side the K-split restriction of the
  full even symbol of `E^{(k)}` (the common alphabet consists of K-split types, tex 10268–10293;
  the restriction's coefficient rules are PROVED from the full ones), the coefficient readings of
  the odd stage source and of the full even source produced by constituent models over finite
  quotients (`ConstituentModelRel`, with their two ELLIOT inputs; GLUE Chebotarev in the finite
  quotient, tex 9524–9548, 9663–9704, 9905–9918), the K-split congruence from lane RC3's trace data
  at the fresh K-split primes, and `C_{e,final}` and the even reading from the inputs of (F.1)
  (batch 3's `F1_unit`); unchanged: the side conditions on `k`, the alphabets, the bounded-weight
  witness, the filters, prime realization and the odd reading (ELLIOT/GLUE; App G 10079–10861, App
  F 9447–9976; owners RC2, RC12, RC11, RC3, batch 3). -/
  address : AddressPackageLeaf6 W
  /-- The inputs of (4.6) at every address (`CalibrationInputsC`): the two-primary Ш and torsion
  orders (ELLIOT + PRINT Kolyvagin), the component groups at `p ∣ k` through the reduction (PRINT
  Edixhoven Thm 5.3, Rem. 5.4.1, as GLUE), the pullback and comparison data, Cassels–Milne isogeny
  invariance at the genuine canonical regulators (PRINT Milne ADT I.7.3 + GLUE), the moving prime in
  the output form of RC17's moving character, and the triangular Kummer model with its central
  quotient block (ELLIOT; tex 3987–4141; owners RC15, RC9, RC19, RC4/RC17, batch 3 Duality). PROVED
  from them: the isogeny and regulator data (RC19's `regulator_inputs_sumDiff`), the free
  generators (from `Prints`), the component fields, the moving-prime fields, and `hvprim` with
  Elliot's total length `2v₂N + 4ω` (batch 3's Calibration). -/
  calibration : CalibrationInputsC W.toRCData
  /-- The inputs of (4.7) at every address as support-triangle data (`CommonCoordinateTriangles`):
  the coefficient ring, the character and the graph-prime factors (definition), the Euler-factor
  identity (ELLIOT, the Frobenius model at `q`), the Frobenius matrices at the unused primes, and
  the triangular models of the support triangle at each relaxation step (ELLIOT; tex 4142–4328;
  owners RC15, RC4, batch 3 CommonCoordinate). The multi-prime (4.7) and `ε_q ∈ Λ^×` are PROVED
  from them (batch 3's `commonCoordinateModel_of_models`), replacing the earlier GLUE. -/
  common_coordinate : CommonCoordinateInputsT W.toRCData
  /-- The inputs of height-one regularity of the primitive coordinates (`PrimRegularityInputsS`): at
  every height-one prime `𝔭 ≠ (2)`, concrete two-term switching data (`HeightOneSwitchDataS`: the
  two-term models with integral class and closed functional, the sign involution, the nonzero
  class, and the switch steps with their (5.5a) and detection inputs) (ELLIOT + GLUE; tex
  4976–5197; owners RC16, batch 3 UniformSwitch / SwitchInputs / HeegnerCohomology). PROVED from
  them: `pos`, the terminal step, `s₊ + s₋ = s`, the nonquadratic `U = F`, and RC16's regularity. -/
  prim_regular : PrimRegularityInputsS W.toRCData
  /-- The inputs of (5.9) from the remaining complex (`ClearingInputsCx`): the identification of the
  remaining complex over `𝒪[G]` (block form, augmentation the old complex, new-local Schur
  differentials, the (5.7) counts, a quasi-isomorphism to a Selmer complex; GLUE), the coordinate
  link (E1a, GLUE) and Elliot's determinant computation (E1b, ELLIOT) (tex 5355–5645; owners RC7,
  batch 3 ClearingComplex / RankCounts). PROVED from them: the Smith model, the generic patterns,
  the entry poles, the budget (5.7), and (5.9) by lane RC7 over RC20's genuine `𝒪`, with the
  exponent `a = 0` and the `μ`-coordinates from batch 3's PairedFunctional. -/
  clearing_model : ClearingInputsCx W.toRCData
  /-- The inputs of the base-zero lemma left by lane RC25's `baseZeroTarget_of_leaves` (lane RC15's
  `baseZero_node` over lane RC20's `Λ_(t)`, the height formula by lane RC19 from Cai–Shu–Tian Thm 1.1
  and the conductor-one Heegner data): the two-term model with central dimensions `(1,1)`, the
  stages of (4.5) at the base (PRINT (4.1) per stage) with the limit at the centre (ELLIOT), and the
  identification of `u_{prim,0}` (definition); (4.7) at the base, `ũ₀ ∈ Λ[1/2]` and the package's
  datum are PROVED from `common_coordinate` and `prim_regular` (tex 4330–4376, 3895–3921,
  4369–4373, 5703–5706; owners RC15, RC19, RC25, batch 3 HeegnerCohomology, RankCounts). -/
  base_zero : BaseZeroAssembly.BaseZeroLeafInputs W.toRCData

/-- **Every remaining hypothesis of Theorem 5.3 beyond the blueprint's `Prints`.** -/
structure RCLeaves where
  /-- Hoffstein–Luo over newforms (PRINT, Math. Res. Lett. 4 (1997), p. 436, as stated by lane
  RC8; tex 1985–1991, App G 9996). -/
  hlPrint : PrintsAnalytic.HoffsteinLuoTheorem
  /-- The twisted functional equation over newforms (PRINT, as quoted in Hoffstein–Luo p. 435,
  display (1); lane RC8). -/
  twistedFE : PrintsAnalytic.TwistedFunctionalEquation
  /-- Modularity in newform form: every elliptic curve over `ℚ` has a weight-two newform with the
  same `L`-function (PRINT: BCDT Thm A with Atkin–Lehner/Carayol; lane RC8). -/
  modularNewform : PrintsAnalytic.ModularNewform
  /-- Absolute convergence of `L(E, s)` on `Re s > 3/2` (GLUE, textbook: Hasse's bound; lane RC8). -/
  hasse : PrintsAnalytic.HasseConvergence
  /-- The one GLUE statement of (3.4): the Artin factorization of the ring-class `L`-functions over
  imaginary quadratic fields (GLUE; tex 2411–2440; owner batch 3 GenusOdd; genus theory's square
  roots, the Galois closure and the splitting criterion are PROVED there). -/
  artin : ZInQ.Contrib.CloudB3RC53.GenusOdd.ArtinFactorization
  /-- The interface data, given the genus partner `h_*`. -/
  data : ∀ ℓ : ℕ, ℤ → WData ℓ
  /-- The leaves not involving `δ_o`, at every genus partner. -/
  pre : ∀ ℓ : ℕ, Adm ℓ → SelmerCorankOne (Ecurve ℓ) → ∀ h : ℤ, IsGenusPartner ℓ h →
    PreLeaves ((data ℓ h).withHstar h)
  /-- The leaves at the chosen `h_*` and the attained odd minimum `δ_o`. -/
  post : ∀ ℓ : ℕ, Adm ℓ → SelmerCorankOne (Ecurve ℓ) → ∀ h : ℤ, IsGenusPartner ℓ h →
    ∀ δ : ℤ, IsLeast (data ℓ h).depthSet δ → PostLeaves ((data ℓ h).withChoices h δ)

/-! ## The steps from the leaves -/

/-- Hoffstein–Luo for elliptic curves (PROVED from the print; lane RC18's `twistDictionary`). -/
theorem RCLeaves.hl (L : RCLeaves) : Nonvanishing.HoffsteinLuo :=
  Nonvanishing.FromRC8.hoffsteinLuo_of_curve
    (TwistDictionary.hoffsteinLuoCurve_of_print L.hlPrint L.modularNewform L.hasse)

/-- BFH's twist sign for elliptic curves (PROVED from the twisted functional equation; lane
RC18's `twistDictionary`; the level of the functional equation is supported on the bad primes by
lane RC22's `levelSupport_of_modularNewform`). -/
theorem RCLeaves.twistSign (L : RCLeaves) : Nonvanishing.BFHTwistSign :=
  Nonvanishing.FromRC8.bfhTwistSign_of_curve
    (TwistDictionary.twistedRootNumberCurve_of_print L.twistedFE L.modularNewform L.hasse)
    (GlueSweep.Ana.levelSupport_of_modularNewform L.modularNewform)

/-- Every elliptic curve over `ℚ` has a root number (PROVED from modularity in newform form and
Hasse's convergence; lane RC8's `exists_rootNumber`). -/
theorem RCLeaves.rootNumberExists (L : RCLeaves) : Nonvanishing.FromRC8.RootNumberExists :=
  fun _ hA => PrintsAnalytic.exists_rootNumber L.modularNewform L.hasse hA

/-- **The thirteen steps of the skeleton from the leaves** (PROVED). -/
theorem rcSteps_of_leaves (P : Prints) (L : RCLeaves) {ℓ : ℕ} (hadm : Adm ℓ)
    (hSel : SelmerCorankOne (Ecurve ℓ)) {h : ℤ} (hG : IsGenusPartner ℓ h) :
    ∃ δ : ℤ, RCSteps ((L.data ℓ h).withChoices h δ).toRCData := by
  set W₁ := (L.data ℓ h).withHstar h with hW₁
  have hp := L.pre ℓ hadm hSel h hG
  obtain ⟨hsupp, hnonp, hidx, hone, hglue⟩ := preFields_of_dataSpec hadm.1 hp.data_spec
  -- `M_θ → ∞` along the ultrafilter (batch 3's `stagesAdvance_of_nonprincipal`)
  have hstages : Tendsto W₁.Mθ (W₁.stages : Filter ℕ) atTop :=
    ZInQ.Contrib.CloudB3RC53.GenusOdd.stagesAdvance_of_nonprincipal _ hnonp _ hidx
  have hHL := L.hl
  have hTS := L.twistSign
  obtain ⟨I⟩ := hp.genusOdd
  have hL : LstarTarget W₁.toRCData :=
    lstarTarget_of hadm.1 L.rootNumberExists (lstarNormalized_of_instance I)
  have hvis : VisibilityTarget W₁.toRCData := visibilityTarget_of_inputs _ hp.visibility
  obtain ⟨A₀, haux⟩ := auxFactor_of_inputs W₁ hsupp hp.aux_factor
  obtain ⟨C₁, h33b⟩ := evenUpper33b_of_RC11Inputs W₁ P hadm.1 hL (lstarNormalized_of_instance I)
    hp.even_upper
  have hF3 : F3Target W₁ := f3Target_of W₁ P
    ZInQ.Contrib.CloudB3RC53.KummerCorankZero.kummerCorankZero_proof hHL hTS
    L.rootNumberExists hadm.1 hL hsupp hp.prepared_spec haux h33b
  -- the attained odd minimum
  obtain ⟨Cdet, hCdet⟩ := hvis
  obtain ⟨A, CE, h33⟩ := hF3
  obtain ⟨Cper, h34, h34k⟩ := gz34Target_of_genusOdd P L.artin L.rootNumberExists I
  have h35 : Eq35Target W₁ := eq35Target_of_inputsGenuineG W₁ hp.eq35
  obtain ⟨CR, h35A⟩ := h35 A
  obtain ⟨δ, hδ⟩ := exists_oddMinimum W₁ h33 h34 h35A hCdet hglue hp.witness
  refine ⟨δ, ?_⟩
  set W₂ := (L.data ℓ h).withChoices h δ with hW₂
  have hq := L.post ℓ hadm hSel h hG δ hδ
  -- the steps for `W₂` (its fields other than `δ_o` are those of `W₁`)
  have hL₂ : LstarTarget W₂.toRCData := hL
  have hvis₂ : VisibilityTarget W₂.toRCData := ⟨Cdet, hCdet⟩
  have hG₂ : GenusPartnerTarget W₂.toRCData := genusPartnerTarget_of hL₂ hG
  have hfam : FinalFamilyTarget W₂.toRCData :=
    finalFamilyTarget_of W₂ hvis₂ hstages ⟨A, CE, h33⟩ ⟨Cper, h34, h34k⟩ h35
      hglue hδ (addressLeaf_of_6 W₂ hq.address)
  have h47 : CommonCoordinateTarget W₂.toRCData :=
    commonCoordinateTarget_of_inputs (commonCoordinateInputs_of_triangles hq.common_coordinate)
  have hheight : HeightOneTarget W₂.toRCData :=
    heightOneTarget_of_inputsS _ hq.prim_regular h47
  exact rcSteps_of_targets _ hL₂ hG₂ hvis₂ hstages hone
    (companionTarget_of hL₂ hq.companion)
    ⟨Cper, h34k⟩ hfam (calibrationTarget_of_C P hadm.1 hq.calibration) h47 hheight
    (clearingTarget_of_complex _ hheight hq.clearing_model) (BaseZeroAssembly.baseZeroTarget_of_leaves P
      (commonCoordinateInputs_of_triangles hq.common_coordinate)
      (primRegularityInputs_of_S _ hq.prim_regular) hq.base_zero)

/-! ## The node and Theorem 5.3 -/

/-- **`BranchPackageNode` from the leaves** (PROVED). -/
theorem branchPackageNode_of_leaves (P : Prints) (L : RCLeaves) : BranchPackageNode := by
  intro ℓ hadm hSel
  have hw := rootNumberNode_proof P ℓ hadm hSel
  obtain ⟨h, hG⟩ := exists_genusPartner L.hl L.twistSign P.bcdt hadm.1 hw
  obtain ⟨δ, S⟩ := rcSteps_of_leaves P L hadm hSel hG
  by_cases hU : ((L.data ℓ h).withChoices h δ).OddEmptyUnit
  · exact Or.inl (rc_of_oddEmptyUnit _ S hU)
  · exact Or.inr (fixedFieldPackage_of_steps hadm.1 P
      ZInQ.Contrib.CloudB3RC53.KummerCorankZero.kummerCorankZero_proof _ S hSel hU)

/-- **Theorem 5.3 (`hyp:RC`) from the printed leaves `Prints` and the remaining hypotheses
`RCLeaves`** (PROVED; standard axioms): the blueprint's assembly with `branchPackageNode_of_leaves`
and lane RC1's `missingAddressNode`. -/
theorem restrictedConverseGenuine_of_leaves (P : Prints) (L : RCLeaves) :
    RestrictedConverseGenuine :=
  restrictedConverseGenuine_of_nodes P (branchPackageNode_of_leaves P L)
    ZInQ.Manuscript.RC.Boolean.missingAddressNode

end ZInQ.Manuscript.RC.Wiring
