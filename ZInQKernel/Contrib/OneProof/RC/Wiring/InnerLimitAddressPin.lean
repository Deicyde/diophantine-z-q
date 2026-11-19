import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitMovingFamily
import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitRegularityFamily
import ZInQKernel.Contrib.OneProof.RC.Wiring.StageSupportCoefficient
import ZInQKernel.Contrib.CloudB3RC53.Prints.CST
import ZInQKernel.Contrib.RC53Assist.RetainedAssembly.SupportChange.SeveralPlaces

/-!
# Theorem 5.3, Lane RC0 round 17: the faithful pin of the height-one leaf

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5200): "use the
actual primitive scalar Selmer complex over `R = Λ_𝔭`" (tex 4976–4980). The configuration family's
actual fibre is not a free choice: it is the specialization at `𝔭` of the retained inner limit
(tex 4385–4451) of the address's actual stage family, whose coefficient modules are
`M_i = (T₂E ⊗ A_i)(χ_{h_x} Ψ_i)` over `K = ℚ(√k)` (tex 2723–2741), with the actual Kummer
conditions at the places above `2N` and the full conditions at the active and moving primes (lane
RC29's table, tex 2748–2760, 3080–3085, 3413–3468), on moving supports (tex 4255–4280).

* `placesTwoN`, `placesOf`: the places above `2N` and above `h`.
* `AddressMovingFamily ℓ h W`: a moving stage family (`MovingStageFamily`) whose characters are
  `α_i = χ_h Ψ_i` (`alphaChar` of `quadChar √h` and the moving exponents `ξ_i`, trivial at `2N`),
  whose old support at stage `i` is the places above `2N`, the places above `h` and the moving
  conductor prime `r_i` (injective in `i`), and whose old conditions are the actual Kummer
  conditions at the places above `2N` (`actualKummerAtS`, through the coefficient comparison
  `condToMinS`) and the full conditions at the other old places (definition, data and GLUE).
* `MovingRetainedLimit Fam`: the retained inner limit of a moving family with its localization at
  the first derivative label and its links (data); `finiteFibre`: its finite side at `𝔭`, the
  old-condition Selmer complex at `𝔭` of the limit with the unramified (finite) condition at the
  label.
* `MovingResidualSteps Fam`, `MovingResidualSteps.package`: the residual package of a moving
  family from a uniform base package and support-and-condition steps at stage-dependent places
  (the RC53 group's support change at several places); `AddressMovingFamily.residualSteps`,
  `AddressMovingFamily.residualPackage`: for the address's family, from the old-support stage
  complexes and one step at the new prime (bound `B + 6`); `MovingArithmeticInputs.ofSteps`.
* `AddressLabelFamily A`: the address's family at a later configuration (the previous derivative
  labels as further old places, the address's characters inflated, the address's Kummer and full
  conditions at its old places).
* `InnerLimitSwitchPinned`: the frame and linked moving switches on the address's families at the
  configurations (`AddressLabelFamily`), with side models.
* `RegularityInputsILP ℓ h k u`, `PrimRegularityInputsILP D` (with `h = h_x`, `k = k`): the leaf
  with the FAITHFUL PIN: the actual fibre homotopy equivalent to the finite fibre of the retained
  limit of the address's actual moving family, and the actual stage equal to the stage of an
  integral model of that finite side (so `zAct`, `lamAct` and the coordinate `u` are the class,
  functional and coordinate of the integral model; tex 3877–3892, 4986–4992). PROVED:
  `RegularityInputsILP.toMdl`, `primRegularityInputs_of_ILP`, `heightOneTarget_of_ILP`.
* The collapse is the terminal case. PROVED: `InnerLimitSwitchPinned.fiberDim_eq_pinned` (the
  actual fibre dimension is `dim H¹` of the address's finite limit fibre),
  `InnerLimitSwitchPinned.fiberDim_eq_one_of_stationary` and
  `HomologySwitchDataPK.fiberDim_eq_one_of_stationary` (a configuration family without proper
  successors, as in every collapse, forces fibre dimension one),
  `PinnedFamilyAt.terminal_of_stationary` (at the clause: then `dim H¹ = 1` of the address's
  finite limit fibre), and
  `InnerLimitSwitchPinned.switch_required` (outside the terminal case a switch on the address's
  family is required).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing Matrix Module
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane lambdaHalfToFrac)
open ZInQ.Manuscript.RC.FibreDuality (RetainedLimitPairingStages RetainedGlobalDualityStages
  splitSelData stageLocMat stagePairingInputOfSel)
open ZInQ.Manuscript.RC.Limits (residualCohomologyAt StageA stageMap stageIdeal
  stageIdeal_tendsToZero)
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex ComplexStages fibreLimitGlobal
  finiteLimitSide)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (ResidualCohomologyFinite)
open ZInQ.Manuscript.RC.CoefModules (ActualConj IsOpenKer CondAt Mcoef fullAt FullTorsion KS
  alphaChar quadChar)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.SelmerComplex (GKS Places Gloc locMap)
open ZInQ.Manuscript.RC.KummerMaps (actualKummerAtS IsLocallyQuadAt)
open ZInQ.Manuscript.RC.Wiring.StageSupport (condToMinS)
open ZInQ.Contrib.RC53Assist.OldOrthogonality.SupportCoefficients (characterAfterSupport)
open ZInQ.Contrib.RC53Assist.InnerLimitMoving (IntegralMatrixStageData selmerStages
  derivativeDiagram retainedRestrictionStages)
open ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange (RetainedStageRealization)
open ZInQ.Contrib.CloudB3RC53.CST (newformLevel)
open ZInQ.Manuscript.RC.Rings (isDiscreteValuationRing_atPrime_of_height_one)
open ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange.SeveralPlaces (StageComplexFamily
  StageResidualPackage SupportConditionStep movingResidualPackage_of_cochain_steps)
open scoped PowerSeries.WithPiTopology

/-! **The address's actual moving stage family** -/

section Address

variable {K : Type} [Field K] [NumberField K]

variable (K) in
/-- The places above `2N`, `N` the conductor of `E_ℓ` (tex 2748–2760). Kind: definition. -/
def placesTwoN (ℓ : ℕ) : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | ((2 * newformLevel (Ecurve ℓ) : ℕ) : 𝓞 K) ∈ v.asIdeal}

variable (K) in
/-- The places above an integer `h` (for `h = h_x`, the places above the active primes).
Kind: definition. -/
def placesOf (h : ℤ) : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | ((h : ℤ) : 𝓞 K) ∈ v.asIdeal}

/-- **The address's actual moving stage family** (tex 2723–2741, 2748–2760, 3080–3085,
3413–3468, 4255–4280), for the twist `h` (`h = h_x`) and the curve `W` (`W = E_ℓ ⊗ K`):
* `Fam`, `hT`: a moving stage family with full torsion over its old supports (data, GLUE);
* `root`, `square`, `nonzero`, `ξ`, `ξ_open`, `character`: its characters are
  `α_i = χ_h Ψ_i`, with `χ_h` the quadratic character of `K(√h)/K` and `Ψ_i = (1 + t)^{ξ_i}`
  (`alphaChar`; tex 2725–2741, 2791);
* `ξ_twoN`: the moving exponents are trivial on the decomposition groups above `2N` (ELLIOT; tex
  2729, 3430–3432, 3503–3506);
* `r`, `r_injective`, `support`: the old support at stage `i` is the places above `2N`, the places
  above `h` (the active primes) and the moving conductor prime `r_i`, which varies with the stage
  (tex 2737–2741, 4268–4272; lane RC29's table);
* `rootS`, `squareS`, `nonzeroS`, `quadS`: the square root of `h` in the field of the enlarged
  support, and the character there quadratic at `2N` (ELLIOT);
* `kummer`, `full`: the old conditions are the actual Kummer conditions above `2N`
  (`actualKummerAtS`, read in the enlarged-support coefficient model through `condToMinS`) and the
  full conditions at the active and moving primes (GLUE, tex 2748–2760, 3080–3085).
At the start no previous derivative label is old. The moving exponents `ξ_i`, the conductor
primes `r_i` and the new primes `q_i` remain choices, as in the text (Proposition
`ex:arith-moving-character`). Kind: definition (data and GLUE). -/
structure AddressMovingFamily (ℓ : ℕ) (h : ℤ) (W : WeierstrassCurve K) [W.IsElliptic] where
  /-- The moving stage family. -/
  Fam : MovingStageFamily W
  /-- Full torsion over every old support. -/
  hT : Fam.FullTorsionAt
  /-- A square root of `h` in the field of the old support. -/
  root : ∀ i, KS K (Fam.oldSupport i)
  /-- It squares to `h`. -/
  square : ∀ i, root i ^ 2 = algebraMap K (KS K (Fam.oldSupport i)) (h : K)
  /-- It is nonzero. -/
  nonzero : ∀ i, root i ≠ 0
  /-- The moving exponents. -/
  ξ : ∀ i, GKS K (Fam.oldSupport i) →* Multiplicative (ZMod (2 ^ (2 * i)))
  /-- They have open kernels. -/
  ξ_open : ∀ i, IsOpen ((ξ i).ker : Set (GKS K (Fam.oldSupport i)))
  /-- The characters are `χ_h Ψ_i`. -/
  character : ∀ i, Fam.α i = alphaChar i (quadChar (root i) (square i) (nonzero i)) (ξ i)
  /-- The moving exponents are trivial above `2N`. -/
  ξ_twoN : ∀ i, ∀ v ∈ placesTwoN K ℓ, ∀ σ : Gloc K v, ξ i (locMap K (Fam.oldSupport i) v σ) = 1
  /-- The moving conductor primes. -/
  r : ℕ → HeightOneSpectrum (𝓞 K)
  /-- They vary with the stage. -/
  r_injective : Function.Injective r
  /-- The old support: the places above `2N`, the places above `h`, and `r_i`. -/
  support : ∀ i, Fam.oldSupport i = placesTwoN K ℓ ∪ placesOf K h ∪ {r i}
  /-- A square root of `h` in the field of the enlarged support. -/
  rootS : ∀ i, KS K (Fam.support i)
  /-- It squares to `h`. -/
  squareS : ∀ i, rootS i ^ 2 = algebraMap K (KS K (Fam.support i)) (h : K)
  /-- It is nonzero. -/
  nonzeroS : ∀ i, rootS i ≠ 0
  /-- The enlarged character is quadratic above `2N`. -/
  quadS : ∀ i, ∀ v ∈ placesTwoN K ℓ, IsLocallyQuadAt (S := Fam.support i) i (Fam.character i)
    (quadChar (rootS i) (squareS i) (nonzeroS i)) v
  /-- The old conditions above `2N` are the actual Kummer conditions. -/
  kummer : ∀ i [NeZero i] (v : Places K (Fam.oldSupport i)) (hv : v.1 ∈ placesTwoN K ℓ),
    condToMinS W i (Fam.character i) (Fam.old i v) =
      actualKummerAtS (subset_refl (Fam.support i)) W i (rootS i) (squareS i) (nonzeroS i)
        (Fam.character i) (Fam.fullTorsion hT i) ⟨v.1, Or.inr v.2⟩ (quadS i v.1 hv)
  /-- The other old conditions are the full conditions. -/
  full : ∀ i [NeZero i] (v : Places K (Fam.oldSupport i)), v.1 ∉ placesTwoN K ℓ →
    Fam.old i v = fullAt K (Fam.support i) (Acoef i) (Fam.coefficient i) ⟨v.1, Or.inr v.2⟩

/-- **The address's family at a later configuration** (tex 4255–4280, 5055–5065, 5137–5153): a
moving stage family whose old support at stage `i` is the address's together with the previous
derivative labels `labels i` (outside the address's old support), whose characters are the
address's characters inflated (`characterAfterSupport`), and whose old conditions at the address's
old places are the address's: the actual Kummer conditions above `2N` (`actualKummerAtS`, through
`condToMinS`) and the full conditions at the active and moving primes. The derivative conditions
at the previous labels (the finite or the singular side chosen at the earlier switches, tex
5055–5065) are not pinned. Kind: definition (data and GLUE). -/
structure AddressLabelFamily {ℓ : ℕ} {h : ℤ} {W : WeierstrassCurve K} [W.IsElliptic]
    (A : AddressMovingFamily ℓ h W) where
  /-- The moving stage family. -/
  Fam : MovingStageFamily W
  /-- Full torsion over every old support. -/
  hT : Fam.FullTorsionAt
  /-- The previous derivative labels at each stage. -/
  labels : ℕ → Set (HeightOneSpectrum (𝓞 K))
  /-- The old support: the address's and the previous labels. -/
  support : ∀ i, Fam.oldSupport i = A.Fam.oldSupport i ∪ labels i
  /-- The labels are new places for the address's family. -/
  labels_new : ∀ i, Disjoint (A.Fam.oldSupport i) (labels i)
  /-- The address's old support is contained in the old support. -/
  hsub : ∀ i, A.Fam.oldSupport i ⊆ Fam.oldSupport i
  /-- The characters are the address's, inflated. -/
  character : ∀ i, Fam.α i = characterAfterSupport (hsub i) i (A.Fam.α i)
  /-- A square root of `h` in the field of the enlarged support. -/
  rootS : ∀ i, KS K (Fam.support i)
  /-- It squares to `h`. -/
  squareS : ∀ i, rootS i ^ 2 = algebraMap K (KS K (Fam.support i)) (h : K)
  /-- It is nonzero. -/
  nonzeroS : ∀ i, rootS i ≠ 0
  /-- The enlarged character is quadratic above `2N`. -/
  quadS : ∀ i, ∀ v ∈ placesTwoN K ℓ, IsLocallyQuadAt (S := Fam.support i) i (Fam.character i)
    (quadChar (rootS i) (squareS i) (nonzeroS i)) v
  /-- The old conditions above `2N` are the actual Kummer conditions. -/
  kummer : ∀ i [NeZero i] (v : Places K (Fam.oldSupport i)) (hv : v.1 ∈ placesTwoN K ℓ),
    condToMinS W i (Fam.character i) (Fam.old i v) =
      actualKummerAtS (subset_refl (Fam.support i)) W i (rootS i) (squareS i) (nonzeroS i)
        (Fam.character i) (Fam.fullTorsion hT i) ⟨v.1, Or.inr v.2⟩ (quadS i v.1 hv)
  /-- The conditions at the address's other old places are the full conditions. -/
  full : ∀ i [NeZero i] (v : Places K (Fam.oldSupport i)), v.1 ∈ A.Fam.oldSupport i →
    v.1 ∉ placesTwoN K ℓ →
      Fam.old i v = fullAt K (Fam.support i) (Acoef i) (Fam.coefficient i) ⟨v.1, Or.inr v.2⟩

end Address

/-! **The retained limit of a moving family and its finite fibre** -/

section Limit

variable {K : Type} [Field K] [NumberField K] {W : WeierstrassCurve K} [W.IsElliptic]

/-- **The retained inner limit of a moving stage family, localized at its first derivative label**
(tex 4385–4451, 4859–4873): the residual package of the stage complexes, the split-stage data at
the new primes (projection, self-paired split Selmer datum, trace, global duality), the retained
data `C`, `D`, `E` with their lifts and ranks, and the links (on a `U`-large set the projection a
quasi-isomorphism over `A_i`; the realization of the retained data on the stage complexes). These
are the fields of `ILStageStepMovingLinked` without the switch inputs (retained local arithmetic,
detection, side-to-stage isomorphisms), with its three residual fields as one package
(`MovingResidualPackage`, produced by `MovingResidualSteps.package`).
Kind: definition (data and inputs). -/
structure MovingRetainedLimit (Fam : MovingStageFamily W) where
  /-- The uniform bound. -/
  B : ℕ
  /-- The residual package: finite residual cohomology of the stage complexes, the range
  `[0, 3]` and the bound `B`. -/
  residual : MovingResidualPackage Fam B
  /-- The condition at the derivative label. -/
  Uq : ∀ i, GCx (Acoef i)
  /-- Its map to the local cochains. -/
  ιq : ∀ i, GHom (Uq i) (Fam.localCx i)
  /-- The split projection of the local cochains. -/
  p : ∀ i, GHom (Fam.localCx i) (splitLocalComplex (Acoef i))
  /-- The self-paired split Selmer datum. -/
  Q : ∀ i, SelPairData
    (splitSelData (Fam.globalCx i) (Fam.stageRes i (p i)) (Uq i) (ghomComp (ιq i) (p i)))
    (splitSelData (Fam.globalCx i) (Fam.stageRes i (p i)) (Uq i) (ghomComp (ιq i) (p i)))
  /-- The trace. -/
  tr : ∀ i, (coneCx (Q i).resE).X 3 →ₗ[Acoef i] Acoef i
  /-- The trace kills coboundaries. -/
  htr : ∀ i z, tr i ((coneCx (Q i).resE).d 2 3 rfl z) = 0
  /-- The split global duality. -/
  hdual : ∀ i, QuasiIso (GHom.toCC (globalDualityMap (Q i) (tr i) (htr i)))
  /-- The ultrafilter of the inner limit. -/
  U : Ultrafilter ℕ
  hU : (U : Filter ℕ) ≤ cofinite
  /-- The retained stage complexes. -/
  C : ComplexStages (R := Lambda) stageIdeal U
  /-- The retained pairing data. -/
  D : RetainedLimitPairingStages U C
  /-- The retained global duality. -/
  E : RetainedGlobalDualityStages D
  /-- The retained local pairing lifts the stage local pairings. -/
  hlift : ∀ i, i ≠ 0 → ∀ a b, (D.loc a b i).map (stageMap i) = stageLocMat (Q i) (tr i) a b
  /-- The model ranks are the residual ranks of the stage complexes on a `U`-large set. -/
  hrank : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i] (n : ℤ),
    C.rank n = Module.finrank (ResidueField (StageA i))
      (residualCohomologyAt (Fam.globalCx i) n)
  /-- The model ranks are bounded by `B`. -/
  hrankB : ∀ n, C.rank n ≤ B
  /-- On a `U`-large set of stages the split projection is a quasi-isomorphism over `A_i`. -/
  projection_model : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i], QuasiIso (GHom.toCC (p i))
  /-- The retained data are realized on the stage complexes. -/
  realized : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i], Nonempty
    (RetainedStageRealization C D i (stagePairingInputOfSel (Q i) (tr i) (htr i)))

/-- **The finite fibre of the retained limit at `𝔭`**: the Selmer complex at `𝔭` of the retained
limit with the finite (unramified) condition at the derivative label, i.e. the old-condition
Selmer complex of the stage family at `𝔭` (tex 4385–4451, 5040–5054). Kind: definition. -/
abbrev MovingRetainedLimit.finiteFibre {Fam : MovingStageFamily W} (L : MovingRetainedLimit Fam)
    (P : Ideal Lambda) [P.IsPrime] : GCx (ResAt P) :=
  selCx (finiteLimitSide (fibreLimitGlobal L.U L.hU P L.C) (L.D.resLimit L.hU P)).Dside

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
  {S : Set (HeightOneSpectrum (𝓞 K))} {Cn : ActualConj K S} {hW : W.map (Cn.κ : K →+* K) = W}
  [HasFullTwoTorsion K S W]

/-- The retained limit of the data of a linked moving switch (forgetting the switch inputs).
Kind: definition. -/
def ILStageStepMovingLinked.retainedLimit {Z₀ Z₁ : TwoTermStage ι}
    (X : ILStageStepMovingLinked P Cn W hW Z₀ Z₁) : MovingRetainedLimit X.Fam where
  B := X.B
  residual := ⟨X.hres, X.hbdd, X.hB⟩
  Uq := X.Uq
  ιq := X.ιq
  p := X.p
  Q := X.Q
  tr := X.tr
  htr := X.htr
  hdual := X.hdual
  U := X.U
  hU := X.hU
  C := X.C
  D := X.D
  E := X.E
  hlift := X.hlift
  hrank := X.hrank
  hrankB := X.hrankB
  projection_model := X.projection_model
  realized := X.realized

end Limit

/-! **The residual package from the support change at several places** -/

section ResidualSteps

variable {K : Type} [Field K] [NumberField K] {W : WeierstrassCurve K} [W.IsElliptic]

/-- **The residual steps of a moving family** (tex 3483–3498, 4391–4406, 4859–4873): the stage
complexes of the family reached from a base family of stage complexes with a uniform residual
package by `k` support-and-condition steps at stage-dependent places (the RC53 group's
`SupportConditionStep`: the inflated old datum, the full local complex at the added place, its
unramified condition and the place's own condition, the support and target cochain
quasi-isomorphisms, and the local cohomology bounds with allowance `c j`). For the address's
family the base is the old-support stage complex (the actual Selmer complex of stage `i` over
`S_i`, which contains the moving conductor prime) and the one step adds the new prime `q_i` with
no condition (`AddressMovingFamily.residualSteps`); for a switch family the previous derivative
labels are further steps. Kind: definition (inputs). -/
structure MovingResidualSteps (Fam : MovingStageFamily W) where
  /-- The intermediate stage-complex families. -/
  G : ℕ → StageComplexFamily
  /-- The number of added places. -/
  k : ℕ
  /-- The local-condition allowances. -/
  c : ℕ → ℕ
  /-- The base bound. -/
  B : ℕ
  /-- The uniform residual package of the base family. -/
  base : StageResidualPackage (G 0) B
  /-- The support-and-condition steps. -/
  step : ∀ j, j < k → ∀ i [NeZero i],
    Nonempty (SupportConditionStep i (G j i) (G (j + 1) i) (c j))
  /-- The last family is the moving family's. -/
  terminal : G k = fun i => Fam.globalCx i

/-- The bound `B + 6k + Σ_{j<k} c_j`. Kind: definition. -/
def MovingResidualSteps.bound {Fam : MovingStageFamily W} (R : MovingResidualSteps Fam) : ℕ :=
  R.B + 6 * R.k + ∑ j ∈ Finset.range R.k, R.c j

omit [W.IsElliptic] in
/-- **The moving residual package from the residual steps** (the RC53 group's
`movingResidualPackage_of_cochain_steps`). Kind: PROVED. -/
theorem MovingResidualSteps.package {Fam : MovingStageFamily W} (R : MovingResidualSteps Fam) :
    MovingResidualPackage Fam R.bound :=
  movingResidualPackage_of_cochain_steps R.G (fun i => Fam.globalCx i) R.c R.k R.B R.terminal
    R.base R.step

/-- **The residual steps of the address's family** (tex 3483–3498, 4401–4406, 5056–5062): from a
base family `G₀` (the stage complexes over the old supports `S_i`) with a uniform residual package
of bound `B`, and at every positive stage a support-and-condition step from `G₀ i` to the stage
complex at the enlarged support, adding the new prime with no condition (the full local complex,
allowance `0`). Kind: definition. -/
def AddressMovingFamily.residualSteps {ℓ : ℕ} {h : ℤ} (A : AddressMovingFamily ℓ h W)
    (G₀ : StageComplexFamily) (B : ℕ) (hbase : StageResidualPackage G₀ B)
    (hstep : ∀ i [NeZero i], Nonempty (SupportConditionStep i (G₀ i) (A.Fam.globalCx i) 0)) :
    MovingResidualSteps A.Fam where
  G j := match j with
    | 0 => G₀
    | _ + 1 => fun i => A.Fam.globalCx i
  k := 1
  c _ := 0
  B := B
  base := hbase
  step j hj i _ := by
    obtain rfl : j = 0 := by omega
    exact hstep i
  terminal := rfl

/-- The bound of the address's residual steps is `B + 6`. Kind: PROVED. -/
theorem AddressMovingFamily.residualSteps_bound {ℓ : ℕ} {h : ℤ} (A : AddressMovingFamily ℓ h W)
    (G₀ : StageComplexFamily) (B : ℕ) (hbase : StageResidualPackage G₀ B)
    (hstep : ∀ i [NeZero i], Nonempty (SupportConditionStep i (G₀ i) (A.Fam.globalCx i) 0)) :
    (A.residualSteps G₀ B hbase hstep).bound = B + 6 := by
  simp [MovingResidualSteps.bound, AddressMovingFamily.residualSteps]

/-- **The moving residual package of the address's family** from the old-support base package
and the step at the new prime. Kind: PROVED. -/
theorem AddressMovingFamily.residualPackage {ℓ : ℕ} {h : ℤ} (A : AddressMovingFamily ℓ h W)
    (G₀ : StageComplexFamily) (B : ℕ) (hbase : StageResidualPackage G₀ B)
    (hstep : ∀ i [NeZero i], Nonempty (SupportConditionStep i (G₀ i) (A.Fam.globalCx i) 0)) :
    MovingResidualPackage A.Fam (B + 6) := by
  have h := (A.residualSteps G₀ B hbase hstep).package
  rwa [A.residualSteps_bound] at h

/-- **The moving arithmetic inputs with the residual package from residual steps** (for the
producer `exists_linked_of_moving_inputs`). Kind: definition. -/
def MovingArithmeticInputs.ofSteps {Fam : MovingStageFamily W} {O : MovingOldDualityData Fam}
    (oldFlat : Fam.NontrivialOldFlat) (R : MovingResidualSteps Fam)
    (stage : ∀ i [NeZero i], MovingStageArithmeticInput Fam O i) :
    MovingArithmeticInputs Fam O where
  oldFlat := oldFlat
  bound := R.bound
  residual := R.package
  stage := stage

end ResidualSteps

/-! **The pinned switching inputs** -/

section Pinned

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F]
  {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W] {ℓ : ℕ} {h : ℤ}

variable {W} in
/-- **Inner-limit switching inputs on the address's families** (tex 4976–5195, 5027–5086): the
frame over `Λ_𝔭` and, at each reached configuration with fiber dimension `> 1`, a successor with a
coordinate step and a linked switch on the address's family at that configuration
(`AddressLabelFamily`: the address's old places with their Kummer and full conditions and the
address's characters inflated, the previous derivative labels becoming old places), with side
models (the limit sides' Selmer complexes homotopy equivalent over `k(𝔭)` to the fibres of the
configuration and of its successor). Kind: definition (inputs). -/
structure InnerLimitSwitchPinned (A : AddressMovingFamily ℓ h W)
    (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P))
    (ι : Localization.AtPrime P →+* F) (u : F) extends SwitchModelFrame Φ ι (resAt P) u where
  /-- The linked switches on the address's families, with side models. -/
  step : ∀ c, Reach Φ.next Φ.actual c → 1 < (stage c).fiberDim (resAt P) →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ X : ILStageStepMovingLinked P Cn W hW (stage c) (stage (Φ.next c p)),
        (∃ Lf : AddressLabelFamily A, X.Fam = Lf.Fam) ∧
        Nonempty (HomotopyEquiv (selCx X.stepData.toStep.SF.Dside).toCC
          (selCx (Φ.fibre c)).toCC) ∧
        Nonempty (HomotopyEquiv (selCx X.stepData.toStep.SS.Dside).toCC
          (selCx (Φ.fibre (Φ.next c p))).toCC)

variable {P Cn hW} {W} {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
  {ι : Localization.AtPrime P →+* F} {u : F} {A : AddressMovingFamily ℓ h W}

/-- The moving inputs of the pinned inputs (forgetting the address tie). Kind: PROVED. -/
def InnerLimitSwitchPinned.toMoving (X : InnerLimitSwitchPinned P Cn hW A Φ ι u) :
    InnerLimitSwitchMoving P Cn W hW Φ ι u where
  toSwitchModelFrame := X.toSwitchModelFrame
  step c hc h1 := by
    obtain ⟨p, hcs, Y, -, hF, hS⟩ := X.step c hc h1
    exact ⟨p, hcs, Y, hF, hS⟩

/-- **The actual fibre dimension is the dimension of the pinned fibre**: if the actual fibre is
homotopy equivalent to a complex `G` over `k(𝔭)`, the actual stage's fibre dimension is
`dim H¹(G)`. Kind: PROVED. -/
theorem InnerLimitSwitchPinned.fiberDim_eq_pinned (X : InnerLimitSwitchPinned P Cn hW A Φ ι u)
    (G : GCx (ResAt P)) (e : HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC G.toCC) :
    (X.stage Φ.actual).fiberDim (resAt P) = finrank (ResAt P) (G.toCC.homology 1) := by
  rw [X.toSwitchModelFrame.fiberDim_eq Φ.actual]
  exact ((e.toHomologyIso 1).toLinearEquiv).finrank_eq

/-- **A stationary family forces fibre dimension one**: if no configuration has a proper
successor (`Φ.next c p = c`, as in every one-configuration collapse), the actual stage of pinned
inputs at a height-one prime has fibre dimension exactly one: at least one by the primitive
kernel vector (the class is nonzero, `Λ_𝔭` a DVR), and at most one since a switch would drop it
by two to itself. Kind: PROVED. -/
theorem InnerLimitSwitchPinned.fiberDim_eq_one_of_stationary (hP : P.height = 1)
    (hι : Function.Injective ι) (X : InnerLimitSwitchPinned P Cn hW A Φ ι u)
    (hstat : ∀ c p, Φ.next c p = c) : (X.stage Φ.actual).fiberDim (resAt P) = 1 := by
  have := isDiscreteValuationRing_atPrime_of_height_one P hP
  obtain ⟨PK⟩ := exists_primitiveKernelVector hι (resAt P) (X.stage Φ.actual)
    (X.class_ne_zero Φ.actual Reach.start)
  have h1 := one_le_fiberDim_of_primitiveKernel PK
  by_contra hne
  have hlt : 1 < (X.stage Φ.actual).fiberDim (resAt P) := by omega
  obtain ⟨p, -, Y, -, -, -⟩ := X.step Φ.actual Reach.start hlt
  have hd := Y.stepData.toStep.toNonquadDims.drop
  rw [hstat] at hd
  omega

/-- **The collapse forces the terminal case**: for pinned inputs at a height-one prime over a
stationary family whose actual fibre is homotopy equivalent to the finite fibre of a retained
limit `L`, that fibre has `dim H¹ = 1` (`fiberDim_eq_pinned`, `fiberDim_eq_one_of_stationary`).
Kind: PROVED. -/
theorem InnerLimitSwitchPinned.terminal_of_stationary (hP : P.height = 1)
    {v : FractionRing Lambda} (X : InnerLimitSwitchPinned P Cn hW A Φ (UniformSwitch.toFracAt P) v)
    {Fam : MovingStageFamily W} (L : MovingRetainedLimit Fam)
    (e : HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (L.finiteFibre P).toCC)
    (hstat : ∀ c p, Φ.next c p = c) :
    finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1 :=
  (X.fiberDim_eq_pinned _ e).symm.trans
    (X.fiberDim_eq_one_of_stationary hP (UniformSwitch.toFracAt_injective P) hstat)

/-- **Outside the terminal case a switch on the address's family is required**: if the finite
fibre of the pinned limit has `dim H¹ > 1`, pinned inputs provide at the actual configuration a
successor with a coordinate step and a linked switch on the address's family at the actual
configuration (`AddressLabelFamily`), with side models. Kind: PROVED. -/
theorem InnerLimitSwitchPinned.switch_required (X : InnerLimitSwitchPinned P Cn hW A Φ ι u)
    {Fam : MovingStageFamily W} (L : MovingRetainedLimit Fam)
    (e : HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (L.finiteFibre P).toCC)
    (hgt : 1 < finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1)) :
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (X.stage Φ.actual).u (X.stage (Φ.next Φ.actual p)).u) ∧
      ∃ Y : ILStageStepMovingLinked P Cn W hW (X.stage Φ.actual) (X.stage (Φ.next Φ.actual p)),
        (∃ Lf : AddressLabelFamily A, Y.Fam = Lf.Fam) ∧
        Nonempty (HomotopyEquiv (selCx Y.stepData.toStep.SF.Dside).toCC
          (selCx (Φ.fibre Φ.actual)).toCC) ∧
        Nonempty (HomotopyEquiv (selCx Y.stepData.toStep.SS.Dside).toCC
          (selCx (Φ.fibre (Φ.next Φ.actual p))).toCC) :=
  X.step Φ.actual Reach.start (by rw [X.fiberDim_eq_pinned _ e]; exact hgt)

end Pinned

/-! **The pinned leaf** -/

section Leaf

/-- **The faithful-pin clause at a height-one prime** (tex 4976–5200), for the curve `E_ℓ`, the
twist `h` (`h = h_x`) and the companion `k` (`K = ℚ(√k)`): a configuration family `Φ` genuine at
`𝔭` (GLUE), the
field `K` (quadratic, containing `√k`), places `S`, the actual conjugation and the curve
`W = E_ℓ ⊗ K` with full two-torsion, the address's actual moving stage family `A`, a retained
limit `L` of it and an integral model `Dfin` of its finite side at `𝔭` (the RC53 group's
`IntegralMatrixStageData`: the actual finite-side class and functional), with
* THE FAITHFUL PIN: the actual fibre of `Φ` homotopy equivalent to the finite fibre of `L` at
  `𝔭` (tex 4976–4980, 4385–4451);
* nonquadratic: `InnerLimitSwitchPinned` over `Φ` starting at `u`, whose actual stage is the
  stage of `Dfin` (so its class, functional and coordinate are `Dfin`'s; tex 3877–3892,
  4986–4992); or quadratic (tex 5005–5008): `HomologySwitchDataPK` over `Φ` whose actual stage is
  the stage of `Dfin`.
Kind: definition. -/
def RegularityInputsILPAt (ℓ : ℕ) (h k : ℤ) (u : FractionRing Lambda) (P : Ideal Lambda)
    [P.IsPrime] : Prop :=
    ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
        (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
        (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W),
        W = (Ecurve ℓ).baseChange K ∧ Module.finrank ℚ K = 2 ∧ (∃ sk : K, sk ^ 2 = (k : K)) ∧
        ∃ (A : AddressMovingFamily ℓ h W) (L : MovingRetainedLimit A.Fam)
          (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
            (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
            (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite))),
          Nonempty (HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (L.finiteFibre P).toCC) ∧
          ((∃ X : InnerLimitSwitchPinned P Cn hW A Φ (UniformSwitch.toFracAt P) u,
              X.stage Φ.actual = Dfin.stage) ∨
            (Φ.quadratic (resAt P) ∧
              ∃ G : HomologySwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u,
                G.stage Φ.actual = Dfin.stage))

/-- **The faithful-pin clause for a given configuration family** `Φ` (the body of
`RegularityInputsILPAt` after genuineness; `regularityInputsILPAt_iff`). Kind: definition. -/
abbrev PinnedFamilyAt (ℓ : ℕ) (h k : ℤ) (u : FractionRing Lambda) (P : Ideal Lambda) [P.IsPrime]
    (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
    (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W),
    W = (Ecurve ℓ).baseChange K ∧ Module.finrank ℚ K = 2 ∧ (∃ sk : K, sk ^ 2 = (k : K)) ∧
    ∃ (A : AddressMovingFamily ℓ h W) (L : MovingRetainedLimit A.Fam)
      (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
        (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
        (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite))),
      Nonempty (HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (L.finiteFibre P).toCC) ∧
      ((∃ X : InnerLimitSwitchPinned P Cn hW A Φ (UniformSwitch.toFracAt P) u,
          X.stage Φ.actual = Dfin.stage) ∨
        (Φ.quadratic (resAt P) ∧
          ∃ G : HomologySwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u,
            G.stage Φ.actual = Dfin.stage))

/-- The clause is genuineness and the pinned clause. Kind: PROVED. -/
theorem regularityInputsILPAt_iff (ℓ : ℕ) (h k : ℤ) (u : FractionRing Lambda) (P : Ideal Lambda)
    [P.IsPrime] : RegularityInputsILPAt ℓ h k u P ↔
      ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
        PinnedFamilyAt ℓ h k u P Φ :=
  Iff.rfl

/-- **The regularity inputs with the faithful pin**: `u = 0` (tex 5196–5197; ELLIOT), or the
clause `RegularityInputsILPAt` at every height-one prime `𝔭 ≠ (2)` of `Λ`. Kind: definition. -/
def RegularityInputsILP (ℓ : ℕ) (h k : ℤ) (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
    RegularityInputsILPAt ℓ h k u P

variable {ℓ : ℕ} {h k : ℤ} {u : FractionRing Lambda}

/-- **The pinned inputs give the model-level inputs** (`InnerLimitSwitchPinned.toMoving`,
`InnerLimitSwitchMoving.toInner`, `InnerLimitSwitchModel.toModelInputs`). Kind: PROVED. -/
theorem RegularityInputsILP.toMdl (hI : RegularityInputsILP ℓ h k u) : RegularityInputsMdl u := by
  rcases hI with hI | hI
  · exact Or.inl hI
  · refine Or.inr fun P _ hP hne => ?_
    obtain ⟨Φ, hΦ, K, _, _, S, Cn, W, hW, _, _, -, -, -, A, L, Dfin, -, hb⟩ := hI P hP hne
    refine ⟨Φ, hΦ, ?_⟩
    rcases hb with ⟨X, -⟩ | ⟨hq, G, -⟩
    · exact Or.inl ⟨X.toMoving.toInner.toModelInputs⟩
    · exact Or.inr ⟨hq, ⟨G⟩⟩

/-- `u ∈ Λ[1/2]` from the pinned inputs. Kind: PROVED. -/
theorem RegularityInputsILP.mem_lambdaHalf (hI : RegularityInputsILP ℓ h k u) :
    u ∈ lambdaHalfToFrac.range :=
  hI.toMdl.mem_lambdaHalf

variable (D : RCData ℓ)

/-- **The height-one leaf with the faithful pin** (tex 4976–5200, at the ring instances of the
final field): for every final family `F` and address `x` a `u ∈ Frac Λ` with
`IsTExpansion u (D.uPrim F x)` (tex 3877–3892; GLUE) and `RegularityInputsILP ℓ (F.h x) D.kfin u`
(the twist `h_x`, the companion `k`). Kind: definition. -/
def PrimRegularityInputsILP : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    ∃ u : FractionRing Lambda, IsTExpansion u (D.uPrim F x) ∧
      RegularityInputsILP ℓ (F.h x) D.kfin u

/-- The pinned leaf gives the model-level leaf. Kind: PROVED. -/
theorem PrimRegularityInputsILP.toMdl (hI : PrimRegularityInputsILP D) :
    PrimRegularityInputsMdl D := by
  intro Co Ce F hF x
  obtain ⟨u, hT, hu⟩ := hI Co Ce F hF x
  exact ⟨u, hT, hu.toMdl⟩

/-- **`PrimRegularityInputs` from the pinned leaf** (the form consumed by the base-zero step).
Kind: PROVED. -/
theorem primRegularityInputs_of_ILP (hI : PrimRegularityInputsILP D) : PrimRegularityInputs D :=
  primRegularityInputs_of_Mdl D hI.toMdl

/-- **`RCSteps.height_one`** from the pinned leaf and (4.7). Kind: PROVED (from the inputs). -/
theorem heightOneTarget_of_ILP (hI : PrimRegularityInputsILP D) (h47 : CommonCoordinateTarget D) :
    HeightOneTarget D :=
  heightOneTarget_of_inputs D (primRegularityInputs_of_ILP D hI) h47

/-- **Degenerate satisfiability**: the leaf holds when the primitive coordinates vanish (the
`u = 0` branch). Kind: PROVED. -/
theorem primRegularityInputsILP_of_uPrim_zero (hD : ∀ F x, D.uPrim F x = 0) :
    PrimRegularityInputsILP D :=
  fun _ _ F _ x => ⟨0, by rw [hD F x]; exact isTExpansion_zero, Or.inl rfl⟩

/-- **A stationary family forces fibre dimension one, homology-level data** (as
`InnerLimitSwitchPinned.fiberDim_eq_one_of_stationary`, at every specialization): at least one
by the primitive kernel vector; at most one since a switch to the same configuration would give,
at a nonquadratic specialization, `s' + 2 = s` with `s' = s`, at a quadratic one with both signs,
`s₊' + s₋' + 2 = s₊ + s₋` with equal sign dimensions (`QuadMixedDims.drop`), and with one sign
only, positive dimensions of both signs of the same involution (`QuadSingleDims.result`), against
the case hypothesis. Kind: PROVED. -/
theorem HomologySwitchDataPK.fiberDim_eq_one_of_stationary {P : Ideal Lambda} [P.IsPrime]
    (hP : P.height = 1) {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
    {v : FractionRing Lambda} (G : HomologySwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) v)
    (hstat : ∀ c p, Φ.next c p = c) : (G.stage Φ.actual).fiberDim (resAt P) = 1 := by
  have := isDiscreteValuationRing_atPrime_of_height_one P hP
  obtain ⟨PK⟩ := exists_primitiveKernelVector (UniformSwitch.toFracAt_injective P) (resAt P)
    (G.stage Φ.actual) (G.class_ne_zero Φ.actual Reach.start)
  have h1 := one_le_fiberDim_of_primitiveKernel PK
  by_contra hne
  have hlt : 1 < (G.stage Φ.actual).fiberDim (resAt P) := by omega
  by_cases hmix : ¬ Φ.quadratic (resAt P) ∨
      (0 < finrank (ResAt P) ↥(signPart (G.σ Φ.actual) (1 : ResAt P)) ∧
        0 < finrank (ResAt P) ↥(signPart (G.σ Φ.actual) (-1 : ResAt P)))
  · obtain ⟨p, -, hq, hn⟩ := G.switch_mixed Φ.actual Reach.start hmix hlt
    by_cases q : Φ.quadratic (resAt P)
    · obtain ⟨M, -, -⟩ := hq q
      have hd := (M.X.toQuadMixedDims M.h2 M.ε M.hε M.hJ2 M.ep M.em M.hp M.hm M.he M.hU M.cp
        M.cm M.hcp M.hcm M.hdet).drop
      rw [finrank_signPart_of_equiv M.φ M.hφ, finrank_signPart_of_equiv M.φ M.hφ,
        finrank_signPart_of_equiv M.φ' M.hφ', finrank_signPart_of_equiv M.φ' M.hφ'] at hd
      rw [hstat] at hd
      omega
    · obtain ⟨N, -, -⟩ := hn q
      have hd := N.toNonquadDims.drop
      rw [hstat] at hd
      omega
  · have q : Φ.quadratic (resAt P) := by
      by_contra hq
      exact hmix (Or.inl hq)
    have hnm : ¬ (0 < finrank (ResAt P) ↥(signPart (G.σ Φ.actual) (1 : ResAt P)) ∧
        0 < finrank (ResAt P) ↥(signPart (G.σ Φ.actual) (-1 : ResAt P))) :=
      fun hm => hmix (Or.inr hm)
    obtain ⟨p, -, M, -, -⟩ := G.switch_single Φ.actual Reach.start q hnm hlt
    have hr := (M.X.toQuadSingleDims M.h2 M.ε M.hε M.hJ2 M.ep M.em M.hp M.hm M.he M.hU M.cp
      M.hcp M.hdet M.hs1 M.hs0).result
    apply hnm
    rcases M.hφ' with hφ | hφ
    · rw [finrank_signPart_of_equiv M.φ' hφ, finrank_signPart_of_equiv M.φ' hφ] at hr
      have hpos : 0 < finrank (ResAt P) ↥(signPart (G.σ (Φ.next Φ.actual p)) (1 : ResAt P)) ∧
          0 < finrank (ResAt P) ↥(signPart (G.σ (Φ.next Φ.actual p)) (-1 : ResAt P)) :=
        ⟨hr.2.1, hr.2.2⟩
      rw [hstat] at hpos
      exact hpos
    · rw [finrank_signPart_of_equiv M.φ' hφ, finrank_signPart_of_equiv M.φ' hφ, signPart_neg_eq,
        signPart_neg_eq, neg_neg] at hr
      have hpos : 0 < finrank (ResAt P) ↥(signPart (G.σ (Φ.next Φ.actual p)) (1 : ResAt P)) ∧
          0 < finrank (ResAt P) ↥(signPart (G.σ (Φ.next Φ.actual p)) (-1 : ResAt P)) :=
        ⟨hr.2.2, hr.2.1⟩
      rw [hstat] at hpos
      exact hpos

/-- **The collapse is the terminal case** (tex 4976–4980, 5154–5159): if the pinned clause holds
for a configuration family without proper successors (the shape of every one-stage collapse),
then its actual fibre has `dim H¹ = 1`, and so does the finite fibre at `𝔭` of the retained limit
of the address's actual moving stage family that it is pinned to. In both branches: the
nonquadratic one through `InnerLimitSwitchPinned.fiberDim_eq_one_of_stationary`, the quadratic
one through `HomologySwitchDataPK.fiberDim_eq_one_of_stationary`. Kind: PROVED. -/
theorem PinnedFamilyAt.terminal_of_stationary {P : Ideal Lambda} [P.IsPrime] (hP : P.height = 1)
    {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
    (hΦ : PinnedFamilyAt ℓ h k u P Φ) (hstat : ∀ c p, Φ.next c p = c) :
    finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) = 1 ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
        (Cn : ActualConj K S) (W : WeierstrassCurve K) (_ : W.map (Cn.κ : K →+* K) = W)
        (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W) (A : AddressMovingFamily ℓ h W)
        (L : MovingRetainedLimit A.Fam),
        Nonempty (HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (L.finiteFibre P).toCC) ∧
        finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1 := by
  obtain ⟨K, _, _, S, Cn, W, hW, _, _, -, -, -, A, L, Dfin, ⟨e⟩, hb⟩ := hΦ
  have hA : finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) = 1 := by
    rcases hb with ⟨X, -⟩ | ⟨-, G, -⟩
    · rw [← X.toSwitchModelFrame.fiberDim_eq Φ.actual]
      exact X.fiberDim_eq_one_of_stationary hP (UniformSwitch.toFracAt_injective P) hstat
    · rw [← fiberDim_eq_h1 (ResAt P) (Localization.AtPrime P) (FractionRing Lambda)
        (UniformSwitch.toFracAt P) (resAt P) (G.stage Φ.actual) (Φ.fibre Φ.actual)
        ⟨G.model Φ.actual⟩]
      exact G.fiberDim_eq_one_of_stationary hP hstat
  refine ⟨hA, K, inferInstance, inferInstance, S, Cn, W, hW, inferInstance, inferInstance, A, L,
    ⟨e⟩, ?_⟩
  rw [← hA]
  exact ((e.toHomologyIso 1).toLinearEquiv).finrank_eq.symm

end Leaf

end ZInQ.Manuscript.RC.Wiring
