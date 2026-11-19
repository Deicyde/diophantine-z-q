import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitCertificate
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.DerivativeOrthogonal

/-!
# RC53 SwitchInputs: the switch steps from the inner-limit objects and RC31's certificate

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex L4976–5195), the switch at a
derivative label (tex L5027–5086), Lemma `ex:limits-inner-limit` (tex L4391–4451): the switch is
taken on the inner-limit objects along derivative labels with `q → 1` (tex L3298–3300, L5030–5032),
not on one fixed characteristic-zero fibre (`DerivativeOrthogonal.lean`, finding (3); `UnrCoords`).

The inner-limit switching objects (`RC53Assist.InnerLimit.Objects`: `fibreLimitGlobal`,
`limitRelaxed`, the finite and singular limit sides, `fibreLimitNonquadStep`) produce a
`QuasiNonquadStep (resAt 𝔭)` from the duality `FibreInnerLimitDuality`; lane RC31's certificate
(`RC/FibreDuality/LimitCertificate.lean`) produces that duality from retained stage data. This file
composes the two and feeds the result into the chain's family consumer.

* `innerLimitNonquadStep'` (PROVED wiring, any `J` with `J² = 1`) and `innerLimitNonquadStep`
  (`J = ρ_T(τ)`, `conjMatrix`): a `QuasiNonquadStep (resAt 𝔭) S₀ S₁` from the retained stage data
  `D : RetainedLimitPairingStages`, `E : RetainedGlobalDualityStages D` (ELLIOT, tex
  L4391–4451, with Nekovář 5.4.3 at the Gorenstein stages), the retained local identity (`hb11`,
  `h20`, resp. `hloc`, tex L5037, L4866), the detection `F ≤ U` (`hdet`) and the side–stage
  isomorphisms `φ`, `φ'` — all explicit inputs.
* `InnerLimitStepData` (hypothesis structure: the inputs of `innerLimitNonquadStep'` at one switch,
  with their own ultrafilter and stage complexes), `InnerLimitStepData.toStep`.
* `InnerLimitSwitchInputs` (hypothesis structure) for a nonquadratic switching family over `k(𝔭)`:
  stage models of the family's fibres, the starting link, primitivity, and at each reachable
  configuration of fibre dimension `> 1` a prime with a coordinate step and inner-limit step data
  whose side Selmer data ARE the family's fibres (`hF`, `hS`: the side-to-stage identification,
  explicit). `InnerLimitSwitchInputs.toGalois` (PROVED): the chain's `GaloisSwitchData`;
  `regular_of_innerLimitSwitchInputs` (PROVED): `∃ a, ι a = u`.
* **`hold` in the inner limit.** `hold` (`DerivativeOrthogonal.lean`) is a statement about the
  genuine fixed-place switch `galRelSwitch` (per-place self-orthogonality of the old conditions);
  it has no counterpart to instantiate here: on the inner-limit route the Selmer duality
  quasi-isomorphism of the limit diagram is supplied whole by RC31's certificate (retained global
  duality `E` and the retained local identity at the derivative label), which replaces both `hq`
  and `hold`. What survives of the fixed-fibre obstruction is the shape of the local planes, and in
  the limit it is the right one: `switchPairing_finPlane_isotropic`,
  `switchPairing_singPlane_isotropic` and `switchPairing_singPlane_orthogonal` (PROVED): both
  planes are isotropic for the limit local pairing and the singular plane is its own orthogonal
  complement in `F ⊕ S` (Lagrangian), whereas at a fixed characteristic-zero fibre `H¹` of the
  singular side vanishes (finding (3) of `DerivativeOrthogonal.lean`).

The family structure requires the side Selmer data of the limit steps to EQUAL the family's fibres
(`GaloisSwitchData`); the inner-limit objects do not provide such identifications (their global
and local diagram are abstract), so `hF`, `hS` and the retained data are inputs to be supplied by
the realization (side-to-stage equivalences and the arithmetic Galois/cochain comparisons).

Kinds: definitions (hypothesis structures, GLUE inputs) and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Filter ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Manuscript.RC.FibreDuality (RetainedLimitPairingStages RetainedGlobalDualityStages
  fibreInnerLimitPairingCertificate_of_retained' fibreInnerLimitDuality_of_retained conjMatrix
  conjMatrix_mul_self transportedPairing localPairingOfMat)
open ZInQ.Manuscript.RC.Limits (stageIdeal)
open ZInQ.Manuscript.RC.Uniform (Lambda switchPairing crossPairing crossPairing_isPerfPair finPlane
  singPlane planePairing_apply)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open NumberField

/-! ### One switch step from the retained data -/

section Step

variable {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
  {C : ComplexStages (R := Lambda) stageIdeal U} {D : RetainedLimitPairingStages U C}
  (E : RetainedGlobalDualityStages D) (P : Ideal Lambda) [P.IsPrime]
  {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}

/-- **A switch step on the inner-limit objects from the retained stage data, any `J`** (tex
L5027–5086 with L4391–4451): the inner-limit `QuasiNonquadStep (resAt 𝔭) S₀ S₁` of the realized
diagram (`fibreLimitNonquadStep` at the retained localization `D.resLimit hU 𝔭`), its duality from
RC31's `fibreInnerLimitPairingCertificate_of_retained'`. Classification: PROVED (wiring, from the
explicit inputs). -/
def innerLimitNonquadStep' (S₀ S₁ : TwoTermStage ι) (ε σ : ResAt P)
    (J : Matrix (Fin 2) (Fin 2) (ResAt P)) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ : J * J = 1)
    (hb11 : ∀ x y, (localPairingOfMat (D.locK P)).b11 x y = -(switchPairing ε σ J y x))
    (h20 : Function.Bijective (localPairingOfMat (D.locK P)).b20)
    (hdet : finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
      (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).U)
    (φ : (selCx (finiteLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside).toCC.homology
      1 ≃ₗ[ResAt P] fiberH1 (resAt P) S₀)
    (φ' : (selCx (singularLimitSide (fibreLimitGlobal U hU P C)
      (D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) S₁) :
    QuasiNonquadStep (resAt P) S₀ S₁ :=
  fibreLimitNonquadStep U hU P C (D.resLimit hU P) S₀ S₁ ε σ J hε hσ hJ
    (fibreInnerLimitDuality_of_certificate U hU P C (D.resLimit hU P) ε σ J hε hσ hJ
      (fibreInnerLimitPairingCertificate_of_retained' hU E P ε σ J hε hσ hJ hb11 h20))
    hdet φ φ'

variable {K : Type} [Field K] [NumberField K] {S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **A switch step on the inner-limit objects for the realized diagram** (`J = ρ_T(τ)`): as
`innerLimitNonquadStep'`, with the duality from RC31's `fibreInnerLimitDuality_of_retained` (the
retained local pairing is the transported one, `hloc`, tex L5037). Classification: PROVED (wiring,
from the explicit inputs). -/
def innerLimitNonquadStep (S₀ S₁ : TwoTermStage ι) (ε₀ ε₂ ε σ : ResAt P) (hε₂ : ε₂ ≠ 0)
    (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hloc : localPairingOfMat (D.locK P) =
      transportedPairing ε₀ ε₂ ε σ (conjMatrix Cn W hW P))
    (hdet : finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
      (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).U)
    (φ : (selCx (finiteLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside).toCC.homology
      1 ≃ₗ[ResAt P] fiberH1 (resAt P) S₀)
    (φ' : (selCx (singularLimitSide (fibreLimitGlobal U hU P C)
      (D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) S₁) :
    QuasiNonquadStep (resAt P) S₀ S₁ :=
  fibreLimitNonquadStep U hU P C (D.resLimit hU P) S₀ S₁ ε σ (conjMatrix Cn W hW P) hε hσ
    (conjMatrix_mul_self Cn W hW P)
    (fibreInnerLimitDuality_of_retained hU E P Cn W hW ε₀ ε₂ ε σ hε₂ hε hσ hloc) hdet φ φ'

end Step

/-! ### The family consumer -/

section Family

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}

/-- **The inner-limit data of one switch step** (tex L4391–4451, L5027–5086): an ultrafilter
`U ≤ cofinite`, retained stage complexes `C` and retained pairing and global-duality data `D`, `E`
(ELLIOT), the retained local identity (`hb11`, `h20`) with scalars `ε, σ ≠ 0` and `J² = 1`, the
detection `F ≤ U` and the side–stage isomorphisms. Classification: hypothesis (structure); its
instances are to come from the realization (actual derivative primes, retained comparisons).
Non-vacuity of the duality half: RC31's labelled toy instance (`LimitNonVacuity.lean`). -/
structure InnerLimitStepData (S₀ S₁ : TwoTermStage ι) where
  /-- The ultrafilter of the inner limit. -/
  U : Ultrafilter ℕ
  hU : (U : Filter ℕ) ≤ cofinite
  /-- The retained stage complexes. -/
  C : ComplexStages (R := Lambda) stageIdeal U
  /-- The retained pairing data. -/
  D : RetainedLimitPairingStages U C
  /-- The retained global duality. -/
  E : RetainedGlobalDualityStages D
  ε : ResAt P
  σ : ResAt P
  /-- The local matrix `J`. -/
  J : Matrix (Fin 2) (Fin 2) (ResAt P)
  hε : ε ≠ 0
  hσ : σ ≠ 0
  hJ : J * J = 1
  /-- The retained residue identity at the derivative label (tex L5037). -/
  hb11 : ∀ x y, (localPairingOfMat (D.locK P)).b11 x y = -(switchPairing ε σ J y x)
  /-- `D⁰` and `D²` are dual (tex L4866). -/
  h20 : Function.Bijective (localPairingOfMat (D.locK P)).b20
  /-- Detection `F ≤ U`. -/
  hdet : finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
    (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).U
  /-- The finite side and the stage `S₀`. -/
  φ : (selCx (finiteLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside).toCC.homology
    1 ≃ₗ[ResAt P] fiberH1 (resAt P) S₀
  /-- The singular side and the stage `S₁`. -/
  φ' : (selCx (singularLimitSide (fibreLimitGlobal U hU P C)
    (D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) S₁

variable {P}

/-- The switch step of inner-limit step data. Classification: PROVED (`innerLimitNonquadStep'`). -/
def InnerLimitStepData.toStep {S₀ S₁ : TwoTermStage ι} (X : InnerLimitStepData P S₀ S₁) :
    QuasiNonquadStep (resAt P) S₀ S₁ :=
  innerLimitNonquadStep' X.hU X.E P S₀ S₁ X.ε X.σ X.J X.hε X.hσ X.hJ X.hb11 X.h20 X.hdet X.φ X.φ'

variable (P)

/-- **Nonquadratic switching inputs on the inner-limit objects** (tex L4976–5195) for a switching
family `Φ` over `k(𝔭)`: stage models of the family's fibres, the starting link to the actual class,
functional and coordinate, nonquadraticity, primitivity, and at each reachable configuration with
fibre dimension `> 1` a prime with a coordinate step and inner-limit step data whose side Selmer
data are the family's fibres (`hF`, `hS`). Classification: GLUE (inputs). No non-vacuity instance
here: it is a conditional interface whose instances need the realization (retained data at actual
derivative primes and the side-to-stage identifications). -/
structure InnerLimitSwitchInputs (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P))
    (ι : Localization.AtPrime P →+* F) (u : F) where
  /-- The stage two-term models. -/
  stage : Φ.Config → TwoTermStage ι
  /-- Each stage models the family's fibre. -/
  model : ∀ c, HomotopyEquiv (selCx (Φ.fibre c)).toCC (twoTermFiberComplex (resAt P) (stage c))
  /-- The actual class. -/
  hz0 : ((model Φ.actual).hom.f 1).hom Φ.zAct = fun i => resAt P ((stage Φ.actual).z i)
  /-- The actual paired functional. -/
  hw0 : ∀ y, Φ.lamAct y = (fun i => resAt P ((stage Φ.actual).w i)) ⬝ᵥ
    (((model Φ.actual).hom.f 2).hom y : Fin _ → ResAt P)
  /-- The actual coordinate. -/
  hu0 : (stage Φ.actual).u = u
  /-- The specialization is nonquadratic. -/
  hnq : ¬ Φ.quadratic (resAt P)
  /-- Primitivity of the stage classes. -/
  primitive : ∀ c, Reach Φ.next Φ.actual c → ∃ i, resAt P ((stage c).z i) ≠ 0
  /-- The inner-limit switch steps, with sides the family's fibres. -/
  step : ∀ c, Reach Φ.next Φ.actual c → 1 < (stage c).fiberDim (resAt P) →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ X : InnerLimitStepData P (stage c) (stage (Φ.next c p)),
        X.toStep.SF.Dside = Φ.fibre c ∧ X.toStep.SS.Dside = Φ.fibre (Φ.next c p)

variable {P} {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {u : F}

/-- **The chain's `GaloisSwitchData` from the inner-limit inputs** (tex L4976–5195): the
nonquadratic switch field from `InnerLimitStepData.toStep`; the quadratic fields are vacuous
(`hnq`), with the identity involutions. Classification: PROVED. -/
def InnerLimitSwitchInputs.toGalois (X : InnerLimitSwitchInputs P Φ ι u) :
    GaloisSwitchData Φ ι (resAt P) u where
  stage := X.stage
  model := X.model
  hz0 := X.hz0
  hw0 := X.hw0
  hu0 := X.hu0
  σ := fun _ => LinearMap.id
  h2 := fun hq => absurd hq X.hnq
  hσ := fun hq => absurd hq X.hnq
  primitive := X.primitive
  switch_mixed c hc _ h1 := by
    obtain ⟨p, hcs, Y, hF, hS⟩ := X.step c hc h1
    exact ⟨p, hcs, fun hq => absurd hq X.hnq, fun _ => ⟨Y.toStep, hF, hS⟩⟩
  switch_single _ _ hq := absurd hq X.hnq

/-- **Regularity from the inner-limit inputs** (tex L4976–5195): `∃ a, ι a = u`, through
`regular_of_galoisSwitchData'`. Classification: PROVED (from the inputs of
`InnerLimitSwitchInputs`, hence from RC31's certificate and the retained data). -/
theorem regular_of_innerLimitSwitchInputs (hι : Function.Injective ι)
    (X : InnerLimitSwitchInputs P Φ ι u) : ∃ a, ι a = u :=
  regular_of_galoisSwitchData' hι (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).mpr hx)
    X.toGalois

end Family

/-! ### The local planes in the limit are Lagrangian -/

section Planes

variable {k : Type} [Field k]

/-- The finite plane `F ⊕ 0` is isotropic for the local switch pairing. PROVED. -/
theorem switchPairing_finPlane_isotropic (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k)
    {x y : (Fin 2 → k) × (Fin 2 → k)} (hx : x ∈ finPlane k (Fin 2 → k) (Fin 2 → k))
    (hy : y ∈ finPlane k (Fin 2 → k) (Fin 2 → k)) : switchPairing ε σ J x y = 0 := by
  obtain ⟨-, hx2⟩ := Submodule.mem_prod.mp hx
  obtain ⟨-, hy2⟩ := Submodule.mem_prod.mp hy
  rw [Submodule.mem_bot] at hx2 hy2
  rw [planePairing_apply, hx2, hy2, map_zero, map_zero, mul_zero, add_zero]

/-- The singular plane `0 ⊕ S` is isotropic for the local switch pairing. PROVED. -/
theorem switchPairing_singPlane_isotropic (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k)
    {x y : (Fin 2 → k) × (Fin 2 → k)} (hx : x ∈ singPlane k (Fin 2 → k) (Fin 2 → k))
    (hy : y ∈ singPlane k (Fin 2 → k) (Fin 2 → k)) : switchPairing ε σ J x y = 0 := by
  obtain ⟨hx1, -⟩ := Submodule.mem_prod.mp hx
  obtain ⟨hy1, -⟩ := Submodule.mem_prod.mp hy
  rw [Submodule.mem_bot] at hx1 hy1
  rw [planePairing_apply, hx1, hy1]
  simp

/-- **The singular plane is its own orthogonal complement** for the local switch pairing (`ε ≠ 0`,
`J² = 1`): `x ⊥ (0 ⊕ S)` iff `x ∈ 0 ⊕ S` (a Lagrangian of the four-dimensional `F ⊕ S`; the shape
of the inner limit, `q → 1`). PROVED. -/
theorem switchPairing_singPlane_orthogonal {ε : k} (hε : ε ≠ 0) (σ : k)
    {J : Matrix (Fin 2) (Fin 2) k} (hJ : J * J = 1) (x : (Fin 2 → k) × (Fin 2 → k)) :
    (∀ y ∈ singPlane k (Fin 2 → k) (Fin 2 → k), switchPairing ε σ J x y = 0) ↔
      x ∈ singPlane k (Fin 2 → k) (Fin 2 → k) := by
  refine ⟨fun h => ?_, fun hx y hy => switchPairing_singPlane_isotropic ε σ J hx hy⟩
  have h1 : crossPairing ε J x.1 = 0 := by
    refine LinearMap.ext fun d => ?_
    have := h (0, d) (Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, Submodule.mem_top⟩)
    rw [planePairing_apply, map_zero, LinearMap.zero_apply, mul_zero, add_zero] at this
    exact this
  have := crossPairing_isPerfPair hε hJ
  have hx1 : x.1 = 0 :=
    (LinearMap.IsPerfPair.bijective_left (crossPairing ε J)).injective
      (h1.trans (map_zero (crossPairing ε J)).symm)
  exact Submodule.mem_prod.mpr ⟨(Submodule.mem_bot k).mpr hx1, Submodule.mem_top⟩

end Planes

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
