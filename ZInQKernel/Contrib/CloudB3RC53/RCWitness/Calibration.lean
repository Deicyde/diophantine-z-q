import ZInQKernel.Contrib.OneProof.RC.Wiring.Leaves
import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.NonVacuity
import ZInQKernel.Contrib.OneProof.RC.Height.NonVacuity

/-!
# RC inhabitability witnesses, group B: calibration, common coordinate, base zero

Witnesses for the structures carried by `PostLeaves.calibration` (`CalibrationInputsC`),
`PostLeaves.common_coordinate` (`CommonCoordinateInputsT`) and `PostLeaves.base_zero`
(`BaseZeroAssembly.BaseZeroLeafInputs`). Nothing here is used by the proof; the file only checks
that the fields of these structures can hold together.

* `finalFamilyAt_trivial`: the trivial family (`b = 0`, `Q = ∅`) satisfies `FinalFamilyAt` for every
  `D`, so each leaf of the form `∀ F, FinalFamilyAt → …` must hold at its address `0` (`h₀ = 1`).
* `exD`: interface data with `kfin = −1`, `u_prim = 1`, `ũ = η · 4` (one graph prime).
* `exTriangles`, `commonCoordinateInputsT_exD`: `CommonCoordinateTriangles` with one relaxation
  step (batch 3's `actualStep_example`), at every address; so `CommonCoordinateInputsT exD` holds,
  non-vacuously.
* `triangles_empty`: with `Q = ∅` the structure exists for every `D` with `ũ = u_prim`.
* `calibrationModelC_of_milne`: every field of `CalibrationModelC` except `hmilne` built at the
  trivial family, with `hmilne` (Cassels–Milne at the genuine Néron–Tate heights) as the one
  hypothesis.
* `exStage`, `exBoundary`, `exCore`: `SplitNormStage`, `Boundary45Base`, `BaseZeroCore` inhabited.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RCWitness.Calibration

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
  ZInQ.Manuscript.RC.Central ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate

abbrev PS : Type := PowerSeries ℚ_[2]

/-! ### The trivial family -/

/-- The trivial family: no address bits, no primes. -/
def trivFam : Family := ⟨0, ∅, fun _ => 0⟩

theorem finalFamilyAt_trivial {ℓ : ℕ} (D : RCData ℓ) (Co Ce : ℤ) : D.FinalFamilyAt Co Ce trivFam :=
  ⟨fun q hq => absurd hq (Finset.notMem_empty q), fun _ hx => absurd (funext fun i => i.elim0) hx⟩

/-! ### One graph prime -/

/-- The quotient factor of the step (`F = 1`, `q = 1`, `z = z⁻¹ = 2`). -/
def lEx : PS := quotientFactor (1 : Matrix (Fin 2) (Fin 2) PS) (PowerSeries.C ((1 : ℕ) : ℚ_[2])⁻¹)
  2 2

/-- The inverse of the point factor `2 − 2 − 2 = −2`. -/
def eiEx : PS := PowerSeries.C (-1 / 2 : ℚ_[2])

/-- `v` with `l e⁻² = 1 + 2 v`. -/
def vEx : PS := PowerSeries.C (1 / 2 : ℚ_[2]) * (lEx * eiEx ^ 2 - 1)

/-- The example data: `kfin = −1`, `u_prim = 1`, `ũ = η · 4` with `η` at the graph prime `5`. -/
def exD : RCData 1 where
  S := ∅
  prepared _ := True
  Lstar _ := 1
  jgen _ := 0
  jrc _ _ := 0
  hstar := -7
  stages := pure 0
  Mθ _ := 0
  aθ _ _ := 0
  admissible _ _ := False
  δo := 0
  kfin := -1
  uPrim _ _ := 1
  uTilde _ _ := eta ({5} : Finset ℕ) (fun _ => vEx) (fun _ => 1) * 4

theorem two_mul_C_half : (2 : PS) * PowerSeries.C (1 / 2 : ℚ_[2]) = 1 := by
  rw [show (2 : PS) = PowerSeries.C (2 : ℚ_[2]) from (map_ofNat PowerSeries.C 2).symm, ← map_mul]
  norm_num

theorem pointFactor_mul_eiEx : pointFactor (2 : PS) 2 2 * eiEx = 1 := by
  rw [pointFactor, eiEx, show (2 : PS) - 2 - 2 = -2 by ring,
    show (-2 : PS) = PowerSeries.C (-2 : ℚ_[2]) by rw [map_neg, map_ofNat], ← map_mul]
  norm_num

theorem actualStep_ex :
    ActualStep (1 : Matrix (Fin 2) (Fin 2) PS) (PowerSeries.C ((1 : ℕ) : ℚ_[2]))
      (PowerSeries.C ((1 : ℕ) : ℚ_[2])⁻¹) 2 2 2 1 4 1 LamUnit LamUnit := by
  simpa using actualStep_example

/-- **`CommonCoordinateTriangles` with one relaxation step**, at every address of every family. -/
def exTriangles (F : Family) (x : Addr F.b) : CommonCoordinateTriangles exD F x where
  R := PS
  chi := RingHom.id PS
  Q := {5}
  v _ := vEx
  g _ := 1
  l _ := lEx
  e _ := pointFactor 2 2 2
  ei _ := eiEx
  hsign _ _ := Or.inl rfl
  hratio _ _ := by
    change lEx * eiEx ^ 2 = 1 + 2 * (PowerSeries.C (1 / 2 : ℚ_[2]) * (lEx * eiEx ^ 2 - 1))
    rw [← mul_assoc, two_mul_C_half]; ring
  hinv _ _ := pointFactor_mul_eiEx
  urel := 4
  U := {5}
  hU q := by simp
  hutilde := rfl
  qn _ := 1
  hodd _ _ := odd_one
  F _ := 1
  a _ := 2
  z _ := 2
  zi _ := 2
  ha _ _ := by simp [Matrix.trace_one]
  hd _ _ := by simp
  hl _ _ := rfl
  he _ _ := rfl
  u T := if 5 ∈ T then 4 else 1
  hrel := by simp
  hprim := by simp [exD]
  eps _ := 1
  hstep T hT p hp hpT := by
    have hp5 : p = 5 := Finset.mem_singleton.mp hp
    subst hp5
    have hT0 : T = ∅ := by
      ext q
      constructor
      · intro hq
        have := Finset.mem_singleton.mp (hT hq)
        subst this
        exact absurd hq hpT
      · simp
    subst hT0
    simpa using actualStep_ex

/-- **`CommonCoordinateInputsT exD`** (non-vacuous: one relaxation step at every address). -/
theorem commonCoordinateInputsT_exD : CommonCoordinateInputsT exD :=
  fun _ _ F _ x => ⟨exTriangles F x⟩

/-- With no graph primes the structure exists for every `D` with `ũ = u_prim`. -/
def triangles_empty {ℓ : ℕ} (D : RCData ℓ) (F : Family) (x : Addr F.b)
    (h : D.uTilde F x = D.uPrim F x) : CommonCoordinateTriangles D F x where
  R := PS
  chi := RingHom.id PS
  Q := ∅
  v _ := 0
  g _ := 1
  l _ := 0
  e _ := 0
  ei _ := 0
  hsign _ hq := absurd hq (Finset.notMem_empty _)
  hratio _ hq := absurd hq (Finset.notMem_empty _)
  hinv _ hq := absurd hq (Finset.notMem_empty _)
  urel := D.uPrim F x
  U := ∅
  hU q := by simp
  hutilde := by rw [h]; simp [eta]
  qn _ := 1
  hodd _ hp := absurd hp (Finset.notMem_empty _)
  F _ := 1
  a _ := 2
  z _ := 0
  zi _ := 0
  ha _ hp := absurd hp (Finset.notMem_empty _)
  hd _ hp := absurd hp (Finset.notMem_empty _)
  hl _ hp := absurd hp (Finset.notMem_empty _)
  he _ hp := absurd hp (Finset.notMem_empty _)
  u _ := D.uPrim F x
  hrel := rfl
  hprim := rfl
  eps _ := 1
  hstep _ _ _ hp := absurd hp (Finset.notMem_empty _)

/-! ### `CalibrationModelC` at the trivial family, conditional on Cassels–Milne -/

section Calib

open ZInQ.Manuscript.RC.Height

/-- The Frobenius of the example: trace `3`, determinant `1`. -/
def FmovEx : Matrix (Fin 2) (Fin 2) ℚ_[2] := !![3, -1; 1, 0]

/-- `2^{s(E) + s(E^{(−1)})}`, the order of `Ш(ℬ)[2^∞]` in the example. -/
def shaBEx : ℕ :=
  2 ^ (shaLength (Etw 1 (trivFam.h 0)) + shaLength (Etw 1 (trivFam.h 0 * exD.kfin)))

instance : (Ecurve 1).IsElliptic := ZInQ.Manuscript.RC.Nonvanishing.curve_nat_isElliptic one_pos

/-- **`CalibrationModelC` at the trivial family**: every field but `hmilne` is constructed
(`kfin = −1`, so the conditions at `p ∣ k` are empty; `K = ℚ(i)`; the moving prime `r = 1`,
`a_r = 3`, `χ = 1`, `c_E = 0`, `B = 1`; the Kummer model `D_K = (0)` with `z = λ = u_K = 1`;
the quotient block empty), and `hmilne` is the one hypothesis: Cassels–Milne at the genuine
Néron–Tate heights with `|Ш(𝒜)| = |tors| = 1`, `|Ш(ℬ)| = shaBEx`, trivial component numbers and
the period ratio `2`. -/
def calibrationModelC_of_milne
    (hm : ∀ (gA : ((qtwist (Ecurve 1) (trivFam.h 0 : ℚ)).baseChange GaussField).toAffine.Point)
      (gB : ((qtwist (Ecurve 1) (trivFam.h 0 : ℚ)).baseChange ℚ).toAffine.Point ×
        ((qtwist (Ecurve 1) ((trivFam.h 0 : ℚ) * (exD.kfin : ℚ))).baseChange ℚ).toAffine.Point),
      IsFreeGenerator gA → IsFreeGenerator gB →
      MilneIsogenyInvariance 1 shaBEx 1 1 1 1 1 1 gA.canonicalHeight
        (heightB (Ecurve 1) (trivFam.h 0 : ℚ) (exD.kfin : ℚ) gB) 1 ((2 : ℚ) * 1)) :
    CalibrationModelC exD 0 0 trivFam 0 where
  shaA := 1
  shaB := shaBEx
  tA := 1
  tB := 1
  shaA_ne := one_ne_zero
  shaB_ne := by unfold shaBEx; positivity
  tA_ne := one_ne_zero
  tB_ne := one_ne_zero
  Scomp := ∅
  cA _ := 1
  cB _ := 1
  hTS := by simp [exD]
  hcpos _ _ := one_pos
  hcancel _ _ _ := rfl
  hA1 _ hp := by simp [exD] at hp
  kres _ := ℚ
  Wred _ := Ecurve 1
  h2 _ hp := by simp [exD] at hp
  hEdix _ hp := by simp [exD] at hp
  K := GaussField
  quad := by simpa [exD] using GaussField.quadData
  aPull := 2
  bPull := 2
  hab := by norm_num
  gam := 1
  kap := 1
  hgam := by norm_num
  hkap := by norm_num
  OmA := 1
  hOmA := one_ne_zero
  rhoOm := 2
  hcv := by norm_num
  hmilne gA gB hA hB := by simpa using hm gA gB hA hB
  hsB := by simp [shaBEx]
  hgB := by simp
  rmov := 1
  amov := 3
  chimov := 1
  Bexp := 1
  cE := 0
  hchi := Or.inl rfl
  hrmov := by norm_num
  hnd := by norm_num
  hcB := le_refl _
  nK := 1
  κ := Fin 0
  DK := 0
  X := 0
  DW := 0
  zK _ := 1
  wK _ := 1
  zP _ := 1
  wP _ := 1
  uK := 1
  hz _ := rfl
  hw _ := rfl
  hP := by
    unfold IsCoordOn
    ext (i | i) (j | j)
    · fin_cases i; fin_cases j
      rw [adjugate_subsingleton]
      simp [exD, vecMulVec_apply]
    all_goals first | exact i.elim0 | exact j.elim0
  hKc := by
    unfold IsClassFunctionalCoord
    ext i j; fin_cases i; fin_cases j
    simp [adjugate_fin_one, vecMulVec_apply]
  hadj := by rw [adjugate_fin_one]; exact one_ne_zero
  hK := by simp [exD, central, v2, diskContribution]
  Fmov := FmovEx
  hFtr := by simp [FmovEx, Matrix.trace_fin_two]
  hFdet := by simp [FmovEx, Matrix.det_fin_two]
  hcentralW := by
    rw [det_fromBlocks_zero₂₁, det_smul, det_one, mul_one, Fintype.card_fin, twoPlaceBlock,
      det_fromBlocks_zero₂₁]
    simp [central, FmovEx, Matrix.det_fin_two, omega]
    norm_num

end Calib

/-! ### The base-zero core -/

section BaseZero

open ZInQ.Manuscript.RC.BaseZeroAssembly ZInQ.Manuscript.RC.Rings Filter Topology

/-- A trivial finite stage over `E(K) = ℤ`, `P = 1`: `Δ` trivial, `a_r = 3`, so (4.1) reads
`y_r = 3 y₁ − y₁ − y₁`. -/
def exStage : SplitNormStage (1 : ℤ) where
  Pt := ℤ
  Δ := Unit
  act := 1
  N := ⊤
  decN := fun _ => isTrue trivial
  T := Finset.univ
  hT _ := ⟨(), by simp, fun _ _ => rfl⟩
  y1 := 1
  hy1 _ _ := rfl
  yr := 1
  a := 3
  σ := 1
  hnorm := by simp
  incl := AddMonoidHom.id ℤ
  hincl := Function.injective_id
  hP := by simp
  W := 1
  hW := by simp

/-- The central Kummer comparison `n ↦ (n)`. -/
def exKappa : ℤ →+ (Fin 1 → ℚ_[2]) := zmultiplesHom (Fin 1 → ℚ_[2]) (fun _ => 1)

/-- **`Boundary45Base` inhabited** (constant stages, `L = 1`, `z̄ = (1)`). -/
def exBoundary : Boundary45Base (1 : ℤ) 1 (fun _ => rhoT 1) where
  stage _ := exStage
  L := 1
  hL := one_ne_zero
  kappa := exKappa
  hlim := by
    have : (fun _ : ℕ => ((1 : ℤ) : ℚ_[2]) • exKappa exStage.W) = fun _ => fun _ => rhoT 1 := by
      funext n i
      simp [exKappa, exStage]
    rw [this]
    exact tendsto_const_nhds

/-- The model complex: `Λ_(t)` in every degree, zero differentials. -/
def exCU : CochainComplex (ModuleCat.{0} LambdaT) ℤ where
  X _ := ModuleCat.of LambdaT (Fin 1 → LambdaT)
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

/-- **`BaseZeroCore` inhabited** (the `1 × 1` model `D = (0)` with central dimensions `(1,1)`, cycle
and functional `1`, coordinate `1`), for the data `exD` at the trivial family. -/
def exCore : BaseZeroCore exD trivFam (1 : ℤ) where
  m := 0
  Dm := 0
  hcentral := by simp
  z _ := 1
  hz := by simp
  CU := exCU
  e1 := LinearEquiv.refl _ _
  e2 := LinearEquiv.refl _ _
  hd _ := by
    change (0 : Fin 1 → LambdaT) = 0 *ᵥ _
    simp
  lam := LinearMap.proj 0
  hlam _ := rfl
  uprim := 1
  hu w _ hw := by
    have h0 := hw (Pi.single 0 1)
    change (Pi.single 0 1 : Fin 1 → LambdaT) 0 = w ⬝ᵥ Pi.single 0 1 at h0
    simp at h0
    unfold IsClassFunctionalCoord
    ext i j; fin_cases i; fin_cases j
    simp [vecMulVec_apply, adjugate_fin_one, ← h0]
  boundary := exBoundary
  hprimId := by simpa [exD] using isTExpansion_algebraMap 1

end BaseZero

end ZInQ.Contrib.CloudB3RC53.RCWitness.Calibration
