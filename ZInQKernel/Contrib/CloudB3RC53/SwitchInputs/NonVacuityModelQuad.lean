import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.SwitchData
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.NonVacuityQuad

/-!
# RC53 SwitchInputs: non-vacuity of the quadratic step bundles of `SelmerModelSwitchData`

LESSON 2 for `SwitchData.lean` (tex L4976–5195, the quadratic switches L5003–5136): genuine
instances of the quadratic step bundles `MixedModelStep` and `SingleModelStep`, and a
`SelmerModelSwitchData` with an actual quadratic switch, built on the Selmer-level examples
`exQuadMixedStep` and `exQuadSingleStep` of `NonVacuityQuad.lean`.

The equivariant fiber isomorphisms are produced as follows. Every stage used here is a two-term
model with zero differential, so its fiber cohomology has dimension the matrix size
(`fiberDim_zero_matrix`). A linear isomorphism `φ : V ≃ fiberH1 S` of the Selmer side cohomology
`V` with the stage fiber exists as soon as the dimensions agree (`fiberEquivOf`); the stage
involution is then the transport `φ σ_V φ⁻¹` (`transportInv`), for which `φ` is equivariant by
construction (`transportInv_comm`) and which is again an involution (`transportInv_sq`).

Nodes (PROVED):
* `mixedModelStepOf`, `singleModelStepOf`: the quadratic step bundles from a Selmer-level step
  and stages of the matching fiber dimensions.
* `exMixedModelStep`: `MixedModelStep` from `exQuadMixedStep` (fiber dimensions three and one).
* `exSingleModelStep`: `SingleModelStep` from `exQuadSingleStep` (zero-differential stages of the
  dimensions of the two sides).
* `exQuadModelSwitchData`: a quadratic `SelmerModelSwitchData` whose stage of fiber dimension three
  carries both cohomology signs and switches (mixed step) to the stage of fiber dimension one
  (`exQuadModelSwitchData_switches`); regularity follows (`exQuadModelSwitch_regular`).

Finding (consistency, not a contradiction of any field): the single-sign example `exQuadSingleStep`
cannot be the first step of a terminating bundle. Its new side has the same dimension as the old
one with both signs (`QuadSingleDims.result`), and the old side has dimension two, so the
following stage (dimension two, both signs) would need a mixed switch to dimension zero, which the
primitive vectors forbid (tex L5154–5157: "A proposed drop from dimension two to zero is therefore
a contradiction"). So the single-sign bundle is inhabited here as a step, and the full bundle with a
quadratic switch uses the mixed step.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module Matrix ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.UniformSwitch
  ZInQ.Contrib.CloudB3RC53.PairedFunctional

variable {k : Type} [Field k]

/-- The transport `φ σ φ⁻¹` of an endomorphism along a linear isomorphism. -/
def transportInv {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (φ : V ≃ₗ[k] W) (σ : V →ₗ[k] V) : W →ₗ[k] W :=
  φ.toLinearMap ∘ₗ σ ∘ₗ φ.symm.toLinearMap

/-- `φ` intertwines `σ` with its transport. PROVED. -/
theorem transportInv_comm {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (φ : V ≃ₗ[k] W) (σ : V →ₗ[k] V) :
    φ.toLinearMap ∘ₗ σ = transportInv φ σ ∘ₗ φ.toLinearMap := by
  ext x; simp [transportInv]

/-- The transport of an involution is an involution. PROVED. -/
theorem transportInv_sq {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (φ : V ≃ₗ[k] W) {σ : V →ₗ[k] V} (h : σ ∘ₗ σ = LinearMap.id) :
    transportInv φ σ ∘ₗ transportInv φ σ = LinearMap.id := by
  ext x
  have hx := LinearMap.congr_fun h (φ.symm x)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx
  simp [transportInv, hx]

/-- A nonzero vector in a submodule of a finite-dimensional space gives positive dimension. -/
theorem finrank_pos_of_mem {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (p : Submodule k W) {x : W} (hx : x ∈ p) (h0 : x ≠ 0) : 0 < finrank k p := by
  refine Nat.pos_of_ne_zero fun h => h0 ?_
  rw [Submodule.finrank_eq_zero] at h
  rw [h] at hx
  exact (Submodule.mem_bot k).mp hx

variable {A F : Type} [CommRing A] [Field F]

/-- A linear isomorphism of a finite-dimensional space with the fiber cohomology of a stage of the
same dimension. -/
def fiberEquivOf {ι : A →+* F} (ρ : A →+* k) (S : TwoTermStage ι) {V : Type} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (h : finrank k V = S.fiberDim ρ) :
    V ≃ₗ[k] fiberH1 ρ S :=
  haveI := fiberH1_finite ρ S
  LinearEquiv.ofFinrankEq _ _ (by rw [h, finrank_h1_twoTermFiberComplex])

/-! ### The quadratic step bundles from Selmer-level steps -/

/-- The fiber isomorphism of the finite side of a mixed step. -/
def mixedφ {ι : A →+* F} (ρ : A →+* k) (Y : SelmerQuadMixedStep k) (S : TwoTermStage ι)
    (h : finrank k ((selCx Y.X.SF.Dside).toCC.homology 1) = S.fiberDim ρ) :
    (selCx Y.X.SF.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S :=
  haveI := Y.X.fin_V
  fiberEquivOf ρ S h

/-- The fiber isomorphism of the singular side of a mixed step. -/
def mixedφ' {ι : A →+* F} (ρ : A →+* k) (Y : SelmerQuadMixedStep k) (S' : TwoTermStage ι)
    (h' : finrank k ((selCx Y.X.SS.Dside).toCC.homology 1) = S'.fiberDim ρ) :
    (selCx Y.X.SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S' :=
  haveI := Y.X.fin_V'
  fiberEquivOf ρ S' h'

/-- **A mixed model step from a Selmer-level mixed step** (tex L5003–5122): stages whose fiber
dimensions are those of the two sides, the fiber isomorphisms `mixedφ`, `mixedφ'`, and the stage
involutions the transports of `σ_V`, `σ_V'`. PROVED. -/
def mixedModelStepOf {ι : A →+* F} (ρ : A →+* k) (Y : SelmerQuadMixedStep k)
    (S S' : TwoTermStage ι)
    (h : finrank k ((selCx Y.X.SF.Dside).toCC.homology 1) = S.fiberDim ρ)
    (h' : finrank k ((selCx Y.X.SS.Dside).toCC.homology 1) = S'.fiberDim ρ) :
    MixedModelStep ρ S S' (transportInv (mixedφ ρ Y S h) Y.X.σV)
      (transportInv (mixedφ' ρ Y S' h') Y.X.σV') where
  Y := Y
  φ := mixedφ ρ Y S h
  hφ := transportInv_comm _ _
  φ' := mixedφ' ρ Y S' h'
  hφ' := transportInv_comm _ _

/-- The fiber isomorphism of the singular side of a single-sign step. -/
def singleφ' {ι : A →+* F} (ρ : A →+* k) (Y : SelmerQuadSingleStep k) (S' : TwoTermStage ι)
    (h' : finrank k ((selCx Y.X.SS.Dside).toCC.homology 1) = S'.fiberDim ρ) :
    (selCx Y.X.SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S' :=
  haveI := Y.X.fin_V'
  fiberEquivOf ρ S' h'

/-- **A single-sign model step from a Selmer-level single-sign step** (tex L5123–5136). PROVED. -/
def singleModelStepOf {ι : A →+* F} (ρ : A →+* k) (Y : SelmerQuadSingleStep k)
    (S S' : TwoTermStage ι)
    (h : finrank k ((selCx Y.X.SF.Dside).toCC.homology 1) = S.fiberDim ρ)
    (h' : finrank k ((selCx Y.X.SS.Dside).toCC.homology 1) = S'.fiberDim ρ) :
    SingleModelStep ρ S S' (transportInv (singleφ' ρ Y S' h') Y.X.σV') where
  Y := Y
  φ := haveI := Y.X.fin_V; fiberEquivOf ρ S h
  φ' := singleφ' ρ Y S' h'
  hφ' := Or.inl (transportInv_comm _ _)

/-! ### Instances over `ℚ` -/

/-- The zero-differential stage `[ℚ^{m+1} --0--> ℚ^{m+1}]` with cycle `e₀`, functional `0` and
coordinate `0`. -/
def zeroStage (m : ℕ) : TwoTermStage (RingHom.id ℚ) where
  n := m
  D := 0
  z := Pi.single 0 1
  w := 0
  u := 0
  hz := Matrix.zero_mulVec _
  hw := Matrix.zero_vecMul _
  hu := by
    unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
    ext i j; simp [vecMulVec]

theorem zeroStage_fiberDim (m : ℕ) : (zeroStage m).fiberDim (RingHom.id ℚ) = m + 1 :=
  fiberDim_zero_matrix _ rfl

/-- **`MixedModelStep` is inhabited** (LESSON 2): the mixed example `exQuadMixedStep` with the stages
of fiber dimensions three (`exStage3`) and one (`exStage1`). PROVED. -/
def exMixedModelStep (u u' : ℚ) :=
  mixedModelStepOf (RingHom.id ℚ) exQuadMixedStep (exStage3 u) (exStage1 u')
    (by
      change finrank ℚ ((selCx exSideF.Dside).toCC.homology 1) = _
      rw [exStage3_fiberDim]; exact exSideF_h1)
    (by
      change finrank ℚ ((selCx exSideS.Dside).toCC.homology 1) = _
      rw [exStage1_fiberDim]; exact exSideS_h1)

/-- The new side of the single-sign example is nonzero (its `+` part is, by
`QuadSingleDims.result`). PROVED. -/
theorem exSingle_V'_pos :
    1 ≤ finrank ℚ ((selCx exQuadSingleStep.X.SS.Dside).toCC.homology 1) := by
  let Y := exQuadSingleStep
  have hres := (Y.X.toQuadSingleDims Y.h2 Y.ε Y.hε Y.hJ2 Y.ep Y.em Y.hp Y.hm Y.he Y.hU Y.cp Y.hcp
    Y.hdet Y.hs1 Y.hs0).result
  have := Y.X.fin_V'
  exact le_trans hres.2.1 (Submodule.finrank_le _)

theorem exSingle_V_pos :
    1 ≤ finrank ℚ ((selCx exQuadSingleStep.X.SF.Dside).toCC.homology 1) :=
  le_trans (by norm_num) two_le_finrank_VB

/-- **`SingleModelStep` is inhabited** (LESSON 2): the single-sign example `exQuadSingleStep` with
zero-differential stages of the dimensions of its two sides. PROVED. -/
def exSingleModelStep :=
  singleModelStepOf (RingHom.id ℚ) exQuadSingleStep
    (zeroStage (finrank ℚ ((selCx exQuadSingleStep.X.SF.Dside).toCC.homology 1) - 1))
    (zeroStage (finrank ℚ ((selCx exQuadSingleStep.X.SS.Dside).toCC.homology 1) - 1))
    (by rw [zeroStage_fiberDim]; exact (Nat.sub_add_cancel exSingle_V_pos).symm)
    (by rw [zeroStage_fiberDim]; exact (Nat.sub_add_cancel exSingle_V'_pos).symm)

/-! ### A quadratic `SelmerModelSwitchData` with a genuine switch -/

/-- The two stages: `true` of fiber dimension three, `false` of fiber dimension one. -/
def exQStage (b : Bool) : TwoTermStage (RingHom.id ℚ) :=
  Bool.rec (exStage1 (exSwitchCoordData 1 1).uS) (exStage3 (exSwitchCoordData 1 1).uF) b

theorem exQ_hF : finrank ℚ ((selCx exQuadMixedStep.X.SF.Dside).toCC.homology 1) =
    (exQStage true).fiberDim (RingHom.id ℚ) := by
  change finrank ℚ ((selCx exSideF.Dside).toCC.homology 1) = (exStage3 _).fiberDim _
  rw [exStage3_fiberDim]; exact exSideF_h1

theorem exQ_hS : finrank ℚ ((selCx exQuadMixedStep.X.SS.Dside).toCC.homology 1) =
    (exQStage false).fiberDim (RingHom.id ℚ) := by
  change finrank ℚ ((selCx exSideS.Dside).toCC.homology 1) = (exStage1 _).fiberDim _
  rw [exStage1_fiberDim]; exact exSideS_h1

/-- The stage involutions: the transports of the mixed example's side involutions. -/
def exQσ (b : Bool) : fiberH1 (RingHom.id ℚ) (exQStage b) →ₗ[ℚ] fiberH1 (RingHom.id ℚ) (exQStage b) :=
  Bool.rec (motive := fun b => fiberH1 (RingHom.id ℚ) (exQStage b) →ₗ[ℚ]
      fiberH1 (RingHom.id ℚ) (exQStage b))
    (transportInv (mixedφ' (RingHom.id ℚ) exQuadMixedStep (exQStage false) exQ_hS)
      exQuadMixedStep.X.σV')
    (transportInv (mixedφ (RingHom.id ℚ) exQuadMixedStep (exQStage true) exQ_hF)
      exQuadMixedStep.X.σV) b

/-- The stage `true` carries both cohomology signs: the transports of the detected classes
`c₊`, `c₋` of `exQuadMixedStep` are nonzero eigenvectors. PROVED. -/
theorem exQ_both_signs :
    0 < finrank ℚ ↥(signPart (exQσ true) (1 : ℚ)) ∧
      0 < finrank ℚ ↥(signPart (exQσ true) (-1 : ℚ)) := by
  let Y := exQuadMixedStep
  let φ := mixedφ (RingHom.id ℚ) Y (exQStage true) exQ_hF
  have := fiberH1_finite (RingHom.id ℚ) (exQStage true)
  have hdet := Y.hdet Y.hcp Y.hcm
  have hcp0 : Y.cp ≠ 0 := fun h => hdet.1 (by rw [h, map_zero])
  have hcm0 : Y.cm ≠ 0 := fun h => hdet.2 (by rw [h, map_zero])
  have key : ∀ c, exQσ true (φ c) = φ (Y.X.σV c) := fun c => by
    have := LinearMap.congr_fun (transportInv_comm φ Y.X.σV) c
    exact this.symm
  refine ⟨finrank_pos_of_mem _ (x := φ Y.cp) ?_ (by simpa using hcp0),
    finrank_pos_of_mem _ (x := φ Y.cm) ?_ (by simpa using hcm0)⟩
  · rw [mem_signPart, key, Y.hcp, one_smul]
  · rw [mem_signPart, key, Y.hcm, map_neg, neg_one_smul]

/-- **A quadratic `SelmerModelSwitchData` with a genuine switch** (LESSON 2): the stage of fiber
dimension three, carrying both signs, switches by the mixed model step `exMixedModelStep`
(coordinate step `exCoordStep`) to the stage of fiber dimension one. PROVED. -/
def exQuadModelSwitchData : SelmerModelSwitchData (k := ℚ) (RingHom.id ℚ) (RingHom.id ℚ) where
  Stage := Bool
  stage := exQStage
  σ := exQσ
  quadratic := True
  h2 _ := two_ne_zero_ℚ
  hσ _ b := by
    cases b
    · exact transportInv_sq _ exQuadMixedStep.X.hV'
    · exact transportInv_sq _ exQuadMixedStep.X.hV
  primitive b := by
    cases b
    · exact ⟨0, by simp [exQStage, exStage1]⟩
    · exact ⟨0, by simp [exQStage, exStage3]⟩
  switch_mixed b _ hs := by
    cases b
    · exfalso
      have h1 := exStage1_fiberDim (exSwitchCoordData 1 1).uS
      change 1 < (exStage1 _).fiberDim (RingHom.id ℚ) at hs
      omega
    · exact ⟨false, ⟨exCoordStep⟩,
        fun _ => ⟨mixedModelStepOf (RingHom.id ℚ) exQuadMixedStep (exQStage true) (exQStage false)
          exQ_hF exQ_hS⟩, fun h => absurd trivial h⟩
  switch_single b _ hnot hs := by
    cases b
    · exfalso
      have h1 := exStage1_fiberDim (exSwitchCoordData 1 1).uS
      change 1 < (exStage1 _).fiberDim (RingHom.id ℚ) at hs
      omega
    · exact absurd exQ_both_signs hnot

/-- The example is quadratic and switches: its stage `true` has fiber dimension three and both
signs. PROVED. -/
theorem exQuadModelSwitchData_switches :
    exQuadModelSwitchData.quadratic ∧
      1 < (exQuadModelSwitchData.stage true).fiberDim (RingHom.id ℚ) ∧
      0 < finrank ℚ ↥(signPart (exQuadModelSwitchData.σ true) (1 : ℚ)) ∧
      0 < finrank ℚ ↥(signPart (exQuadModelSwitchData.σ true) (-1 : ℚ)) := by
  refine ⟨trivial, ?_, exQ_both_signs⟩
  change 1 < (exStage3 _).fiberDim (RingHom.id ℚ)
  rw [exStage3_fiberDim]; norm_num

/-- Regularity from the quadratic example bundle. PROVED. -/
theorem exQuadModelSwitch_regular (b : Bool) :
    ∃ a : ℚ, RingHom.id ℚ a = (exQuadModelSwitchData.stage b).u :=
  regular_of_selmerModelSwitchData (fun _ _ h => h) (fun x hx => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at hx
    simp [hx]) exQuadModelSwitchData b

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
