import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.SharedStrict

/-!
# RC53 SwitchInputs: the height-one switching data from per-stage fiber models

Proposition `ex:limits-uniform-lower-bound`, the height-one regularity paragraph, tex L4976–5195:
the switching process at a height-one prime runs through configurations whose fiber cohomology
`V = H¹(C ⊗ k)` has dimension `s` (tex L4986–4996), carries the cohomology signs `V = V₊ ⊕ V₋` at
the quadratic primes (tex L5009–5026), and changes at each switch by the exact sequences (5.5a)
(tex L5055–5086).

`Plug.lean`'s `SelmerSwitchData` asks, per switch, for a Selmer-level step together with
identifications of the stage dimensions (`fiberDim`, and the sign dimensions `sp`, `sm`) with the
Selmer cohomology dimensions. This file builds `SelmerSwitchData` from a bundle in which those
identifications are **derived**:

* every stage carries an involution `σ_S` on the `H¹` of its two-term fiber
  (`twoTermFiberComplex`), and the sign dimensions are *defined* as `sp S = dim V₊(σ_S)`,
  `sm S = dim V₋(σ_S)`; `sign_sum` is then PROVED (`InvolutionSplitting` and
  `finrank_h1_twoTermFiberComplex`);
* every switch step carries linear isomorphisms between the Selmer side cohomology and the stage
  fiber cohomology (equivariant for the involutions in the quadratic case); they follow from a
  homotopy equivalence between the Selmer complex and the stage's two-term fiber
  (`h1EquivOfHomotopyEquiv`), i.e. from the stage being a finite free model of the configuration's
  Selmer complex;
* the nonquadratic step is built on one shared strict condition (`StrictIdentification`), so `hk0`
  is PROVED (`SelmerNonquadStep.ofStrict`).

Nodes (PROVED):
* `finrank_signPart_of_equiv`: equivariant linear isomorphisms preserve sign-part dimensions.
* `SelmerModelSwitchData.toSelmerSwitchData`: the full `SelmerSwitchData` from the bundle.
* `regular_of_selmerModelSwitchData`: every stage coordinate lies in `ι(A)` (RC16 regularity).
* Non-vacuity (LESSON 2): `exSelmerModelSwitchData`, a bundle with a genuine nonquadratic switch
  from fiber dimension three to one (`exSelmerModelSwitchData_switches`).

Remaining inputs (GLUE, carried in the step bundles): localization duality, detection, the
detecting primes, the Galois-derived involutions of `SelmerQuadSwitch`, and `CoordStep`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module Matrix ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.UniformSwitch

variable {k : Type} [Field k]

/-! ### Sign parts under equivariant isomorphisms -/

/-- An equivariant linear isomorphism maps the `ε`-part onto the `ε`-part. -/
theorem signPart_map_equiv {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (φ : V ≃ₗ[k] W) {T : V →ₗ[k] V} {T' : W →ₗ[k] W}
    (hφ : φ.toLinearMap ∘ₗ T = T' ∘ₗ φ.toLinearMap) (ε : k) :
    (signPart T ε).map φ.toLinearMap = signPart T' ε := by
  have hφx : ∀ x, φ (T x) = T' (φ x) := fun x => LinearMap.congr_fun hφ x
  ext y
  simp only [Submodule.mem_map, mem_signPart]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change T' (φ x) = ε • φ x
    rw [← hφx, hx, map_smul]
  · intro hy
    refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
    apply φ.injective
    rw [hφx, φ.apply_symm_apply, map_smul, φ.apply_symm_apply]
    exact hy

/-- **Equivariant isomorphisms preserve sign-part dimensions.** PROVED. -/
theorem finrank_signPart_of_equiv {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (φ : V ≃ₗ[k] W) {T : V →ₗ[k] V} {T' : W →ₗ[k] W}
    (hφ : φ.toLinearMap ∘ₗ T = T' ∘ₗ φ.toLinearMap) (ε : k) :
    finrank k ↥(signPart T ε) = finrank k ↥(signPart T' ε) := by
  rw [← signPart_map_equiv φ hφ ε, LinearEquiv.finrank_map_eq]

/-- The `ε`-part of `−T` is the `(−ε)`-part of `T`. -/
theorem signPart_neg_eq {V : Type} [AddCommGroup V] [Module k V] (T : V →ₗ[k] V) (ε : k) :
    signPart (-T) ε = signPart T (-ε) := by
  ext v
  simp only [mem_signPart, LinearMap.neg_apply, neg_smul]
  constructor
  · intro h; rw [← h, neg_neg]
  · intro h; rw [h, neg_neg]

/-! ### The fiber cohomology of a stage -/

variable {A F : Type} [CommRing A] [Field F]

/-- The `H¹` of a stage's two-term fiber. -/
abbrev fiberH1 {ι : A →+* F} (ρ : A →+* k) (S : TwoTermStage ι) : Type :=
  (twoTermFiberComplex ρ S).homology 1

/-- The fiber cohomology is finite-dimensional (it is `ker D̄ ⊆ k^{n+1}`). -/
theorem fiberH1_finite {ι : A →+* F} (ρ : A →+* k) (S : TwoTermStage ι) :
    FiniteDimensional k (fiberH1 ρ S) := by
  set K := twoTermFiberComplex ρ S
  have hd0 : K.d 0 1 = 0 := by
    change ModuleCat.ofHom (0 : PUnit.{1} →ₗ[k] (Fin (S.n + 1) → k)) = 0
    rfl
  have e1 := (K.isoHomologyπ 0 1 (by simp) hd0).symm
  have e2 := K.cyclesIsoSc' 0 1 2 (by simp) (by simp)
  have e3 := (K.sc' 0 1 2).moduleCatCyclesIso
  have e := (e1 ≪≫ e2 ≪≫ e3).toLinearEquiv
  have h2 : FiniteDimensional k ((K.sc' 0 1 2).X₂) := by
    change FiniteDimensional k (Fin (S.n + 1) → k); infer_instance
  have : FiniteDimensional k ((K.sc' 0 1 2).moduleCatLeftHomologyData.K) := by
    change FiniteDimensional k (LinearMap.ker (K.sc' 0 1 2).g.hom)
    infer_instance
  exact LinearEquiv.finiteDimensional e.symm

/-- A homotopy equivalence between a Selmer complex and a stage's two-term fiber gives a linear
isomorphism of the degree-one cohomology (the stage is a finite free model of the configuration's
Selmer complex, tex L4976–4996). PROVED. -/
noncomputable def h1EquivOfHomotopyEquiv {ι : A →+* F} (ρ : A →+* k) (S : TwoTermStage ι)
    (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData k)
    (e : HomotopyEquiv (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx D).toCC
      (twoTermFiberComplex ρ S)) :
    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx D).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S :=
  (e.toHomologyIso 1).toLinearEquiv

/-- `dim H¹` of a Selmer complex isomorphic (in degree one cohomology) to a stage fiber is the
fiber dimension. PROVED. -/
theorem fiberDim_eq_of_h1Equiv {ι : A →+* F} (ρ : A →+* k) (S : TwoTermStage ι) {V : Type}
    [AddCommGroup V] [Module k V] (φ : V ≃ₗ[k] fiberH1 ρ S) : S.fiberDim ρ = finrank k V := by
  rw [← finrank_h1_twoTermFiberComplex ρ S, φ.finrank_eq]

/-! ### The step bundles -/

open ZInQ.Contrib.CloudB3RC53.PairedFunctional in
/-- **A nonquadratic switch step with its fiber models** (tex L4997–5003, L5055–5086): the relaxed
localization, the two sides on one shared strict condition (`StrictIdentification`), the duality
(GLUE) and detection inputs, and isomorphisms of the side cohomology with the two stage fibers. -/
structure NonquadModelStep {ι : A →+* F} (ρ : A →+* k) (S S' : TwoTermStage ι) where
  R : RelaxedLocalization k
  SF : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))
  SS : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))
  fG : FiniteDimensional k (R.D.G.X 1)
  fL : FiniteDimensional k (R.D.L.X 0)
  fF : FiniteDimensional k (SF.U₁.X 1)
  fS : FiniteDimensional k (SS.U₁.X 1)
  I : StrictIdentification SF SS
  ε : k
  σ : k
  J : Matrix (Fin 2) (Fin 2) k
  hε : ε ≠ 0
  hσ : σ ≠ 0
  hJ2 : J * J = 1
  hdual : LocalizationDualityInput ε σ J hε hσ hJ2 R.U
  hdet : finPlane k (Fin 2 → k) (Fin 2 → k) ≤ R.U
  φ : (selCx SF.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S
  φ' : (selCx SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S'

/-- The Selmer step of a nonquadratic model step (`hk0` from the shared strict condition). -/
def NonquadModelStep.step {ι : A →+* F} {ρ : A →+* k} {S S' : TwoTermStage ι}
    (X : NonquadModelStep ρ S S') : SelmerNonquadStep k :=
  SelmerNonquadStep.ofStrict X.R X.SF X.SS X.fG X.fL X.fF X.fS X.I X.ε X.σ X.J X.hε X.hσ X.hJ2
    X.hdual X.hdet

open ZInQ.Contrib.CloudB3RC53.PairedFunctional in
/-- **A mixed-sign quadratic switch step with its fiber models** (tex L5003–5122): the Selmer step
and isomorphisms of the side cohomology with the stage fibers, equivariant for the side involutions
and the stage involutions `σS`, `σS'`. -/
structure MixedModelStep {ι : A →+* F} (ρ : A →+* k) (S S' : TwoTermStage ι)
    (σS : fiberH1 ρ S →ₗ[k] fiberH1 ρ S) (σS' : fiberH1 ρ S' →ₗ[k] fiberH1 ρ S') where
  Y : SelmerQuadMixedStep k
  φ : (selCx Y.X.SF.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S
  hφ : φ.toLinearMap ∘ₗ Y.X.σV = σS ∘ₗ φ.toLinearMap
  φ' : (selCx Y.X.SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S'
  hφ' : φ'.toLinearMap ∘ₗ Y.X.σV' = σS' ∘ₗ φ'.toLinearMap

open ZInQ.Contrib.CloudB3RC53.PairedFunctional in
/-- **A single-sign quadratic switch step with its fiber models** (tex L5123–5136): the Selmer step,
an isomorphism of the finite side cohomology with the old stage fiber, and an isomorphism of the
singular side cohomology with the new stage fiber intertwining `σV'` with `±σS'` (a common sign
interchanges the names `+` and `−`, tex L5036–5037). -/
structure SingleModelStep {ι : A →+* F} (ρ : A →+* k) (S S' : TwoTermStage ι)
    (σS' : fiberH1 ρ S' →ₗ[k] fiberH1 ρ S') where
  Y : SelmerQuadSingleStep k
  φ : (selCx Y.X.SF.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S
  φ' : (selCx Y.X.SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S'
  hφ' : φ'.toLinearMap ∘ₗ Y.X.σV' = σS' ∘ₗ φ'.toLinearMap ∨
    φ'.toLinearMap ∘ₗ Y.X.σV' = (-σS') ∘ₗ φ'.toLinearMap

/-! ### The bundle and the switching data -/

/-- **Height-one switching data from per-stage fiber models** (tex L4976–5195): the stages, an
involution on each stage's fiber cohomology (the cohomology signs; only used when `quadratic`),
the primitive vectors, and for each switch a step bundle (nonquadratic, mixed or single sign) with
a coordinate step. The sign dimensions are the sign-part dimensions of the stage involutions.
Caveat: the coordinate steps `CoordStep` are free inputs, and the stages are not tied to the genuine
fibre models of the configuration (only the stage dimensions come from the step bundles); linking
the stages to the genuine fibre models is pending (genuine switching data on the
`rc53-switch-genuine` branch, not yet in the tree). -/
structure SelmerModelSwitchData (ι : A →+* F) (ρ : A →+* k) where
  Stage : Type
  stage : Stage → TwoTermStage ι
  σ : ∀ S, fiberH1 ρ (stage S) →ₗ[k] fiberH1 ρ (stage S)
  quadratic : Prop
  h2 : quadratic → (2 : k) ≠ 0
  hσ : quadratic → ∀ S, σ S ∘ₗ σ S = LinearMap.id
  primitive : ∀ S, ∃ i, ρ ((stage S).z i) ≠ 0
  switch_mixed : ∀ S, (¬ quadratic ∨
      (0 < finrank k ↥(signPart (σ S) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ S) (-1 : k)))) →
    1 < (stage S).fiberDim ρ →
    ∃ S', Nonempty (CoordStep ι (stage S).u (stage S').u) ∧
      (quadratic → Nonempty (MixedModelStep ρ (stage S) (stage S') (σ S) (σ S'))) ∧
      (¬ quadratic → Nonempty (NonquadModelStep ρ (stage S) (stage S')))
  switch_single : ∀ S, quadratic →
    ¬ (0 < finrank k ↥(signPart (σ S) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ S) (-1 : k))) →
    1 < (stage S).fiberDim ρ →
    ∃ S', Nonempty (CoordStep ι (stage S).u (stage S').u) ∧
      Nonempty (SingleModelStep ρ (stage S) (stage S') (σ S'))

/-- **The Selmer switching data from the fiber-model bundle**: every identification of
`SelmerSwitchData` is derived — `sign_sum` from the involution splitting of the stage fibers, the
nonquadratic identifications and `hk0` from the fiber isomorphisms and the shared strict condition,
the quadratic sign identifications from the equivariant fiber isomorphisms. PROVED. -/
noncomputable def SelmerModelSwitchData.toSelmerSwitchData {ι : A →+* F} {ρ : A →+* k}
    (P : SelmerModelSwitchData ι ρ) : SelmerSwitchData ι ρ where
  Stage := P.Stage
  stage := P.stage
  quadratic := P.quadratic
  sp S := finrank k ↥(signPart (P.σ S) (1 : k))
  sm S := finrank k ↥(signPart (P.σ S) (-1 : k))
  sign_sum q S := by
    have := fiberH1_finite ρ (P.stage S)
    rw [← finrank_h1_twoTermFiberComplex ρ (P.stage S),
      (involutionSplitting_proof k _ (P.σ S) (P.h2 q) (P.hσ q S)).2.2 this,
      signPart_one_eq_plusPart, signPart_neg_one_eq_minusPart]
  primitive := P.primitive
  switch_mixed S h1 h2 := by
    obtain ⟨S', hc, hq, hn⟩ := P.switch_mixed S h1 h2
    refine ⟨S', hc, fun q => ?_, fun nq => ?_⟩
    · obtain ⟨M⟩ := hq q
      exact ⟨M.Y, (finrank_signPart_of_equiv M.φ M.hφ 1).symm,
        (finrank_signPart_of_equiv M.φ M.hφ (-1)).symm,
        (finrank_signPart_of_equiv M.φ' M.hφ' 1).symm,
        (finrank_signPart_of_equiv M.φ' M.hφ' (-1)).symm⟩
    · obtain ⟨N⟩ := hn nq
      exact ⟨N.step, fiberDim_eq_of_h1Equiv ρ _ N.φ, fiberDim_eq_of_h1Equiv ρ _ N.φ'⟩
  switch_single S q h1 h2 := by
    obtain ⟨S', hc, ⟨M⟩⟩ := P.switch_single S q h1 h2
    refine ⟨S', finrank k ↥(signPart M.Y.X.σV' (1 : k)),
      finrank k ↥(signPart M.Y.X.σV' (-1 : k)), hc, ⟨M.Y, ?_, rfl, rfl⟩, ?_⟩
    · have hV := M.Y.X.fin_V
      rw [fiberDim_eq_of_h1Equiv ρ _ M.φ,
        (involutionSplitting_proof k _ M.Y.X.σV M.Y.h2 M.Y.X.hV).2.2 hV,
        signPart_one_eq_plusPart, ← signPart_neg_one_eq_minusPart, ← M.Y.hs0, add_zero]
    · rcases M.hφ' with h | h
      · exact Or.inl ⟨(finrank_signPart_of_equiv M.φ' h 1).symm,
          (finrank_signPart_of_equiv M.φ' h (-1)).symm⟩
      · refine Or.inr ⟨?_, ?_⟩
        · change finrank k ↥(signPart (P.σ S') (1 : k)) = _
          rw [finrank_signPart_of_equiv M.φ' h (-1), signPart_neg_eq, neg_neg]
        · change finrank k ↥(signPart (P.σ S') (-1 : k)) = _
          rw [finrank_signPart_of_equiv M.φ' h 1, signPart_neg_eq]

/-- **Regularity at the height-one prime from the fiber-model bundle** (tex L4976–5195): every
stage coordinate lies in `ι(A)` (RC16's `regular_of_switchProcess` through
`regular_of_selmerSwitchData`). Classification: PROVED (from the inputs of the bundle). -/
theorem regular_of_selmerModelSwitchData [IsLocalRing A] {ι : A →+* F}
    (hι : Function.Injective ι) {ρ : A →+* k} (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0)
    (P : SelmerModelSwitchData ι ρ) (S : P.Stage) : ∃ a : A, ι a = (P.stage S).u :=
  regular_of_selmerSwitchData hι hρ P.toSelmerSwitchData S

/-! ### Non-vacuity (LESSON 2) -/

section NonVacuity

/-- The fiber of `exStage3` has dimension three, that of `exStage1` dimension one. -/
theorem fiberH1_exStage3 (u : ℚ) : finrank ℚ (fiberH1 (RingHom.id ℚ) (exStage3 u)) = 3 := by
  rw [finrank_h1_twoTermFiberComplex, exStage3_fiberDim]

theorem fiberH1_exStage1 (u : ℚ) : finrank ℚ (fiberH1 (RingHom.id ℚ) (exStage1 u)) = 1 := by
  rw [finrank_h1_twoTermFiberComplex, exStage1_fiberDim]

/-- **A nonquadratic model step with a genuine switch** (fiber dimensions three and one): the
example relaxed localization and sides of `NonVacuity.lean` on the shared strict condition
(`exStrictIdentification`), and the fiber isomorphisms (dimensions `3 = 3`, `1 = 1`). -/
noncomputable def exNonquadModelStep (u u' : ℚ) :
    NonquadModelStep (RingHom.id ℚ) (exStage3 u) (exStage1 u') where
  R := exRel
  SF := exSideF
  SS := exSideS
  fG := exSelmerNonquadStep.fG
  fL := exSelmerNonquadStep.fL
  fF := exSelmerNonquadStep.fF
  fS := exSelmerNonquadStep.fS
  I := exStrictIdentification
  ε := 1
  σ := 1
  J := J₀
  hε := one_ne_zero
  hσ := one_ne_zero
  hJ2 := J₀_sq
  hdual := exSelmerNonquadStep.hdual
  hdet := exSelmerNonquadStep.hdet
  φ := by
    haveI : FiniteDimensional ℚ (exRel.D.G.X 1) := exSelmerNonquadStep.fG
    haveI : FiniteDimensional ℚ (exRel.D.L.X 0) := exSelmerNonquadStep.fL
    haveI : FiniteDimensional ℚ (exSideF.U₁.X 1) := exSelmerNonquadStep.fF
    haveI := finiteDimensional_side exSideF
    haveI := fiberH1_finite (RingHom.id ℚ) (exStage3 u)
    exact LinearEquiv.ofFinrankEq _ _ (by rw [exSideF_h1, fiberH1_exStage3])
  φ' := by
    haveI : FiniteDimensional ℚ (exRel.D.G.X 1) := exSelmerNonquadStep.fG
    haveI : FiniteDimensional ℚ (exRel.D.L.X 0) := exSelmerNonquadStep.fL
    haveI : FiniteDimensional ℚ (exSideS.U₁.X 1) := exSelmerNonquadStep.fS
    haveI := finiteDimensional_side exSideS
    haveI := fiberH1_finite (RingHom.id ℚ) (exStage1 u')
    exact LinearEquiv.ofFinrankEq _ _ (by rw [exSideS_h1, fiberH1_exStage1])

/-- **`SelmerModelSwitchData` with a genuine switch** (LESSON 2): the stages of fiber dimensions
three and one of `exSelmerSwitchData`, the identity involutions (nonquadratic case), and the
nonquadratic model step `exNonquadModelStep`. -/
noncomputable def exSelmerModelSwitchData :
    SelmerModelSwitchData (k := ℚ) (RingHom.id ℚ) (RingHom.id ℚ) where
  Stage := Bool
  stage := exSelmerSwitchData.stage
  σ _ := LinearMap.id
  quadratic := False
  h2 h := h.elim
  hσ h := h.elim
  primitive := exSelmerSwitchData.primitive
  switch_mixed b _ hs := by
    cases b
    · exfalso
      have h1 := exStage1_fiberDim (exSwitchCoordData 1 1).uS
      change 1 < (exStage1 _).fiberDim (RingHom.id ℚ) at hs
      omega
    · exact ⟨false, ⟨exCoordStep⟩, fun h => h.elim, fun _ => ⟨exNonquadModelStep _ _⟩⟩
  switch_single _ h := h.elim

/-- The example switches: its stage `true` has fiber dimension three. PROVED. -/
theorem exSelmerModelSwitchData_switches :
    1 < (exSelmerModelSwitchData.stage true).fiberDim (RingHom.id ℚ) := by
  change 1 < (exStage3 _).fiberDim (RingHom.id ℚ)
  rw [exStage3_fiberDim]; norm_num

/-- Regularity from the example bundle. PROVED. -/
theorem exSelmerModelSwitch_regular (b : Bool) :
    ∃ a : ℚ, RingHom.id ℚ a = (exSelmerModelSwitchData.stage b).u :=
  regular_of_selmerModelSwitchData (fun _ _ h => h) (fun x hx => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at hx
    simp [hx]) exSelmerModelSwitchData b

/-- **A strict identification of the single-sign example sides** (`exSideFB`, `exSideSB` of
`NonVacuityQuad.lean`): both are built on the same (zero) strict condition, so `e = e' = id`.
This gives the strict cohomology identification `eK` without the explicit common type `TstrB`
used there. PROVED. -/
def exStrictIdentificationB : StrictIdentification exSideFB exSideSB where
  e := ZInQ.Contrib.CloudB3RC53.SelmerDuality.idGHom (zGCx Zn)
  e' := ZInQ.Contrib.CloudB3RC53.SelmerDuality.idGHom (zGCx Zn)
  he'e _ _ := rfl
  hee' _ _ := rfl
  hι n x := by
    have hx : x = 0 := funext fun i => Fin.elim0 i
    subst hx
    exact ((exSideFB.Dstr.ι.f n n rfl).map_zero).trans ((exSideSB.Dstr.ι.f n n rfl).map_zero).symm

/-- The strict identification `eK` of the single-sign example, from `exStrictIdentificationB`. -/
noncomputable def exEKB' : (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx exSideSB.Dstr).toCC.homology 1
    ≃ₗ[ℚ] (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx exSideFB.Dstr).toCC.homology 1 :=
  exStrictIdentificationB.eK

/-- The shared strict dimension of the single-sign example. PROVED. -/
theorem exStrictIdentificationB_hk0 :
    finrank ℚ ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx exSideFB.Dstr).toCC.homology 1) =
      finrank ℚ ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx exSideSB.Dstr).toCC.homology 1) :=
  exStrictIdentificationB.hk0

end NonVacuity

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
