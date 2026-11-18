import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.SwitchData

/-!
# RC53 SwitchInputs: genuine height-one switching data (no one-stage bypass)

Proposition `ex:limits-uniform-lower-bound`, paragraph "Height-one regularity", tex L4976–5195.

**The defect repaired.** `HeightOneSwitchData`, `SelmerSwitchData` and `SelmerModelSwitchData`
(UniformSwitch/Regularity.lean, Plug.lean, SwitchData.lean) quantify over free stages and Selmer
data tied to the genuine configuration only through the starting coordinate. A one-stage datum of
fiber dimension one satisfies every field (the switch fields are guarded by `1 < fiberDim`), so
`∃ D S₀, (D.stage S₀).u = u` is equivalent to `u ∈ ι(A)` and the hypothesis carries no information
(truth check, Part B, D1–D3). The structures below keep those names compiling and add a tightened
version.

**The tightened structure.** A `SwitchFamily` fixes, as parameters (not fields chosen per proof):
the configurations of the switching argument (finite sets of derivative primes in the text) with a
successor map `next c p` (add the derivative prime `p`), the actual starting configuration, the
fiber Selmer complex `fibre c` of every configuration (`C ⊗_R k`, as Selmer data over the residue
field `k`), the actual class `z` and the paired functional `λ_z` of the starting fiber (as a
degree-one cocycle and a closed degree-two cochain functional), and the moving variable `t`, so
that "quadratic" is the condition `t̄(t̄ + 2) = 0` in `k` (tex L5005–5008), not a free proposition.

`GenuineSwitchData Φ ι ρ u` then asks:
* (a) every configuration's stage IS a finite free model of the genuine fiber: a homotopy
  equivalence `C(fibre c) ≃ [k^{n+1} --D̄--> k^{n+1}]` (`model`);
* (b) the starting stage carries the actual class and functional: under the model, the reduction
  of the stage cycle is the image of the actual class, the actual functional is the stage functional
  pulled back, and the stage coordinate is `u`;
* (c) the switches follow the configuration sequence: each switch is a choice of prime `p`, and the
  next stage is the stage of `next c p`, with the step's Selmer sides equal to the fibers of `c` and
  `next c p` (`GenuineNonquadStep`, `GenuineMixedStep`, `GenuineSingleStep`). Only configurations
  reachable from the actual one are constrained (`Reach`).

The GLUE inputs inside the steps (`LocalizationDualityInput`, detection, `DetectingPrime(Plus)`, the
side involutions, `CoordStep`) stay explicit; they are now stated for the configurations' own
fibers.

Nodes (PROVED):
* `GenuineSwitchData.fiberDim_eq` / `CollapseForcesFibre` (`collapse_forces_fibre`): every stage's
  fiber dimension is the genuine `dim_k H¹(fibre c)`; in particular a one-stage datum of fiber
  dimension one forces the genuine starting fiber to have `H¹` of dimension one. The fiber
  dimensions are independent of the datum (`fiberDim_indep`), so no free choice remains.
* `GenuineSwitchData.toSelmerModelSwitchData`, `RegularOfGenuineSwitchData`
  (`regular_of_genuineSwitchData`): regularity `∃ a, ι a = u` from the tightened data.
* Non-vacuity (LESSON 2): `exGenuineFamily` / `exGenuineSwitchData`, a configuration family over `ℚ`
  whose actual fiber is the Selmer complex with `G = ℚ` in degrees one and two, and a genuine
  datum for it; `exGenuine_fibre_forced` shows its fiber dimension is the genuine `H¹` dimension
  `1`.

`DEPARTURE` (form): the fiber complexes are the SelmerDuality/SelmerSES models (`selCx` of Selmer
data over `k`), not the continuous-cochain complexes of the genuine Galois lane; the Selmer sides of
the switch steps need quotients literally concentrated in degree one (`SwitchSide`), which genuine
cochains give only up to quasi-isomorphism. The family is therefore a parameter fixed by the
configuration, and its identification with the genuine Galois complexes is left to the bridge with
the genuine lane.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module Matrix ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.UniformSwitch
  ZInQ.Contrib.CloudB3RC53.PairedFunctional

/-- Configurations reachable from `c₀` by successive switches `c ↦ next c p`. -/
inductive Reach {C P : Type} (next : C → P → C) (c₀ : C) : C → Prop
  | start : Reach next c₀ c₀
  | step {c : C} (p : P) : Reach next c₀ c → Reach next c₀ (next c p)

/-- **A configuration family of the switching argument** (tex L4976–5195), fixed as a parameter:
configurations with successor `next c p` (add the derivative prime `p`), the actual configuration,
the fiber Selmer complex of each configuration over `k`, the actual class and paired functional of
the starting fiber, and the moving variable `t` of `A`. -/
structure SwitchFamily (k : Type) [Field k] (A : Type) [CommRing A] where
  Config : Type
  Prime : Type
  actual : Config
  next : Config → Prime → Config
  fibre : Config → SelData k
  t : A
  zAct : (selCx (fibre actual)).toCC.X 1
  hzAct : ((selCx (fibre actual)).toCC.d 1 2).hom zAct = 0
  lamAct : (selCx (fibre actual)).toCC.X 2 →ₗ[k] k
  hlamAct : ∀ y, lamAct (((selCx (fibre actual)).toCC.d 1 2).hom y) = 0

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]

/-- The specialization at the height-one prime is quadratic: `t̄ (t̄ + 2) = 0` in `k` (tex
L5005–5008: "quadraticity implies `t(t+2) = 0` in `k`"). -/
def SwitchFamily.quadratic (Φ : SwitchFamily k A) (ρ : A →+* k) : Prop :=
  ρ Φ.t * (ρ Φ.t + 2) = 0

/-- **A nonquadratic switch step between the fibers of `c` and `c'`** (tex L4997–5003): a model step
whose finite side is the fiber of `c` and whose singular side is the fiber of `c'`. -/
structure GenuineNonquadStep {ι : A →+* F} (ρ : A →+* k) (Φ : SwitchFamily k A)
    (stage : Φ.Config → TwoTermStage ι) (c c' : Φ.Config) where
  N : NonquadModelStep ρ (stage c) (stage c')
  hF : N.SF.Dside = Φ.fibre c
  hS : N.SS.Dside = Φ.fibre c'

/-- **A mixed-sign quadratic switch step between the fibers of `c` and `c'`** (tex L5003–5122). -/
structure GenuineMixedStep {ι : A →+* F} (ρ : A →+* k) (Φ : SwitchFamily k A)
    (stage : Φ.Config → TwoTermStage ι) (σ : ∀ c, fiberH1 ρ (stage c) →ₗ[k] fiberH1 ρ (stage c))
    (c c' : Φ.Config) where
  M : MixedModelStep ρ (stage c) (stage c') (σ c) (σ c')
  hF : M.Y.X.SF.Dside = Φ.fibre c
  hS : M.Y.X.SS.Dside = Φ.fibre c'

/-- **A single-sign quadratic switch step between the fibers of `c` and `c'`** (tex L5123–5136). -/
structure GenuineSingleStep {ι : A →+* F} (ρ : A →+* k) (Φ : SwitchFamily k A)
    (stage : Φ.Config → TwoTermStage ι) (σ : ∀ c, fiberH1 ρ (stage c) →ₗ[k] fiberH1 ρ (stage c))
    (c c' : Φ.Config) where
  M : SingleModelStep ρ (stage c) (stage c') (σ c')
  hF : M.Y.X.SF.Dside = Φ.fibre c
  hS : M.Y.X.SS.Dside = Φ.fibre c'

/-- **Genuine height-one switching data** (tex L4976–5195) over a fixed configuration family `Φ`,
for the actual coordinate `u`: (a) a stage per configuration with a homotopy equivalence from the
genuine fiber; (b) the starting stage carries the actual class, the actual functional and the
coordinate `u`; (c) the switches follow the configuration sequence. -/
structure GenuineSwitchData (Φ : SwitchFamily k A) (ι : A →+* F) (ρ : A →+* k) (u : F) where
  stage : Φ.Config → TwoTermStage ι
  model : ∀ c, HomotopyEquiv (selCx (Φ.fibre c)).toCC (twoTermFiberComplex ρ (stage c))
  hz0 : ((model Φ.actual).hom.f 1).hom Φ.zAct = fun i => ρ ((stage Φ.actual).z i)
  hw0 : ∀ y, Φ.lamAct y =
    (fun i => ρ ((stage Φ.actual).w i)) ⬝ᵥ (((model Φ.actual).hom.f 2).hom y : Fin _ → k)
  hu0 : (stage Φ.actual).u = u
  σ : ∀ c, fiberH1 ρ (stage c) →ₗ[k] fiberH1 ρ (stage c)
  h2 : Φ.quadratic ρ → (2 : k) ≠ 0
  hσ : Φ.quadratic ρ → ∀ c, σ c ∘ₗ σ c = LinearMap.id
  primitive : ∀ c, Reach Φ.next Φ.actual c → ∃ i, ρ ((stage c).z i) ≠ 0
  switch_mixed : ∀ c, Reach Φ.next Φ.actual c → (¬ Φ.quadratic ρ ∨
      (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ c) (-1 : k)))) →
    1 < (stage c).fiberDim ρ →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      (Φ.quadratic ρ → Nonempty (GenuineMixedStep ρ Φ stage σ c (Φ.next c p))) ∧
      (¬ Φ.quadratic ρ → Nonempty (GenuineNonquadStep ρ Φ stage c (Φ.next c p)))
  switch_single : ∀ c, Reach Φ.next Φ.actual c → Φ.quadratic ρ →
    ¬ (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ c) (-1 : k))) →
    1 < (stage c).fiberDim ρ →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      Nonempty (GenuineSingleStep ρ Φ stage σ c (Φ.next c p))

namespace GenuineSwitchData

variable {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}

/-- **The fiber dimensions are the genuine ones** (tex L4976–4996): every stage's fiber dimension is
`dim_k H¹` of the configuration's genuine fiber. PROVED. -/
theorem fiberDim_eq (G : GenuineSwitchData Φ ι ρ u) (c : Φ.Config) :
    (G.stage c).fiberDim ρ = finrank k ((selCx (Φ.fibre c)).toCC.homology 1) :=
  fiberDim_eq_h1 k A F ι ρ (G.stage c) (Φ.fibre c) ⟨G.model c⟩

/-- **No free choice of fiber dimensions remains**: two genuine data over the same family have the
same fiber dimension at every configuration. PROVED. -/
theorem fiberDim_indep (G G' : GenuineSwitchData Φ ι ρ u) (c : Φ.Config) :
    (G.stage c).fiberDim ρ = (G'.stage c).fiberDim ρ := by
  rw [G.fiberDim_eq, G'.fiberDim_eq]

/-- **The Selmer-model switching data of a genuine datum**: stages are the reachable configurations,
and every switch goes to `next c p`. PROVED. -/
def toSelmerModelSwitchData (G : GenuineSwitchData Φ ι ρ u) : SelmerModelSwitchData ι ρ where
  Stage := {c // Reach Φ.next Φ.actual c}
  stage s := G.stage s.1
  σ s := G.σ s.1
  quadratic := Φ.quadratic ρ
  h2 := G.h2
  hσ q s := G.hσ q s.1
  primitive s := G.primitive s.1 s.2
  switch_mixed s h1 h2 := by
    obtain ⟨p, hc, hq, hn⟩ := G.switch_mixed s.1 s.2 h1 h2
    exact ⟨⟨Φ.next s.1 p, Reach.step p s.2⟩, hc,
      fun q => (hq q).map fun M => M.M, fun nq => (hn nq).map fun N => N.N⟩
  switch_single s q h1 h2 := by
    obtain ⟨p, hc, hs⟩ := G.switch_single s.1 s.2 q h1 h2
    exact ⟨⟨Φ.next s.1 p, Reach.step p s.2⟩, hc, hs.map fun M => M.M⟩

end GenuineSwitchData

/-- **The collapse no longer happens** (truth check D1): over a fixed family, a genuine datum whose
starting stage has fiber dimension one (the one-stage datum, where no switch is demanded) forces the
genuine starting fiber to have `dim_k H¹ = 1`; more generally the starting fiber dimension is the
genuine one, whatever datum is chosen. Classification: PROVED. -/
def CollapseForcesFibre : Prop :=
  ∀ (k : Type) [Field k] (A F : Type) [CommRing A] [Field F] (Φ : SwitchFamily k A)
    (ι : A →+* F) (ρ : A →+* k) (u : F) (G : GenuineSwitchData Φ ι ρ u),
    (G.stage Φ.actual).fiberDim ρ = 1 →
      finrank k ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) = 1

theorem collapse_forces_fibre : CollapseForcesFibre := by
  intro k _ A F _ _ Φ ι ρ u G h
  rw [← G.fiberDim_eq, h]

/-- **Regularity from genuine switching data** (tex L4976–5195): the actual coordinate lies in
`ι(A)`. Classification: PROVED (from the inputs of the datum). -/
def RegularOfGenuineSwitchData : Prop :=
  ∀ (k : Type) [Field k] (A F : Type) [CommRing A] [IsLocalRing A] [Field F] (Φ : SwitchFamily k A)
    (ι : A →+* F) (ρ : A →+* k) (u : F), Function.Injective ι →
    (∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) →
    GenuineSwitchData Φ ι ρ u → ∃ a : A, ι a = u

theorem regular_of_genuineSwitchData : RegularOfGenuineSwitchData := by
  intro k _ A F _ _ _ Φ ι ρ u hι hρ G
  obtain ⟨a, ha⟩ := regular_of_selmerModelSwitchData hι hρ G.toSelmerModelSwitchData
    ⟨Φ.actual, Reach.start⟩
  exact ⟨a, ha.trans G.hu0⟩

/-! ### Non-vacuity (LESSON 2) -/

section NonVacuity

/-- `ℚ` in degrees one and two, `0` elsewhere (dimension count). -/
def dim12 (n : ℤ) : ℕ := if n = 1 ∨ n = 2 then 1 else 0

/-- The module `ℚ^{dim12 n}`. -/
abbrev X12 (n : ℤ) : ModuleCat.{0} ℚ := ModuleCat.of ℚ (Fin (dim12 n) → ℚ)

/-- **The example fiber**: Selmer data with `G = ℚ` in degrees one and two (zero differential),
`U = L = 0`. Its Selmer complex is `ℚ` in degrees one and two with zero differential, the fiber of
a configuration with one surviving class and one dual class. -/
def exFibreD : SelData ℚ where
  G := zGCx X12
  U := zGCx Zn
  L := zGCx Zn
  res := zHom fun _ => 0
  ι := zHom fun _ => 0

/-- The example stage: `[ℚ --0--> ℚ]`, class and functional `1`, coordinate `1`. -/
def exGenStage : TwoTermStage (RingHom.id ℚ) where
  n := 0
  D := 0
  z := fun _ => 1
  w := fun _ => 1
  u := 1
  hz := by ext i; simp
  hw := by ext i; simp
  hu := by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.adjugate_fin_one, Matrix.vecMulVec_apply]

theorem exGenStage_fiberDim : exGenStage.fiberDim (RingHom.id ℚ) = 1 := by
  have := fiberDim_zero_matrix exGenStage rfl
  simpa [exGenStage] using this

theorem selCx_exFibre_d (i j : ℤ) : (selCx exFibreD).toCC.d i j = 0 := by
  by_cases h : i + 1 = j
  · ext x
    obtain ⟨a, b, c⟩ := x
    change (if h : i + 1 = j then ModuleCat.ofHom (selD exFibreD i j h) else 0).hom (a, b, c) = 0
    rw [dif_pos h]
    change selD exFibreD i j h (a, b, c) = 0
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    · exact funext fun x => Fin.elim0 x
    · exact funext fun x => Fin.elim0 x
  · exact (selCx exFibreD).toCC.shape i j h

theorem twoTerm_exGen_d (i j : ℤ) : (twoTermFiberComplex (RingHom.id ℚ) exGenStage).d i j = 0 := by
  by_cases h : i + 1 = j
  · subst h
    by_cases h0 : i = 0
    · subst h0
      change ModuleCat.ofHom (0 : PUnit.{1} →ₗ[ℚ] (Fin (0 + 1) → ℚ)) = 0
      rfl
    by_cases h1 : i = 1
    · subst h1
      change ModuleCat.ofHom ((exGenStage.D.map (RingHom.id ℚ)).mulVecLin) = 0
      rw [show (exGenStage.D.map (RingHom.id ℚ)).mulVecLin = 0 from by
        apply LinearMap.ext; intro x; ext i; simp [exGenStage]; rfl]
      rfl
    · exact threeTermD_eq_zero _ _ i (i + 1) (fun h => h0 h.1) (fun h => h1 h.1)
  · exact (twoTermFiberComplex (RingHom.id ℚ) exGenStage).shape i j h

instance finiteDimensional_exFibre (n : ℤ) :
    FiniteDimensional ℚ ((selCx exFibreD).toCC.X n) := by
  change FiniteDimensional ℚ ((Fin (dim12 n) → ℚ) × (Fin 0 → ℚ) × (Fin 0 → ℚ))
  infer_instance

theorem finite_of_subsingleton {M : Type} [AddCommGroup M] [Module ℚ M] [Subsingleton M] :
    Module.Finite ℚ M :=
  ⟨by rw [show (⊤ : Submodule ℚ M) = ⊥ from Subsingleton.elim _ _]; exact Submodule.fg_bot⟩

theorem subsingleton_exGen (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    Subsingleton ((twoTermFiberComplex (RingHom.id ℚ) exGenStage).X n) := by
  by_cases h0 : n = 0
  · subst h0
    exact ⟨fun _ _ => rfl⟩
  · exact threeTermX_subsingleton n h0 h1 h2

instance finiteDimensional_exGen (n : ℤ) :
    FiniteDimensional ℚ ((twoTermFiberComplex (RingHom.id ℚ) exGenStage).X n) := by
  by_cases h1 : n = 1
  · subst h1; change FiniteDimensional ℚ (Fin (0 + 1) → ℚ); infer_instance
  by_cases h2 : n = 2
  · subst h2; change FiniteDimensional ℚ (Fin (0 + 1) → ℚ); infer_instance
  have := subsingleton_exGen n h1 h2
  exact finite_of_subsingleton

theorem finrank_exFibre (n : ℤ) : finrank ℚ ((selCx exFibreD).toCC.X n) = dim12 n := by
  change finrank ℚ ((Fin (dim12 n) → ℚ) × (Fin 0 → ℚ) × (Fin 0 → ℚ)) = dim12 n
  simp

theorem finrank_exGen (n : ℤ) :
    finrank ℚ ((twoTermFiberComplex (RingHom.id ℚ) exGenStage).X n) = dim12 n := by
  by_cases h1 : n = 1
  · subst h1; change finrank ℚ (Fin (0 + 1) → ℚ) = dim12 1; simp [dim12]
  by_cases h2 : n = 2
  · subst h2; change finrank ℚ (Fin (0 + 1) → ℚ) = dim12 2; simp [dim12]
  have := subsingleton_exGen n h1 h2
  rw [Module.finrank_zero_of_subsingleton]
  simp [dim12, h1, h2]

/-- The degreewise isomorphisms of the example (equal finite dimensions). -/
def exGenIsoX (n : ℤ) :
    (selCx exFibreD).toCC.X n ≅ (twoTermFiberComplex (RingHom.id ℚ) exGenStage).X n :=
  (LinearEquiv.ofFinrankEq _ _ ((finrank_exFibre n).trans (finrank_exGen n).symm)).toModuleIso

/-- The example model: an isomorphism of complexes (both differentials vanish). -/
def exGenIso : (selCx exFibreD).toCC ≅ twoTermFiberComplex (RingHom.id ℚ) exGenStage :=
  HomologicalComplex.Hom.isoOfComponents exGenIsoX fun i j _ => by
    rw [selCx_exFibre_d, twoTerm_exGen_d]; simp

/-- **The example configuration family**: one configuration, no primes, fiber `exFibreD`, actual
class and functional the preimages of the stage class and functional, `t = 1` (nonquadratic). -/
def exGenuineFamily : SwitchFamily ℚ ℚ where
  Config := Unit
  Prime := Empty
  actual := ()
  next c _ := c
  fibre _ := exFibreD
  t := 1
  zAct := (exGenIso.inv.f 1).hom (fun _ => (1 : ℚ))
  hzAct := by rw [selCx_exFibre_d]; rfl
  lamAct :=
    { toFun := fun y => (fun _ => (1 : ℚ)) ⬝ᵥ ((exGenIso.hom.f 2).hom y : Fin (0 + 1) → ℚ)
      map_add' := fun y y' => by
        change (fun _ => (1 : ℚ)) ⬝ᵥ ((exGenIso.hom.f 2).hom (y + y') : Fin (0 + 1) → ℚ) = _
        rw [map_add]
        exact dotProduct_add _ _ _
      map_smul' := fun c y => by
        change (fun _ => (1 : ℚ)) ⬝ᵥ ((exGenIso.hom.f 2).hom (c • y) : Fin (0 + 1) → ℚ) = _
        rw [map_smul]
        exact dotProduct_smul _ _ _ }
  hlamAct y := by
    change (fun _ => (1 : ℚ)) ⬝ᵥ ((exGenIso.hom.f 2).hom (((selCx exFibreD).toCC.d 1 2).hom y) :
      Fin (0 + 1) → ℚ) = 0
    rw [selCx_exFibre_d]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
    exact dotProduct_zero (fun _ : Fin (0 + 1) => (1 : ℚ))

/-- **A genuine switching datum for the example family**: the model is the isomorphism `exGenIso`,
the starting stage carries the actual class and functional, and no switch is demanded (fiber
dimension one, forced by the genuine fiber). -/
def exGenuineSwitchData :
    GenuineSwitchData exGenuineFamily (RingHom.id ℚ) (RingHom.id ℚ) 1 where
  stage _ := exGenStage
  model _ := HomotopyEquiv.ofIso exGenIso
  hz0 := by
    change (exGenIso.inv.f 1 ≫ exGenIso.hom.f 1).hom (fun _ => (1 : ℚ)) = _
    rw [← HomologicalComplex.comp_f, exGenIso.inv_hom_id]
    rfl
  hw0 y := rfl
  hu0 := rfl
  σ _ := LinearMap.id
  h2 _ := two_ne_zero
  hσ _ _ := rfl
  primitive _ _ := ⟨0, one_ne_zero⟩
  switch_mixed _ _ _ h := absurd h (by rw [exGenStage_fiberDim]; exact lt_irrefl 1)
  switch_single _ _ _ _ h := absurd h (by rw [exGenStage_fiberDim]; exact lt_irrefl 1)

/-- **The example fiber dimension is forced**: it is the genuine `H¹` dimension `1` of the example
fiber. PROVED. -/
theorem exGenuine_fibre_forced :
    finrank ℚ ((selCx (exGenuineFamily.fibre exGenuineFamily.actual)).toCC.homology 1) = 1 :=
  collapse_forces_fibre ℚ ℚ ℚ _ _ _ _ exGenuineSwitchData exGenStage_fiberDim

/-- Regularity for the example (the coordinate `1`). -/
theorem exGenuine_regular : ∃ a : ℚ, RingHom.id ℚ a = 1 :=
  regular_of_genuineSwitchData ℚ ℚ ℚ _ _ _ _ Function.injective_id
    (fun x hx => by simpa using hx) exGenuineSwitchData

end NonVacuity

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
