import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchPK
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchCollapse
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineOuterTies

/-!
**Theorem 5.3, Lane RC0 round 8: non-vacuity of the leaves on the text's primitive kernel vector**

Checks for `GenuineSwitchDataPK` and `RegularityInputsGPK` (`GenuineSwitchPK.lean`), all PROVED:

* **The old structure pins the actual fiber class** (`isEmpty_genuineSwitchData_of_zAct_eq_zero`):
  batch 3's `GenuineSwitchData` over a family whose actual fiber class `zAct` is `0` does not exist,
  for any coordinate (its fields `hz0` and `primitive` make the reduction of the actual class
  nonzero). In the text the actual class `z = c · v` may be divisible by the uniformizer (tex
  4987–4992), and then its reduction, the actual fiber class, is `0`.
* **At the level of the structure, over the DVR `ℚ⟦X⟧`** (residue map the constant coefficient):
  `exPKFamily` (one configuration, fiber batch 3's `exFibreD`, actual fiber class and functional
  `0`, nonquadratic), with `exPKData : GenuineSwitchDataPK exPKFamily psι psρ (psι (X²))` on the
  RC53 group's `peerStage` (`[ℚ⟦X⟧ --0--> ℚ⟦X⟧]`, actual class `z = X`, functional `X`); its actual
  class is not primitive (`exPKData_not_primitive`), its primitive kernel vector is derived
  (`exPKData_primitiveKernel`), its coordinate `X²` is regular (`exPKData_regular`), and the old
  structure rejects the family for every coordinate (`exPKFamily_no_old`, `exPK_contrast`).
* **At the level of the leaf** (families genuine at `𝔭`): a witness with `u ≠ 0` needs a genuine
  Galois Selmer complex over `k(𝔭)` with nonzero `H¹`, which is not in the tree (the statement `E`
  of `GenuineSwitchCollapse.lean`). The only formalized genuine family has `H¹ = 0` and carries
  neither old nor new data (`exZeroFamily_no_dataPK`). Under `E` at one height-one prime
  `𝔭 ≠ (2)`, `leafContrast_of_unitFibre` gives a family genuine at `𝔭` with a new datum at a
  nonzero coordinate whose actual class is the uniformizer of `Λ_𝔭` (not primitive), over which no
  old datum exists; and `regularityInputsGPK_iff_of_unitFibre` (under `E` everywhere the new leaf
  is equivalent to its target, as the old one).
* Satisfiability of the new leaves: `primRegularityInputsGPK_of_uPrim_zero`,
  `eq35InputsGenuineGGPK_of_not_prepared` (degenerate witnesses, as for the old leaves).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings
  Module CategoryTheory Matrix

open ZInQ.Contrib.CloudB3RC53.PairedFunctional (SelData selCx)
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (SwitchFamily GenuineSwitchData Reach
  twoTermFiberComplex exFibreD exGenStage exGenIso)
open ZInQ.Contrib.CloudB3RC53.UniformSwitch (TwoTermStage psι psρ psι_injective psρ_maximalIdeal
  peerStage peerStage_fiberDim peerStage_not_primitive PrimitiveKernelVector)

/-! **The old structure pins the actual fiber class** -/

section Pin

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]

/-- **No old datum over a family whose actual fiber class is zero**, whatever the coordinate:
`hz0` makes the reduction of the starting class the image of `zAct = 0`, which `primitive`
forbids. The new structure has no such constraint. Kind: PROVED. -/
theorem isEmpty_genuineSwitchData_of_zAct_eq_zero {Φ : SwitchFamily k A} {ι : A →+* F}
    {ρ : A →+* k} (h0 : Φ.zAct = 0) (u : F) : IsEmpty (GenuineSwitchData Φ ι ρ u) := by
  refine ⟨fun G => ?_⟩
  obtain ⟨i, hi⟩ := G.primitive Φ.actual Reach.start
  have h := G.hz0
  rw [h0, map_zero] at h
  have h' : (0 : Fin ((G.stage Φ.actual).n + 1) → k) =
      fun i => ρ ((G.stage Φ.actual).z i) := h
  exact hi (by simpa using (congrFun h' i).symm)

end Pin

/-! **A family that the new structure admits and the old one rejects, over `ℚ⟦X⟧`** -/

section PowerSeriesExample

/-- The fiber of the RC53 group's `peerStage` is the fiber of batch 3's `exGenStage` (both are
`[ℚ --0--> ℚ]`). Kind: PROVED. -/
theorem twoTerm_peerStage_eq :
    twoTermFiberComplex psρ peerStage = twoTermFiberComplex (RingHom.id ℚ) exGenStage := by
  have hD : peerStage.D.map psρ = exGenStage.D.map (RingHom.id ℚ) := by
    ext i j
    show psρ (peerStage.D i j) = RingHom.id ℚ (exGenStage.D i j)
    rw [show peerStage.D i j = 0 from rfl, show exGenStage.D i j = 0 from rfl, map_zero,
      map_zero]
  unfold twoTermFiberComplex
  simp only [hD]
  rfl

/-- The model of the example: batch 3's `exGenIso`, read on the fiber of `peerStage`. -/
def exPKIso : (selCx exFibreD).toCC ≅ twoTermFiberComplex psρ peerStage :=
  exGenIso ≪≫ eqToIso twoTerm_peerStage_eq.symm

/-- **The example configuration family over `ℚ⟦X⟧`**: one configuration, no primes, fiber batch 3's
`exFibreD` (`ℚ` in degrees one and two), actual fiber class and functional `0` (the reduction of a
class and a functional divisible by `X`), `t = 1` (nonquadratic). Kind: definition. -/
def exPKFamily : SwitchFamily ℚ (PowerSeries ℚ) where
  Config := Unit
  Prime := Empty
  actual := ()
  next c _ := c
  fibre _ := exFibreD
  t := 1
  zAct := 0
  hzAct := map_zero _
  lamAct := 0
  hlamAct _ := rfl

/-- **A new datum over the example family** (non-vacuity of `GenuineSwitchDataPK`): the stage
`peerStage` (`[ℚ⟦X⟧ --0--> ℚ⟦X⟧]`, actual class `z = X`, functional `w = X`, coordinate `X²`), the
model `exPKIso`, and no switch (fiber dimension one). Kind: definition. -/
def exPKData : GenuineSwitchDataPK exPKFamily psι psρ (psι (PowerSeries.X ^ 2)) where
  stage _ := peerStage
  model _ := HomotopyEquiv.ofIso exPKIso
  hz0 := by
    change (exPKIso.hom.f 1).hom (0 : (selCx exFibreD).toCC.X 1) = _
    rw [map_zero]
    show (0 : Fin (0 + 1) → ℚ) = fun i => psρ (peerStage.z i)
    funext i
    simp [peerStage]
  hw0 y := by
    show exPKFamily.lamAct y =
      (fun i => psρ (peerStage.w i)) ⬝ᵥ ((exPKIso.hom.f 2).hom y : Fin (0 + 1) → ℚ)
    have hX : psρ PowerSeries.X = 0 := by simp
    simp only [dotProduct, peerStage, hX, zero_mul, Finset.sum_const_zero]
    rfl
  hu0 := rfl
  σ _ := LinearMap.id
  h2 _ := two_ne_zero
  hσ _ _ := LinearMap.id_comp _
  class_ne_zero _ _ := ⟨0, PowerSeries.X_ne_zero⟩
  switch_mixed _ _ _ h := absurd h (by rw [peerStage_fiberDim]; exact lt_irrefl 1)
  switch_single _ _ _ _ h := absurd h (by rw [peerStage_fiberDim]; exact lt_irrefl 1)

/-- **The actual class of the example is not primitive** (it reduces to `0`). Kind: PROVED. -/
theorem exPKData_not_primitive :
    ¬ ∃ i, psρ ((exPKData.stage exPKFamily.actual).z i) ≠ 0 :=
  peerStage_not_primitive

/-- **The primitive kernel vector of the example is derived** (saturation over the DVR `ℚ⟦X⟧`).
Kind: PROVED. -/
theorem exPKData_primitiveKernel :
    Nonempty (PrimitiveKernelVector (exPKData.stage exPKFamily.actual) psρ) :=
  exPKData.primitiveKernel psι_injective exPKFamily.actual Reach.start

/-- **Regularity for the example**: the coordinate `X²` is integral. Kind: PROVED. -/
theorem exPKData_regular : ∃ a : PowerSeries ℚ, psι a = psι (PowerSeries.X ^ 2) :=
  regular_of_genuineSwitchDataPK psι_injective psρ_maximalIdeal exPKData

/-- **The old structure rejects the example family for every coordinate.** Kind: PROVED. -/
theorem exPKFamily_no_old (u : FractionRing (PowerSeries ℚ)) :
    IsEmpty (GenuineSwitchData exPKFamily psι psρ u) :=
  isEmpty_genuineSwitchData_of_zAct_eq_zero rfl u

/-- **The weakening is strict at the level of the structure**: over `exPKFamily` there is a new
datum and no old one. Kind: PROVED. -/
theorem exPK_contrast :
    Nonempty (GenuineSwitchDataPK exPKFamily psι psρ (psι (PowerSeries.X ^ 2))) ∧
      ∀ u, IsEmpty (GenuineSwitchData exPKFamily psι psρ u) :=
  ⟨⟨exPKData⟩, exPKFamily_no_old⟩

end PowerSeriesExample

/-! **At the level of the leaf** -/

section Leaf

variable (P : Ideal Lambda) [P.IsPrime]

/-- **The zero genuine family carries no new datum either**, for any coordinate (its fiber has
`H¹ = 0`). Kind: PROVED. -/
theorem exZeroFamily_no_dataPK (u : FractionRing Lambda) :
    IsEmpty (GenuineSwitchDataPK (exZeroFamily P) (UniformSwitch.toFracAt P) (resAt P) u) :=
  isEmpty_genuineSwitchDataPK_of_h1_eq_zero (UniformSwitch.toFracAt_injective P) u
    (exZeroFamily_h1 P)

/-- The stage `[Λ_𝔭 --0--> Λ_𝔭]` with actual class and functional `a` and coordinate `a²`.
Kind: definition. -/
def scalarStageAt (a : Localization.AtPrime P) :
    TwoTermStage (UniformSwitch.toFracAt P) where
  n := 0
  D := 0
  z := fun _ => a
  w := fun _ => a
  u := UniformSwitch.toFracAt P (a ^ 2)
  hz := by simp
  hw := by simp
  hu := by
    unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
    rw [adjugate_fin_one]
    ext i j; fin_cases i; fin_cases j; simp [vecMulVec, pow_two]

theorem scalarStageAt_fiberDim (a : Localization.AtPrime P) :
    (scalarStageAt P a).fiberDim (resAt P) = 1 := by
  have h0 : ((scalarStageAt P a).D.map (resAt P)).mulVecLin = 0 := by
    apply LinearMap.ext; intro v; ext i
    simp [scalarStageAt]; rfl
  rw [TwoTermStage.fiberDim, h0, LinearMap.ker_zero, finrank_top, finrank_fin_fun]; rfl

variable {P}

/-- The one-configuration family over a genuine fiber `F` with actual fiber class and functional
`0` and moving variable `t = X`. Kind: definition. -/
def zeroClassFamily (F : SelData (ResAt P)) : SwitchFamily (ResAt P) (Localization.AtPrime P) where
  Config := Unit
  Prime := Empty
  actual := ()
  next c _ := c
  fibre _ := F
  t := algebraMap Lambda (Localization.AtPrime P) PowerSeries.X
  zAct := 0
  hzAct := map_zero _
  lamAct := 0
  hlamAct _ := rfl

/-- **A new datum whose actual class `a ∈ 𝔪` is not primitive**, over `zeroClassFamily F`, from a
model `e` of `F` by the one-stage fiber (no switch is demanded since the fiber dimension is one).
Kind: definition. -/
def zeroClassData (F : SelData (ResAt P)) (e : HomotopyEquiv (selCx F).toCC (unitFibre P))
    (h2 : (2 : ResAt P) ≠ 0) (a : Localization.AtPrime P)
    (ha : a ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P)) (ha0 : a ≠ 0) :
    GenuineSwitchDataPK (zeroClassFamily F) (UniformSwitch.toFracAt P) (resAt P)
      (UniformSwitch.toFracAt P (a ^ 2)) where
  stage _ := scalarStageAt P a
  model _ := e
  hz0 := by
    change (e.hom.f 1).hom (0 : (selCx F).toCC.X 1) = _
    rw [map_zero]
    show (0 : Fin (0 + 1) → ResAt P) = fun _ => resAt P a
    funext i
    exact ((IsLocalRing.residue_eq_zero_iff a).2 ha).symm
  hw0 y := by
    show (zeroClassFamily F).lamAct y =
      (fun _ => resAt P a) ⬝ᵥ ((e.hom.f 2).hom y : Fin (0 + 1) → ResAt P)
    have hra : resAt P a = 0 := (IsLocalRing.residue_eq_zero_iff a).2 ha
    simp only [dotProduct, hra, zero_mul, Finset.sum_const_zero]
    rfl
  hu0 := rfl
  σ _ := LinearMap.id
  h2 _ := h2
  hσ _ _ := LinearMap.id_comp _
  class_ne_zero _ _ := ⟨0, ha0⟩
  switch_mixed _ _ _ h := absurd h (by rw [scalarStageAt_fiberDim]; exact lt_irrefl 1)
  switch_single _ _ _ _ h := absurd h (by rw [scalarStageAt_fiberDim]; exact lt_irrefl 1)

/-- **The weakening at the level of the leaf, under `E` at one prime**: if at a height-one prime
`𝔭 ≠ (2)` some genuine Galois Selmer datum `F` over `k(𝔭)` is homotopy equivalent to the one-stage
fiber, then there is a family genuine at `𝔭` with a new datum at a nonzero coordinate (actual class
the uniformizer of `Λ_𝔭`, not primitive) over which no old datum exists for any coordinate.
Kind: PROVED. -/
theorem leafContrast_of_unitFibre (hP : P.height = 1) (hne : P ≠ Ideal.span {2})
    (F : SelData (ResAt P)) (hF : IsGaloisSelData F)
    (e : HomotopyEquiv (selCx F).toCC (unitFibre P)) :
    ∃ (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)) (u : FractionRing Lambda),
      IsGenuineFamilyAt P Φ ∧ u ≠ 0 ∧
      Nonempty (GenuineSwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u) ∧
      ∀ u', IsEmpty (GenuineSwitchData Φ (UniformSwitch.toFracAt P) (resAt P) u') := by
  have := isDiscreteValuationRing_atPrime_of_height_one P hP
  have hc := charZero_residueField_of_height_one P hP hne
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  have hm : ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  refine ⟨zeroClassFamily F, UniformSwitch.toFracAt P (ϖ ^ 2), ⟨fun _ => hF, rfl⟩, ?_,
    ⟨zeroClassData F e two_ne_zero ϖ hm hϖ.ne_zero⟩,
    fun u' => isEmpty_genuineSwitchData_of_zAct_eq_zero rfl u'⟩
  exact (map_ne_zero_iff _ (UniformSwitch.toFracAt_injective P)).mpr (pow_ne_zero 2 hϖ.ne_zero)

/-- **Under `E` the new height-one inputs are target-shaped, as the old ones**
(`regularityInputsG_of_unitFibre` and `RegularityInputsG.toPK`). Kind: PROVED. -/
theorem regularityInputsGPK_iff_of_unitFibre
    (hE : ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
      (2 : ResAt P) ≠ 0 ∧ ∃ F : SelData (ResAt P), IsGaloisSelData F ∧
        Nonempty (HomotopyEquiv (selCx F).toCC (unitFibre P))) (u : FractionRing Lambda) :
    RegularityInputsGPK u ↔ u ∈ lambdaHalfToFrac.range :=
  ⟨fun h => h.mem_lambdaHalf, fun hu => (regularityInputsG_of_unitFibre hu hE).toPK⟩

end Leaf

/-! **Satisfiability of the new leaves** -/

/-- **`PrimRegularityInputsGPK D` is satisfiable** (through its `u = 0` branch) whenever the
primitive coordinates vanish. Kind: PROVED. -/
theorem primRegularityInputsGPK_of_uPrim_zero {ℓ : ℕ} (D : RCData ℓ)
    (hD : ∀ F x, D.uPrim F x = 0) : PrimRegularityInputsGPK D :=
  PrimRegularityInputsG.toPK D (primRegularityInputsG_of_uPrim_zero D hD)

/-- **`Eq35InputsGenuineGGPK W` is satisfiable**: it holds when the prepared filter is empty.
Kind: PROVED. -/
theorem eq35InputsGenuineGGPK_of_not_prepared {ℓ : ℕ} (W : WData ℓ) (hW : ∀ h, ¬ W.prepared h) :
    Eq35InputsGenuineGGPK W :=
  Eq35InputsGenuineGG.toPK W (eq35InputsGenuineGG_of_not_prepared W hW)

end ZInQ.Manuscript.RC.Wiring
