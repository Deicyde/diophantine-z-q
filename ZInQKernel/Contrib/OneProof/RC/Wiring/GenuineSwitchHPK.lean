import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenuineSteps
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchPK

/-!
**Theorem 5.3: height-one switching data on the primitive kernel vector, with homology-level steps**

Proposition `ex:limits-uniform-lower-bound`, paragraph "Height-one regularity, including quadratic
specializations", tex 4976–5195 (switch sequences (5.5a), tex 5055–5086; localization duality,
tex 5068–5075).

**The obstruction removed.** `GenuineSwitchDataPK` (`GenuineSwitchPK.lean`) takes its switch steps
from batch 3's `GenuineMixedStep`, `GenuineNonquadStep` and `GenuineSingleStep`, whose model-step
bundles demand finite-dimensional cochain modules at their source (`fG : FiniteDimensional k
(R.D.G.X 1)`, tied to the configuration's fibre by `hF`). Over genuine continuous-cochain Selmer
data `C¹_cont` is infinite-dimensional, so no such step can be formed and every witness of the old
leaf has `dim H¹ = 1` at the actual fibre (the case `s(𝔭) > 1` of the switching argument is
excluded). The homology-level step bundles of the RC53 group (`QuasiMixedStep`, `QuasiNonquadStep`,
`QuasiSingleStep`, `GenuineSteps.lean`) ask only for finiteness of the cohomology of the switch
sides, which is the finiteness of Galois cohomology.

**The new structure.** `HomologySwitchDataPK Φ ι ρ u` has the fields of `GenuineSwitchDataPK`
(stages, the homotopy equivalences `model c : C(fibre c) ≃ [k^{n+1} --D̄--> k^{n+1}]`, the
actual class and functional at the start, the signs, the actual class of every reached
configuration nonzero) with the switch steps replaced by the homology-level bundles whose sides ARE the
configurations' fibres (`M.X.SF.Dside = Φ.fibre c`, `M.X.SS.Dside = Φ.fibre (Φ.next c p)`).

PROVED here:
* `HomologySwitchDataPK.toPK`, `regular_of_homologyPK`: over a DVR, `u ∈ ι(R)` (through the RC53
  group's `HeightOneSwitchDataPK` and `regular_of_switchDataPK`: the primitive kernel vectors from
  `class_ne_zero` by saturation, the dimension counts from the homology-level steps);
* `GenuineSwitchDataPK.toHomology`: the old data give the new (each literal step through batch 3's
  `toQuasi`), so the new leaves are implied by the old;
* the leaves `RegularityInputsHPK`, `PrimRegularityInputsHPK`, their consumers
  (`RegularityInputsHPK.mem_lambdaHalf`, `RegularityInputsHPK.toS`, `primRegularityInputs_of_HPK`,
  `heightOneTarget_of_HPK`) and the comparison `regularity_GPK_to_HPK`.

Non-vacuity, with a family whose fibres have infinite-dimensional global cochains, over which the
old data are impossible and the new data exist: `GenuineSwitchHNonVacuity.lean`.

**What remains.** The homotopy equivalences `model c` are existential: they are not tied to the
text's finite free models of the configuration's complex. The intended source is lane RC31's
`exists_gradedModel` (`RC/Limits/GradedFiniteFree.lean`, Lemma `ex:limits-inner-limit`, tex
4391–4451: a graded finite free model with actual inclusion, projection and contraction homotopy,
a homotopy equivalence by `GRetract.homotopyEquiv`, `RC/Limits/GradedModel.lean`); the identification
of the genuine derivative conditions with the quasi switch sides (`hF`, `hS`) and the remaining GLUE
of the step bundles (duality in the `localPair` form, `DetectingPrime`, `CoordStep`) are as in
`GenuineSteps.lean`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Module Matrix ZInQ.Manuscript.RC.Uniform
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.Uniform.QuadraticCase

section General

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]

/-- **Height-one switching data on the primitive kernel vector with homology-level steps** (tex
4976–5195) over a fixed configuration family `Φ`, for the actual coordinate `u`: the fields of
`GenuineSwitchDataPK`, with every switch step a homology-level bundle (the RC53 group's
`QuasiMixedStep`, `QuasiNonquadStep`, `QuasiSingleStep`) whose side complexes are the
configurations' fibres. No finiteness of cochain modules is asked. Kind: definition. -/
structure HomologySwitchDataPK (Φ : SwitchFamily k A) (ι : A →+* F) (ρ : A →+* k) (u : F) where
  /-- The two-term model of every configuration (tex 4983–4987). -/
  stage : Φ.Config → TwoTermStage ι
  /-- The model is homotopy equivalent to the configuration's fibre (tex 4976–4996). -/
  model : ∀ c, HomotopyEquiv (selCx (Φ.fibre c)).toCC (twoTermFiberComplex ρ (stage c))
  /-- The reduction of the starting stage's class is the family's actual fibre class. -/
  hz0 : ((model Φ.actual).hom.f 1).hom Φ.zAct = fun i => ρ ((stage Φ.actual).z i)
  /-- The family's actual functional is the starting stage's functional pulled back. -/
  hw0 : ∀ y, Φ.lamAct y =
    (fun i => ρ ((stage Φ.actual).w i)) ⬝ᵥ (((model Φ.actual).hom.f 2).hom y : Fin _ → k)
  /-- The starting stage's coordinate is `u` (tex 4986–4992, 5159–5189). -/
  hu0 : (stage Φ.actual).u = u
  /-- The cohomology signs (tex 5009–5054). -/
  σ : ∀ c, fiberH1 ρ (stage c) →ₗ[k] fiberH1 ρ (stage c)
  h2 : Φ.quadratic ρ → (2 : k) ≠ 0
  hσ : Φ.quadratic ρ → ∀ c, σ c ∘ₗ σ c = LinearMap.id
  /-- tex 4992, 5137–5144: the actual class of every reached configuration is nonzero. -/
  class_ne_zero : ∀ c, Reach Φ.next Φ.actual c → ∃ i, (stage c).z i ≠ 0
  /-- The switches with both signs (or at a nonquadratic prime), homology-level, sides the fibres
  (tex 4997–5003, 5055–5122, 5137–5153). -/
  switch_mixed : ∀ c, Reach Φ.next Φ.actual c → (¬ Φ.quadratic ρ ∨
      (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ c) (-1 : k)))) →
    1 < (stage c).fiberDim ρ →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      (Φ.quadratic ρ → ∃ M : QuasiMixedStep ρ (stage c) (stage (Φ.next c p)) (σ c)
          (σ (Φ.next c p)), M.X.SF.Dside = Φ.fibre c ∧ M.X.SS.Dside = Φ.fibre (Φ.next c p)) ∧
      (¬ Φ.quadratic ρ → ∃ N : QuasiNonquadStep ρ (stage c) (stage (Φ.next c p)),
          N.SF.Dside = Φ.fibre c ∧ N.SS.Dside = Φ.fibre (Φ.next c p))
  /-- The switches with one sign only, homology-level, sides the fibres (tex 5123–5136). -/
  switch_single : ∀ c, Reach Φ.next Φ.actual c → Φ.quadratic ρ →
    ¬ (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ c) (-1 : k))) →
    1 < (stage c).fiberDim ρ →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ M : QuasiSingleStep ρ (stage c) (stage (Φ.next c p)) (σ (Φ.next c p)),
        M.X.SF.Dside = Φ.fibre c ∧ M.X.SS.Dside = Φ.fibre (Φ.next c p)

variable {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}

/-- **The RC53 group's height-one switching data from the homology-level data** (over a DVR): the
reached configurations as stages, the primitive kernel vectors by saturation
(`exists_primitiveKernelVector`, tex 4987–4992), `s₊ + s₋ = s` from the involution splitting, and
the dimension inputs of the switches from the homology-level steps (`toQuadMixedDims`,
`toNonquadDims`, `toQuadSingleDims`, with the fibre isomorphisms). Kind: PROVED. -/
def HomologySwitchDataPK.toPK [IsDomain A] [IsDiscreteValuationRing A]
    (hι : Function.Injective ι) (G : HomologySwitchDataPK Φ ι ρ u) :
    HeightOneSwitchDataPK ι ρ where
  Stage := {c // Reach Φ.next Φ.actual c}
  stage s := G.stage s.1
  quadratic := Φ.quadratic ρ
  sp s := finrank k ↥(signPart (G.σ s.1) (1 : k))
  sm s := finrank k ↥(signPart (G.σ s.1) (-1 : k))
  sign_sum q s := by
    have := fiberH1_finite ρ (G.stage s.1)
    rw [← finrank_h1_twoTermFiberComplex ρ (G.stage s.1),
      (involutionSplitting_proof k _ (G.σ s.1) (G.h2 q) (G.hσ q s.1)).2.2 this,
      signPart_one_eq_plusPart, signPart_neg_one_eq_minusPart]
  primitiveKernel s := exists_primitiveKernelVector hι ρ (G.stage s.1) (G.class_ne_zero s.1 s.2)
  switch_mixed s h1 h2 := by
    obtain ⟨p, hc, hq, hn⟩ := G.switch_mixed s.1 s.2 h1 h2
    refine ⟨⟨Φ.next s.1 p, Reach.step p s.2⟩, hc, fun q => ?_, fun nq => ?_⟩
    · obtain ⟨M, -, -⟩ := hq q
      exact ⟨QuadMixedDims.cast' (M.X.toQuadMixedDims M.h2 M.ε M.hε M.hJ2 M.ep M.em M.hp M.hm M.he
        M.hU M.cp M.cm M.hcp M.hcm M.hdet)
        (finrank_signPart_of_equiv M.φ M.hφ 1).symm (finrank_signPart_of_equiv M.φ M.hφ (-1)).symm
        (finrank_signPart_of_equiv M.φ' M.hφ' 1).symm
        (finrank_signPart_of_equiv M.φ' M.hφ' (-1)).symm⟩
    · obtain ⟨N, -, -⟩ := hn nq
      exact ⟨N.toNonquadDims⟩
  switch_single s q h1 h2 := by
    obtain ⟨p, hc, M, -, -⟩ := G.switch_single s.1 s.2 q h1 h2
    refine ⟨⟨Φ.next s.1 p, Reach.step p s.2⟩, finrank k ↥(signPart M.X.σV' (1 : k)),
      finrank k ↥(signPart M.X.σV' (-1 : k)), hc, ⟨QuadSingleDims.cast'
        (M.X.toQuadSingleDims M.h2 M.ε M.hε M.hJ2 M.ep M.em M.hp M.hm M.he M.hU M.cp M.hcp M.hdet
          M.hs1 M.hs0) ?_ rfl rfl⟩, ?_⟩
    · have hV := M.X.fV
      rw [fiberDim_eq_of_h1Equiv ρ _ M.φ,
        (involutionSplitting_proof k _ M.X.σV M.h2 M.X.hV).2.2 hV,
        signPart_one_eq_plusPart, ← signPart_neg_one_eq_minusPart, ← M.hs0, add_zero]
    · rcases M.hφ' with h | h
      · exact Or.inl ⟨(finrank_signPart_of_equiv M.φ' h 1).symm,
          (finrank_signPart_of_equiv M.φ' h (-1)).symm⟩
      · refine Or.inr ⟨?_, ?_⟩
        · change finrank k ↥(signPart (G.σ (Φ.next s.1 p)) (1 : k)) = _
          rw [finrank_signPart_of_equiv M.φ' h (-1), signPart_neg_eq, neg_neg]
        · change finrank k ↥(signPart (G.σ (Φ.next s.1 p)) (-1 : k)) = _
          rw [finrank_signPart_of_equiv M.φ' h 1, signPart_neg_eq]

/-- **The old data give the new**: every `GenuineSwitchDataPK` gives a `HomologySwitchDataPK` over
the same family, with the same stages, models and signs, each literal step through batch 3's
`toQuasi`. Kind: PROVED. -/
def GenuineSwitchDataPK.toHomology (G : GenuineSwitchDataPK Φ ι ρ u) :
    HomologySwitchDataPK Φ ι ρ u where
  stage := G.stage
  model := G.model
  hz0 := G.hz0
  hw0 := G.hw0
  hu0 := G.hu0
  σ := G.σ
  h2 := G.h2
  hσ := G.hσ
  class_ne_zero := G.class_ne_zero
  switch_mixed c hc h1 h2 := by
    obtain ⟨p, hcs, hq, hn⟩ := G.switch_mixed c hc h1 h2
    refine ⟨p, hcs, fun q => ?_, fun nq => ?_⟩
    · obtain ⟨M⟩ := hq q
      exact ⟨M.M.toQuasi, M.hF, M.hS⟩
    · obtain ⟨N⟩ := hn nq
      exact ⟨N.N.toQuasi, N.hF, N.hS⟩
  switch_single c hc q h1 h2 := by
    obtain ⟨p, hcs, ⟨M⟩⟩ := G.switch_single c hc q h1 h2
    exact ⟨p, hcs, M.M.toQuasi, M.hF, M.hS⟩

/-- **Regularity from the homology-level data** (tex 4976–5195): over a DVR `A` with residue map
`ρ`, the actual coordinate lies in `ι(A)`. Kind: PROVED. -/
theorem regular_of_homologyPK [IsDomain A] [IsDiscreteValuationRing A]
    (hι : Function.Injective ι) (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0)
    (G : HomologySwitchDataPK Φ ι ρ u) : ∃ a : A, ι a = u := by
  obtain ⟨a, ha⟩ := regular_of_switchDataPK hι hρ (G.toPK hι) ⟨Φ.actual, Reach.start⟩
  exact ⟨a, ha.trans G.hu0⟩

end General

/-! **The leaves with homology-level switching data** -/

section Leaves

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Rings ZInQ.Contrib.CloudB3RC53

/-- **The regularity inputs with homology-level switching data** (tex 4976–5194): `u = 0`, or at
every height-one prime `𝔭 ≠ (2)` of `Λ` a configuration family genuine at `𝔭` with
`HomologySwitchDataPK` over it starting at `u`. As `RegularityInputsGPK`, with the homology-level
steps. Kind: definition. -/
def RegularityInputsHPK (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
    ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      Nonempty (HomologySwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u)

/-- **The new regularity inputs give `u ∈ Λ[1/2]`** (tex 4976–5195, 5196–5200): at every height-one
prime `𝔭 ≠ (2)` the coordinate is in `Λ_𝔭` (`regular_of_homologyPK` over the DVR `Λ_𝔭`, lane RC20's
`isDiscreteValuationRing_atPrime_of_height_one`). Kind: PROVED. -/
theorem RegularityInputsHPK.mem_lambdaHalf {u : FractionRing Lambda}
    (h : RegularityInputsHPK u) : u ∈ lambdaHalfToFrac.range := by
  rw [mem_range_lambdaHalf_iff_forall_height_one]
  intro P _ hP hne
  rcases h with rfl | h
  · exact Subalgebra.zero_mem _
  · obtain ⟨Φ, -, ⟨G⟩⟩ := h P hP hne
    have := isDiscreteValuationRing_atPrime_of_height_one P hP
    obtain ⟨a, ha⟩ := regular_of_homologyPK (UniformSwitch.toFracAt_injective P)
      (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx) G
    rw [← ha]
    exact ⟨a, rfl⟩

/-- **The old regularity inputs give the new** (`GenuineSwitchDataPK.toHomology`). Kind: PROVED. -/
theorem regularity_GPK_to_HPK {u : FractionRing Lambda} (h : RegularityInputsGPK u) :
    RegularityInputsHPK u := by
  rcases h with h0 | h
  · exact Or.inl h0
  · refine Or.inr fun P _ hP hne => ?_
    obtain ⟨Φ, hΦ, ⟨G⟩⟩ := h P hP hne
    exact ⟨Φ, hΦ, ⟨G.toHomology⟩⟩

/-- **The new regularity inputs give the consumers' form** `RegularityInputsS`. Kind: PROVED. -/
theorem RegularityInputsHPK.toS {u : FractionRing Lambda} (h : RegularityInputsHPK u) :
    RegularityInputsS u := (regularityInputsS_iff u).mpr h.mem_lambdaHalf

/-- **The height-one regularity inputs of the primitive coordinates, homology-level** (tex
4976–5197): for every final family and address, a `T`-expansion `u` of the primitive coordinate
with `RegularityInputsHPK u`. Kind: definition. -/
def PrimRegularityInputsHPK {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    ∃ u : FractionRing Lambda, IsTExpansion u (D.uPrim F x) ∧ RegularityInputsHPK u

/-- **`PrimRegularityInputs` from the homology-level inputs**: every primitive coordinate is in
`Λ[1/2]`. Kind: PROVED. -/
theorem primRegularityInputs_of_HPK {ℓ : ℕ} (D : RCData ℓ) (h : PrimRegularityInputsHPK D) :
    PrimRegularityInputs D := by
  apply (primRegularityInputs_iff D).mpr
  intro Co Ce F hF x
  obtain ⟨u, hT, hu⟩ := h Co Ce F hF x
  exact inLamHalf_of_isTExpansion hT hu.mem_lambdaHalf

/-- **The height-one target from the homology-level inputs** and the common-coordinate target.
Kind: PROVED. -/
theorem heightOneTarget_of_HPK {ℓ : ℕ} (D : RCData ℓ) (h : PrimRegularityInputsHPK D)
    (h47 : CommonCoordinateTarget D) : HeightOneTarget D :=
  heightOneTarget_of_inputs D (primRegularityInputs_of_HPK D h) h47

end Leaves

end ZInQ.Manuscript.RC.Wiring
