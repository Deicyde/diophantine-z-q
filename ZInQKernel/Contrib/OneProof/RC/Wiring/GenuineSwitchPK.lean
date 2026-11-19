import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineEq35Leaf
import ZInQKernel.Contrib.CloudB3RC53.UniformSwitch.PrimitiveKernel
import ZInQKernel.Contrib.OneProof.RC.Rings.HeightOne

/-!
**Theorem 5.3, Lane RC0 round 8: the height-one leaves on the text's primitive kernel vector**

Proposition `ex:limits-uniform-lower-bound`, paragraph "Height-one regularity, including quadratic
specializations", tex 4976–5195 (with the unknown base, tex 5196–5200).

**The departure removed.** The leaves `PostLeaves.prim_regular` and the regularity part of
`PreLeaves.eq35` asked, through `RegularityInputsG` (`GenuineSwitchLeaf.lean`), for batch 3's
`GenuineSwitchData`, whose field `primitive` (`∃ i, ρ ((stage c).z i) ≠ 0` at every reached
configuration) says that the actual class itself is primitive. The text separates a primitive
kernel vector from the actual class (tex 4987–4992): "Choose a primitive vector `v ∈ ker d`. Such a
vector exists because `ker d` is saturated in `R^s`: divide a nonzero kernel vector by its largest
common power of a uniformizer. Thus `v̄ ≠ 0` in `V = H¹(C ⊗_R k)` and `dim_k V = s ≥ 1`. The actual
class `z` is a nonzero fraction-field multiple of `v`." The vector `v` only selects the primes; "we
do not replace the actual class by the chosen primitive vector" (tex 5145–5147). At the later
configurations the new class spans the new generic kernel (tex 5137–5144), and "each new generic
kernel has rank one and has a primitive integral vector, so its fiber dimension is at least one"
(tex 5154–5157; tex 5131–5134 after a single-sign switch).

**The new structure.** `GenuineSwitchDataPK Φ ι ρ u` has the fields of `GenuineSwitchData`, with
`primitive` replaced by `class_ne_zero`: the actual class of every reached configuration is
NONZERO (`∃ i, (stage c).z i ≠ 0`). The primitive kernel vector is not an input: over the DVR
`R = Λ_𝔭` (lane RC20's `isDiscreteValuationRing_atPrime_of_height_one`) it is PROVED by the text's
saturation argument (the RC53 group's `exists_primitiveKernelVector`), and `pos` follows from `v̄`
(`one_le_fiberDim_of_primitiveKernel`), through the RC53 group's `HeightOneSwitchDataPK` and
`regular_of_switchDataPK`.

PROVED here:
* `GenuineSwitchDataPK.primitiveKernel`: over a DVR, every reached configuration has a primitive
  kernel vector `v` (`D v = 0`, `v̄ ≠ 0`) of which its actual class is a nonzero fraction-field
  multiple;
* `GenuineSwitchDataPK.toSwitchDataPK`, `regular_of_genuineSwitchDataPK`: `u ∈ ι(R)` (the switch
  fields as in batch 3's `toSelmerModelSwitchData`, `toSelmerSwitchData` and `toSwitchData`);
* `GenuineSwitchDataPK.ofGenuineSwitchData`: batch 3's data give the new data with the same stages
  (a primitive class is nonzero), so every new leaf is implied by the old one;
* the leaves `RegularityInputsGPK`, `PrimRegularityInputsGPK`, `Eq35InputsGenuineGGPK` (the round 4
  leaves with `GenuineSwitchDataPK` in place of `GenuineSwitchData`), their conversions to the
  consumers of the round 4 leaves (`RegularityInputsGPK.toS`, `heightOneTarget_of_inputsGPK`,
  `primRegularityInputs_of_GPK`, `eq35Target_of_inputsGGPK`) and from the round 4 leaves
  (`RegularityInputsG.toPK`, `PrimRegularityInputsG.toPK`, `Eq35InputsGenuineGG.toPK`);
* ties: `GenuineSwitchDataPK.fiberDim_eq`, `GenuineSwitchDataPK.one_le_h1`,
  `isEmpty_genuineSwitchDataPK_of_h1_eq_zero`, `RegularityInputsGPK.fiberDim_forced`,
  `RegularityInputsGPK.oneStage_forces`.

Non-vacuity, and a family that the new structure admits and the old one rejects:
`GenuineSwitchPKNonVacuity.lean`.

**Caveat** (as for the round 4 leaves, `GenuineSwitchLeaf.lean`). The configuration family is
existential and only required to be some genuine Galois Selmer data with `t = X`. Over the actual
genuine complexes of the address no switch step can be formed (`fG`: `C¹_cont` is
infinite-dimensional), so the actual family witnesses the leaf only when `s(𝔭) = 1`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings Module CategoryTheory Filter

open ZInQ.Contrib.CloudB3RC53.PairedFunctional (SelData selCx)
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (SwitchFamily GenuineSwitchData Reach)
open ZInQ.Manuscript.RC.Determinant (OO)

attribute [local instance] Nat.fact_prime_two

/-! **Genuine switching data with the text's primitive kernel vector** -/

section General

open ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Contrib.CloudB3RC53.UniformSwitch Matrix

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]

/-- **Genuine height-one switching data on the text's primitive kernel vector** (tex 4976–5195)
over a fixed configuration family `Φ`, for the actual coordinate `u`: the fields of batch 3's
`GenuineSwitchData`, with its field `primitive` (the actual class itself primitive) replaced by
`class_ne_zero` (the actual class nonzero). The primitive kernel vector of the text is derived from
`class_ne_zero` over a DVR (`GenuineSwitchDataPK.primitiveKernel`). Kind: definition. -/
structure GenuineSwitchDataPK (Φ : SwitchFamily k A) (ι : A →+* F) (ρ : A →+* k) (u : F) where
  /-- The two-term model of every configuration (tex 4983–4987). -/
  stage : Φ.Config → TwoTermStage ι
  /-- The model is a finite free model of the configuration's fiber (tex 4976–4996). -/
  model : ∀ c, HomotopyEquiv (selCx (Φ.fibre c)).toCC (twoTermFiberComplex ρ (stage c))
  /-- The reduction of the starting stage's class is the family's actual fiber class. -/
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
  /-- tex 4992, 5137–5144: the actual class of every reached configuration is nonzero ("a nonzero
  fraction-field multiple of `v`"; the new class spans the new generic kernel). -/
  class_ne_zero : ∀ c, Reach Φ.next Φ.actual c → ∃ i, (stage c).z i ≠ 0
  /-- The switches with both signs (or at a nonquadratic prime), along the configuration sequence
  (tex 4997–5003, 5055–5122, 5137–5153). -/
  switch_mixed : ∀ c, Reach Φ.next Φ.actual c → (¬ Φ.quadratic ρ ∨
      (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ c) (-1 : k)))) →
    1 < (stage c).fiberDim ρ →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      (Φ.quadratic ρ → Nonempty (GenuineMixedStep ρ Φ stage σ c (Φ.next c p))) ∧
      (¬ Φ.quadratic ρ → Nonempty (GenuineNonquadStep ρ Φ stage c (Φ.next c p)))
  /-- The switches with one sign only (tex 5123–5136, 5137–5153). -/
  switch_single : ∀ c, Reach Φ.next Φ.actual c → Φ.quadratic ρ →
    ¬ (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ c) (-1 : k))) →
    1 < (stage c).fiberDim ρ →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      Nonempty (GenuineSingleStep ρ Φ stage σ c (Φ.next c p))

namespace GenuineSwitchDataPK

variable {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}

/-- **The old data give the new**: batch 3's `GenuineSwitchData` gives `GenuineSwitchDataPK` with
the same stages, models and switches (a primitive class is nonzero). Kind: PROVED. -/
def ofGenuineSwitchData (G : GenuineSwitchData Φ ι ρ u) : GenuineSwitchDataPK Φ ι ρ u where
  stage := G.stage
  model := G.model
  hz0 := G.hz0
  hw0 := G.hw0
  hu0 := G.hu0
  σ := G.σ
  h2 := G.h2
  hσ := G.hσ
  class_ne_zero c hc := by
    obtain ⟨i, hi⟩ := G.primitive c hc
    exact ⟨i, fun h => hi (by rw [h, map_zero])⟩
  switch_mixed := G.switch_mixed
  switch_single := G.switch_single

/-- **The fiber dimensions are the genuine ones** (tex 4976–4996): every stage's fiber dimension is
`dim_k H¹` of its configuration's fiber. Kind: PROVED. -/
theorem fiberDim_eq (G : GenuineSwitchDataPK Φ ι ρ u) (c : Φ.Config) :
    (G.stage c).fiberDim ρ = finrank k ((selCx (Φ.fibre c)).toCC.homology 1) :=
  fiberDim_eq_h1 k A F ι ρ (G.stage c) (Φ.fibre c) ⟨G.model c⟩

/-- **The primitive kernel vector of every reached configuration** (tex 4987–4992; tex 5131–5134,
5154–5157 at the later configurations): over a DVR `R` with `ι` injective, the actual class of a
reached configuration, nonzero by `class_ne_zero`, is a nonzero fraction-field multiple of a
primitive vector `v ∈ ker d` with `v̄ ≠ 0`, by the saturation of `ker d` (the RC53 group's
`exists_primitiveKernelVector`). Kind: PROVED. -/
theorem primitiveKernel [IsDomain A] [IsDiscreteValuationRing A] (hι : Function.Injective ι)
    (G : GenuineSwitchDataPK Φ ι ρ u) (c : Φ.Config) (hc : Reach Φ.next Φ.actual c) :
    Nonempty (PrimitiveKernelVector (G.stage c) ρ) :=
  exists_primitiveKernelVector hι ρ (G.stage c) (G.class_ne_zero c hc)

/-- **The text-faithful switching data of a genuine datum** (tex 4976–5195): the RC53 group's
`HeightOneSwitchDataPK` on the reached configurations, with the primitive kernel vectors of
`primitiveKernel`, `sp, sm` the sign dimensions of the stage involutions, `sign_sum` from the
involution splitting of the fibers, and the switch dimensions from the step bundles exactly as in
batch 3's `toSelmerModelSwitchData`, `toSelmerSwitchData` and `toSwitchData`. Kind: PROVED. -/
def toSwitchDataPK [IsDomain A] [IsDiscreteValuationRing A] (hι : Function.Injective ι)
    (G : GenuineSwitchDataPK Φ ι ρ u) : HeightOneSwitchDataPK ι ρ where
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
  primitiveKernel s := G.primitiveKernel hι s.1 s.2
  switch_mixed s h1 h2 := by
    obtain ⟨p, hc, hq, hn⟩ := G.switch_mixed s.1 s.2 h1 h2
    refine ⟨⟨Φ.next s.1 p, Reach.step p s.2⟩, hc, fun q => ?_, fun nq => ?_⟩
    · obtain ⟨⟨M, -, -⟩⟩ := hq q
      exact ⟨QuadMixedDims.cast' (M.Y.X.toQuadMixedDims M.Y.h2 M.Y.ε M.Y.hε M.Y.hJ2 M.Y.ep M.Y.em
        M.Y.hp M.Y.hm M.Y.he M.Y.hU M.Y.cp M.Y.cm M.Y.hcp M.Y.hcm M.Y.hdet)
        (finrank_signPart_of_equiv M.φ M.hφ 1).symm (finrank_signPart_of_equiv M.φ M.hφ (-1)).symm
        (finrank_signPart_of_equiv M.φ' M.hφ' 1).symm
        (finrank_signPart_of_equiv M.φ' M.hφ' (-1)).symm⟩
    · obtain ⟨⟨N, -, -⟩⟩ := hn nq
      exact ⟨N.step.toNonquadDims (fiberDim_eq_of_h1Equiv ρ _ N.φ)
        (fiberDim_eq_of_h1Equiv ρ _ N.φ')⟩
  switch_single s q h1 h2 := by
    obtain ⟨p, hc, ⟨⟨M, -, -⟩⟩⟩ := G.switch_single s.1 s.2 q h1 h2
    refine ⟨⟨Φ.next s.1 p, Reach.step p s.2⟩, finrank k ↥(signPart M.Y.X.σV' (1 : k)),
      finrank k ↥(signPart M.Y.X.σV' (-1 : k)), hc, ⟨QuadSingleDims.cast'
        (M.Y.X.toQuadSingleDims M.Y.h2 M.Y.ε M.Y.hε M.Y.hJ2 M.Y.ep M.Y.em M.Y.hp M.Y.hm M.Y.he
          M.Y.hU M.Y.cp M.Y.hcp M.Y.hdet M.Y.hs1 M.Y.hs0) ?_ rfl rfl⟩, ?_⟩
    · have hV := M.Y.X.fin_V
      rw [fiberDim_eq_of_h1Equiv ρ _ M.φ,
        (involutionSplitting_proof k _ M.Y.X.σV M.Y.h2 M.Y.X.hV).2.2 hV,
        signPart_one_eq_plusPart, ← signPart_neg_one_eq_minusPart, ← M.Y.hs0, add_zero]
    · rcases M.hφ' with h | h
      · exact Or.inl ⟨(finrank_signPart_of_equiv M.φ' h 1).symm,
          (finrank_signPart_of_equiv M.φ' h (-1)).symm⟩
      · refine Or.inr ⟨?_, ?_⟩
        · change finrank k ↥(signPart (G.σ (Φ.next s.1 p)) (1 : k)) = _
          rw [finrank_signPart_of_equiv M.φ' h (-1), signPart_neg_eq, neg_neg]
        · change finrank k ↥(signPart (G.σ (Φ.next s.1 p)) (-1 : k)) = _
          rw [finrank_signPart_of_equiv M.φ' h 1, signPart_neg_eq]

/-- **The actual fiber has nonzero `H¹`**: a datum forces `dim_k H¹(selCx (Φ.fibre actual)) ≥ 1`
(the actual class is nonzero, so the fiber dimension is at least one by semicontinuity, lane RC0's
`TwoTermStage.one_le_fiberDim_of_ne_zero`, and it is the genuine `dim_k H¹`). Over a DVR this is
also `one_le_fiberDim_of_primitiveKernel` at `primitiveKernel`. Kind: PROVED. -/
theorem one_le_h1 (hι : Function.Injective ι) (G : GenuineSwitchDataPK Φ ι ρ u) :
    1 ≤ finrank k ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) := by
  rw [← G.fiberDim_eq]
  obtain ⟨i, hi⟩ := G.class_ne_zero Φ.actual Reach.start
  exact TwoTermStage.one_le_fiberDim_of_ne_zero hι ρ _ fun h => hi (congrFun h i)

end GenuineSwitchDataPK

/-- **Regularity from the text-faithful genuine data** (tex 4976–5195): the actual coordinate lies
in `ι(R)`, through `GenuineSwitchDataPK.toSwitchDataPK` and the RC53 group's
`regular_of_switchDataPK` at the actual configuration. Kind: PROVED (from the inputs of the datum).
-/
theorem regular_of_genuineSwitchDataPK [IsDomain A] [IsDiscreteValuationRing A]
    {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F} (hι : Function.Injective ι)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) (G : GenuineSwitchDataPK Φ ι ρ u) :
    ∃ a : A, ι a = u := by
  obtain ⟨a, ha⟩ := regular_of_switchDataPK hι hρ (G.toSwitchDataPK hι) ⟨Φ.actual, Reach.start⟩
  exact ⟨a, ha.trans G.hu0⟩

/-- **No datum over a family whose actual fiber has `H¹ = 0`**, whatever the coordinate `u`.
Kind: PROVED. -/
theorem isEmpty_genuineSwitchDataPK_of_h1_eq_zero {Φ : SwitchFamily k A} {ι : A →+* F}
    {ρ : A →+* k} (hι : Function.Injective ι) (u : F)
    (h0 : finrank k ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) = 0) :
    IsEmpty (GenuineSwitchDataPK Φ ι ρ u) :=
  ⟨fun G => by have := G.one_le_h1 hι; omega⟩

end General

/-! **The new height-one leaf** -/

/-- **The height-one regularity inputs on the text's primitive kernel vector** (replaces
`RegularityInputsG u`; tex 4976–5200). Either `u = 0` ("If its actual generic class is zero, its
coordinate is zero", tex 5196–5197; ELLIOT; owner RC15 / RC16), or at every height-one prime
`𝔭 ≠ (2)` of `Λ` (tex; kind; owner):

1. a configuration family `Φ` over `R = Λ_𝔭` and `k = Frac(Λ/𝔭)`, genuine at `𝔭`
   (`IsGenuineFamilyAt`, as in `RegularityInputsG`; tex 4976–4984, 5055–5072; GLUE identification
   of `Φ` with the address's actual Selmer complex and its switches; owners RC26, batch 3, RC15);
2. `GenuineSwitchDataPK Φ ι ρ u` with `ι : Λ_𝔭 → Frac Λ`, `ρ` the residue map: the fields of
   batch 3's `GenuineSwitchData` (models, actual class and functional at the start, the coordinate
   `u`, sign involutions, switches with their GLUE step data; tex, kinds and owners as at
   `RegularityInputsG`), except that the actual class of every reached configuration is only asked
   to be NONZERO (tex 4992, 5137–5144; ELLIOT; owners RC15, RC16). The primitive kernel vector of
   tex 4987–4991 is PROVED from it over the DVR `Λ_𝔭` (`GenuineSwitchDataPK.primitiveKernel`).

Kind: definition. -/
def RegularityInputsGPK (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
    ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      Nonempty (GenuineSwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u)

/-- **The old leaf gives the new one** (`GenuineSwitchDataPK.ofGenuineSwitchData` at every
height-one prime). Kind: PROVED. -/
theorem RegularityInputsG.toPK {u : FractionRing Lambda} (h : RegularityInputsG u) :
    RegularityInputsGPK u := by
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr fun P _ hP hne => ?_
    obtain ⟨Φ, hΦ, ⟨G⟩⟩ := h P hP hne
    exact ⟨Φ, hΦ, ⟨GenuineSwitchDataPK.ofGenuineSwitchData G⟩⟩

/-- **`u ∈ Λ[1/2]` from the new inputs**: at every height-one prime `𝔭 ≠ (2)`, `Λ_𝔭` is a DVR
(lane RC20), so `regular_of_genuineSwitchDataPK` gives `u ∈ ι(Λ_𝔭)`; then the normal-domain
intersection formula (`mem_range_lambdaHalf_iff_forall_height_one`, tex 5190–5194) gives
`u ∈ Λ[1/2]`. Kind: PROVED from the inputs. -/
theorem RegularityInputsGPK.mem_lambdaHalf {u : FractionRing Lambda} (h : RegularityInputsGPK u) :
    u ∈ lambdaHalfToFrac.range := by
  rw [mem_range_lambdaHalf_iff_forall_height_one]
  intro P _ hP hne
  rcases h with rfl | h
  · exact Subalgebra.zero_mem _
  · obtain ⟨Φ, -, ⟨G⟩⟩ := h P hP hne
    have := isDiscreteValuationRing_atPrime_of_height_one P hP
    obtain ⟨a, ha⟩ := regular_of_genuineSwitchDataPK (UniformSwitch.toFracAt_injective P)
      (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx) G
    rw [← ha]
    exact ⟨a, rfl⟩

/-- `RegularityInputsGPK u → RegularityInputsS u` (through `u ∈ Λ[1/2]` and
`regularityInputsS_iff`). Kind: PROVED. -/
theorem RegularityInputsGPK.toS {u : FractionRing Lambda} (h : RegularityInputsGPK u) :
    RegularityInputsS u :=
  (regularityInputsS_iff u).mpr h.mem_lambdaHalf

section HeightOneTarget

variable {ℓ : ℕ} (D : RCData ℓ)

/-- **The height-one leaf on the text's primitive kernel vector** (replaces
`PrimRegularityInputsG D`; tex 4976–5200, at the ring instances `(h_x, k)` of the final field; at
`x = 0` the unknown full-corank-one base, tex 5196–5200). For every final family `F` (any
`C_o, C_e`) and every address `x` there is `u ∈ Frac Λ` with (tex; kind; owner):

1. `IsTExpansion u (D.uPrim F x)` (tex 3877–3892, 3895–3985; GLUE interface identification; owner
   RC0, with RC15);
2. `RegularityInputsGPK u`: `u = 0` (tex 5196–5197; ELLIOT; owner RC15 / RC16) or, at every
   height-one prime `𝔭 ≠ (2)`, a configuration family genuine at `𝔭` and `GenuineSwitchDataPK`
   over it starting at `u` (fields and owners as listed at `RegularityInputsGPK`: the actual classes
   nonzero, not primitive).

PROVED from it (not inputs): the primitive kernel vectors (saturation over the DVR `Λ_𝔭`), `pos`
from them, `terminal`, `s₊ + s₋ = s`, the nonquadratic `U = F`, the descent (the RC53 group's
`regular_of_switchDataPK`), the intersection formula and the transfer to `ℚ₂[[t]]`.
Kind: definition. -/
def PrimRegularityInputsGPK : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    ∃ u : FractionRing Lambda, IsTExpansion u (D.uPrim F x) ∧ RegularityInputsGPK u

/-- **The old leaf gives the new one.** Kind: PROVED. -/
theorem PrimRegularityInputsG.toPK (h : PrimRegularityInputsG D) : PrimRegularityInputsGPK D :=
  fun Co Ce F hF x =>
    let ⟨u, hT, hreg⟩ := h Co Ce F hF x
    ⟨u, hT, hreg.toPK⟩

/-- **`u_{prim,x} ∈ Λ[1/2]`** at every address of every final family, from the new leaf.
Kind: PROVED from the inputs. -/
theorem primLambdaHalf_of_inputsGPK (h : PrimRegularityInputsGPK D) :
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      InLamHalf (D.uPrim F x) := by
  intro Co Ce F hF x
  obtain ⟨u, hT, hreg⟩ := h Co Ce F hF x
  exact inLamHalf_of_isTExpansion hT hreg.mem_lambdaHalf

/-- **`RCSteps.height_one`** (tex 4909–5205, 5703–5704) from the new leaf and (4.7).
Kind: PROVED from the inputs. -/
theorem heightOneTarget_of_inputsGPK (h : PrimRegularityInputsGPK D)
    (h47 : CommonCoordinateTarget D) : HeightOneTarget D :=
  heightOneTarget_of_prim D (primLambdaHalf_of_inputsGPK D h) h47

/-- **Conversion to the round-3 leaf** `PrimRegularityInputsS D`. Kind: PROVED. -/
theorem primRegularityInputsS_of_GPK (h : PrimRegularityInputsGPK D) : PrimRegularityInputsS D :=
  (primRegularityInputsS_iff D).mpr (primLambdaHalf_of_inputsGPK D h)

/-- **Conversion to the old leaf** `PrimRegularityInputs D` (the form consumed by lane RC25's
base-zero assembly). Kind: PROVED. -/
theorem primRegularityInputs_of_GPK (h : PrimRegularityInputsGPK D) : PrimRegularityInputs D :=
  primRegularityInputs_of_S D (primRegularityInputsS_of_GPK D h)

end HeightOneTarget

/-! **The (3.5) leaf on the text's primitive kernel vector** -/

section Eq35GGPK

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The inputs of (3.5) on the text's primitive kernel vector** (replaces
`Eq35InputsGenuineGG W`; Proposition `ex:limits-uniform-lower-bound`, tex 4909–5202, at the ring
instances `(h, k')` of Proposition `ex:sec7-genus-lower`, tex 2418–2446): the conjuncts of
`Eq35InputsGenuineGG W` verbatim (data `uprim`, `C₀`; (4.6); the outer models and switches; tex,
kinds and owners there), except that the regularity conjunct is `RegularityInputsGPK (uprim h k')`
at every companion pair (tex 4976–5194; the actual classes nonzero, the primitive kernel vectors
PROVED; fields and owners at `RegularityInputsGPK`). Kind: definition. -/
def Eq35InputsGenuineGGPK : Prop :=
  ∃ (uprim : ℤ → ℤ → FractionRing Lambda) (C₀ : ℤ),
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputsGPK (uprim h k')) ∧
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      ∀ uh : LambdaHalf, lambdaHalfToFrac uh = uprim h k' →
        ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ C₀ ∧
          v2 (centralSpecialization uh) =
            ((2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
              ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ)) ∧
    ∃ (Pl : Type) (G : SwitchInputs.GenuineOuterModels (2 : OO) (FractionRing OO) (RingInst W) Pl),
      (∀ i l, IsGenuineInstanceModel (G.model i l)) ∧
      (∀ i : RingInst W, vO (G.model i []).coordOf = vO (iotaO (uprim i.1.1 i.1.2))) ∧
      ∀ A : ℕ, ∀ inst : ℕ → CompanionPair W A,
        SwitchInputs.GenuineOuterSwitchData (Filter.hyperfilter ℕ) G (fun j => (inst j).toInst)

/-- **The old leaf gives the new one** (`RegularityInputsG.toPK` in the regularity conjunct; the
other conjuncts verbatim). Kind: PROVED. -/
theorem Eq35InputsGenuineGG.toPK (hin : Eq35InputsGenuineGG W) : Eq35InputsGenuineGGPK W := by
  obtain ⟨uprim, C₀, hreg, h46, hout⟩ := hin
  exact ⟨uprim, C₀, fun h k' h1 h2 h3 => (hreg h k' h1 h2 h3).toPK, h46, hout⟩

/-- **(3.5) for each fixed `A` at the rough companions** (tex 2441–2446, 5200–5202) from the new
leaf: as `eq35Target_of_inputsGG` (RC16's `exLimitsUniformLowerBound` over lane RC20's genuine `𝒪`,
the outer processes of batch 3's `GenuineOuterSwitchData.toOuterSwitchData` at the starting
configuration `[]`), with the regularity of `RegularityInputsGPK`; `C_R(E, A) = C + C₀ + 2A`.
Kind: PROVED from the inputs. -/
theorem eq35Target_of_inputsGGPK (hin : Eq35InputsGenuineGGPK W) : Eq35Target W := by
  obtain ⟨uprim, C₀, hreg, h46, Pl, G, -, hcoord, hsw⟩ := hin
  intro A
  obtain ⟨C, -, hC⟩ := exLimitsUniformLowerBound vO iotaO valuationOfO_genuine A
    (fun i : CompanionPair W A => uprim i.h i.k)
    (fun inst => ⟨0, ((hsw A inst).toOuterSwitchData injective_algebraMap_OO isPiAdicOn_two_vO
      0).toProcess vO _, [], Eventually.of_forall fun j => hcoord (inst j).toInst⟩)
    (fun i => (hreg i.h i.k i.prepared i.simpleZero i.rough).toS.rc16)
  refine ⟨(C : ℤ) + (C₀ + 2 * (A : ℤ)), ?_⟩
  intro h k' hprep hrank hrough hω
  obtain ⟨uh, huh, -, h35⟩ := hC ⟨h, k', hprep, hrank, hrough, hω⟩
  obtain ⟨t, err, ht, herr, hv⟩ := h46 h k' hprep hrank hrough uh huh
  obtain ⟨hne, hval⟩ := v2_eq_coe_iff.mp hv
  have hcard : k'.natAbs.primeFactors.card ≤ A := by
    have := card_primeFactors_natAbs k'
    omega
  have h46' : |Padic.valuation (centralSpecialization uh) -
      (2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
        ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ))| ≤ C₀ := by
    rw [hval]
    convert herr using 2
    ring
  have key := h35 (W.jrc h k') (omega h : ℤ) (sFun ℓ h) (sFun ℓ (h * k')) C₀
    k'.natAbs.primeFactors (fun p => (t p : ℤ)) hne
    (fun p _ => ⟨Int.natCast_nonneg _, by exact_mod_cast ht p⟩) hcard h46'
  linarith

/-- The height-one part of the new (3.5) leaf implies that of the round-3 leaf
`Eq35InputsGenuineG` (`RegularityInputsGPK.toS`). Kind: PROVED. -/
theorem eq35InputsGenuineG_regularity_of_GGPK {uprim : ℤ → ℤ → FractionRing Lambda}
    (h : ∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputsGPK (uprim h k')) :
    ∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputsS (uprim h k') :=
  fun a b h1 h2 h3 => (h a b h1 h2 h3).toS

end Eq35GGPK

/-! **Ties to the genuine objects** -/

section Ties

/-- **The fiber dimensions in every witness of the new leaf are the genuine ones**: at a height-one
prime `𝔭 ≠ (2)` (and `u ≠ 0`), the family of the witness is genuine at `𝔭`, every stage's fiber
dimension is `dim_k H¹` of the genuine Galois Selmer complex of its configuration, and the actual
one is at least one. Kind: PROVED. -/
theorem RegularityInputsGPK.fiberDim_forced {u : FractionRing Lambda} (h : RegularityInputsGPK u)
    (hu : u ≠ 0) (P : Ideal Lambda) [P.IsPrime] (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) :
    ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      ∃ G : GenuineSwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u,
        (∀ c, (G.stage c).fiberDim (resAt P) =
          finrank (ResAt P) ((selCx (Φ.fibre c)).toCC.homology 1)) ∧
        1 ≤ finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) := by
  rcases h with h0 | h
  · exact absurd h0 hu
  · obtain ⟨Φ, hΦ, ⟨G⟩⟩ := h P hP hne
    exact ⟨Φ, hΦ, G, G.fiberDim_eq, G.one_le_h1 (UniformSwitch.toFracAt_injective P)⟩

/-- **The one-stage bypass forces the genuine fiber**: in a witness of the new leaf whose starting
stage has fiber dimension one (no switch demanded), the genuine Galois Selmer complex of the actual
configuration has `dim_k H¹ = 1`. Kind: PROVED. -/
theorem RegularityInputsGPK.oneStage_forces (P : Ideal Lambda) [P.IsPrime]
    {u : FractionRing Lambda} {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
    (G : GenuineSwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u)
    (h1 : (G.stage Φ.actual).fiberDim (resAt P) = 1) :
    finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) = 1 := by
  rw [← G.fiberDim_eq, h1]

end Ties

end ZInQ.Manuscript.RC.Wiring
