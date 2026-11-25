import ZInQKernel.Contrib.OneProof.RC.Wiring.Genuine
import ZInQKernel.Contrib.CloudB3RC53.UniformSwitch.Outer
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.ExactSequences
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.SignSplitting
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.OuterMinors
import ZInQKernel.Contrib.OneProof.RC.Rings.LimitsBridge

/-!
# Theorem 5.3, Lane RC0 round 3: the leaves of RC16 from the concrete switching models

Two leaves of `Leaves.lean` carried (before this file) lane RC16's abstract switching processes
(`Wiring/Uniform.lean`, `Wiring/Genuine.lean`):

* `PostLeaves.prim_regular : PrimRegularityInputs W.toRCData` (height-one regularity, through
  `RegularitySwitchProcessPF`);
* `PreLeaves.eq35 : Eq35InputsGenuine W` ((3.5): height-one regularity, (4.6) and the outer
  switching process `OuterSwitchProcessPF` over the genuine `𝒪`).

Batch 3's `UniformSwitch` builds RC16's processes from concrete two-term models
(`Regularity.lean`, `Outer.lean`): `pos` and `terminal` are proved from the models and the switch
steps come from inputs that carry the hypotheses of RC16's own cores (tex 4927–5200). Batch 3's
`SwitchInputs` proves the sign splitting, the relaxed image of a nonquadratic switch and the outer
minors. This file replaces the abstract processes of the two leaves by these models:

* `PrimRegularityInputsS D` (replaces `PrimRegularityInputs D`), through `RegularityInputsS u` and
  the height-one switching data `HeightOneSwitchDataS`;
* `Eq35InputsGenuineS W` (replaces `Eq35InputsGenuine W`), with `RegularityInputsS` for the
  regularity conjunct and the outer switching data `OuterSwitchDataS` for the outer conjunct.

The leaves now read `PostLeaves.prim_regular : PrimRegularityInputsS W.toRCData` and
`PreLeaves.eq35 : Eq35InputsGenuineG W` (genuine outer models, below).

Conversions (PROVED): `primRegularityInputs_of_S` (to the old leaf), `heightOneTarget_of_inputsS`
(to `HeightOneTarget D`), `eq35Target_of_inputsGenuineS` (to `Eq35Target W`, through RC16's
`exLimitsUniformLowerBound` over lane RC20's genuine `𝒪`).

What is restated, relative to batch 3's `HeightOneSwitchData` / `OuterSwitchData` (which already
prove `pos` and `terminal`). The structures are existential and are not tied to the actual Selmer
complexes, so they do not constrain the genuine objects: `PrimRegularityInputsS` is equivalent to
`u_{prim,x} ∈ Λ[1/2]` at every final address (`primRegularityInputsS_iff`) and
`Eq35InputsGenuineG` to (3.5) itself; as leaves
they are Elliot's steps (ELLIOT), not reductions of them. The restatements:

* `pos` from a **nonzero** actual class (`class_ne_zero`) instead of a primitive one: Elliot's actual
  class is "a nonzero fraction-field multiple" of the primitive vector `v` (tex 4987–4992), and the
  primitive vector "is used only to select the prime" (tex 5145–5147). The proof is semicontinuity:
  `z ≠ 0` gives `det D = 0`, so `det (D ⊗ k) = 0` and `dim_k ker (D ⊗ k) ≥ 1`
  (`TwoTermStage.one_le_fiberDim_of_ne_zero`).
* the sign dimensions `s_± = dim V_±` are the dimensions of the eigenspaces of an involution of
  `V = H¹(C ⊗ k) = ker (D ⊗ k)` (the action of `τ`, tex 5009–5013), so `s_+ + s_- = s` is batch 3's
  `involutionSplitting_proof` (with `2 ≠ 0` from the switch data) instead of an input.
* the nonquadratic relaxed image `U = F` is batch 3's `relaxedImageFinite_proof` from the
  localization duality `U = U^⊥` (GLUE, Nekovář 6.3.3–6.3.4, tex 5068–5072) and rank-two
  detection `F ≤ U` (tex 4997–5003), instead of an input (`NonquadInputs`), for the height-one
  switches and for the outer switches.
* `minor_link` of the outer data is stated along the ultrafilter (the round 3 field shape of
  `UniformSwitch/Outer.lean`), the form batch 3's `minorLinkEventually_proof` proves from the
  genuine outer model.

What remains is listed with tex lines, kind and owner in the docstrings of `HeightOneSwitchDataS`,
`OuterSwitchDataS`, `PrimRegularityInputsS` and `Eq35InputsGenuineS`. Equivalences and
non-vacuity (PROVED):
`regularityInputsS_iff` (`RegularityInputsS u ↔ u ∈ Λ[1/2]`), `primRegularityInputsS_iff`,
`exampleOuterDataS` (the outer data over `v_𝒪` are inhabited).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings ZInQ.Manuscript.RC.Determinant Filter Topology
  Matrix Module

attribute [local instance] Nat.fact_prime_two

/-! ## `pos` from a nonzero actual class -/

section Pos

variable {A F k : Type*} [CommRing A] [Field F] [Field k]

/-- **`pos` from a nonzero actual class** (tex 4986–4992, 5154–5157; semicontinuity, tex 4934): if
the integral cycle `z` of a two-term model `[A^{n+1} --D--> A^{n+1}]` is nonzero (and `ι : A → F`
is injective), then `det D = 0`, so `det (D ⊗ k) = ρ(det D) = 0` and the fiber dimension
`dim_k ker (D ⊗_ρ k)` is at least one. No primitivity of `z` is used. Kind: PROVED. -/
theorem TwoTermStage.one_le_fiberDim_of_ne_zero {ι : A →+* F} (hι : Function.Injective ι)
    (ρ : A →+* k) (S : UniformSwitch.TwoTermStage ι) (hz0 : S.z ≠ 0) : 1 ≤ S.fiberDim ρ := by
  have hzι : (ι ∘ S.z) ≠ 0 := fun h => hz0 (funext fun i => hι (by
    have := congrFun h i
    simpa using this))
  have hDι : (S.D.map ι) *ᵥ (ι ∘ S.z) = 0 := by
    funext i
    have h := RingHom.map_mulVec ι S.D S.z i
    rw [S.hz, Pi.zero_apply, map_zero] at h
    rw [← h, Pi.zero_apply]
  have hdetι : (S.D.map ι).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hzι, hDι⟩
  have hdet : S.D.det = 0 :=
    hι (by rw [RingHom.map_det, RingHom.mapMatrix_apply, hdetι, map_zero])
  have hdetρ : (S.D.map ρ).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_zero]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetρ
  have hmem : v ∈ LinearMap.ker (S.D.map ρ).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hv]
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have hbot := Submodule.finrank_eq_zero.mp h0
  rw [hbot, Submodule.mem_bot] at hmem
  exact hv0 hmem

end Pos

/-! ## The nonquadratic switch inputs in batch 3's form -/

/-- **The nonquadratic switch inputs** (tex 4997–5003, 5055–5086), the hypotheses of batch 3's
`nonquadSwitchDims_of_inputs`: a relaxed localization image `U ⊆ F ⊕ S = k² × k²` which

* is its own annihilator for the switch pairing `β(x, y) = ε e₂(x, J y)` (batch 3's
  `LocalizationDualityInput`; GLUE: Nekovář, *Selmer complexes*, 6.3.3–6.3.4, as cited at tex
  5068–5072; owner batch 3 SelmerDuality);
* contains the finite plane (rank-two detection, Lemma `ex:limits-kernel-detection`, tex
  4997–5001; ELLIOT; owner RC16 `KernelDetection`, batch 3);
* satisfies the two (5.5a) equations `s = k₀ + dim (U ∩ F)`, `s' = k₀ + dim (U ∩ S)` (tex
  5073–5083; ELLIOT, the cone triangles; owner batch 3 `SwitchDimsOfSES`).

The conclusion `U = F` of the old input `NonquadDims` is then batch 3's `relaxedImageFinite_proof`
(`NonquadInputs.nonquadDims`). Kind: definition. -/
def NonquadInputs (k : Type) [Field k] (s s' : ℕ) : Prop :=
  ∃ (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (U : Submodule k ((Fin 2 → k) × (Fin 2 → k))) (k₀ : ℕ),
    SwitchInputs.LocalizationDualityInput ε σ J hε hσ hJ2 U ∧
    finPlane k (Fin 2 → k) (Fin 2 → k) ≤ U ∧
    s = k₀ + finrank k ↥(U ⊓ finPlane k (Fin 2 → k) (Fin 2 → k)) ∧
    s' = k₀ + finrank k ↥(U ⊓ singPlane k (Fin 2 → k) (Fin 2 → k))

/-- The old input `NonquadDims` from `NonquadInputs` (the relaxed image is the finite plane by
batch 3's `relaxedImageFinite_proof`). Kind: PROVED. -/
theorem NonquadInputs.nonquadDims {k : Type} [Field k] {s s' : ℕ} (h : NonquadInputs k s s') :
    Nonempty (UniformSwitch.NonquadDims (k := k) s s') := by
  obtain ⟨ε, σ, J, hε, hσ, hJ2, U, k₀, hdual, hdet, hs, hs'⟩ := h
  exact ⟨⟨U, SwitchInputs.relaxedImageFinite_proof k ε σ J hε hσ hJ2 U hdual hdet, k₀, hs, hs'⟩⟩

/-! ## The height-one switching data -/

section HeightOneData

variable {A F : Type*} [CommRing A] [Field F] {k : Type} [Field k]

/-- The `+1` sign dimension `s_+ = dim V_+` of an involution of `V = ker (D ⊗ k)`. -/
abbrev signDimPlus {V : Type} [AddCommGroup V] [Module k V] (T : V →ₗ[k] V) : ℕ :=
  finrank k (SwitchInputs.plusPart T)

/-- The `−1` sign dimension `s_- = dim V_-`. -/
abbrev signDimMinus {V : Type} [AddCommGroup V] [Module k V] (T : V →ₗ[k] V) : ℕ :=
  finrank k (SwitchInputs.minusPart T)

/-- **The height-one switching data at one height-one prime, refined** (tex 4976–5193), over a
local ring `A` (`= Λ_𝔭`) with `ι : A → F` (`F = Frac Λ`) and residue map `ρ : A → k`. It is batch
3's `HeightOneSwitchData` with three inputs made smaller (see the module docstring). Fields (tex;
kind; owner):

* `Stage`, `stage`: the configurations and their two-term models `[A^{n+1} --D--> A^{n+1}]` with
  integral actual class `z`, integral closed functional `w` at every configuration (ELLIOT input:
  integrality of the transported paired functional with the added derivative conditions, tex
  5162–5187; assumed through the type of `w`, not derived from batch 3's
  `pairedFunctionalHeightOne_proof`) and the class-functional coordinate
  `z ⊗ w = u · adj D` (tex 3877–3892, 4976–4992, 5159–5189; GLUE identification of the Selmer
  complex over `R` with its minimal two-term model and of `u` with the coordinate; owner batch 3
  HeegnerCohomology / RC15).
* `quadratic`: a free datum (in the text's witness, whether `𝔭 = (t)` or `(t + 2)`, tex
  5004–5008; not constrained in Lean).
* `sign`, `sign_invol`: at a quadratic prime, the involution of `V = H¹(C ⊗ k) = ker (D ⊗ k)`
  induced by the action `c ↦ J c(τ⁻¹ · τ)` (tex 5009–5013, 5035–5054; GLUE that it is the actual
  action, owner batch 3 SignSplitting); `V = V_+ ⊕ V_-` is then PROVED.
* `class_ne_zero`: the actual class is nonzero (tex 4987–4992 "a nonzero fraction-field multiple
  of `v`", 5141–5142 "nonzero generically"; ELLIOT; owner batch 3 HeegnerCohomology / RC15).
* `switch_mixed`: both signs occur (or nonquadratic) and `s > 1`: a next configuration with the
  coordinate relation from a switch plane (`CoordStep`, tex 5137–5153; GLUE identification of the
  stage coordinates with the finite and singular switch coordinates, unit volumes; owner RC16
  `Switch`, batch 3), the quadratic sign bookkeeping (`QuadMixedDims`, tex 5116–5122; ELLIOT/GLUE;
  owner RC16 `QuadraticCase`, batch 3 SignSplitting / ExactSequences) or the nonquadratic inputs
  (`NonquadInputs`, tex 4997–5003).
* `switch_single`: one sign only and `s > 1` (`QuadSingleDims`, tex 5123–5136; as above). -/
structure HeightOneSwitchDataS (ι : A →+* F) (ρ : A →+* k) where
  /-- The configurations reached by successive switches. -/
  Stage : Type
  /-- The two-term model of each configuration. -/
  stage : Stage → UniformSwitch.TwoTermStage ι
  /-- Whether the specialization is quadratic (`𝔭 = (t)` or `(t + 2)`). -/
  quadratic : Prop
  /-- The sign involution of `V = H¹(C ⊗ k) = ker (D ⊗ k)` at each configuration. -/
  sign : ∀ S, Module.End k ↥(LinearMap.ker ((stage S).D.map ρ).mulVecLin)
  /-- tex 5009–5013: at a quadratic prime the action of `τ` is an involution. -/
  sign_invol : quadratic → ∀ S, sign S ∘ₗ sign S = LinearMap.id
  /-- tex 4987–4992, 5141–5142: the actual class is nonzero. -/
  class_ne_zero : ∀ S, (stage S).z ≠ 0
  /-- tex 4997–5003, 5116–5122, 5137–5153: both signs occur (or nonquadratic) and `s > 1`. -/
  switch_mixed : ∀ S, (¬ quadratic ∨ (0 < signDimPlus (sign S) ∧ 0 < signDimMinus (sign S))) →
    1 < (stage S).fiberDim ρ →
    ∃ S', Nonempty (UniformSwitch.CoordStep ι (stage S).u (stage S').u) ∧
      (quadratic → Nonempty (UniformSwitch.QuadMixedDims (k := k) (signDimPlus (sign S))
        (signDimMinus (sign S)) (signDimPlus (sign S')) (signDimMinus (sign S')))) ∧
      (¬ quadratic → NonquadInputs k ((stage S).fiberDim ρ) ((stage S').fiberDim ρ))
  /-- tex 5123–5136, 5137–5153: one sign only and `s > 1`. -/
  switch_single : ∀ S, quadratic →
    ¬ (0 < signDimPlus (sign S) ∧ 0 < signDimMinus (sign S)) → 1 < (stage S).fiberDim ρ →
    ∃ S' a b, Nonempty (UniformSwitch.CoordStep ι (stage S).u (stage S').u) ∧
      Nonempty (UniformSwitch.QuadSingleDims (k := k) ((stage S).fiberDim ρ) a b) ∧
      ((signDimPlus (sign S') = a ∧ signDimMinus (sign S') = b) ∨
        (signDimPlus (sign S') = b ∧ signDimMinus (sign S') = a))

namespace HeightOneSwitchDataS

variable {ι : A →+* F} {ρ : A →+* k}

/-- **`s_+ + s_- = s`** (tex 5009–5024): batch 3's `involutionSplitting_proof` applied to the sign
involution of `ker (D ⊗ k)`. Kind: PROVED. -/
theorem sign_sum (P : HeightOneSwitchDataS ι ρ) (hq : P.quadratic) (h2 : (2 : k) ≠ 0)
    (S : P.Stage) :
    signDimPlus (P.sign S) + signDimMinus (P.sign S) = (P.stage S).fiberDim ρ :=
  ((SwitchInputs.involutionSplitting_proof k _ (P.sign S) h2 (P.sign_invol hq S)).2.2
    inferInstance).symm

/-- **The instance of RC16's `RegularitySwitchProcess`** from the refined data, with `Reg` any
predicate containing `ι(A)` (tex 4976–5193): `pos` from the nonzero actual class, `terminal` from the
two-term model (batch 3's `coord_integral_of_fiberDim_one`), the switches from RC16's cores through
batch 3's `CoordStep.relation`, `QuadMixedDims.drop`, `QuadSingleDims.result` and
`NonquadDims.drop`. Kind: PROVED. -/
def toProcess [IsLocalRing A] (hι : Function.Injective ι)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) (Reg : F → Prop)
    (hReg : ∀ a : A, Reg (ι a)) (P : HeightOneSwitchDataS ι ρ) : RegularitySwitchProcess Reg where
  Stage := P.Stage
  fiberDim S := (P.stage S).fiberDim ρ
  mixed S := ¬ P.quadratic ∨ (0 < signDimPlus (P.sign S) ∧ 0 < signDimMinus (P.sign S))
  coord S := (P.stage S).u
  pos S := TwoTermStage.one_le_fiberDim_of_ne_zero hι ρ (P.stage S) (P.class_ne_zero S)
  switch_mixed S hmix hs := by
    obtain ⟨S', ⟨hC⟩, hQ, hN⟩ := P.switch_mixed S hmix hs
    obtain ⟨c, hc⟩ := hC.relation
    refine ⟨S', ?_, ι c, hReg c, hc⟩
    by_cases hq : P.quadratic
    · obtain ⟨Q⟩ := hQ hq
      have h := Q.drop
      rw [P.sign_sum hq Q.h2 S, P.sign_sum hq Q.h2 S'] at h
      exact h
    · obtain ⟨N⟩ := (hN hq).nonquadDims
      exact N.drop
  switch_single S hmix hs := by
    have hq : P.quadratic := by
      by_contra hq; exact hmix (Or.inl hq)
    have hns : ¬ (0 < signDimPlus (P.sign S) ∧ 0 < signDimMinus (P.sign S)) :=
      fun h => hmix (Or.inr h)
    obtain ⟨S', a, b, ⟨hC⟩, ⟨hQ⟩, hab⟩ := P.switch_single S hq hns hs
    obtain ⟨c, hc⟩ := hC.relation
    obtain ⟨hsum, ha, hb⟩ := hQ.result
    refine ⟨S', ?_, Or.inr ?_, ι c, hReg c, hc⟩
    · rw [← P.sign_sum hq hQ.h2 S']
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  terminal S h1 := by
    obtain ⟨u₀, hu₀⟩ := (P.stage S).coord_integral_of_fiberDim_one hι ρ hρ h1
    rw [← hu₀]; exact hReg u₀

/-- Batch 3's `HeightOneSwitchData` gives the refined data whenever its sign dimensions are those
of an involution (a primitive class is nonzero; `NonquadDims` gives `NonquadInputs` only through
duality data, so this direction is not claimed in general). Kind: PROVED for the nonzero-class
field: a primitive cycle is nonzero. -/
theorem class_ne_zero_of_primitive (S : UniformSwitch.TwoTermStage ι)
    (h : ∃ i, ρ (S.z i) ≠ 0) : S.z ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  intro h0
  exact hi (by rw [h0, Pi.zero_apply, map_zero])

end HeightOneSwitchDataS

end HeightOneData

/-! ## Over the genuine `Λ_𝔭` -/

/-- The refined switching data over `Λ_𝔭` with the residue map of the local ring `Λ_𝔭`. -/
abbrev HeightOneSwitchDataAt (P : Ideal Lambda) [P.IsPrime] : Type 1 :=
  HeightOneSwitchDataS (UniformSwitch.toFracAt P) (IsLocalRing.residue (Localization.AtPrime P))

/-- **RC16's `RegularitySwitchProcess (RegularAtPrime 𝔭)`** from refined switching data over the
genuine `Λ_𝔭 = Localization.AtPrime 𝔭 ⊂ Frac Λ`. Kind: PROVED. -/
def HeightOneSwitchDataS.processAtPrime (P : Ideal Lambda) [P.IsPrime]
    (Sw : HeightOneSwitchDataAt P) : RegularitySwitchProcess (RegularAtPrime P) :=
  Sw.toProcess (UniformSwitch.toFracAt_injective P)
    (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx) (RegularAtPrime P) (fun a => ⟨a, rfl⟩)

/-- **The refined process of `Wiring/Uniform.lean` from RC16's process**, at a height-one prime
`𝔭 ≠ (2)`: the terminal step `TerminalPairedFunctional` from RC16's `Reg (coord S)` by
`terminalPairedFunctional_of_regularAtPrime`. Kind: PROVED. -/
def RegularitySwitchProcessPF.ofProcess {P : Ideal Lambda} [P.IsPrime] (hP : P.height = 1)
    (hne : P ≠ Ideal.span {2}) (Pr : RegularitySwitchProcess (RegularAtPrime P)) :
    RegularitySwitchProcessPF P where
  Stage := Pr.Stage
  fiberDim := Pr.fiberDim
  mixed := Pr.mixed
  coord := Pr.coord
  pos := Pr.pos
  switch_mixed := Pr.switch_mixed
  switch_single := Pr.switch_single
  terminal S hS := terminalPairedFunctional_of_regularAtPrime hP hne (Pr.terminal S hS)

/-! ## The height-one leaf -/

/-- **The height-one regularity inputs from the concrete models** (tex 4976–5200), replacing
`RegularityInputs u`: either `u = 0` (the actual generic class is zero, tex 5196–5197; ELLIOT;
owner RC15 / RC16), or at every height-one prime `𝔭 ≠ (2)` of `Λ` refined switching data over
`Λ_𝔭` (`HeightOneSwitchDataS`, whose fields carry the tex lines, kinds and owners) start at `u`
("use the actual primitive scalar Selmer complex over `R`", tex 4976–4980; also at the unknown
base, tex 5196–5200). Kind: definition. -/
def RegularityInputsS (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
    ∃ (Sw : HeightOneSwitchDataAt P) (S₀ : Sw.Stage), (Sw.stage S₀).u = u

/-- `RegularityInputsS u` gives the hypothesis `regular` of RC16's `mem_lambdaHalf_of_regularity`
and `exLimitsUniformLowerBound`. Kind: PROVED. -/
theorem RegularityInputsS.rc16 {u : FractionRing Lambda} (h : RegularityInputsS u) :
    u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
      ∃ (Pr : RegularitySwitchProcess (RegularAtPrime P)) (S₀ : Pr.Stage), Pr.coord S₀ = u := by
  rcases h with h0 | h
  · exact Or.inl h0
  · refine Or.inr fun P _ hP hne => ?_
    obtain ⟨Sw, S₀, hS₀⟩ := h P hP hne
    exact ⟨HeightOneSwitchDataS.processAtPrime P Sw, S₀, hS₀⟩

/-- **`u ∈ Λ[1/2]`** from the refined inputs (RC16's `mem_lambdaHalf_of_regularity`). Kind: PROVED
from the inputs. -/
theorem RegularityInputsS.mem_lambdaHalf {u : FractionRing Lambda} (h : RegularityInputsS u) :
    u ∈ lambdaHalfToFrac.range :=
  mem_lambdaHalf_of_regularity u h.rc16

/-- **Conversion to the old leaf**: `RegularityInputsS u → RegularityInputs u`. Kind: PROVED. -/
theorem RegularityInputsS.toRegularityInputs {u : FractionRing Lambda} (h : RegularityInputsS u) :
    RegularityInputs u := by
  rcases h.rc16 with h0 | h
  · exact Or.inl h0
  · refine Or.inr fun P _ hP hne => ?_
    obtain ⟨Pr, S₀, hS₀⟩ := h P hP hne
    exact ⟨RegularitySwitchProcessPF.ofProcess hP hne Pr, S₀, hS₀⟩

section HeightOneTarget

variable {ℓ : ℕ} (D : RCData ℓ)

/-- **The height-one leaf from the concrete models** (replaces `PrimRegularityInputs D`; tex
4976–5200, at the ring instances `(h_x, k)` of the final field; at `x = 0` the unknown
full-corank-one base, tex 5196–5200). For every final family `F` (any `C_o, C_e`) and every
address `x` there is `u ∈ Frac Λ` with (tex; kind; owner):

1. `IsTExpansion u (D.uPrim F x)` (tex 3878–3892; definition, DEPARTURE 3: needs `u` regular at
   `(t)`, proved at `x ≠ 0` by the regularity clause at `𝔭 = (t)`, tex 5004–5008, 5191–5192, and at
   `x = 0` by Lemma `ex:arith-base-zero`, tex 4334–4336, 4350–4368, under full Selmer corank one for
   `E/K`; owner RC0, with RC15);
2. `RegularityInputsS u`: `u = 0` (tex 5196–5197; ELLIOT; owner RC15 / RC16) or, at every
   height-one prime `𝔭 ≠ (2)`, `HeightOneSwitchDataS` over `Λ_𝔭` starting at `u` (fields as listed
   there: the two-term models and their identification, the sign involution, the nonzero actual
   class, the switch-plane coordinate relation, the sign bookkeeping, the nonquadratic duality and
   detection).

Equivalent to `∀ Co Ce F, D.FinalFamilyAt Co Ce F → ∀ x, InLamHalf (D.uPrim F x)`
(`primRegularityInputsS_iff`): the structures are a non-binding presentation of tex 4976–5194 and
do not constrain the genuine objects, so as a leaf this is Elliot's regularity assertion itself
(ELLIOT). PROVED for these abstract data: `pos`, `terminal`, `s_+ + s_- = s`, the nonquadratic
`U = F`, the descent and the intersection formula (RC16), the transfer to `ℚ₂[[t]]`.
Kind: definition. -/
def PrimRegularityInputsS : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    ∃ u : FractionRing Lambda, IsTExpansion u (D.uPrim F x) ∧ RegularityInputsS u

/-- **Conversion to the old leaf** `PrimRegularityInputs D`. Kind: PROVED. -/
theorem primRegularityInputs_of_S (h : PrimRegularityInputsS D) : PrimRegularityInputs D := by
  intro Co Ce F hF x
  obtain ⟨u, hT, hreg⟩ := h Co Ce F hF x
  exact ⟨u, hT, hreg.toRegularityInputs⟩

/-- **`u_{prim,x} ∈ Λ[1/2]`** at every address of every final family, from the refined leaf (RC16's
`mem_lambdaHalf_of_regularity`, then `inLamHalf_of_isTExpansion`). Kind: PROVED from the inputs. -/
theorem primLambdaHalf_of_inputsS (h : PrimRegularityInputsS D) :
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      InLamHalf (D.uPrim F x) := by
  intro Co Ce F hF x
  obtain ⟨u, hT, hreg⟩ := h Co Ce F hF x
  exact inLamHalf_of_isTExpansion hT hreg.mem_lambdaHalf

/-- **`RCSteps.height_one`** (tex 4909–5205, 5703–5704) from the refined leaf and (4.7).
Kind: PROVED from the inputs. -/
theorem heightOneTarget_of_inputsS (h : PrimRegularityInputsS D)
    (h47 : CommonCoordinateTarget D) : HeightOneTarget D :=
  heightOneTarget_of_prim D (primLambdaHalf_of_inputsS D h) h47

end HeightOneTarget

/-! ## The outer switching data, refined -/

section OuterData

/-- **The outer switching data, refined** (tex 4927–4964): batch 3's `OuterSwitchData` (round 3
field shape: `minor_link` along the ultrafilter) with the nonquadratic outer switch given by
`NonquadInputs` over `K_out`. Fields (tex; kind; owner):

* `Stage`, `stage`: the configurations; each has its outer model `D_out` over `K_out`
  (`= Frac 𝒪_∞`) with the outer image `z_out ≠ 0` of the primitive inner cycles, and inner minimal
  models of one size over `K` (`= Frac 𝒪`) with cycles, closed functionals and complements (tex
  4935–4940; the fixed size is "fixing the bounded `n` on an outer-large set", tex 4938–4939, from
  (5.1); GLUE identification of the completed Selmer models; owners RC6, batch 3 RankCounts /
  HeegnerCohomology).
* `minor_link`: a nonzero outer maximal minor gives inner minors at one position, nonzero on an
  outer-large set, integral and not negligible (tex 4732–4738, 4958–4960; GLUE; owner batch 3
  `SwitchInputs.minorLinkEventually_proof` proves it when `D_out` is the entrywise image of the
  inner integral models).
* `cycle_integral`, `functional_bound`: integral inner cycles and `v λ_j ≥ −a` (tex 4962–4963,
  3704–3720, 3864–3869; ELLIOT; owner batch 3 PairedFunctional).
* `switch`: for `s > 1`, a next configuration with `NonquadInputs` over `K_out` (duality and
  detection, tex 4940–4945) and, on an outer-large set, switch-plane data identifying the old and
  new inner coordinates with the finite and singular coordinates, unit volumes (tex 4946–4950; GLUE;
  owner RC16 `Switch`, batch 3). -/
structure OuterSwitchDataS {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) {J : Type*}
    (𝒰 : Ultrafilter J) (Kout : Type) [Field Kout] (a : ℕ) where
  /-- The configurations reached by successive switches. -/
  Stage : Type
  /-- The outer and inner models of each configuration. -/
  stage : Stage → UniformSwitch.OuterStage Kout K J
  /-- tex 4732–4738, 4958–4960: the outer minors are the classes of the inner minors. -/
  minor_link : ∀ S (k0 j0 : Fin ((stage S).m + 1)),
    ((stage S).Dout.submatrix k0.succAbove j0.succAbove).det ≠ 0 →
    ∃ (k1 j1 : Fin ((stage S).n + 1)),
      (∀ᶠ j in (𝒰 : Filter J), (((stage S).D j).submatrix k1.succAbove j1.succAbove).det ≠ 0) ∧
      (∀ᶠ j in (𝒰 : Filter J),
        (0 : WithTop ℤ) ≤ v ((((stage S).D j).submatrix k1.succAbove j1.succAbove).det)) ∧
      ¬ OuterNegligible v 𝒰 (fun j => (((stage S).D j).submatrix k1.succAbove j1.succAbove).det)
  /-- tex 4962: the inner cycles are integral. -/
  cycle_integral : ∀ S j i, (0 : WithTop ℤ) ≤ v ((stage S).z j i)
  /-- tex 4962–4963, 3864–3869: the functional exponent `a`. -/
  functional_bound : ∀ S j i, (((-a : ℤ)) : WithTop ℤ) ≤ v ((stage S).lam j i)
  /-- tex 4940–4950: a switch, with batch 3's nonquadratic inputs over `K_out`. -/
  switch : ∀ S, 1 < (stage S).outerDim → ∃ S',
    NonquadInputs Kout (stage S).outerDim (stage S').outerDim ∧
    ∀ᶠ j in (𝒰 : Filter J), ∃ X : UniformSwitch.SwitchCoordData K,
      v X.μF = 0 ∧ v X.μS = 0 ∧ (stage S).coord j = X.uF ∧ (stage S').coord j = X.uS

variable {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)} {J : Type*} {𝒰 : Ultrafilter J}
  {Kout : Type} [Field Kout] {a : ℕ}

/-- Batch 3's `OuterSwitchData` from the refined data (`NonquadInputs.nonquadDims`).
Kind: PROVED. -/
def OuterSwitchDataS.toData (P : OuterSwitchDataS v 𝒰 Kout a) :
    UniformSwitch.OuterSwitchData (Kout := Kout) v 𝒰 a where
  Stage := P.Stage
  stage := P.stage
  minor_link := P.minor_link
  cycle_integral := P.cycle_integral
  functional_bound := P.functional_bound
  switch S hs := by
    obtain ⟨S', hN, hX⟩ := P.switch S hs
    exact ⟨S', hN.nonquadDims, hX⟩

/-- RC16's `OuterSwitchProcess v 𝒰 a` from the refined data (batch 3's
`OuterSwitchData.toProcess`). Kind: PROVED. -/
def OuterSwitchDataS.toProcess (P : OuterSwitchDataS v 𝒰 Kout a) : OuterSwitchProcess v 𝒰 a :=
  P.toData.toProcess v 𝒰

end OuterData

/-! ## The (3.5) leaf -/

section Eq35

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The inputs of (3.5) over the genuine `𝒪` from the concrete models** (replaces
`Eq35InputsGenuine W`; Proposition `ex:limits-uniform-lower-bound`, tex 4909–5202, at the ring
instances `(h, k')` of Proposition `ex:sec7-genus-lower`, tex 2418–2446, with `K = Frac 𝒪`,
`v = v_𝒪`, `ι = ι_𝒪` of lane RC20). Conjuncts (tex; kind; owner):

1. An existential witness `uprim h k' ∈ Frac Λ` (read as the primitive coordinate of tex
   3877–3892, 4911–4913, but not tied to it in Lean; owner RC15) and `C₀` (the error of (4.6), tex
   3999–4000; definition; owner RC15).
2. Regularity: `RegularityInputsS (uprim h k')` at every companion pair (tex 4976–5194; fields of
   `HeightOneSwitchDataS`).
3. (4.6) at every companion pair, verbatim from `Eq35InputsGenuine` (tex 3987–4047; ELLIOT on
   GLUE Kolyvagin Thm 1 (cited statement) and PRINTs Milne ADT I.7.3, Edixhoven Thm 5.3; owner
   RC15, RC9).
4. Outer data: for every `A` and every sequence of companion pairs with `ω(k') ≤ A`, a field `K_out`,
   an exponent `a` and refined outer switching data `OuterSwitchDataS v_𝒪 (hyperfilter ℕ) K_out a`
   whose starting inner coordinates have the valuations of `ι_𝒪 (uprim h_j k'_j)` on an outer-large
   set (tex 4927–4964; fields of `OuterSwitchDataS`; owners RC6, batch 3, RC16).

PROVED from it (not inputs): `ValuationOfO` (lane RC20), `pos`, `terminal` (Cramer data, RC16),
the outer switch drop (batch 3's `relaxedImageFinite_proof`), the equal inner valuations (RC16's
`switch_equal_valuation`), (5.5), `u_prim ∈ Λ[1/2]` and (5.5) + (4.6) ⇒ (3.5)
(`exLimitsUniformLowerBound`). These hold for the abstract witnesses: (5.5) and
`u_prim ∈ Λ[1/2]` are equivalent to conjuncts 4 and 2 (one-configuration data;
`regularityInputsS_iff`), and the whole is equivalent to `Eq35Target W` (with
`eq35InputsGenuineS_of_G`). Kind: definition. -/
def Eq35InputsGenuineS : Prop :=
  ∃ (uprim : ℤ → ℤ → FractionRing Lambda) (C₀ : ℤ),
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputsS (uprim h k')) ∧
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      ∀ uh : LambdaHalf, lambdaHalfToFrac uh = uprim h k' →
        ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ C₀ ∧
          v2 (centralSpecialization uh) =
            ((2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
              ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ)) ∧
    (∀ A : ℕ, ∀ inst : ℕ → CompanionPair W A,
      ∃ (Kout : Type) (_ : Field Kout) (a : ℕ)
        (P : OuterSwitchDataS vO (Filter.hyperfilter ℕ) Kout a) (S₀ : P.Stage),
        ∀ᶠ j in ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ),
          vO ((P.stage S₀).coord j) = vO (iotaO (uprim (inst j).h (inst j).k)))

/-- **(3.5) for each fixed `A` at the rough companions** (tex 2441–2446, 5200–5202) from the
refined leaf: RC16's `exLimitsUniformLowerBound` over lane RC20's genuine `𝒪`
(`valuationOfO_genuine`), with the outer processes `OuterSwitchDataS.toProcess` and the regularity
processes `RegularityInputsS.rc16`; `C_R(E, A) = C + C₀ + 2A`. Kind: PROVED from the inputs. -/
theorem eq35Target_of_inputsGenuineS (hin : Eq35InputsGenuineS W) : Eq35Target W := by
  obtain ⟨uprim, C₀, hreg, h46, houter⟩ := hin
  intro A
  obtain ⟨C, -, hC⟩ := exLimitsUniformLowerBound vO iotaO valuationOfO_genuine A
    (fun i : CompanionPair W A => uprim i.h i.k)
    (fun inst => by
      obtain ⟨Kout, _, a, P, S₀, hS₀⟩ := houter A inst
      exact ⟨a, P.toProcess, S₀, hS₀⟩)
    (fun i => (hreg i.h i.k i.prepared i.simpleZero i.rough).rc16)
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

end Eq35


/-! ## The genuine outer model: `minor_link` proved -/

section GenuineOuter

variable {J : Type} (𝒰 : Ultrafilter J)

/-- `v_𝒪` is the `2`-adic valuation on `𝒪` (`n ≤ v_𝒪 r ↔ 2ⁿ ∣ r`), the hypothesis `IsPiAdicOn` of
batch 3's outer-minor link, from lane RC20's Gauss form `le_vO_iff_forall_coeffZ`. Kind: PROVED. -/
theorem isPiAdicOn_two_vO : SwitchInputs.IsPiAdicOn (K := FractionRing OO) (2 : OO) vO :=
  fun r n => (le_vO_iff_forall_coeffZ n r).trans (two_pow_dvd_iff_forall_coeffZ n r).symm

/-- The fraction field of the outer ring `𝒪_∞ = (∏_𝒰 𝒪)/(infinitesimals)` of (5.3) (lane RC6's
`OInf`, uniformizer `2`). Kind: definition. -/
abbrev KOut : Type := FractionRing (ZInQ.Manuscript.RC.Limits.OInf 𝒰 (2 : OO))

/-- **The outer model**: the entrywise image in `Frac 𝒪_∞` of the integral inner models (tex
4732–4738, "Integral minimal-model matrices ... pass to (5.3)"; lane RC6's `outerMatrix`).
Kind: definition. -/
def outerModel {n : ℕ} (M : J → Matrix (Fin (n + 1)) (Fin (n + 1)) OO) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (KOut 𝒰) :=
  (ZInQ.Manuscript.RC.Limits.outerMatrix 𝒰 (2 : OO) M).map (algebraMap _ (KOut 𝒰))

/-- **A configuration of the outer process with its genuine outer model** (tex 4935–4940): integral
inner minimal models `M_j` over `𝒪` of one size (`𝒪_j = 𝒪`), their cycles, closed functionals and
admissible complements over `K = Frac 𝒪`, and a nonzero kernel vector `z_out` of the outer model
`outerModel 𝒰 M` (the outer image of the primitive inner cycles, tex 4938–4940; GLUE; owner RC6 /
batch 3). The inner models being the completed minimal Selmer models of the ring instances is the
GLUE identification of the data (owners RC6, batch 3 RankCounts / HeegnerCohomology).
Kind: definition. -/
structure GenuineOuterStage where
  /-- The size `n + 1` of the inner models (fixed on an outer-large set, tex 4938–4939, by (5.1); a
  genuine witness pads the other instances, which changes neither the outer model nor the eventual
  valuations). -/
  n : ℕ
  /-- The integral inner minimal models. -/
  M : J → Matrix (Fin (n + 1)) (Fin (n + 1)) OO
  /-- The outer kernel vector. -/
  zout : Fin (n + 1) → KOut 𝒰
  hzout : outerModel 𝒰 M *ᵥ zout = 0
  hzout0 : zout ≠ 0
  /-- The inner cycles, closed functionals and complements over `Frac 𝒪`. -/
  z : J → Fin (n + 1) → FractionRing OO
  lam : J → Fin (n + 1) → FractionRing OO
  w : J → Fin n → Fin (n + 1) → FractionRing OO
  y : J → Fin (n + 1) → FractionRing OO
  hz : ∀ j, (M j).map (algebraMap OO (FractionRing OO)) *ᵥ z j = 0
  hlam : ∀ j, lam j ᵥ* (M j).map (algebraMap OO (FractionRing OO)) = 0
  hden : ∀ j, detCols (colsDWY ((M j).map (algebraMap OO (FractionRing OO))) (w j) (y j)) ≠ 0

variable {𝒰}

/-- Batch 3's `OuterStage` of a genuine configuration (outer model `outerModel 𝒰 M`, inner models
`M_j` over `Frac 𝒪`). Kind: definition. -/
def GenuineOuterStage.toStage (S : GenuineOuterStage 𝒰) :
    UniformSwitch.OuterStage (KOut 𝒰) (FractionRing OO) J where
  m := S.n
  Dout := outerModel 𝒰 S.M
  zout := S.zout
  hzout := S.hzout
  hzout0 := S.hzout0
  n := S.n
  D j := (S.M j).map (algebraMap OO (FractionRing OO))
  z := S.z
  lam := S.lam
  w := S.w
  y := S.y
  hz := S.hz
  hlam := S.hlam
  hden := S.hden

/-- **`minor_link` for the genuine outer model** (tex 4732–4738, 4958–4960): batch 3's
`minorLinkEventually_proof` over `𝒪` with `v_𝒪` (`isPiAdicOn_two_vO`): a nonzero outer maximal
minor gives the inner minors at the same position, nonzero on an outer-large set, integral and not
outer-negligible. Kind: PROVED. -/
theorem GenuineOuterStage.minor_link (S : GenuineOuterStage 𝒰) (k0 j0 : Fin (S.toStage.m + 1))
    (h : (S.toStage.Dout.submatrix k0.succAbove j0.succAbove).det ≠ 0) :
    ∃ (k1 j1 : Fin (S.toStage.n + 1)),
      (∀ᶠ j in (𝒰 : Filter J), ((S.toStage.D j).submatrix k1.succAbove j1.succAbove).det ≠ 0) ∧
      (∀ᶠ j in (𝒰 : Filter J),
        (0 : WithTop ℤ) ≤ vO (((S.toStage.D j).submatrix k1.succAbove j1.succAbove).det)) ∧
      ¬ OuterNegligible vO 𝒰
        (fun j => ((S.toStage.D j).submatrix k1.succAbove j1.succAbove).det) := by
  obtain ⟨h1, h2, h3⟩ := SwitchInputs.minorLinkEventually_proof 𝒰 vO (ϖ := (2 : OO))
    (K := FractionRing OO) S.n S.M (IsFractionRing.injective OO (FractionRing OO))
    isPiAdicOn_two_vO k0 j0 h
  exact ⟨k0, j0, h1, Eventually.of_forall h2, h3⟩

variable (𝒰)

/-- **The outer switching data with genuine outer models** (tex 4927–4964): `OuterSwitchDataS` over
`v_𝒪` and `K_out = Frac 𝒪_∞` whose configurations carry genuine outer models, so that
`minor_link` is PROVED (`GenuineOuterStage.minor_link`). Remaining fields (tex; kind; owner):

* `stage`: the genuine configurations (see `GenuineOuterStage`);
* `cycle_integral`, `functional_bound`: integral inner cycles, `v λ_j ≥ −a` (tex 4962–4963,
  3864–3869; ELLIOT; owner batch 3 PairedFunctional);
* `switch`: `NonquadInputs` over `Frac 𝒪_∞` (duality and detection, tex 4940–4945) and the
  per-instance switch-plane data with unit volumes (tex 4946–4950; GLUE; owner RC16 `Switch`,
  batch 3). -/
structure GenuineOuterSwitchData (a : ℕ) where
  /-- The configurations reached by successive switches. -/
  Stage : Type
  /-- The genuine configuration of each stage. -/
  stage : Stage → GenuineOuterStage 𝒰
  /-- tex 4962: the inner cycles are integral. -/
  cycle_integral : ∀ S j i, (0 : WithTop ℤ) ≤ vO ((stage S).z j i)
  /-- tex 4962–4963, 3864–3869: the functional exponent `a`. -/
  functional_bound : ∀ S j i, (((-a : ℤ)) : WithTop ℤ) ≤ vO ((stage S).lam j i)
  /-- tex 4940–4950: a switch. -/
  switch : ∀ S, 1 < (stage S).toStage.outerDim → ∃ S',
    NonquadInputs (KOut 𝒰) (stage S).toStage.outerDim (stage S').toStage.outerDim ∧
    ∀ᶠ j in (𝒰 : Filter J), ∃ X : UniformSwitch.SwitchCoordData (FractionRing OO),
      vO X.μF = 0 ∧ vO X.μS = 0 ∧ (stage S).toStage.coord j = X.uF ∧
        (stage S').toStage.coord j = X.uS

variable {𝒰}

/-- The refined outer data from genuine outer models (`minor_link` by
`GenuineOuterStage.minor_link`). Kind: PROVED. -/
def GenuineOuterSwitchData.toDataS {a : ℕ} (P : GenuineOuterSwitchData 𝒰 a) :
    OuterSwitchDataS vO 𝒰 (KOut 𝒰) a where
  Stage := P.Stage
  stage S := (P.stage S).toStage
  minor_link S := (P.stage S).minor_link
  cycle_integral := P.cycle_integral
  functional_bound := P.functional_bound
  switch := P.switch

end GenuineOuter

section Eq35G

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The inputs of (3.5) with genuine outer models** (replaces `Eq35InputsGenuine W`; as a leaf
this is (3.5) itself, ELLIOT: `uprim` is an existential witness not tied to the genuine coordinate,
the structures do not constrain the genuine objects, and the whole is equivalent to
`Eq35Target W`): `Eq35InputsGenuineS W` with the outer conjunct
given by
`GenuineOuterSwitchData (hyperfilter ℕ) a` (outer models over `Frac 𝒪_∞` the images of the inner
models, so `minor_link` is PROVED). Conjuncts 1–3 (the witness `uprim`, regularity
`RegularityInputsS`, (4.6)) are
those of `Eq35InputsGenuineS`; conjunct 4: for every `A` and every sequence of companion pairs with
`ω(k') ≤ A`, an exponent `a` and genuine outer switching data whose starting inner coordinates have
the valuations of `ι_𝒪 (uprim h_j k'_j)` on an outer-large set (tex 4927–4964; fields of
`GenuineOuterSwitchData`). Kind: definition. -/
def Eq35InputsGenuineG : Prop :=
  ∃ (uprim : ℤ → ℤ → FractionRing Lambda) (C₀ : ℤ),
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputsS (uprim h k')) ∧
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      ∀ uh : LambdaHalf, lambdaHalfToFrac uh = uprim h k' →
        ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ C₀ ∧
          v2 (centralSpecialization uh) =
            ((2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
              ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ)) ∧
    (∀ A : ℕ, ∀ inst : ℕ → CompanionPair W A,
      ∃ (a : ℕ) (P : GenuineOuterSwitchData (Filter.hyperfilter ℕ) a) (S₀ : P.Stage),
        ∀ᶠ j in ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ),
          vO ((P.stage S₀).toStage.coord j) = vO (iotaO (uprim (inst j).h (inst j).k)))

/-- **Conversion**: `Eq35InputsGenuineG W → Eq35InputsGenuineS W`. Kind: PROVED. -/
theorem eq35InputsGenuineS_of_G (h : Eq35InputsGenuineG W) : Eq35InputsGenuineS W := by
  obtain ⟨uprim, C₀, hreg, h46, houter⟩ := h
  refine ⟨uprim, C₀, hreg, h46, fun A inst => ?_⟩
  obtain ⟨a, P, S₀, hS₀⟩ := houter A inst
  exact ⟨KOut (Filter.hyperfilter ℕ), inferInstance, a, P.toDataS, S₀, hS₀⟩

/-- **(3.5) for each fixed `A`** (tex 2441–2446, 5200–5202) from the genuine-outer-model leaf.
Kind: PROVED from the inputs. -/
theorem eq35Target_of_inputsGenuineG (h : Eq35InputsGenuineG W) : Eq35Target W :=
  eq35Target_of_inputsGenuineS W (eq35InputsGenuineS_of_G W h)

end Eq35G

/-! ## Non-vacuity -/

section NonVacuity

variable (P : Ideal Lambda) [P.IsPrime]

/-- The one-stage two-term model `[Λ_𝔭 --0--> Λ_𝔭]` with class `1`, functional `r` and coordinate
`r` (non-vacuity). Kind: definition. -/
def oneStageAt (r : Localization.AtPrime P) : UniformSwitch.TwoTermStage (UniformSwitch.toFracAt P)
    where
  n := 0
  D := 0
  z := fun _ => 1
  w := fun _ => r
  u := UniformSwitch.toFracAt P r
  hz := by simp
  hw := by simp
  hu := by
    unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
    rw [adjugate_fin_one]
    ext i j; fin_cases i; fin_cases j; simp [vecMulVec]

theorem oneStageAt_fiberDim (r : Localization.AtPrime P) :
    (oneStageAt P r).fiberDim (IsLocalRing.residue (Localization.AtPrime P)) = 1 := by
  have h0 : ((oneStageAt P r).D.map (IsLocalRing.residue (Localization.AtPrime P))).mulVecLin =
      0 := by
    apply LinearMap.ext; intro v; ext i
    simp [oneStageAt]; rfl
  rw [UniformSwitch.TwoTermStage.fiberDim, h0, LinearMap.ker_zero, finrank_top, finrank_fin_fun]; rfl

/-- The one-stage refined data at a coordinate `r ∈ Λ_𝔭` (fiber dimension one, nonquadratic).
Kind: definition (non-vacuity). -/
def oneStageSwitchData (r : Localization.AtPrime P) : HeightOneSwitchDataAt P where
  Stage := Unit
  stage _ := oneStageAt P r
  quadratic := False
  sign _ := LinearMap.id
  sign_invol h := h.elim
  class_ne_zero _ h := one_ne_zero (congrFun h 0)
  switch_mixed _ _ hs := by rw [oneStageAt_fiberDim] at hs; omega
  switch_single _ h := h.elim

/-- **`RegularityInputsS u ↔ u ∈ Λ[1/2]`** (non-vacuity of the refined height-one inputs; `←` by
one-stage data and RC16's intersection formula). Kind: PROVED. -/
theorem regularityInputsS_iff (u : FractionRing Lambda) :
    RegularityInputsS u ↔ u ∈ lambdaHalfToFrac.range := by
  refine ⟨fun h => h.mem_lambdaHalf, fun hu => Or.inr fun P _ hP hne => ?_⟩
  obtain ⟨r, hr⟩ := (mem_range_lambdaHalf_iff_forall_height_one u).mp hu P hP hne
  exact ⟨oneStageSwitchData P r, (), hr⟩

/-- **`PrimRegularityInputsS D` holds exactly when every `u_{prim,x}` of every final family lies in
`Λ[1/2]`** (non-vacuity of the refined height-one leaf). Kind: PROVED. -/
theorem primRegularityInputsS_iff {ℓ : ℕ} (D : RCData ℓ) :
    PrimRegularityInputsS D ↔ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      ∀ x : Addr F.b, InLamHalf (D.uPrim F x) := by
  refine ⟨primLambdaHalf_of_inputsS D, fun h Co Ce F hF x => ?_⟩
  obtain ⟨u, hT, hu⟩ := exists_isTExpansion_of_inLamHalf (h Co Ce F hF x)
  exact ⟨u, hT, (regularityInputsS_iff u).mpr hu⟩

/-- `detCols` of the one-column example is nonzero (over any field). -/
theorem example_hdenK (K : Type) [Field K] :
    detCols (colsDWY (0 : Matrix (Fin 1) (Fin 1) K) Fin.elim0 (fun _ => 1)) ≠ 0 := by
  have : colsDWY (0 : Matrix (Fin 1) (Fin 1) K) Fin.elim0 (fun _ => 1) = fun _ _ => 1 := by
    funext i r
    obtain rfl : i = Fin.last 0 := Fin.eq_of_val_eq (by omega)
    rw [colsDWY, Fin.snoc_last]
  rw [this]
  change Matrix.det (Matrix.of fun _ _ : Fin 1 => (1 : K)) ≠ 0
  rw [Matrix.det_fin_one]; simp

/-- The single configuration of the outer example over `K_out = ℚ` and `K = Frac 𝒪`: outer model
`[ℚ --0--> ℚ]`, inner models `[K --0--> K]` with cycle, functional and complement `1`. -/
def exampleOuterStageO : UniformSwitch.OuterStage ℚ (FractionRing OO) ℕ where
  m := 0
  Dout := 0
  zout := fun _ => 1
  hzout := by simp
  hzout0 := fun h => by simpa using congrFun h 0
  n := 0
  D := fun _ => 0
  z := fun _ _ => 1
  lam := fun _ _ => 1
  w := fun _ => Fin.elim0
  y := fun _ _ => 1
  hz := fun _ => by simp
  hlam := fun _ => by simp
  hden := fun _ => example_hdenK _

theorem exampleOuterStageO_outerDim : exampleOuterStageO.outerDim = 1 := by
  have h0 : (exampleOuterStageO.Dout).mulVecLin = 0 := by
    apply LinearMap.ext; intro v; ext i; simp [exampleOuterStageO]; rfl
  rw [UniformSwitch.OuterStage.outerDim, h0, LinearMap.ker_zero, finrank_top, finrank_fin_fun]; rfl

/-- The empty minor of the `1 × 1` example is `1`. -/
theorem example_minorO : ((0 : Matrix (Fin 1) (Fin 1) (FractionRing OO)).submatrix
    (0 : Fin 1).succAbove (0 : Fin 1).succAbove).det = 1 := Matrix.det_isEmpty

/-- **Non-vacuity of `OuterSwitchDataS` over the genuine `v_𝒪`**: one configuration of outer
dimension one, minors `1`. Kind: PROVED. -/
def exampleOuterDataS (𝒰 : Ultrafilter ℕ) : OuterSwitchDataS vO 𝒰 ℚ 0 where
  Stage := Unit
  stage _ := exampleOuterStageO
  minor_link _ _ _ _ := ⟨(0 : Fin 1), (0 : Fin 1),
    Eventually.of_forall fun _ h => one_ne_zero (example_minorO.symm.trans h),
    Eventually.of_forall fun _ =>
      (le_of_eq (by rw [AddValuation.map_one] : (0 : WithTop ℤ) = vO 1)).trans_eq
        (congrArg vO example_minorO).symm,
    fun h => by
      obtain ⟨j, hj⟩ := (h 1).exists
      have hj' : ((1 : ℤ) : WithTop ℤ) ≤ vO 1 := hj.trans_eq (congrArg vO example_minorO)
      rw [AddValuation.map_one] at hj'
      exact absurd (WithTop.coe_le_coe.mp hj') (by norm_num)⟩
  cycle_integral _ _ _ := by
    change (0 : WithTop ℤ) ≤ vO 1
    rw [AddValuation.map_one]
  functional_bound _ _ _ := by
    change (((-(0 : ℕ) : ℤ)) : WithTop ℤ) ≤ vO 1
    rw [AddValuation.map_one]; rfl
  switch S hs := by
    exfalso
    have h1 : exampleOuterStageO.outerDim = 1 := exampleOuterStageO_outerDim
    exact absurd (h1 ▸ hs : 1 < 1) (lt_irrefl 1)

/-- The outer model of the zero inner models is zero. -/
theorem outerModel_zero (𝒰 : Ultrafilter ℕ) :
    outerModel 𝒰 (fun _ : ℕ => (0 : Matrix (Fin 1) (Fin 1) OO)) = 0 := by
  have h : ZInQ.Manuscript.RC.Limits.outerMatrix 𝒰 (2 : OO)
      (fun _ : ℕ => (0 : Matrix (Fin 1) (Fin 1) OO)) = 0 := by
    ext a b
    exact map_zero (ZInQ.Manuscript.RC.Limits.toOInf 𝒰 (2 : OO))
  rw [outerModel, h]
  exact Matrix.map_zero _ (map_zero _)

/-- The genuine one-configuration example: inner models `0 ∈ 𝒪^{1×1}`, outer model `0`,
`z_out = 1`, inner cycle, functional and complement `1`. -/
def exampleGenuineStage (𝒰 : Ultrafilter ℕ) : GenuineOuterStage 𝒰 where
  n := 0
  M := fun _ => 0
  zout := fun _ => 1
  hzout := by
    show outerModel 𝒰 (fun _ : ℕ => (0 : Matrix (Fin 1) (Fin 1) OO)) *ᵥ (fun _ => 1) = 0
    rw [outerModel_zero]; exact Matrix.zero_mulVec _
  hzout0 := fun h => by simpa using congrFun h 0
  z := fun _ _ => 1
  lam := fun _ _ => 1
  w := fun _ => Fin.elim0
  y := fun _ _ => 1
  hz := fun _ => by simp
  hlam := fun _ => by simp
  hden := fun _ => by
    show detCols (colsDWY ((0 : Matrix (Fin 1) (Fin 1) OO).map (algebraMap OO (FractionRing OO)))
      Fin.elim0 (fun _ => 1)) ≠ 0
    rw [show ((0 : Matrix (Fin 1) (Fin 1) OO).map (algebraMap OO (FractionRing OO))) = 0 by simp]
    exact example_hdenK _

/-- The kernel of a `1 × 1` matrix over a field has dimension at most one. -/
theorem finrank_ker_fin_one_le {F' : Type} [Field F'] (D : Matrix (Fin 1) (Fin 1) F') :
    finrank F' (LinearMap.ker D.mulVecLin) ≤ 1 :=
  (Submodule.finrank_le _).trans (Module.finrank_fin_fun F').le

theorem exampleGenuineStage_outerDim_le (𝒰 : Ultrafilter ℕ) :
    (exampleGenuineStage 𝒰).toStage.outerDim ≤ 1 :=
  finrank_ker_fin_one_le (F' := KOut 𝒰) (exampleGenuineStage 𝒰).toStage.Dout

/-- **Non-vacuity of `GenuineOuterSwitchData`** (genuine outer models over `Frac 𝒪_∞`, `v_𝒪`): one
configuration of outer dimension one. Kind: PROVED. -/
def exampleGenuineOuterData (𝒰 : Ultrafilter ℕ) : GenuineOuterSwitchData 𝒰 0 where
  Stage := Unit
  stage _ := exampleGenuineStage 𝒰
  cycle_integral _ _ _ := by
    change (0 : WithTop ℤ) ≤ vO 1
    rw [AddValuation.map_one]
  functional_bound _ _ _ := by
    change (((-(0 : ℕ) : ℤ)) : WithTop ℤ) ≤ vO 1
    rw [AddValuation.map_one]; rfl
  switch S hs := absurd (exampleGenuineStage_outerDim_le 𝒰) (not_le.mpr hs)

end NonVacuity

end ZInQ.Manuscript.RC.Wiring
