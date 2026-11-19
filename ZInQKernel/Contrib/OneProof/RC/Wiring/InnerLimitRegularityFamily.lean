import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitStageFamily
import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitRegularityModel
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchCollapse
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Bridge

/-!
# Theorem 5.3, Lane RC0 round 15: the height-one leaf on the stage family, fibres pinned

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5200), on the text's
inner-limit route at nonquadratic specializations (tex 5027–5086, 4834–4907, 4385–4451) with the
stage family of tex 5056–5062 (no Selmer condition at the new prime in the stage complex), and
with homology-level single-sign and mixed switches at quadratic specializations (tex 5005–5054,
5116–5136).

`PrimRegularityInputsILF D`: for every final family and address a `t`-expansion `u` of the
primitive coordinate with `RegularityInputsILF u`: either `u = 0`, or at every height-one prime
`𝔭 ≠ (2)` a configuration family genuine at `𝔭`, a number field `K` with places `S`, the actual
conjugation and the curve `W = E_ℓ ⊗ K` with full two-torsion, such that
* the actual fibre of the family is the genuine Selmer complex of the `Λ`-adic fibre
  `V_𝔭 = k(𝔭) ⊗ T₂E` (twisted by a continuous `Λ`-valued character) with some genuine local
  conditions (lane RC28's `fibreSelData`): the actual fibre is pinned to the `Λ`-adic module (the
  other configurations' fibres are only genuine Galois Selmer data);
* at a nonquadratic specialization `InnerLimitSwitchFamily` over the family, and at a quadratic
  specialization `HomologySwitchDataPK`.

PROVED: `RegularityInputsILF.toMdl`, `PrimRegularityInputsILF.toMdl`,
`primRegularityInputs_of_ILF`, `heightOneTarget_of_ILF`, `primRegularityInputsILF_of_uPrim_zero`.

**How conclusion-shaped the leaves are, exactly.**
* `primRegularityInputsILM_iff_of_unitFibre`: the round-14 leaf `PrimRegularityInputsILM` is
  equivalent to `PrimRegularityInputs` as soon as some genuine Galois Selmer complex over each
  `k(𝔭)` has the homotopy type of `[k --0--> k]` (no switch is then required).
* `primRegularityInputsILF_iff_of_unitFibre`: the pinned leaf is equivalent to
  `PrimRegularityInputs` as soon as some genuine Selmer complex OF THE `Λ`-ADIC FIBRE `V_𝔭` (for
  some local conditions and some continuous character) has that homotopy type at each `𝔭` (a
  sufficient condition; no converse is proved).
The actual fibres must come from the `Λ`-adic module; `RC/LambdaCoef` provides conditional
fixed-character constructions; their identification with the retained inner-limit diagrams
remains open. The pin fixes the module of the actual fibre only, not its local conditions or
character, which remain existential and are not tied to the stage family's characters and old
conditions; the successor fibres and the family's actual class and functional (`zAct`, `lamAct`)
are not pinned (the text's conditions are the old conditions of the address and its character is
`χ_{h_x} Ψ_i`, tex 2791). DEPARTURE: the pinned character and the stage family's characters are
characters of `G_{K,S}` for the fixed finite `S`, whereas the text's `χ_h Ψ_i` ramify at conductor
primes `r_i` that vary with the precision and need not be restrictions of one character (tex
2727–2741, 4268–4272), so neither can be the text's characters; the leaf is stated for
fixed-support characters (lane RC28's conditional construction).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing Module
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.Uniform (Lambda lambdaHalfToFrac mem_range_lambdaHalf_iff_forall_height_one)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion IsHeightOneOdd IsContChar VP
  fibreSelData)
open ZInQ.Manuscript.RC.SelmerComplex (GKS GaloisLocalConditions)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness MilneGlobalFiniteness)

/-- **The regularity inputs on the stage family of the text, fibres pinned** (tex 4976–5200), for
the curve `E_ℓ`: `u = 0` (tex 5196–5197; ELLIOT), or at every height-one prime `𝔭 ≠ (2)` of `Λ` a
configuration family `Φ` genuine at `𝔭` (`IsGenuineFamilyAt`; GLUE), a number field `K`, places
`S`, the actual conjugation `Cn` and the curve `W = E_ℓ ⊗ K` fixed by it with full two-torsion
(the address's curve; data and GLUE), with
* the actual fibre of `Φ` the genuine Selmer complex of the `Λ`-adic fibre `V_𝔭` for a continuous
  character and some genuine local conditions (`fibreSelData`; GLUE, tex 3455–3463, 4976);
* `InnerLimitSwitchFamily` over `Φ` starting at `u` (its frame makes the specialization
  nonquadratic), or, at a quadratic specialization (tex 5005–5008), `HomologySwitchDataPK`.

Kind: definition. -/
def RegularityInputsILF (ℓ : ℕ) (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime] (hP : P.height = 1) (hne : P ≠ Ideal.span {2}),
    haveI : IsHeightOneOdd P := ⟨hP, hne⟩
    ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
        (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
        (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W),
        W = (Ecurve ℓ).baseChange K ∧
        (∃ (α : GKS K S →* Lambdaˣ) (_ : IsContChar α)
          (Δ : GaloisLocalConditions K S (ResAt P) (VP K S W P α)),
          Φ.fibre Φ.actual = fibreSelData W P α Δ) ∧
        (Nonempty (InnerLimitSwitchFamily P Cn W hW Φ (UniformSwitch.toFracAt P) u) ∨
          (Φ.quadratic (resAt P) ∧
            Nonempty (HomologySwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u)))

variable {ℓ : ℕ} {u : FractionRing Lambda}

/-- **The pinned family inputs give the model-level inputs** (`InnerLimitSwitchFamily.toInner`,
`InnerLimitSwitchModel.toModelInputs`). Kind: PROVED. -/
theorem RegularityInputsILF.toMdl (h : RegularityInputsILF ℓ u) : RegularityInputsMdl u := by
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr fun P _ hP hne => ?_
    obtain ⟨Φ, hΦ, K, _, _, S, Cn, W, hW, _, _, -, -, hb⟩ := h P hP hne
    refine ⟨Φ, hΦ, ?_⟩
    rcases hb with ⟨⟨X⟩⟩ | hq
    · exact Or.inl ⟨X.toInner.toModelInputs⟩
    · exact Or.inr hq

/-- `u ∈ Λ[1/2]` from the pinned family inputs. Kind: PROVED. -/
theorem RegularityInputsILF.mem_lambdaHalf (h : RegularityInputsILF ℓ u) :
    u ∈ lambdaHalfToFrac.range :=
  h.toMdl.mem_lambdaHalf

variable (D : RCData ℓ)

/-- **The height-one leaf on the stage family of the text, fibres pinned** (tex 4976–5200, at the
ring instances of the final field): for every final family `F` and address `x` a `u ∈ Frac Λ`
with `IsTExpansion u (D.uPrim F x)` (tex 3877–3892; GLUE) and `RegularityInputsILF ℓ u`. Kind:
definition. -/
def PrimRegularityInputsILF : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    ∃ u : FractionRing Lambda, IsTExpansion u (D.uPrim F x) ∧ RegularityInputsILF ℓ u

/-- The pinned family leaf gives the model-level leaf. Kind: PROVED. -/
theorem PrimRegularityInputsILF.toMdl (h : PrimRegularityInputsILF D) :
    PrimRegularityInputsMdl D := by
  intro Co Ce F hF x
  obtain ⟨u, hT, hu⟩ := h Co Ce F hF x
  exact ⟨u, hT, hu.toMdl⟩

/-- **`PrimRegularityInputs` from the pinned family leaf** (the form consumed by the base-zero
step). Kind: PROVED. -/
theorem primRegularityInputs_of_ILF (h : PrimRegularityInputsILF D) : PrimRegularityInputs D :=
  primRegularityInputs_of_Mdl D h.toMdl

/-- **`RCSteps.height_one`** from the pinned family leaf and (4.7). Kind: PROVED (from the
inputs). -/
theorem heightOneTarget_of_ILF (h : PrimRegularityInputsILF D) (h47 : CommonCoordinateTarget D) :
    HeightOneTarget D :=
  heightOneTarget_of_inputs D (primRegularityInputs_of_ILF D h) h47

/-- **Degenerate satisfiability**: the leaf holds when the primitive coordinates vanish (the
`u = 0` branch). Kind: PROVED. -/
theorem primRegularityInputsILF_of_uPrim_zero (hD : ∀ F x, D.uPrim F x = 0) :
    PrimRegularityInputsILF D :=
  fun _ _ F _ x => ⟨0, by rw [hD F x]; exact isTExpansion_zero, Or.inl rfl⟩

/-! **How conclusion-shaped the leaves are** -/

section UnitFibre

variable {ℓ : ℕ}

/-- The frame of a one-stage collapse family, with nonzero class. Kind: PROVED. -/
def collapseFrame {P : Ideal Lambda} [P.IsPrime] (F : SelData (ResAt P))
    (e : HomotopyEquiv (selCx F).toCC (unitFibre P)) (r : Localization.AtPrime P)
    (h2 : (2 : ResAt P) ≠ 0) (u : FractionRing Lambda) (hu : UniformSwitch.toFracAt P r = u)
    (hq : ¬ (collapseFamily F e r).quadratic (resAt P)) :
    SwitchModelFrame (collapseFamily F e r) (UniformSwitch.toFracAt P) (resAt P) u where
  stage := (collapseData F e r h2 u hu).stage
  model := (collapseData F e r h2 u hu).model
  hz0 := (collapseData F e r h2 u hu).hz0
  hw0 := (collapseData F e r h2 u hu).hw0
  hu0 := (collapseData F e r h2 u hu).hu0
  hnq := hq
  class_ne_zero c hc := by
    obtain ⟨i, hi⟩ := (collapseData F e r h2 u hu).primitive c hc
    exact ⟨i, fun hn => hi (by rw [hn, map_zero])⟩

/-- No switch is required on a one-stage collapse family. Kind: PROVED. -/
theorem collapse_no_switch {P : Ideal Lambda} [P.IsPrime] (F : SelData (ResAt P))
    (e : HomotopyEquiv (selCx F).toCC (unitFibre P)) (r : Localization.AtPrime P)
    (h2 : (2 : ResAt P) ≠ 0) (u : FractionRing Lambda) (hu : UniformSwitch.toFracAt P r = u)
    (c : (collapseFamily F e r).Config) :
    ¬ 1 < ((collapseData F e r h2 u hu).stage c).fiberDim (resAt P) := by
  change ¬ 1 < (oneStageAt P r).fiberDim (resAt P)
  rw [oneStageAt_fiberDim]
  exact lt_irrefl 1

/-- **The round-14 leaf is target-shaped under one genuine one-stage fibre**: given a curve datum
(`W = E_ℓ ⊗ K` with the actual conjugation and full two-torsion) and, at every height-one prime
`𝔭 ≠ (2)`, `2 ≠ 0` in `k(𝔭)` and one genuine Galois Selmer complex over `k(𝔭)` homotopy equivalent
to `[k --0--> k]`, `RegularityInputsILM ℓ … u ↔ u ∈ Λ[1/2]`: no switch is then required. Kind:
PROVED. -/
theorem regularityInputsILM_iff_of_unitFibre (hmloc : MilneLocalFiniteness)
    (hmglob : MilneGlobalFiniteness) (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (Cn : ActualConj K S) (W : WeierstrassCurve K)
    (hW : W.map (Cn.κ : K →+* K) = W) [W.IsElliptic] [HasFullTwoTorsion K S W]
    (hWE : W = (Ecurve ℓ).baseChange K)
    (hE : ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
      (2 : ResAt P) ≠ 0 ∧ ∃ F : SelData (ResAt P), IsGaloisSelData F ∧
        Nonempty (HomotopyEquiv (selCx F).toCC (unitFibre P))) (u : FractionRing Lambda) :
    RegularityInputsILM ℓ hmloc hmglob u ↔ u ∈ lambdaHalfToFrac.range := by
  refine ⟨fun h => h.mem_lambdaHalf, fun hu => Or.inr fun P _ hP hne => ?_⟩
  obtain ⟨r, hr⟩ := (mem_range_lambdaHalf_iff_forall_height_one u).mp hu P hP hne
  obtain ⟨h2, F, hF, ⟨e⟩⟩ := hE P hP hne
  refine ⟨collapseFamily F e r, ⟨fun _ => hF, rfl⟩, ?_⟩
  by_cases hq : (collapseFamily F e r).quadratic (resAt P)
  · exact Or.inr ⟨hq, ⟨(GenuineSwitchDataPK.ofGenuineSwitchData
      (collapseData F e r h2 u hr)).toHomology⟩⟩
  · refine Or.inl ⟨K, inferInstance, inferInstance, S, Cn, W, hW, inferInstance, inferInstance,
      hWE, ⟨{ toSwitchModelFrame := collapseFrame F e r h2 u hr hq, step := ?_ }⟩⟩
    intro c _ hd
    exact absurd hd (collapse_no_switch F e r h2 u hr c)

/-- **The round-14 leaf is equivalent to `PrimRegularityInputs` under one genuine one-stage fibre
at every height-one prime** (given a curve datum). Kind: PROVED. -/
theorem primRegularityInputsILM_iff_of_unitFibre (D : RCData ℓ) (hmloc : MilneLocalFiniteness)
    (hmglob : MilneGlobalFiniteness) (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (Cn : ActualConj K S) (W : WeierstrassCurve K)
    (hW : W.map (Cn.κ : K →+* K) = W) [W.IsElliptic] [HasFullTwoTorsion K S W]
    (hWE : W = (Ecurve ℓ).baseChange K)
    (hE : ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
      (2 : ResAt P) ≠ 0 ∧ ∃ F : SelData (ResAt P), IsGaloisSelData F ∧
        Nonempty (HomotopyEquiv (selCx F).toCC (unitFibre P))) :
    PrimRegularityInputsILM D ↔ PrimRegularityInputs D := by
  refine ⟨primRegularityInputs_of_ILM D, fun hD => ⟨hmloc, hmglob, fun Co Ce F hF x => ?_⟩⟩
  obtain ⟨u, hu, hr⟩ := exists_isTExpansion_of_inLamHalf
    ((primRegularityInputs_iff D).mp hD Co Ce F hF x)
  exact ⟨u, hu, (regularityInputsILM_iff_of_unitFibre hmloc hmglob K S Cn W hW hWE hE u).mpr hr⟩

/-- **The pinned leaf is target-shaped under a one-stage `Λ`-adic fibre** (a sufficient
condition; no converse is proved): given, at every
height-one prime `𝔭 ≠ (2)`, `2 ≠ 0` in `k(𝔭)`, a curve datum `W = E_ℓ ⊗ K`, a continuous character
and genuine local conditions for which the genuine Selmer complex of the `Λ`-adic fibre `V_𝔭` is
a genuine Galois Selmer complex homotopy equivalent to `[k --0--> k]`,
`RegularityInputsILF ℓ u ↔ u ∈ Λ[1/2]`. Kind: PROVED. -/
theorem regularityInputsILF_iff_of_unitFibre
    (hE : ∀ (P : Ideal Lambda) [P.IsPrime] (hP : P.height = 1) (hne : P ≠ Ideal.span {2}),
      haveI : IsHeightOneOdd P := ⟨hP, hne⟩
      (2 : ResAt P) ≠ 0 ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
        (Cn : ActualConj K S) (W : WeierstrassCurve K) (_ : W.map (Cn.κ : K →+* K) = W)
        (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W),
        W = (Ecurve ℓ).baseChange K ∧
        ∃ (α : GKS K S →* Lambdaˣ) (_ : IsContChar α)
          (Δ : GaloisLocalConditions K S (ResAt P) (VP K S W P α)),
          IsGaloisSelData (fibreSelData W P α Δ) ∧
          Nonempty (HomotopyEquiv (selCx (fibreSelData W P α Δ)).toCC (unitFibre P)))
    (u : FractionRing Lambda) :
    RegularityInputsILF ℓ u ↔ u ∈ lambdaHalfToFrac.range := by
  refine ⟨fun h => h.mem_lambdaHalf, fun hu => Or.inr fun P _ hP hne => ?_⟩
  have : IsHeightOneOdd P := ⟨hP, hne⟩
  obtain ⟨r, hr⟩ := (mem_range_lambdaHalf_iff_forall_height_one u).mp hu P hP hne
  obtain ⟨h2, K, _, _, S, Cn, W, hW, _, _, hWE, α, _, Δ, hF, ⟨e⟩⟩ := hE P hP hne
  refine ⟨collapseFamily (fibreSelData W P α Δ) e r, ⟨fun _ => hF, rfl⟩, K, inferInstance,
    inferInstance, S, Cn, W, hW, inferInstance, inferInstance, hWE, ⟨α, inferInstance, Δ, rfl⟩, ?_⟩
  by_cases hq : (collapseFamily (fibreSelData W P α Δ) e r).quadratic (resAt P)
  · exact Or.inr ⟨hq, ⟨(GenuineSwitchDataPK.ofGenuineSwitchData
      (collapseData _ e r h2 u hr)).toHomology⟩⟩
  · refine Or.inl ⟨{ toSwitchModelFrame := collapseFrame _ e r h2 u hr hq, step := ?_ }⟩
    intro c _ hd
    exact absurd hd (collapse_no_switch _ e r h2 u hr c)

/-- **The pinned leaf is equivalent to `PrimRegularityInputs` under a one-stage `Λ`-adic fibre at
every height-one prime** (a sufficient condition; no converse is proved). Kind: PROVED. -/
theorem primRegularityInputsILF_iff_of_unitFibre (D : RCData ℓ)
    (hE : ∀ (P : Ideal Lambda) [P.IsPrime] (hP : P.height = 1) (hne : P ≠ Ideal.span {2}),
      haveI : IsHeightOneOdd P := ⟨hP, hne⟩
      (2 : ResAt P) ≠ 0 ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
        (Cn : ActualConj K S) (W : WeierstrassCurve K) (_ : W.map (Cn.κ : K →+* K) = W)
        (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W),
        W = (Ecurve ℓ).baseChange K ∧
        ∃ (α : GKS K S →* Lambdaˣ) (_ : IsContChar α)
          (Δ : GaloisLocalConditions K S (ResAt P) (VP K S W P α)),
          IsGaloisSelData (fibreSelData W P α Δ) ∧
          Nonempty (HomotopyEquiv (selCx (fibreSelData W P α Δ)).toCC (unitFibre P))) :
    PrimRegularityInputsILF D ↔ PrimRegularityInputs D := by
  refine ⟨primRegularityInputs_of_ILF D, fun hD Co Ce F hF x => ?_⟩
  obtain ⟨u, hu, hr⟩ := exists_isTExpansion_of_inLamHalf
    ((primRegularityInputs_iff D).mp hD Co Ce F hF x)
  exact ⟨u, hu, (regularityInputsILF_iff_of_unitFibre hE u).mpr hr⟩

end UnitFibre

end ZInQ.Manuscript.RC.Wiring
