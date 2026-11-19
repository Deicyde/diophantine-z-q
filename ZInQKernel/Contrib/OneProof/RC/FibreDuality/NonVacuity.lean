import ZInQKernel.Contrib.OneProof.RC.FibreDuality.Pairing
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.NonVacuity
import ZInQKernel.Contrib.OneProof.RC.CoefModules.ConjStable

/-!
# Lane RC31, part 11: non-vacuity of the fibre-duality hypotheses

Manuscript `diophantine_zq.tex`, tex 1760–1830 (the curves `E_ℓ : y² = x(x−ℓ)(x+3ℓ)`) and
tex 4976–5200 (the fibres at height-one primes). Lane RC28's example: `E_1 : y² = x(x−1)(x+3)` over
`ℚ`, the prime `𝔭 = (t)` of `Λ` (residue field `k((t)) = ℚ₂`).

The structures used as hypotheses by the PRINTs and their corollaries have the following
instances here. Only the trace packet is exhibited solely outside a valid setting (at `S = ∅`);
the Tate twist is unconditional at `S = Set.univ` (not finite) and holds at `S6` through
`nekovarFibre_hypotheses_E1`; the global traces with `InducesIsoH3` have no Lean instance (they
come from the PRINT `NekovarFibreTraces`). Details in the bullets:

* `NekovarFibreSetting ℚ S6` for `S6` = the primes above `6` (finite, contains the prime above `2`;
  `E_1` has good reduction outside `2·3`): PROVED.
* `HasTwoPowerRoots ℚ Set.univ` (through `E_1`'s full `2`-power torsion over `K̄`, lane RC28's
  `hasFullTwoTorsion_univ`): PROVED.
* `IsLatticeTop` and `IsTateTwistFibre` for the twist `k((t))(1) = Tate1P`: PROVED
  (`IsTateTwistFibre` at `S = Set.univ`, where `μ_{2^∞} ⊆ K_S` is PROVED) (`S = Set.univ` is not
  finite; at `S6` this holds under the GLUE, `nekovarFibre_hypotheses_E1`).
* `FibreLocalTraces` (one trace packet): only the empty packet for `S = ∅`, which is outside
  `NekovarFibreSetting` (`above_two`); at a valid `S` (e.g. `S6`) the packet and the global traces
  with `InducesIsoH3` are supplied only by the PRINT `NekovarFibreTraces` (no Lean instance).
* the truncated isotropy data of (relaxed, strict) and (strict, relaxed) for the fibres:
  `relaxedStrictTruncIsotropy`, `strictRelaxedTruncIsotropy` (`Duality.lean`).
* **`E_1` at `(t)` over `S6`**: `IsLatticeTop` for `V_(t)(α)` and `V_(t)(α⁻¹)` (unconditional,
  `isLatticeTop_vp_E1`); under lane RC28's GLUE `HasFullTwoTorsion ℚ S6 curveE1`
  (Néron–Ogg–Shafarevich: `E_1` has good reduction outside `2 · 3`, so `ℚ(E_1[2^∞])` is unramified
  outside `{2, 3, ∞}`) ALL hypotheses of the PRINTs hold with the genuine coefficient data
  (`nekovarFibre_hypotheses_E1`), and the consumer duality specializes
  (`fibreSelmerDuality_E1`).
* The transported (conjugate) form: an actual complex conjugation for `ℚ` (`actualConjQ`),
  `E_1^κ = E_1`, and `α ∘ c = α⁻¹` for RC28's `α = χ_1 Ψ_0` (`alphaLam_conj`).

Kinds: PROVED (instances, theorems and `example`s), under the stated GLUE where marked.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open NumberField IsDedekindDomain PowerSeries
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.LambdaCoef (curveE1 Pt0 alphaLam HasFullTwoTorsion IsHeightOneOdd VP
  lambdaChar coe_lambdaChar onePlusTPow_zero fibreRelaxed fibreStrict)
open ZInQ.Manuscript.RC.CoefModules (ActualConj exists_complexConj_algClosure quadChar)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-- The primes of `ℚ` above `6 = 2 · 3` (the bad primes of `E_1` and the prime above `2`). -/
abbrev S6 : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | (6 : 𝓞 ℚ) ∈ v.asIdeal}

/-- **The fibre standing hypotheses hold for `S6`**: finite, containing the prime above `2`.
Kind: PROVED. -/
theorem nekovarFibreSetting_S6 : NekovarFibreSetting ℚ S6 where
  finite_S := by
    have h : Ideal.span {(6 : 𝓞 ℚ)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      norm_num
    refine (Ideal.finite_factors h).subset ?_
    intro v hv
    simpa [Ideal.span_singleton_le_iff_mem] using hv
  above_two v hv := by
    change (6 : 𝓞 ℚ) ∈ v.asIdeal
    have : (6 : 𝓞 ℚ) = 3 * 2 := by norm_num
    rw [this]
    exact v.asIdeal.mul_mem_left 3 hv

/-- **`μ_{2^∞} ⊆ K̄`**: `HasTwoPowerRoots ℚ Set.univ` (from `E_1`'s full `2`-power torsion over
`K_{univ} = K̄`). Kind: PROVED. -/
instance hasTwoPowerRoots_univ : HasTwoPowerRoots ℚ Set.univ :=
  hasTwoPowerRoots_of_fullTwoTorsion ℚ Set.univ curveE1

/-- **Non-vacuity of `IsTateTwistFibre`**: `k((t))(1)` over `G_{ℚ}` (`S = Set.univ`).
Kind: PROVED. -/
theorem isTateTwistFibre_example :
    IsTateTwistFibre ℚ Set.univ Pt0 (Tate1P ℚ Set.univ Pt0) :=
  isTateTwistFibre_tate1P ℚ Set.univ Pt0

/-- **Non-vacuity of `IsLatticeTop`**: `k((t))(1)` with its lattice topology, for every `S`
(here `S6`). Kind: PROVED. -/
theorem isLatticeTop_tate1P_example : IsLatticeTop (GKS ℚ S6) (Tate1P ℚ S6 Pt0) :=
  isLatticeTop_tate1P ℚ S6 Pt0

/-- **The trace packet is a non-vacuous structure**: for `S = ∅` the empty packet. Kind: PROVED. -/
def emptyLocalTraces (k T : Type) [CommRing k] [AddCommGroup T] [Module k T]
    [DistribMulAction (GKS ℚ (∅ : Set (HeightOneSpectrum (𝓞 ℚ)))) T]
    [SMulCommClass (GKS ℚ (∅ : Set (HeightOneSpectrum (𝓞 ℚ)))) k T] [TopologicalSpace T]
    [ContinuousAdd T] [ContinuousConstSMul k T]
    [ContinuousSMul (GKS ℚ (∅ : Set (HeightOneSpectrum (𝓞 ℚ)))) T] :
    FibreLocalTraces (∅ : Set (HeightOneSpectrum (𝓞 ℚ))) k T where
  trv v := absurd v.2 (Set.notMem_empty _)
  htrv v := absurd v.2 (Set.notMem_empty _)
  iso v := absurd v.2 (Set.notMem_empty _)

/-! ### `E_1` at `(t)` over `S6` -/

/-- **`V_(t)(E_1)` and its Kummer dual carry Nekovář's topology** (`IsLatticeTop`), over `S6`,
unconditionally (`T_2E` is finitely generated, `isLatticeTop_vp'`). Kind: PROVED. -/
theorem isLatticeTop_vp_E1 :
    IsLatticeTop (GKS ℚ S6) (VP ℚ S6 curveE1 Pt0 (alphaLam ℚ S6)) ∧
      IsLatticeTop (GKS ℚ S6) (VP ℚ S6 curveE1 Pt0 (alphaLam ℚ S6)⁻¹) :=
  ⟨isLatticeTop_vp' Pt0, isLatticeTop_vp' Pt0⟩

section GLUE

variable [HasFullTwoTorsion ℚ S6 curveE1]

/-- **All hypotheses of the PRINTs hold for `E_1` at `(t)` over `S6`** with the genuine
coefficient data: `V_(t)(α)`, its Kummer dual `V_(t)(α⁻¹)`, `T = k((t))(1)` and the
Weil/determinant pairing `betaT` (equivariant and continuous by `betaT_smul`,
`continuous_betaT`). Kind: PROVED under lane RC28's GLUE `HasFullTwoTorsion ℚ S6 curveE1`
(Néron–Ogg–Shafarevich). -/
theorem nekovarFibre_hypotheses_E1 :
    NekovarFibreSetting ℚ S6 ∧
      IsLatticeTop (GKS ℚ S6) (VP ℚ S6 curveE1 Pt0 (alphaLam ℚ S6)) ∧
      IsLatticeTop (GKS ℚ S6) (VP ℚ S6 curveE1 Pt0 (alphaLam ℚ S6)⁻¹) ∧
      IsLatticeTop (GKS ℚ S6) (Tate1P ℚ S6 Pt0) ∧
      IsTateTwistFibre ℚ S6 Pt0 (Tate1P ℚ S6 Pt0) ∧
      Function.Bijective (betaT curveE1 Pt0 (alphaLam ℚ S6)) ∧
      Function.Bijective (betaT curveE1 Pt0 (alphaLam ℚ S6)).flip :=
  ⟨nekovarFibreSetting_S6, isLatticeTop_vp' Pt0, isLatticeTop_vp' Pt0,
    isLatticeTop_tate1P ℚ S6 Pt0,
    (haveI := hasTwoPowerRoots_of_fullTwoTorsion ℚ S6 curveE1; isTateTwistFibre_tate1P ℚ S6 Pt0),
    betaT_bijective curveE1 Pt0 _, betaT_flip_bijective curveE1 Pt0 _⟩

/-- **The consumer duality for `E_1` at `(t)`**: from the PRINT, for any trace inducing
`H³_c ≅ k((t))`, `C_rel(V_(t)(α)) ≃ Hom(C_str(V_(t)(α⁻¹)), k((t)))[−3]` on lane RC28's fibre Selmer
data. Kind: PROVED from the PRINT, under the GLUE `HasFullTwoTorsion ℚ S6 curveE1`. -/
theorem fibreSelmerDuality_E1 (h : NekovarFibreGlobalDuality ℚ)
    (tr : (coneCx (fibrePairRelStr curveE1 Pt0 (alphaLam ℚ S6)).resE).X 3 →ₗ[ResAt Pt0] ResAt Pt0)
    (htr : ∀ z, tr ((coneCx (fibrePairRelStr curveE1 Pt0 (alphaLam ℚ S6)).resE).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (fibrePairRelStr curveE1 Pt0 (alphaLam ℚ S6)) tr htr)) :=
  fibreSelmerDuality_relaxed_strict_VP curveE1 Pt0 _ h nekovarFibreSetting_S6 tr htr htr3

/-- The pairing data is between lane RC28's relaxed fibre data of `V_(t)(α)` and its strict
fibre data of `V_(t)(α⁻¹)`. -/
example : SelPairData (fibreRelaxed (S := S6) curveE1 Pt0 (alphaLam ℚ S6))
    (fibreStrict (S := S6) curveE1 Pt0 (alphaLam ℚ S6)⁻¹) :=
  fibrePairRelStr curveE1 Pt0 (alphaLam ℚ S6)

end GLUE

/-! ### The transported form: an actual complex conjugation for `ℚ` -/

/-- **An actual complex conjugation for `ℚ`** (tex 2778: "Fix an actual complex conjugation
`τ ∈ G_ℚ`, so that `τ² = 1`"): complex conjugation restricted to `ℚ̄`
(`exists_complexConj_algClosure`), with `κ = id`; every `S` is `κ`-stable. Kind: definition. -/
def actualConjQ (S : Set (HeightOneSpectrum (𝓞 ℚ))) : ActualConj ℚ S :=
  let h := exists_complexConj_algClosure ℚ
  { ι := h.choose
    τ := h.choose_spec.choose
    κ := RingEquiv.refl ℚ
    hτ := fun x => by
      rw [RingEquiv.refl_apply]
      exact map_ratCast _ x
    hι := h.choose_spec.choose_spec.1
    hinv := h.choose_spec.choose_spec.2
    hS := fun v w hw => by
      have hvw : w = v := by
        apply HeightOneSpectrum.ext
        rw [hw]
        exact Ideal.map_id v.asIdeal
      rw [hvw] }

/-- **`E_1^κ = E_1`** for `κ = id`. Kind: PROVED. -/
theorem curveE1_map_conj (S : Set (HeightOneSpectrum (𝓞 ℚ))) :
    curveE1.map ((actualConjQ S).κ : ℚ →+* ℚ) = curveE1 :=
  WeierstrassCurve.map_id curveE1

/-- RC28's `α = χ_1 Ψ_0` is the trivial character (`√1 = 1` is fixed, `Ψ_0 = (1 + t)^0`). Kind:
PROVED. -/
theorem alphaLam_apply (S : Set (HeightOneSpectrum (𝓞 ℚ))) (σ : GKS ℚ S) :
    alphaLam ℚ S σ = 1 := by
  apply Units.ext
  rw [coe_lambdaChar, Units.val_one]
  have hq : quadChar (1 : ZInQ.Manuscript.RC.CoefModules.KS ℚ S)
      ZInQ.Manuscript.RC.LambdaCoef.one_sq_eq one_ne_zero σ = 1 :=
    ite_eq_left_of_eq_true _ _ (eq_true (map_one (ZInQ.Manuscript.RC.CoefModules.galS ℚ S σ)))
  rw [hq, MonoidHom.one_apply, toAdd_one, onePlusTPow_zero]
  simp

/-- **`α ∘ c = α⁻¹` for RC28's `α`** (tex 2786–2795, `α^τ = α^{-1}`). Kind: PROVED. -/
theorem alphaLam_conj (S : Set (HeightOneSpectrum (𝓞 ℚ))) (σ : GKS ℚ S) :
    alphaLam ℚ S ((actualConjQ S).conj σ) = (alphaLam ℚ S σ)⁻¹ := by
  rw [alphaLam_apply, alphaLam_apply, inv_one]

/-- **The transported pairing for `E_1` at `(t)`** (tex 2798–2805: `(v, w) ↦ e_2(v, ρ_T(τ) w)`):
equivariant, perfect and continuous; with it the transported duality
`fibreSelmerDuality_conj` applies to `E_1`. Kind: PROVED under the GLUE
`HasFullTwoTorsion ℚ S6 curveE1`. -/
theorem betaConj_E1 [HasFullTwoTorsion ℚ S6 curveE1] :
    (∀ (σ : GKS ℚ S6) v w,
      betaConj curveE1 Pt0 (alphaLam ℚ S6) (actualConjQ S6) (curveE1_map_conj S6) (σ • v)
        (σ • w) =
      σ • betaConj curveE1 Pt0 (alphaLam ℚ S6) (actualConjQ S6) (curveE1_map_conj S6) v w) ∧
    Function.Bijective
      (betaConj curveE1 Pt0 (alphaLam ℚ S6) (actualConjQ S6) (curveE1_map_conj S6)) ∧
    Function.Bijective
      (betaConj curveE1 Pt0 (alphaLam ℚ S6) (actualConjQ S6) (curveE1_map_conj S6)).flip ∧
    Continuous fun x : VP ℚ S6 curveE1 Pt0 (alphaLam ℚ S6) ×
        ZInQ.Manuscript.RC.CoefModules.PullMod (actualConjQ S6).conj
          (VP ℚ S6 curveE1 Pt0 (alphaLam ℚ S6)) =>
      betaConj curveE1 Pt0 (alphaLam ℚ S6) (actualConjQ S6) (curveE1_map_conj S6) x.1 x.2 :=
  ⟨betaConj_smul curveE1 Pt0 _ _ _ (alphaLam_conj S6), betaConj_bijective curveE1 Pt0 _ _ _,
    betaConj_flip_bijective curveE1 Pt0 _ _ _, continuous_betaConj curveE1 Pt0 _ _ _⟩

end ZInQ.Manuscript.RC.FibreDuality
