import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate17Actual
import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitFamilyPin

/-!
# Lane RC32's presentation with a support varying with the stage

Manuscript `diophantine_zq.tex`, Section `sec:arithmetic` (tex 2720–2741: `K = ℚ(√k)`,
`A_i = (ℤ/2^i)[t]/t^i`, `M_i = (T₂E ⊗ A_i)(χ_h Ψ_i)`; tex 2729–2737: the moving character
`Ψ_i = (1 + t)^{ψ_i}`, ramified at the moving prime `r_i`, the same `Ψ_i` for all characters of
the family), the support comparisons (tex 3455–3498) and Lemma `ex:arith-common-coordinate`
(tex 4142–4194) at the stages of the inner limit (tex 4385–4451).

The presentation `ActualPresentation` (`CommonCoordinate17Actual.lean`) has one support `S₀` for
all stages. The text's moving character `Ψ_i` is ramified at a prime `r_i` that varies with the
stage (lane RC0's `FamilyMovingCharacter`: `r` injective, `Sr i` containing the places above
`r i`), so the support of the coefficients at the stage `i` is `S₀ ∪ Sr(i)`, which varies with the
stage. This file restates the presentation with a support `S₀ s` at each stage `s` and the
family's moving character:

* **`StagedPresentation C D Fam x Ψ`**: as `ActualPresentation`, with the support `S₀ s`, the
  conjugation, the square root of `h_x` and the chain's splitting data at every stage, and the
  moving character of the family `Ψ` (lane RC0's `FamilyMovingCharacter`, one per family): at the
  stage `s` the moving exponent is `ξ_s = Ψ.ψ s` inflated from `G_{K,S₀ s}` to `G_{K, Sr s}`
  (`hSr : Sr s ⊆ S₀ s`), and the moving character is `(1 + t)^{ξ_s}` (`expU`); the Kummer places
  are the places above `2N` (`hPk`);
* `StagedPresentation.ξ`, `.alphaF s s'`: the character `χ_h (1 + t)^{ξ_s}` over `G_{K,S₀ s}` at
  the coefficient precision `s'`; only `s' = s` enters the chain at the stage `s`; the moving part
  is `(1 + t)^{(·)}` at `s' = s` (`hψf`) and trivial at `s' ≠ s` (`hψoff`), so the families of the
  generic chain constructions are pinned at every precision;
* PROVED: the open kernels (`hπ`), the triviality above `2N` at every precision (`hΨ`, from the
  family's `twoN`), the prescribed value and the anticyclotomy at the stage (`moving`,
  `movingConj`, from the fields `xiFrob`, `xiConj` on the family's exponent);
* the objects at the stage `s` over the support `S₀ s`: `famM P s`, `famConds P s`, `famX P s`,
  `famEU P s` (the families over the precisions `s'` of lane E2's `MinS`, `stageCondsK`, `urRep`
  and the genuine splits, as in `CommonCoordinate17Actual.lean`), and the support complexes
  `stagedCx P s`, switches `stagedSw P s` of the stage;
* the Frobenius discharge at the stage: `staged_stageFrobInput`, `stagedFrob`, **`stagedSteps`**,
  **`stagedSteps_stageFrobAt`** (as `actualSteps`).

Kinds: definitions, PROVED; the fields of `StagedPresentation` carry their kinds.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain TensorProduct
open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion MilneADT_I_2_8)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef unitPowHom)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Local (IwasawaGenerators GenuineCochainsInjective)
open ZInQ.Contrib.CloudB3E2.NormCochain (alphaStage alphaShap stageCondsK stageIsoA
  PsiTrivialAt2N univChar)
open scoped PowerSeries.WithPiTopology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-! ### The presentation -/

section Presentation

variable {ℓ : ℕ}

/-- **The moving character `(1 + t)^{(·)}` at the stage `s`** (tex 2781–2783): the
homomorphism `ℤ/2^{2s} → A_s^×`, `n ↦ (1 + t)^n`. Kind: definition. -/
abbrev expU (s : ℕ) : Multiplicative (ZMod (2 ^ (2 * s))) →* (Acoef s)ˣ :=
  unitPowHom (2 * s) (ZInQ.Manuscript.RC.CoefModules.onePlusT s) (onePlusT_pow s)

/-- **The actual presentation at an address with a support varying with the stage** (tex
2720–2741, 2778–2796, 3455–3498, 4142–4194, 4385–4451), for the moving character `Ψ` of the family
(lane RC0's `FamilyMovingCharacter`, one per family; tex 2737). Fields and kinds:

* `r`, `hr`, `hgen`, `hprime`, `split` (definition; tex 2678–2680, 2720–2722): `K = ℚ(√k)`, the
  graph primes odd, prime to `k` and split;
* `S₀`, `hSr` (definition; tex 2729–2741, 3455–3463): the support of the coefficients at each
  stage, containing the family's moving support `Sr s` at the stage `s`;
* `full` (GLUE: Néron–Ogg–Shafarevich, Silverman AEC VII.7.1; tex 2836–2838): `E[2^∞]` rational
  over `K_{S₀ s}`;
* `Cc`, `sh`, `hs`, `hs0` (definition; tex 2726, 2778): a complex conjugation of `K_{S₀ s}` and
  `√h_x ∈ K_{S₀ s}` at each stage;
* `ψf`, `hψf`, `hψoff` (definition): the moving part of the character at the precision `s'`
  over `G_{K,S₀ s}`: `(1 + t)^{(·)}` at `s' = s`, trivial at `s' ≠ s` (the precisions `s' ≠ s`
  enter no statement about the stage `s`);
* `Pk`, `hPk` (definition; tex 2743–2760): the places of the old Kummer conditions are the
  places above `2N`;
* `ι`, `pl`, `hw`, `pidx`, `ps`, `hnd`, `hps`, `hnew`, `places` (definition; tex 4142–4146): the
  indices and places of the chain (outside every `S₀ s`), the order of the unused primes, the two
  places of the `i`-th step above the `i`-th unused prime;
* `xiFrob` (ELLIOT (data property of the text's construction, Proposition
  `ex:arith-moving-character`, tex 2731–2736, 2781–2788); it follows from the family's
  `orient_one` when the first place of each index is the family's orientation): the family's
  exponent has value `1` at the Frobenius of the first place of each index;
* `xiConj` (ELLIOT (data property of the text's construction, Proposition
  `ex:arith-moving-character`, tex 2731–2736, 2781–2788)): the family's exponent is inverted by
  the conjugation.

Kind: definition (data). -/
structure StagedPresentation (C : TateCoef (Ecurve ℓ)) (D : RCData ℓ) (Fam : Family)
    (x : Addr Fam.b) (Ψ : FamilyMovingCharacter C.K ℓ Fam.Q) : Type 1 where
  /-- `√k ∈ K` (definition; tex 2720) -/
  r : C.K
  /-- `r² = k` (definition; tex 2720) -/
  hr : r ^ 2 = ((D.kfin : ℤ) : C.K)
  /-- `K = ℚ(r)` (definition; tex 2720) -/
  hgen : Algebra.adjoin ℚ {r} = ⊤
  /-- the graph primes are odd primes (definition; tex 2678–2680, 4143) -/
  hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2
  /-- the graph primes are prime to `k` and split in `K` (definition; tex 2720–2722) -/
  split : ∀ q ∈ Fam.Q, ¬ (q : ℤ) ∣ D.kfin ∧ IsSquare ((D.kfin : ℤ) : ZMod q)
  /-- the support of the coefficients at each stage (definition; tex 2729–2741, 3455–3463) -/
  S₀ : ℕ → Set (HeightOneSpectrum (𝓞 C.K))
  /-- it contains the family's moving support at the stage (definition; tex 2729–2731) -/
  hSr : ∀ s, Ψ.Sr s ⊆ S₀ s
  /-- `E[2^∞]` is rational over `K_{S₀ s}` (GLUE: Néron–Ogg–Shafarevich, Silverman AEC VII.7.1;
  tex 2836–2838) -/
  full : ∀ s, HasFullTwoTorsion C.K (S₀ s) ((Ecurve ℓ).baseChange C.K)
  /-- an actual complex conjugation at each stage (definition; tex 2778) -/
  Cc : ∀ s, ActualConj C.K (S₀ s)
  /-- `√h_x ∈ K_{S₀ s}` (definition; tex 2726) -/
  sh : ∀ s, KS C.K (S₀ s)
  /-- `sh² = h_x` (definition; tex 2726) -/
  hs : ∀ s, sh s ^ 2 = algebraMap C.K (KS C.K (S₀ s)) ((Fam.h x : ℤ) : C.K)
  /-- `sh ≠ 0` (definition; tex 2726) -/
  hs0 : ∀ s, sh s ≠ 0
  /-- the moving part at the precision `s'` over `G_{K,S₀ s}` (definition; tex 2781–2783) -/
  ψf : ∀ s s', Multiplicative (ZMod (2 ^ (2 * s))) →* (Acoef s')ˣ
  /-- at the precision of the stage it is `(1 + t)^{(·)}` (definition; tex 2781–2783) -/
  hψf : ∀ s, ψf s s = expU s
  /-- at the other precisions it is trivial (definition: auxiliary) -/
  hψoff : ∀ s s', s' ≠ s → ψf s s' = 1
  /-- the places of the old Kummer conditions (definition; tex 2743–2760) -/
  Pk : Set (HeightOneSpectrum (𝓞 C.K))
  /-- they are the places above `2N` (definition; tex 2743–2760) -/
  hPk : Pk = placesTwoN C.K ℓ
  /-- the indices of the chain (definition; tex 4142–4146) -/
  ι : Type
  /-- decidable equality of the indices (definition) -/
  [decι : DecidableEq ι]
  /-- the two places of each index (definition; tex 4142–4146) -/
  pl : ι × Bool → HeightOneSpectrum (𝓞 C.K)
  /-- they are outside the support of the coefficients at every stage (definition;
  tex 3470–3498) -/
  hw : ∀ s j, pl j ∉ S₀ s
  /-- the index relaxed at each step (definition; tex 4142–4146) -/
  pidx : ℕ → ι
  /-- the order of the unused primes (definition; tex 4142–4146) -/
  ps : List ℕ
  /-- each unused prime is relaxed once (definition; tex 4142–4146) -/
  hnd : ps.Nodup
  /-- the chain relaxes exactly the unused primes (definition; tex 4142–4146) -/
  hps : ps.toFinset = unusedAt Fam x
  /-- each relaxed index is new (definition; tex 4142–4146) -/
  hnew : ∀ i < ps.length, pidx i ∉ chainT pidx i
  /-- the two places of the `i`-th step lie above the `i`-th unused prime (definition;
  tex 4142–4146) -/
  places : ∀ s, ∀ i < ps.length,
    SplitPair (Cc s).κ (ps.getD i 1) (pl (pidx i, false)) (pl (pidx i, true))
  /-- the family's exponent has value `1` at the Frobenius of the first place of each index
  (ELLIOT (data property of the text's construction, Proposition `ex:arith-moving-character`,
  tex 2731–2736, 2781–2788)) -/
  xiFrob : ∀ s (p : ι), (Ψ.ψ s).comp (inflMap C.K (hSr s)).toMonoidHom
    (urFrobElt C.K (⟨pl (p, false), Set.mem_union_right (S₀ s) (Set.mem_range_self (p, false)),
      hw s (p, false)⟩ : NewPlaces C.K (S₀ s) (S₀ s ∪ Set.range pl))) = Multiplicative.ofAdd 1
  /-- the family's exponent is inverted by the conjugation (ELLIOT (data property of the text's
  construction, Proposition `ex:arith-moving-character`, tex 2731–2736, 2781–2788)) -/
  xiConj : ∀ s σ, (Ψ.ψ s).comp (inflMap C.K (hSr s)).toMonoidHom ((Cc s).conj σ) =
    ((Ψ.ψ s).comp (inflMap C.K (hSr s)).toMonoidHom σ)⁻¹

attribute [instance] StagedPresentation.decι

namespace StagedPresentation

variable {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b}
  {Ψ : FamilyMovingCharacter C.K ℓ Fam.Q} (P : StagedPresentation C D Fam x Ψ)

/-- `E[2^∞] ⊆ E(K_{S₀ s})` as an instance (GLUE `full`; tex 2836–2838). Kind: definition. -/
instance fullInst (s : ℕ) : HasFullTwoTorsion C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) :=
  P.full s

/-- **The Selmer support at the stage `s`**: `S₀ s ∪ {places of the chain}` (tex 3455–3463,
4142–4146). Kind: definition. -/
abbrev S (s : ℕ) : Set (HeightOneSpectrum (𝓞 C.K)) := P.S₀ s ∪ Set.range P.pl

/-- `S₀ s ⊆ S s` (tex 3455–3463). Kind: PROVED. -/
theorem hS (s : ℕ) : P.S₀ s ⊆ P.S s := Set.subset_union_left

/-- **The places of the chain as places of `S s`** (tex 4142–4146). Kind: definition. -/
abbrev place (s : ℕ) (j : P.ι × Bool) : Places C.K (P.S s) :=
  ⟨P.pl j, Set.mem_union_right (P.S₀ s) (Set.mem_range_self j)⟩

/-- The places of the chain are outside `S₀ s` (tex 3470–3498). Kind: PROVED. -/
theorem hwp (s : ℕ) (j : P.ι × Bool) : (P.place s j).1 ∉ P.S₀ s := P.hw s j

/-- **The family's moving exponent at the stage `s`** over `G_{K,S₀ s}` (tex 2729–2737): lane
RC0's `Ψ.ψ s` inflated along `Sr s ⊆ S₀ s`. Kind: definition. -/
abbrev ξ (s : ℕ) : GKS C.K (P.S₀ s) →* Multiplicative (ZMod (2 ^ (2 * s))) :=
  (Ψ.ψ s).comp (inflMap C.K (P.hSr s)).toMonoidHom

/-- **The character `χ_{h_x} (1 + t)^{ξ_s}` at the precision `s'`** over `G_{K,S₀ s}` (lane E2's
`alphaStage`; tex 2726, 2781–2791). Kind: definition. -/
abbrev alphaF (s s' : ℕ) : GKS C.K (P.S₀ s) →* (Acoef s')ˣ :=
  alphaStage s' (P.sh s) (P.hs s) (P.hs0 s) (P.ξ s) (P.ψf s s')

/-- **The family's exponent has open kernel over `G_{K,S₀ s}`** (tex 2729): the family's `ψ_open`
and the continuity of the inflation. Kind: PROVED. -/
theorem hπ (s : ℕ) : IsOpen ((P.ξ s).ker : Set (GKS C.K (P.S₀ s))) := by
  exact (Ψ.ψ_open s).preimage (inflMap C.K (P.hSr s)).continuous

/-- **The moving part is trivial above `2N` at every precision** (tex 2729, 3430–3432): from the
family's `twoN` at the precision of the stage and by `hψoff` at the others. Kind: PROVED. -/
theorem hΨ (s s' : ℕ) : PsiTrivialAt2N s' (P.ξ s) (P.ψf s s') P.Pk := by
  intro v hv σ
  by_cases h : s' = s
  · subst h
    rw [P.hψf s']
    have hv' : v ∈ placesTwoN C.K ℓ := P.hPk ▸ hv
    change expU s' ((Ψ.ψ s') (inflMap C.K (P.hSr s') (locMap C.K (P.S₀ s') v σ))) = 1
    rw [locMap_compat, Ψ.twoN s' v hv' σ, map_one]
  · rw [P.hψoff s s' h, MonoidHom.one_apply]

/-- **The prescribed value at the stage** (tex 2731–2736, 2783): `MovingValueAt` for the
family's exponent at a positive stage, from `xiFrob`. Kind: PROVED. -/
theorem moving {s : ℕ} (hs1 : 0 < s) (p : P.ι) :
    MovingValueAt s (P.ξ s) (P.ψf s s)
      (⟨P.pl (p, false), Set.mem_union_right (P.S₀ s) (Set.mem_range_self (p, false)),
        P.hw s (p, false)⟩ : NewPlaces C.K (P.S₀ s) (P.S s)) := by
  rw [P.hψf s]
  exact movingValueAt_of_xi hs1 (P.ξ s) _ (P.xiFrob s p)

/-- **The anticyclotomy at the stage** (tex 2786–2788): from `xiConj`. Kind: PROVED. -/
theorem movingConj (s : ℕ) : MovingAnticyclotomic (P.Cc s) (P.ξ s) (P.ψf s s) := by
  rw [P.hψf s]
  exact movingAnticyclotomic_of_xi (P.Cc s) (P.ξ s) (P.xiConj s)

end StagedPresentation

end Presentation

/-! ### The objects of the presentation at a stage -/

section Objects

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} {Ψ : FamilyMovingCharacter C.K ℓ Fam.Q}
  (P : StagedPresentation C D Fam x Ψ)

namespace StagedPresentation

/-- **The character has open kernel at every precision** (tex 2726–2729). Kind: PROVED. -/
instance alphaF_isOpenKer (s s' : ℕ) : IsOpenKer (P.alphaF s s') :=
  @isOpenKer_charMul _ _ _ _ _ _ _ _
    (isOpenKer_map (quadChar (P.sh s) (P.hs s) (P.hs0 s)) (intUnitsTo _))
    (isOpenKer_comp_of_isOpen (P.ξ s) (P.hπ s) (P.ψf s s'))

/-- **Lane E2's Shapiro-level character has open kernel** (tex 2726–2729). Kind: PROVED. -/
instance alphaShap_isOpenKer (s : ℕ) :
    IsOpenKer (alphaShap (P.sh s) (P.hs s) (P.hs0 s) (P.ξ s)) :=
  @isOpenKer_charMul _ _ _ _ _ _ _ _
    (isOpenKer_map (quadChar (P.sh s) (P.hs s) (P.hs0 s)) (intUnitsTo _))
    (isOpenKer_comp_of_isOpen (P.ξ s) (P.hπ s) (univChar _))

/-- **`M = (E[2^{s'}] ⊗ A_{s'})(α)` over the stage ring** through `stageEquiv s'` (tex 2724–2727,
4385–4451). Kind: definition. -/
instance mcoefModule (s s' : ℕ) :
    Module (StageRing s') (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s')) :=
  stageCompModule s' (P.alphaF s s') _

/-- The Galois action commutes with the stage ring (tex 2724–2727). Kind: PROVED. -/
instance mcoefSMulComm (s s' : ℕ) : SMulCommClass (GKS C.K (P.S₀ s)) (StageRing s')
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s')) :=
  stageComp_smulCommClass s' (P.alphaF s s') _

/-- **The rank-two stage basis** (tex 2724–2727, 2836–2838). Kind: definition. -/
def mcoefBasis (s s' : ℕ) : Module.Basis (Fin 2) (StageRing s')
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s')) :=
  Module.Basis.ofEquivFun ((stageCoefEquiv s' _ (P.alphaF s s')).trans
    (stageBasis (tateBasis (K := C.K) (S := P.S₀ s) (W := (Ecurve ℓ).baseChange C.K)) s'))

/-- The module is free of rank two over the stage ring (tex 2724–2727). Kind: PROVED. -/
instance mcoefFree (s s' : ℕ) : Module.Free (StageRing s')
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s')) :=
  Module.Free.of_basis (P.mcoefBasis s s')

/-- The module is discrete for the stage ring (tex 2724–2727). Kind: PROVED. -/
instance mcoefContinuousConstSMul (s s' : ℕ) : ContinuousConstSMul (StageRing s')
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s')) :=
  ⟨fun _ => continuous_of_discreteTopology⟩

end StagedPresentation

/-- **The coefficient modules of the stage `s` at the precisions `s'`** (tex 2724–2727,
3455–3463): lane E2's `MinS` at `i = s'` over `G_{K,S₀ s}` inflated to `G_{K,S s}`; at `s' = s`
it is the actual `M_s = (T₂E ⊗ A_s)(χ_{h_x} Ψ_s)`. Kind: definition. -/
abbrev famM (s : ℕ) : ℕ → Type := fun s' =>
  MinS (P.hS s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s')

/-- The coefficient modules are free over the stage rings (tex 2724–2727). Kind: PROVED. -/
instance famM_free (s s' : ℕ) : Module.Free (StageRing s') (famM P s s') :=
  inferInstanceAs (Module.Free (StageRing s')
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s')))

/-- The coefficient modules are finite (tex 2724–2727). Kind: PROVED. -/
instance famM_finite (s s' : ℕ) : Finite (famM P s s') :=
  inferInstanceAs (Finite (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s')))

/-- **The unramified representations at the places of the chain** (tex 3470–3498): lane E2's
`urRep` at `place s j`. Kind: definition. -/
abbrev famX (s s' : ℕ) : (j : P.ι × Bool) → TopRep.{0} (StageRing s') (GUr C.K (P.place s j).1) :=
  urChainRep (P.place s) (P.hwp s)
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s'))

/-- The unramified representations are discrete modules (tex 3470–3498). Kind: PROVED. -/
instance famX_continuousSMul (s s' : ℕ) (j : P.ι × Bool) :
    ContinuousSMul (GUr C.K (P.place s j).1) (famX P s s' j).V :=
  urRep_continuousSMul (StageRing s')
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s'))
    (newPlace (P.place s j) (P.hwp s j))

/-- The unramified representations are free over the stage ring (tex 3470–3498).
Kind: PROVED. -/
instance famX_free (s s' : ℕ) (j : P.ι × Bool) : Module.Free (StageRing s') (famX P s s' j).V :=
  inferInstanceAs (Module.Free (StageRing s')
    (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s')))

/-- The splits of the genuine inflations exist (tex 3470–3487; `exists_genuineSplitsS`).
Kind: PROVED. -/
theorem famEU_exists (s s' : ℕ) :
    ∃ EU : ∀ j, SplitInclusion
        (genuineUq C.K (P.S s) (StageRing s') (P.place s j) (famX P s s' j))
        (genuineLq C.K (P.S s) (StageRing s') (famM P s s') (P.place s j)),
      ∀ j, (EU j).i = genuineιq C.K (P.S s) (StageRing s') (famM P s s') (P.place s j)
        (famX P s s' j)
        (urId (P.hS s) (StageRing s')
          (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s'))
          (newPlace (P.place s j) (P.hwp s j)))
        (urId_compat (P.hS s) (StageRing s')
          (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s')) (P.place s j)
          (P.hwp s j)) :=
  exists_genuineSplitsS C.K (P.S s) (StageRing s') (famM P s s') (P.place s) (famX P s s') _ _
    (fun j => (urId_bijective (StageRing s') _ (P.hS s) (newPlace (P.place s j) (P.hwp s j))).1)

/-- **The splits of the genuine inflations** along `urId` (tex 3470–3487). Kind: definition. -/
def famEU (s s' : ℕ) (j : P.ι × Bool) :
    SplitInclusion (genuineUq C.K (P.S s) (StageRing s') (P.place s j) (famX P s s' j))
      (genuineLq C.K (P.S s) (StageRing s') (famM P s s') (P.place s j)) :=
  Classical.choose (famEU_exists P s s') j

/-- **The inclusions of the splits are the genuine inflations** along `urId` (tex 3470–3487).
Kind: PROVED. -/
theorem famEU_i (s s' : ℕ) (j : P.ι × Bool) :
    (famEU P s s' j).i = ofCCHom (urToLocal_galois C.K (P.S s) (P.place s j) (famX P s s' j)
      (urId (P.hS s) (StageRing s')
        (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s'))
        (newPlace (P.place s j) (P.hwp s j)))
      (urId_compat (P.hS s) (StageRing s')
        (Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s')) (P.place s j)
        (P.hwp s j))) :=
  Classical.choose_spec (famEU_exists P s s') j

/-- **The old local conditions of the stage `s` at the precisions `s'`** (tex 2743–2760): at a
precision `s' + 1` lane E2's `stageCondsK` (Kummer at `Pk`, full at `S₀ s − Pk`), at the zero
ring the full conditions. Kind: definition. -/
def famConds (s : ℕ) : (s' : ℕ) → LocalConditions (StageRing s') (GKS C.K (P.S s))
    (fun v : Places C.K (P.S₀ s) => Gloc C.K v.1) (fun v => locMap C.K (P.S s) v.1)
    (famM P s s')
  | 0 => relaxedConditions (StageRing 0) (GKS C.K (P.S s))
      (fun v : Places C.K (P.S₀ s) => Gloc C.K v.1) (fun v => locMap C.K (P.S s) v.1)
      (famM P s 0)
  | s' + 1 =>
    letI := acoefTop (s' + 1)
    haveI := acoefTop_discrete (s' + 1)
    letI := stageIsoA (s' + 1)
    stageCondsK (P.hS s) ((Ecurve ℓ).baseChange C.K) (s' + 1) (P.sh s) (P.hs s) (P.hs0 s)
      (HasFullTwoTorsion.full (s' + 1)) (P.ξ s) (P.ψf s (s' + 1)) P.Pk (P.hΨ s (s' + 1))
      (StageRing (s' + 1))

variable [∀ s, DecidableEq (Places C.K (P.S₀ s))]

/-- **The support complexes of the stage `s`** (tex 3470–3498, 4142–4194): lane RC32's `genCx` on
the objects of the stage, over `G_{K, S s}`, at the precision `s`. Kind: definition. -/
abbrev stagedCx (s : ℕ) : Finset P.ι → GCx (StageRing s) :=
  genCx C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s) (famX P s) (famEU P s) s

/-- **The switches of the stage `s`** (tex 4142–4194). Kind: definition. -/
abbrev stagedSw (s : ℕ) (T : Finset P.ι) (p : P.ι) :
    SplitInclusion (stagedCx P s T) (stagedCx P s (insert p T)) :=
  genSw C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s) (famX P s) (famEU P s) s T p

end Objects

/-! ### The Frobenius discharge at a stage -/

section Discharge

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} {Ψ : FamilyMovingCharacter C.K ℓ Fam.Q}
  (P : StagedPresentation C D Fam x Ψ)

omit [(Ecurve ℓ).IsElliptic] in
/-- The prime of the `i`-th step is an unused graph prime (tex 4142–4146). Kind: PROVED. -/
theorem StagedPresentation.mem_unused {i : ℕ} (hi : i < P.ps.length) :
    P.ps.getD i 1 ∈ unusedAt Fam x := by
  rw [← P.hps, List.getD_eq_getElem P.ps 1 hi]
  exact List.mem_toFinset.mpr (List.getElem_mem hi)

omit [(Ecurve ℓ).IsElliptic] in
include P in
/-- **`FrobQFixes` at every graph prime** (`frobQFixes_of_sqrt`; tex 2720–2722).
Kind: PROVED. -/
theorem StagedPresentation.frobQFixes {q : ℕ} (hq : q ∈ Fam.Q) : FrobQFixes C q :=
  frobQFixes_of_sqrt C (P.hprime q hq).1 (P.hprime q hq).2 (P.split q hq).1 (P.split q hq).2
    P.r P.hr P.hgen

/-- **The stage Frobenius inputs at both places of the `i`-th step, at the leaf's values**, at a
positive stage (tex 4144–4145, 4171, 4176–4184). Kind: PROVED. -/
theorem staged_stageFrobInput {s : ℕ} (hs1 : 0 < s) {i : ℕ} (hi : i < P.ps.length) :
    (∃ eT : StageRing s ⊗[ℤ] Lev C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s ≃ₗ[StageRing s]
        (Fin 2 → StageRing s), StageFrobInput eT (stageRingChar s (P.alphaF s s))
          (newPlace (P.place s (P.pidx i, false)) (P.hwp s (P.pidx i, false)))
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).z i)) ∧
      ∃ eT : StageRing s ⊗[ℤ] Lev C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s ≃ₗ[StageRing s]
        (Fin 2 → StageRing s), StageFrobInput eT (stageRingChar s (P.alphaF s s))
          (newPlace (P.place s (P.pidx i, true)) (P.hwp s (P.pidx i, true)))
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).zi i) := by
  obtain ⟨hqQ, hun⟩ := mem_unusedAt.mp (P.mem_unused hi)
  exact exists_stageFrobInput_at C (P.Cc s) Fam (fun q hq => (P.hprime q hq).1) x s (P.sh s)
    (P.hs s) (P.hs0 s) rfl (P.ξ s) (P.ψf s s) (P.movingConj s) (P.hprime _ hqQ).2 hqQ hun
    (P.frobQFixes hqQ) (P.places s i hi) (P.moving hs1 (P.pidx i))

/-- **Stage bases at the two places of every step, at the leaf's values**, at a positive stage
(tex 4176–4184, 4385–4451). Kind: PROVED. -/
theorem staged_stageBases {s : ℕ} (hs1 : 0 < s) :
    ∃ e₁ e₂ : ℕ → StageRing s ⊗[ℤ] Lev C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s ≃ₗ[
        StageRing s] (Fin 2 → StageRing s), ∀ i < P.ps.length,
      StageFrobInput (e₁ i) (stageRingChar s (P.alphaF s s))
          (newPlace (P.place s (P.pidx i, false)) (P.hwp s (P.pidx i, false)))
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).z i) ∧
        StageFrobInput (e₂ i) (stageRingChar s (P.alphaF s s))
          (newPlace (P.place s (P.pidx i, true)) (P.hwp s (P.pidx i, true)))
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).zi i) := by
  have hex : ∀ i, ∃ e₁ e₂ : StageRing s ⊗[ℤ] Lev C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s
      ≃ₗ[StageRing s] (Fin 2 → StageRing s), i < P.ps.length →
      StageFrobInput e₁ (stageRingChar s (P.alphaF s s))
          (newPlace (P.place s (P.pidx i, false)) (P.hwp s (P.pidx i, false)))
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).z i) ∧
        StageFrobInput e₂ (stageRingChar s (P.alphaF s s))
          (newPlace (P.place s (P.pidx i, true)) (P.hwp s (P.pidx i, true)))
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).Fr i)
          (((leafFrobΛ C Fam x P.ps).map (stageMk s)).zi i) := by
    intro i
    by_cases hi : i < P.ps.length
    · obtain ⟨⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩ := staged_stageFrobInput P hs1 hi
      exact ⟨e₁, e₂, fun _ => ⟨h₁, h₂⟩⟩
    · exact ⟨stageBasis (tateBasisAt C (P.S₀ s)) s, stageBasis (tateBasisAt C (P.S₀ s)) s,
        fun h' => absurd h' hi⟩
  choose e₁ e₂ he using hex
  exact ⟨e₁, e₂, fun i hi => he i hi⟩

/-- **The Frobenius fields of the genuine stage chain at a positive stage** (tex 3470–3498,
4176–4184): `f j = urId`, the bases of `staged_stageBases`, with `Fr`, `z`, `zi` those of
`leafFrobΛ` at the stage (`stageChainFrobE2`). Kind: definition. -/
def stagedFrob {s : ℕ} (hs1 : 0 < s) : StageChainFrob (StageRing s) (famM P s s) (P.place s)
    (famX P s s) P.pidx P.ps.length (fun i => ((leafFrobΛ C Fam x P.ps).map (stageMk s)).Fr i)
    (fun i => ((leafFrobΛ C Fam x P.ps).map (stageMk s)).z i)
    (fun i => ((leafFrobΛ C Fam x P.ps).map (stageMk s)).zi i) :=
  stageChainFrobE2 (P.hS s) (P.place s) (P.hwp s) ((Ecurve ℓ).baseChange C.K) s (P.alphaF s s)
    P.pidx P.ps.length _ _ _ (Classical.choose (staged_stageBases P hs1))
    (Classical.choose (Classical.choose_spec (staged_stageBases P hs1)))
    (fun i hi => (Classical.choose_spec (Classical.choose_spec (staged_stageBases P hs1)) i hi).1)
    (fun i hi => (Classical.choose_spec (Classical.choose_spec (staged_stageBases P hs1)) i hi).2)

variable [∀ s, DecidableEq (Places C.K (P.S₀ s))]

/-- **The genuine data of one chain at a positive stage on the staged presentation**
(tex 4142–4194, 4176–4184, 4385–4451): `GenuineStageSteps.ofFrob` of `stagedFrob`, with the step
cardinalities `q i = ps[i]`, `hE` by `famEU_i`, `hexp`, `hqodd`, `hqc` PROVED from the
presentation; the model of `C_∅` and the relaxed classes and functionals given.
Kind: definition. -/
def stagedSteps {s : ℕ} (hs1 : 0 < s) (m0 m1 m2 : ℕ)
    (st0 : CMState m0 m1 m2 (stagedCx P s ∅) 0)
    (zR : ∀ i, (stagedCx P s (insert (P.pidx i) (chainT P.pidx i))).X 1)
    (hzR : ∀ i, (stagedCx P s (insert (P.pidx i) (chainT P.pidx i))).d 1 2 rfl (zR i) = 0)
    (lamR : ∀ i, (stagedCx P s (insert (P.pidx i) (chainT P.pidx i))).X 2 →ₗ[StageRing s]
      StageRing s)
    (hlamR : ∀ i, lamR i ∘ₗ (stagedCx P s (insert (P.pidx i) (chainT P.pidx i))).d 1 2 rfl = 0) :
    GenuineStageSteps C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s) (famX P s)
      (famEU P s) s m0 m1 m2 P.pidx P.ps.length :=
  GenuineStageSteps.ofFrob (stagedFrob P hs1) P.hnew st0 (fun i => P.ps.getD i 1) zR hzR lamR
    hlamR (fun j => famEU_i P s s j)
    (exists_two_pow_smul_inflMod (P.hS s) ((Ecurve ℓ).baseChange C.K) s (P.alphaF s s))
    (fun i hi => by
      obtain ⟨hqQ, -⟩ := mem_unusedAt.mp (P.mem_unused hi)
      exact (P.hprime _ hqQ).1.odd_of_ne_two (P.hprime _ hqQ).2)
    (fun i hi c => by
      cases c
      · exact (P.places s i hi).card.symm
      · exact (P.places s i hi).card'.symm)

/-- **The leaf's Frobenius data on the staged presentation** (tex 4144–4145, 4176–4184,
4385–4451): `StageFrobAt` for the chain of `stagedSteps` with the traces of `leafFrobΛ` at the
stage. Kind: PROVED. -/
theorem stagedSteps_stageFrobAt (h28 : MilneADT_I_2_8) (hI : IwasawaGenerators)
    (hInj : GenuineCochainsInjective) {s : ℕ} (hs1 : 0 < s)
    (m0 m1 m2 : ℕ) (st0 : CMState m0 m1 m2 (stagedCx P s ∅) 0)
    (zR : ∀ i, (stagedCx P s (insert (P.pidx i) (chainT P.pidx i))).X 1)
    (hzR : ∀ i, (stagedCx P s (insert (P.pidx i) (chainT P.pidx i))).d 1 2 rfl (zR i) = 0)
    (lamR : ∀ i, (stagedCx P s (insert (P.pidx i) (chainT P.pidx i))).X 2 →ₗ[StageRing s]
      StageRing s)
    (hlamR : ∀ i, lamR i ∘ₗ (stagedCx P s (insert (P.pidx i) (chainT P.pidx i))).d 1 2 rfl = 0) :
    StageFrobAt (Cx := stagedCx P) (Ex := stagedSw P) (leafFrobΛ C Fam x P.ps) s
      ((stagedSteps P hs1 m0 m1 m2 st0 zR hzR lamR hlamR).toChainM h28 hI hInj)
      (fun i => ((leafFrobΛ C Fam x P.ps).map (stageMk s)).a i) := by
  intro i _
  exact ⟨rfl, map_natCast (stageMk s) (P.ps.getD i 1), rfl, rfl, rfl⟩

end Discharge

end ZInQ.Manuscript.RC.Wiring
