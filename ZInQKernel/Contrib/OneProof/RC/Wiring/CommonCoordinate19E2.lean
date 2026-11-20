import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19Pin
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19Theta
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18E2

/-!
# Lane E2's classes of the actual Heegner points as a class provider on the staged presentation

Manuscript `diophantine_zq.tex`: the actual anchored Heegner points and their norm relations
(tex 2914–2936), the finite character of `Δ_f` (tex 2847–2855), the family's moving character
(tex 2725–2741, 3500–3702), the Kummer classes as classes of the presentation (tex 3080–3084,
3203–3215, 3471–3487) and the step identity of Lemma `ex:arith-common-coordinate`
(tex 4142–4194, 4157–4172), at a positive stage `t + 1` of lane RC32's staged presentation
`P : StagedPresentation C D Fam x G.toFamily` (`CommonCoordinate19Staged.lean`) for a genuine
family moving character `G` (lane RC0's `GenuineFamilyMovingCharacter`).

**The moving character as a map to `A_s^×`.** Lane E2's construction takes the character as
`ψ ∘ π` with `π : G_{K,S₀} → Δ` and `ψ : Δ → A_s^×` injective (the old-place inputs at the
Kummer places use `π` trivial there, from `ψ ∘ π` trivial and the injectivity). On the staged
presentation `π = ξ_s` has values in `ℤ/2^{2s}` and `ψ = (1 + t)^{(·)}`, which is not injective
for `s ≥ 1` (the order of `1 + t` in `A_s^×` is smaller than `2^{2s}`; at `s = 1`, `1 + t = 1`,
`expU_one_not_injective`). This file therefore uses `π' = Ψ_s = (1 + t)^{ξ_s} : G_{K,S₀ s} → A_s^×`
(`piU`) and `ψ' = id`: the character `χ_h ψ' π'`, the coefficient module and the old conditions
are those of the presentation by definition (`alphaStageU_eq`, by `rfl`), and `id` is injective.

* `piU`, `piU_ker_open`, `alphaStageU_eq`, `psiTrivialU` and the open-kernel instances
  (PROVED): the reparametrization;
* **`thetaOfDelta_piU`** (PROVED): the character condition `ThetaOfDelta f` for `π' = Ψ_s` at
  every `f` divisible by `thetaCond Fam x r_s` with the primes of `f` in the support (lane E2's
  genus theory and lane E1's factorization of `genuinePsi` through `Gal(H_r/K)`);
* `classSupportS` (definition) and **`E2ChainInputsS P t`** (data): the inputs that do not follow
  from `P`; the character condition and the splitting of the step primes are DERIVED
  (`E2ChainInputsS.hθ`, `E2ChainInputsS.hsplit`);
* `E2ChainInputsS.hα` (PROVED), `E2ChainInputsS.actualPt`, `E2ChainInputsS.gE2`,
  `E2ChainInputsS.g` (definitions), **`E2ChainInputsS.hG`**, `E2ChainInputsS.urContU`,
  `E2ChainInputsS.hloc` (PROVED) and **`e2ProviderS P t I : StageClassesAtS P (t + 1)`**, as in
  `CommonCoordinate18E2.lean`, with `staged_stageFrobInput` for the junction and `P.places`,
  `P.movingConj` for the places.

Kinds: definitions, data, PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion)
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.PrintsArith (Qbar HeegnerPointData CCLThm2_15Applied)
open ZInQ.Contrib.CloudB3E2.NormCochain (CSTParam FullAnchor ThetaOfDelta heegnerActual gx
  gx_step_heegner_at exists_ux stageIsoA eK alphaStage alphaShap hα_of_theta groupRingTop
  PsiTrivialAt2N univChar thetaOfDelta_of quadOfDelta_family piOfDelta_of_moving inflMap_trans)
open ZInQ.Contrib.CloudB3E2.NormCochain (fixH heegnerL alphaInfl)
open ZInQ.Contrib.CloudB3E1RingClass (mem_primeTo_of_not_mem ringClassOrder_eq_conductorOrder
  ringClassRes_eq_one_of_fix)
open scoped PowerSeries.WithPiTopology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass groupRingTop

/-! ### The moving character as a map to `A_s^×` -/

/-- **`(1 + t)^{(·)}` is not injective at `s = 1`** (PROVED): `A_1 = 𝔽₂`, so `1 + t = 1` while
`ℤ/4` has four elements. Lane E2's injectivity hypothesis on `ψ` cannot be met by
`ψ = (1 + t)^{(·)}`; this file uses `ψ' = id` instead. -/
theorem expU_one_not_injective : ¬ Function.Injective (expU 1) := by
  intro h
  have ht : (ZInQ.Manuscript.RC.CoefModules.onePlusT 1 : (Acoef 1)ˣ) = 1 := by
    apply Units.ext
    change (1 + Ideal.Quotient.mk _ Polynomial.X : Acoef 1) = 1
    rw [add_eq_left, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have h1 : expU 1 (Multiplicative.ofAdd 1) = 1 := by
    change ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom (2 * 1)
      (ZInQ.Manuscript.RC.CoefModules.onePlusT 1) (onePlusT_pow 1) (Multiplicative.ofAdd 1) = 1
    rw [ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom_apply, ht, one_pow]
  exact absurd (h (h1.trans (expU 1).map_one.symm)) (by decide)

section Staged

variable {ℓ : ℕ} {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b}
  {Ψ : FamilyMovingCharacter C.K ℓ Fam.Q} (P : StagedPresentation C D Fam x Ψ)

namespace StagedPresentation

/-- **The moving character `Ψ_s = (1 + t)^{ξ_s}` with values in `A_s^×`** (tex 2781–2783), the
`π` of lane E2's construction (with `ψ = id`). Kind: definition. -/
abbrev piU (s : ℕ) : GKS C.K (P.S₀ s) →* (Acoef s)ˣ := (P.ψf s s).comp (P.ξ s)

/-- Its kernel is open (PROVED: it contains the open kernel of `ξ_s`). -/
theorem piU_ker_open (s : ℕ) : IsOpen ((P.piU s).ker : Set (GKS C.K (P.S₀ s))) :=
  Subgroup.isOpen_mono (fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.comp_apply, hg, map_one]) (P.hπ s)

/-- **The character of lane E2's construction is the presentation's** (PROVED, by definition):
`χ_h · id ∘ Ψ_s = χ_h · (1 + t)^{ξ_s}`. -/
theorem alphaStageU_eq (s : ℕ) :
    alphaStage (Δ := (Acoef s)ˣ) s (P.sh s) (P.hs s) (P.hs0 s) (P.piU s) (MonoidHom.id _) =
      P.alphaF s s := rfl

/-- Lane E2's Shapiro-level character for `π' = Ψ_s` has open kernel (PROVED). -/
instance alphaShapU_isOpenKer (s : ℕ) :
    IsOpenKer (alphaShap (Δ := (Acoef s)ˣ) (P.sh s) (P.hs s) (P.hs0 s) (P.piU s)) :=
  @isOpenKer_charMul _ _ _ _ _ _ _ _
    (isOpenKer_map (quadChar (P.sh s) (P.hs s) (P.hs0 s)) (intUnitsTo _))
    (isOpenKer_comp_of_isOpen (P.piU s) (P.piU_ker_open s) (univChar (Acoef s)ˣ))

/-- The stage character for `(π', id)` has open kernel (PROVED: it is the presentation's). -/
instance alphaStageU_isOpenKer (s : ℕ) :
    IsOpenKer (alphaStage (Δ := (Acoef s)ˣ) s (P.sh s) (P.hs s) (P.hs0 s) (P.piU s)
      (MonoidHom.id _)) :=
  P.alphaF_isOpenKer s s

/-- **`id ∘ Ψ_s` is trivial above `2N`** (PROVED: the presentation's `hΨ` at the stage). -/
theorem psiTrivialU (s : ℕ) : PsiTrivialAt2N (Δ := (Acoef s)ˣ) s (P.piU s) (MonoidHom.id _) P.Pk :=
  P.hΨ s s

end StagedPresentation

/-- `id` is injective (the hypothesis `hψ` of lane E2's construction for `ψ' = id`; PROVED). -/
theorem id_units_injective (s : ℕ) : Function.Injective (MonoidHom.id (Acoef s)ˣ) :=
  fun _ _ h => h

end Staged

/-! ### The character condition for `Ψ_s` -/

section Theta

variable {ℓ : ℕ} {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b}

/-- **`ThetaOfDelta f` for `π' = Ψ_s` on the staged presentation** (PROVED; tex 2683–2684,
2847–2855, 3500–3506): for `f` divisible by `thetaCond Fam x r_s` (the moving conductor and the
primes `q` with `λ_q(x) = 1`) with the primes of `f` in the Selmer support `S s`: the quadratic
part by lane E2's genus theory (`quadOfDelta_family`), the moving part by lane E2's
`piOfDelta_of_moving` with lane E1's `ringClassRes_eq_one_of_fix` (the moving exponent is the
genuine `genuinePsi`, which factors through `Gal(H_{r_s}/K)`). -/
theorem thetaOfDelta_piU {G : GenuineFamilyMovingCharacter C.K ℓ Fam.Q}
    (P : StagedPresentation C D Fam x G.toFamily) (s : ℕ) (hk0 : D.kfin < 0) (f : ℕ) [NeZero f]
    (hf : thetaCond Fam x (G.r s) ∣ f)
    (hSf : ∀ v : HeightOneSpectrum (𝓞 C.K), (f : 𝓞 C.K) ∈ v.asIdeal → v ∈ P.S s) :
    ThetaOfDelta (Δ := (Acoef s)ˣ) (P.hS s) (Set.Subset.refl (P.S s)) (P.sh s) (P.hs s)
      (P.hs0 s) (P.piU s) f := by
  have : NeZero (G.r s) := ⟨(G.r_prime s).ne_zero⟩
  have hrf : G.r s ∣ f := (dvd_thetaCond_r Fam x (G.r s)).trans hf
  have hq := quadOfDelta_family (P.hS s) (Set.Subset.refl (P.S s)) (P.sh s) (P.hs s) (P.hs0 s)
    (finrank_of_sqrt P.hr P.hgen hk0) (isTotallyComplex_of_sqrt P.hr hk0) Fam x P.hprime rfl f
    (fun _ hq hl => (dvd_thetaCond_q Fam x (G.r s) hq hl).trans hf) hSf
  have hr1 : ∀ v : HeightOneSpectrum (𝓞 C.K), ((G.r s : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ P.S s :=
    fun v hv => hSf v (by
      obtain ⟨c, hc⟩ := hrf
      rw [hc, Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hv)
  have hp := piOfDelta_of_moving (Δ := (Acoef s)ˣ) (P.hS s) (Set.Subset.refl (P.S s)) (P.piU s)
    hrf hr1 (fun {_} {S'} {S₁'} hS' h1' hr1' g hg => by
      change P.ψf s s (genuinePsi G.C (G.r s) (2 * s) (G.ξ₀ s)
        (inflMap C.K (P.hSr s) (inflMap C.K hS' g))) = 1
      rw [← inflMap_trans (P.hSr s) hS' g]
      have key := ringClassRes_eq_one_of_fix (hS := G.C.hSr (G.r s)) (G.r_prime s)
        ((P.hSr s).trans hS') h1' hr1' g hg
      have h0 : genuinePsi G.C (G.r s) (2 * s) (G.ξ₀ s)
          (inflMap C.K ((P.hSr s).trans hS') g) = 1 :=
        (congrArg (fun y => AddMonoidHom.toMultiplicative (G.ξ₀ s)
          (Multiplicative.ofAdd (Additive.ofMul y))) key).trans (map_one _)
      rw [h0, map_one])
  have h := thetaOfDelta_of (Δ := (Acoef s)ˣ) (P.hS s) (Set.Subset.refl (P.S s)) (P.sh s)
    (P.hs s) (P.hs0 s) (P.piU s) f hq hp
  exact h

end Theta

/-! ### The inputs -/

section E2Inputs

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} {G : GenuineFamilyMovingCharacter C.K ℓ Fam.Q}

attribute [local instance] acoefTop acoefTop_discrete stageIsoA

/-- **The support of the division points of the `j`-th point at the stage `s`** (tex 3471–3487):
`S₀ s` together with the primes dividing `d_j`. Kind: definition. -/
def classSupportS (P : StagedPresentation C D Fam x G.toFamily) (s d j : ℕ) :
    Set (HeightOneSpectrum (𝓞 C.K)) :=
  P.S₀ s ∪ {v | ((chainCond d P.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal}

omit [(Ecurve ℓ).IsElliptic] in
/-- The step primes are positive: primes for the steps, `1` past the end (tex 2678–2680).
Kind: PROVED. -/
theorem StagedPresentation.ps_getD_pos (P : StagedPresentation C D Fam x G.toFamily) (j : ℕ) :
    0 < P.ps.getD j 1 := by
  by_cases hj : j < P.ps.length
  · obtain ⟨hqQ, -⟩ := mem_unusedAt.mp (P.mem_unused hj)
    exact (P.hprime _ hqQ).1.pos
  · rw [List.getD_eq_default _ _ (not_lt.mp hj)]
    exact one_pos

omit [(Ecurve ℓ).IsElliptic] in
/-- The step primes are primes (tex 2678–2680). Kind: PROVED. -/
theorem StagedPresentation.ps_getD_prime (P : StagedPresentation C D Fam x G.toFamily) {i : ℕ}
    (hi : i < P.ps.length) : (P.ps.getD i 1).Prime := by
  obtain ⟨hqQ, -⟩ := mem_unusedAt.mp (P.mem_unused hi)
  exact (P.hprime _ hqQ).1

/-- **The inputs of lane E2's construction of the classes at the stage `t + 1` of the staged
presentation** that do not follow from `P` (tex 2595–2603, 2847–2855, 2914–2936, 3471–3487,
4142–4194). The character condition and the splitting of the step primes are derived
(`E2ChainInputsS.hθ`, `E2ChainInputsS.hsplit`). Each field's kind and tex lines are in its
docstring. Kind: definition (data). -/
structure E2ChainInputsS (P : StagedPresentation C D Fam x G.toFamily) (t : ℕ) where
  /-- the modular parametrization data (definition; tex 2914–2917) -/
  cp : CSTParam (Ecurve ℓ)
  /-- the complex embedding of `ℚ̄` (definition; tex 2914–2917) -/
  emb : Qbar →ₐ[ℚ] ℂ
  /-- the identification `ℚ̄ ≃ K̄` (definition; tex 2914–2936) -/
  κ : Qbar ≃ₐ[ℚ] AlgebraicClosure C.K
  /-- GLUE: Cai–Chen–Liu, Trans. AMS 370 (2018), Theorem 2.15, read through the modular
  parametrization and joined with lane E2's full anchor (tex 2914–2936) -/
  print : CCLThm2_15Applied (Ecurve ℓ) (FullAnchor (Ecurve ℓ) C.K cp emb κ)
  /-- `k < 0` (definition: the final companion; from the ELLIOT field `RCSteps.companion`,
  tex 2595–2603) -/
  hk0 : D.kfin < 0
  /-- `k` is squarefree (definition: the final companion; from `RCSteps.companion`,
  tex 2595–2603) -/
  hksq : Squarefree D.kfin
  /-- `k ≡ 1 (mod 4)` (definition: the final companion; from `RCSteps.companion`,
  tex 2595–2603) -/
  hk4 : D.kfin % 4 = 1
  /-- the base conductor at the stage (definition; tex 2914–2921, 2847–2855) -/
  d : ℕ
  /-- it is positive (definition) -/
  hd : 0 < d
  /-- it is prime to `2 N D_K` (definition: admissibility; tex 2920–2921; with `hfd` it requires
  `r_{t+1} ∤ 2 N k`) -/
  hd2 : Nat.Coprime d (2 * CST.newformLevel (Ecurve ℓ) * (discr C.K).natAbs)
  /-- it is divisible by the conductor of the character at the stage, `r_{t+1}` and the primes
  `q` with `λ_q(x) = 1` (definition; tex 2847–2855) -/
  hfd : thetaCond Fam x (G.r (t + 1)) ∣ d
  /-- its primes lie in the support of the stage (definition; tex 3455–3463) -/
  hdS0 : ∀ v : HeightOneSpectrum (𝓞 C.K), (d : 𝓞 C.K) ∈ v.asIdeal → v ∈ P.S₀ (t + 1)
  /-- the primes above `2` lie in the support of the stage (definition; tex 2729–2741) -/
  htwo : ∀ v : HeightOneSpectrum (𝓞 C.K), (2 : 𝓞 C.K) ∈ v.asIdeal → v ∈ P.S₀ (t + 1)
  /-- `E` has good reduction outside the support of the stage (definition: it contains the
  primes above `N`; tex 2729–2741) -/
  hgood : ∀ v : HeightOneSpectrum (𝓞 C.K), v ∉ P.S₀ (t + 1) →
    ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt ((Ecurve ℓ).baseChange C.K) v
  /-- the places of the other indices do not lie above the step prime (definition: distinct
  indices carry the places of distinct primes; tex 4142–4146) -/
  hsep : ∀ i < P.ps.length, ∀ (p : P.ι) (c : Bool), p ≠ P.pidx i →
    ((P.ps.getD i 1 : ℕ) : 𝓞 C.K) ∉ (P.pl (p, c)).asIdeal
  /-- the step prime does not divide `6 d_i N D_K` (definition: admissibility;
  tex 2920–2921) -/
  hq : ∀ i < P.ps.length, ¬ P.ps.getD i 1 ∣
    6 * chainCond d P.ps i * CST.newformLevel (Ecurve ℓ) * (discr C.K).natAbs

namespace E2ChainInputsS

variable {P : StagedPresentation C D Fam x G.toFamily} {t : ℕ} (I : E2ChainInputsS P t)

/-- The base conductor is nonzero (PROVED). -/
instance neZero_d : NeZero I.d := ⟨I.hd.ne'⟩

omit [(Ecurve ℓ).IsElliptic] in
include I in
/-- **The step primes split: `jacobiSym (disc K) q_i = 1`** (PROVED from `P.split` and the
companion facts; tex 2720–2722, 4142–4146). -/
theorem hsplit {i : ℕ} (hi : i < P.ps.length) : jacobiSym (discr C.K) (P.ps.getD i 1) = 1 := by
  rw [discr_of_sqrt P.hr P.hgen I.hk0 I.hksq I.hk4]
  obtain ⟨hqQ, -⟩ := mem_unusedAt.mp (P.mem_unused hi)
  exact jacobiSym_of_split (P.hprime _ hqQ).1 (P.split _ hqQ)

omit [(Ecurve ℓ).IsElliptic] in
/-- The chain conductors are positive (tex 2914–2921). Kind: PROVED. -/
theorem chainCond_pos : ∀ j, 0 < chainCond I.d P.ps j
  | 0 => I.hd
  | j + 1 => Nat.mul_pos (chainCond_pos j) (P.ps_getD_pos j)

omit [(Ecurve ℓ).IsElliptic] in
/-- The chain conductors are prime to `2 N D_K` (tex 2920–2921). Kind: PROVED. -/
theorem chainCond_coprime : ∀ j, Nat.Coprime (chainCond I.d P.ps j)
    (2 * CST.newformLevel (Ecurve ℓ) * (discr C.K).natAbs)
  | 0 => I.hd2
  | j + 1 => by
    refine Nat.Coprime.mul_left (chainCond_coprime j) ?_
    by_cases hj : j < P.ps.length
    · refine (Nat.Prime.coprime_iff_not_dvd (P.ps_getD_prime hj)).2 fun h => I.hq j hj ?_
      exact h.trans ⟨3 * chainCond I.d P.ps j, by ring⟩
    · rw [List.getD_eq_default _ _ (not_lt.mp hj)]
      exact Nat.coprime_one_left _

omit [(Ecurve ℓ).IsElliptic] in
/-- **The chain's places off the support do not divide the conductor** (PROVED from `hdS0`,
`hsep` and `P.hw`; tex 3471–3487). -/
theorem cond_not_mem : ∀ (j : ℕ) (p : P.ι) (c : Bool), p ∉ chainT P.pidx j →
    ((chainCond I.d P.ps j : ℕ) : 𝓞 C.K) ∉ (P.pl (p, c)).asIdeal
  | 0, p, c, _ => fun h => P.hw (t + 1) (p, c) (I.hdS0 _ h)
  | j + 1, p, c, hp => by
    have hp' : p ≠ P.pidx j ∧ p ∉ chainT P.pidx j := by
      simpa [chainT, not_or] using hp
    intro h
    change (((chainCond I.d P.ps j * P.ps.getD j 1 : ℕ) : 𝓞 C.K)) ∈ (P.pl (p, c)).asIdeal at h
    rw [Nat.cast_mul] at h
    rcases (P.pl (p, c)).isPrime.mem_or_mem h with h1 | h1
    · exact cond_not_mem j p c hp'.2 h1
    · by_cases hj : j < P.ps.length
      · exact I.hsep j hj p c hp'.1 h1
      · rw [List.getD_eq_default _ _ (not_lt.mp hj), Nat.cast_one] at h1
        exact (P.pl (p, c)).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

omit [(Ecurve ℓ).IsElliptic] in
/-- The primes dividing a chain conductor lie in the Selmer support of the stage (PROVED from
`hdS0` and `P.places`; tex 3455–3463). -/
theorem mem_S_of_cond : ∀ (j : ℕ) (v : HeightOneSpectrum (𝓞 C.K)),
    ((chainCond I.d P.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ P.S (t + 1)
  | 0, v, h => P.hS (t + 1) (I.hdS0 v h)
  | j + 1, v, h => by
    change (((chainCond I.d P.ps j * P.ps.getD j 1 : ℕ) : 𝓞 C.K)) ∈ v.asIdeal at h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h1 | h1
    · exact mem_S_of_cond j v h1
    · by_cases hj : j < P.ps.length
      · rcases (P.places (t + 1) j hj).above v.asIdeal v.isPrime h1 with h2 | h2
        · exact Set.mem_union_right _ ⟨(P.pidx j, false), (HeightOneSpectrum.ext h2).symm⟩
        · exact Set.mem_union_right _ ⟨(P.pidx j, true), (HeightOneSpectrum.ext h2).symm⟩
      · rw [List.getD_eq_default _ _ (not_lt.mp hj), Nat.cast_one] at h1
        exact absurd ((Ideal.eq_top_iff_one _).2 h1) v.isPrime.ne_top

omit [(Ecurve ℓ).IsElliptic] in
/-- The support of the division points lies in the Selmer support (PROVED). -/
theorem classSupport_subset (j : ℕ) : classSupportS P (t + 1) I.d j ⊆ P.S (t + 1) := by
  rintro v (hv | hv)
  · exact P.hS (t + 1) hv
  · exact I.mem_S_of_cond j v hv

omit [(Ecurve ℓ).IsElliptic] in
/-- The primes of `d_j` lie in the support (PROVED). -/
theorem hSd (j : ℕ) : ∀ v : HeightOneSpectrum (𝓞 C.K),
    ((chainCond I.d P.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ classSupportS P (t + 1) I.d j :=
  fun _ hv => Or.inr hv

omit [(Ecurve ℓ).IsElliptic] in
/-- The primes of `2^{t+1}` lie in the support (PROVED from `htwo`). -/
theorem hm (j : ℕ) : ∀ v : HeightOneSpectrum (𝓞 C.K),
    ((2 ^ (t + 1) : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ classSupportS P (t + 1) I.d j := by
  intro v hv
  rw [Nat.cast_pow, Nat.cast_ofNat] at hv
  exact Or.inl (I.htwo v (v.isPrime.mem_of_pow_mem _ hv))

omit [(Ecurve ℓ).IsElliptic] in
/-- `E` has good reduction outside the support (PROVED from `hgood`). -/
theorem hgood' (j : ℕ) : ∀ v : HeightOneSpectrum (𝓞 C.K), v ∉ classSupportS P (t + 1) I.d j →
    ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt ((Ecurve ℓ).baseChange C.K) v :=
  fun v hv => I.hgood v fun h => hv (Or.inl h)

omit [(Ecurve ℓ).IsElliptic] in
/-- No place of the chain off `chainT pidx j` lies in the support (PROVED from `cond_not_mem`
and `P.hw`). -/
theorem hpl (j : ℕ) : ∀ jj : P.ι × Bool, jj.1 ∉ chainT P.pidx j →
    (P.place (t + 1) jj).1 ∉ classSupportS P (t + 1) I.d j := by
  rintro ⟨p, c⟩ hp (h | h)
  · exact P.hw (t + 1) (p, c) h
  · exact I.cond_not_mem j p c hp h

omit [(Ecurve ℓ).IsElliptic] in
/-- **The character condition at the base conductor** (PROVED from `thetaOfDelta_piU` with
`hfd`, `hdS0` and the companion fact `hk0`; tex 2847–2855). -/
theorem hθ : ThetaOfDelta (Δ := (Acoef (t + 1))ˣ) (P.hS (t + 1)) (Set.Subset.refl (P.S (t + 1)))
    (P.sh (t + 1))
    (P.hs (t + 1)) (P.hs0 (t + 1)) (P.piU (t + 1)) I.d :=
  by
    have h := thetaOfDelta_piU P (t + 1) I.hk0 I.d I.hfd fun v hv => P.hS (t + 1) (I.hdS0 v hv)
    exact h

/-! ### The anchored datum and the classes -/

/-- **The anchored datum of lane E2's step identity at the stage** (tex 2914–2936).
Kind: definition. -/
def datum : HeegnerPointData (Ecurve ℓ) :=
  letI := Classical.decEq (Places C.K (P.S₀ (t + 1)))
  Classical.choose (gx_step_heegner_at (Δ := (Acoef (t + 1))ˣ) (Ecurve ℓ) (P.hS (t + 1))
    (P.hS (t + 1))
    (Set.Subset.refl (P.S (t + 1))) (t + 1) (P.sh (t + 1)) (P.hs (t + 1)) (P.hs0 (t + 1))
    (HasFullTwoTorsion.full (t + 1)) (P.piU (t + 1)) (MonoidHom.id _) P.Pk
    (id_units_injective (t + 1)) (P.psiTrivialU (t + 1)) (StageRing (t + 1)) (P.place (t + 1))
    I.print)

/-- The full anchor of the datum (tex 2914–2936). Kind: PROVED. -/
theorem anchor : FullAnchor (Ecurve ℓ) C.K I.cp I.emb I.κ I.datum := by
  let _ := Classical.decEq (Places C.K (P.S₀ (t + 1)))
  have h := (Classical.choose_spec (gx_step_heegner_at (Δ := (Acoef (t + 1))ˣ) (Ecurve ℓ)
    (P.hS (t + 1)) (P.hS (t + 1)) (Set.Subset.refl (P.S (t + 1))) (t + 1) (P.sh (t + 1))
    (P.hs (t + 1)) (P.hs0 (t + 1)) (HasFullTwoTorsion.full (t + 1)) (P.piU (t + 1))
    (MonoidHom.id _) P.Pk (id_units_injective (t + 1)) (P.psiTrivialU (t + 1))
    (StageRing (t + 1)) (P.place (t + 1)) I.print)).fst
  exact h

/-- The conductors are prime to `N D_K` for the datum (PROVED). -/
theorem hcop (j : ℕ) : Nat.Coprime (chainCond I.d P.ps j) (I.datum.N * I.datum.DK.natAbs) := by
  rw [I.anchor.anchor.1, I.anchor.anchor.2.1]
  exact Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 (by ring)) (I.chainCond_coprime j)

/-- **Every step is admissible for the datum** (PROVED from `hd2`, `hq` and the anchor's
`D.N = N`, `D.DK = D_K`; tex 2920–2921). -/
theorem hadmD {i : ℕ} (hi : i < P.ps.length) :
    I.datum.Admissible (chainCond I.d P.ps i) (P.ps.getD i 1) := by
  refine ⟨I.chainCond_pos i, ?_, P.ps_getD_prime hi, ?_⟩
  · rw [I.anchor.anchor.1, I.anchor.anchor.2.1]
    exact I.chainCond_coprime i
  · rw [I.anchor.anchor.1, I.anchor.anchor.2.1]
    exact I.hq i hi

/-- **Every step prime splits for the datum** (PROVED from `hsplit`; tex 2720–2722). -/
theorem hsplitD {i : ℕ} (hi : i < P.ps.length) : jacobiSym I.datum.DK (P.ps.getD i 1) = 1 := by
  rw [I.anchor.anchor.2.1]
  exact I.hsplit hi

omit [(Ecurve ℓ).IsElliptic] in
/-- **The character is trivial on the transfer subgroup `G_{H_{d_j}}`** (PROVED from `hθ`, lane
E2's `hα_of_theta`; tex 2847–2855). -/
theorem hα (j : ℕ) [NeZero (chainCond I.d P.ps j)] :
    fixH ((I.classSupport_subset j).trans (Set.Subset.refl (P.S (t + 1))))
        (heegnerL (chainCond I.d P.ps j) (I.hSd j)) ≤
      (alphaInfl (Δ := (Acoef (t + 1))ˣ) (P.hS (t + 1)) (P.sh (t + 1)) (P.hs (t + 1))
        (P.hs0 (t + 1)) (P.piU (t + 1))).ker := by
  have h := hα_of_theta (Δ := (Acoef (t + 1))ˣ) (P.hS (t + 1)) (Set.Subset.refl (P.S (t + 1)))
    (P.sh (t + 1)) (P.hs (t + 1)) (P.hs0 (t + 1)) (P.piU (t + 1)) (I.classSupport_subset j) I.d
  exact h I.hθ (dvd_chainCond I.d P.ps j) (I.hSd j)

/-- **The actual Heegner point of conductor `d_j` on the support `chainT pidx j`** (tex
3080–3084, 3203–3215): lane E2's `heegnerActual` for `π' = Ψ_{t+1}`, `ψ' = id`.
Kind: definition. -/
def actualPt (j : ℕ) :=
  haveI : NeZero (chainCond I.d P.ps j) := ⟨(I.chainCond_pos j).ne'⟩
  let mk := heegnerActual (Δ := (Acoef (t + 1))ˣ) (Ecurve ℓ) (P.hS (t + 1)) (P.hS (t + 1))
    (Set.Subset.refl (P.S (t + 1))) (t + 1) (P.sh (t + 1)) (P.hs (t + 1)) (P.hs0 (t + 1))
    (HasFullTwoTorsion.full (t + 1)) (P.piU (t + 1)) (MonoidHom.id _) P.Pk
  mk (id_units_injective (t + 1)) (P.psiTrivialU (t + 1)) (P.place (t + 1)) (Tp := chainT P.pidx j)
    I.anchor (I.classSupport_subset j) (chainCond I.d P.ps j) (I.hcop j) (I.hSd j) (I.hm j)
    (I.hgood' j) (I.hα j) (I.hpl j)

/-- **The class of lane E2's construction for the conductor `d_j`** (tex 3080–3084, 4157–4170):
lane E2's `gx` of `actualPt j`, with its own type. Kind: definition. -/
def gE2 (j : ℕ) :=
  letI := Classical.decEq (Places C.K (P.S₀ (t + 1)))
  let push := gx (Δ := (Acoef (t + 1))ˣ) (P.hS (t + 1)) (P.hS (t + 1))
    (Set.Subset.refl (P.S (t + 1))) ((Ecurve ℓ).baseChange C.K) (t + 1) (P.sh (t + 1))
    (P.hs (t + 1)) (P.hs0 (t + 1)) (HasFullTwoTorsion.full (t + 1)) (P.piU (t + 1))
    (MonoidHom.id _) P.Pk (StageRing (t + 1)) (P.place (t + 1))
  push (I.actualPt j)

/-- **The global class of conductor `d_j` at the stage `t + 1`** (tex 3080–3084, 4157–4170):
`gE2 j` in the global complex of the presentation's coefficient module (the same type, by
`alphaStageU_eq`). Kind: definition. -/
def g (j : ℕ) :
    (globalCx (StageRing (t + 1)) (GKS C.K (P.S (t + 1))) (famM P (t + 1) (t + 1))).X 1 :=
  I.gE2 j

/-! ### The step identities -/

omit [(Ecurve ℓ).IsElliptic] in
/-- **The places of a step are anticyclotomic for the stage character** (PROVED from
`P.movingConj`; tex 2778–2796, 4171). -/
theorem hanti {i : ℕ} (hi : i < P.ps.length) :
    AnticyclotomicAt (alphaStage (Δ := (Acoef (t + 1))ˣ) (t + 1) (P.sh (t + 1)) (P.hs (t + 1))
      (P.hs0 (t + 1))
      (P.piU (t + 1)) (MonoidHom.id _))
      (newPlace (P.place (t + 1) (P.pidx i, false)) (P.hwp (t + 1) (P.pidx i, false)))
      (newPlace (P.place (t + 1) (P.pidx i, true)) (P.hwp (t + 1) (P.pidx i, true))) := by
  have hκh : (P.Cc (t + 1)).κ ((Fam.h x : ℤ) : C.K) = ((Fam.h x : ℤ) : C.K) := map_intCast _ _
  obtain ⟨g, hg⟩ := frobConjugatePlaces_proved (P.S (t + 1)) (P.Cc (t + 1))
    (newPlace (P.place (t + 1) (P.pidx i, false)) (P.hwp (t + 1) (P.pidx i, false)))
    (newPlace (P.place (t + 1) (P.pidx i, true)) (P.hwp (t + 1) (P.pidx i, true)))
    (P.places (t + 1) i hi).conj
  exact anticyclotomicAt_of_conj (P.Cc (t + 1)) (alphaStage_conj (P.Cc (t + 1)) (P.sh (t + 1))
    (P.hs (t + 1)) (P.hs0 (t + 1)) hκh (P.ξ (t + 1)) (t + 1) (P.ψf (t + 1) (t + 1))
    (P.movingConj (t + 1))) hg

omit [(Ecurve ℓ).IsElliptic] in
/-- **The places of a step are prime to the conductors** (PROVED from `cond_not_mem`, `P.hnew`
and lane E1's `mem_primeTo_of_not_mem`; tex 2914–2936). -/
theorem hwd {i : ℕ} (hi : i < P.ps.length) [NeZero (chainCond I.d P.ps i)] :
    ∀ w ∈ [newPlace (P.place (t + 1) (P.pidx i, false)) (P.hwp (t + 1) (P.pidx i, false)),
      newPlace (P.place (t + 1) (P.pidx i, true)) (P.hwp (t + 1) (P.pidx i, true))],
      ((chainCond I.d P.ps i : ℕ) : 𝓞 C.K) ∉ w.1.asIdeal ∧
      w.1.asIdeal ∈ TauCeti.GlobalNumberFields.integralIdealsPrimeTo
        (CST.conductorOrder C.K (chainCond I.d P.ps i)).conductorModulus ∧
      w.1.asIdeal ∈ TauCeti.GlobalNumberFields.integralIdealsPrimeTo
        (ZInQ.Contrib.CloudB3E1RingClass.ringClassOrder (K := C.K) (chainCond I.d P.ps i)
          (NeZero.ne _)).conductorModulus := by
  intro w hw
  have hnot : ((chainCond I.d P.ps i : ℕ) : 𝓞 C.K) ∉ w.1.asIdeal := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact I.cond_not_mem i _ _ (P.hnew i hi)
    · exact I.cond_not_mem i _ _ (P.hnew i hi)
  have hJ := mem_primeTo_of_not_mem (chainCond I.d P.ps i) (NeZero.ne _) w.1 hnot
  refine ⟨hnot, ?_, hJ⟩
  rw [← ringClassOrder_eq_conductorOrder]
  exact hJ

/-- **The junction: lane E2's point factor at the stage is the leaf's** (PROVED; tex 3915,
4158–4172, 4176–4184): `a_q`, `z = α(Frob_{w₀})` and `z⁻¹` pushed to `StageRing (t + 1)` are the
leaf's `a`, `z`, `zi` at the stage (`staged_stageFrobInput` at the first place of the step). -/
theorem stepFactor_eq {i : ℕ} (hi : i < P.ps.length) :
    pointFactor (((Ecurve ℓ).LFunction (P.ps.getD i 1) : ℤ) : StageRing (t + 1))
        ((eK (StageRing (t + 1)) (t + 1)).symm
          (alphaStage (Δ := (Acoef (t + 1))ˣ) (t + 1) (P.sh (t + 1)) (P.hs (t + 1))
            (P.hs0 (t + 1)) (P.piU (t + 1))
            (MonoidHom.id _) (urFrobElt C.K (newPlace (P.place (t + 1) (P.pidx i, false))
              (P.hwp (t + 1) (P.pidx i, false)))) : Acoef (t + 1)))
        ((eK (StageRing (t + 1)) (t + 1)).symm
          (((alphaStage (Δ := (Acoef (t + 1))ˣ) (t + 1) (P.sh (t + 1)) (P.hs (t + 1))
            (P.hs0 (t + 1)) (P.piU (t + 1))
            (MonoidHom.id _) (urFrobElt C.K (newPlace (P.place (t + 1) (P.pidx i, false))
              (P.hwp (t + 1) (P.pidx i, false)))))⁻¹ : (Acoef (t + 1))ˣ) : Acoef (t + 1))) =
      pointFactor (((leafFrobΛ C Fam x P.ps).map (stageMk (t + 1))).a i)
        (((leafFrobΛ C Fam x P.ps).map (stageMk (t + 1))).z i)
        (((leafFrobΛ C Fam x P.ps).map (stageMk (t + 1))).zi i) := by
  obtain ⟨⟨_, h1⟩, -⟩ := staged_stageFrobInput P (Nat.succ_pos t) hi
  set u := alphaStage (Δ := (Acoef (t + 1))ˣ) (t + 1) (P.sh (t + 1)) (P.hs (t + 1))
    (P.hs0 (t + 1)) (P.piU (t + 1))
    (MonoidHom.id _) (urFrobElt C.K (newPlace (P.place (t + 1) (P.pidx i, false))
      (P.hwp (t + 1) (P.pidx i, false)))) with hu
  have hz : (eK (StageRing (t + 1)) (t + 1)).symm (u : Acoef (t + 1)) =
      ((leafFrobΛ C Fam x P.ps).map (stageMk (t + 1))).z i := h1.charValue
  have hleaf : ((leafFrobΛ C Fam x P.ps).map (stageMk (t + 1))).z i *
      ((leafFrobΛ C Fam x P.ps).map (stageMk (t + 1))).zi i = 1 := by
    change stageMk (t + 1) ((zAt Fam x (P.ps.getD i 1) : Lambdaˣ) : Lambda) *
      stageMk (t + 1) (((zAt Fam x (P.ps.getD i 1))⁻¹ : Lambdaˣ) : Lambda) = 1
    rw [← map_mul, Units.mul_inv, map_one]
  have hinv : (eK (StageRing (t + 1)) (t + 1)).symm (u : Acoef (t + 1)) *
      (eK (StageRing (t + 1)) (t + 1)).symm ((u⁻¹ : (Acoef (t + 1))ˣ) : Acoef (t + 1)) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hzi : (eK (StageRing (t + 1)) (t + 1)).symm ((u⁻¹ : (Acoef (t + 1))ˣ) : Acoef (t + 1)) =
      ((leafFrobΛ C Fam x P.ps).map (stageMk (t + 1))).zi i := by
    rw [hz] at hinv
    calc _ = ((leafFrobΛ C Fam x P.ps).map (stageMk (t + 1))).zi i *
          (((leafFrobΛ C Fam x P.ps).map (stageMk (t + 1))).z i *
            (eK (StageRing (t + 1)) (t + 1)).symm ((u⁻¹ : (Acoef (t + 1))ˣ) : Acoef (t + 1))) := by
          rw [← mul_assoc, mul_comm _ (((leafFrobΛ C Fam x P.ps).map (stageMk (t + 1))).z i),
            hleaf, one_mul]
      _ = _ := by rw [hinv, mul_one]
  have ha : (((Ecurve ℓ).LFunction (P.ps.getD i 1) : ℤ) : StageRing (t + 1)) =
      ((leafFrobΛ C Fam x P.ps).map (stageMk (t + 1))).a i := by
    change _ = stageMk (t + 1) ((apE ℓ (P.ps.getD i 1) : ℤ) : Lambda)
    rw [map_intCast]
    rfl
  rw [ha, hz, hzi]

/-- **The global identities of the chain from lane E2's step identity** (PROVED; tex 2914–2936,
4157–4172): `g_{i+1} = pointFactor a_i z_i z_i⁻¹ • g_i + d b_i` with the leaf's values at the
stage, from `gx_step_heegner_at` at the two places of the step (`P.places`, `hanti`, `hwd`) and
the junction `stepFactor_eq`. -/
theorem hG : ∀ i < P.ps.length,
    ∃ bG : (globalCx (StageRing (t + 1)) (GKS C.K (P.S (t + 1))) (famM P (t + 1) (t + 1))).X 0,
      I.g (i + 1) = pointFactor (((leafFrobΛ C Fam x P.ps).map (stageMk (t + 1))).a i)
          (((leafFrobΛ C Fam x P.ps).map (stageMk (t + 1))).z i)
          (((leafFrobΛ C Fam x P.ps).map (stageMk (t + 1))).zi i) • I.g i +
        (globalCx (StageRing (t + 1)) (GKS C.K (P.S (t + 1))) (famM P (t + 1) (t + 1))).d 0 1
          rfl bG := by
  intro i hi
  let _ := Classical.decEq (Places C.K (P.S₀ (t + 1)))
  have : NeZero (chainCond I.d P.ps i) := ⟨(I.chainCond_pos i).ne'⟩
  have : NeZero (P.ps.getD i 1) := ⟨(P.ps_getD_pos i).ne'⟩
  obtain ⟨hA, -, hall⟩ := Classical.choose_spec (gx_step_heegner_at (Δ := (Acoef (t + 1))ˣ)
    (Ecurve ℓ) (P.hS (t + 1))
    (P.hS (t + 1)) (Set.Subset.refl (P.S (t + 1))) (t + 1) (P.sh (t + 1)) (P.hs (t + 1))
    (P.hs0 (t + 1)) (HasFullTwoTorsion.full (t + 1)) (P.piU (t + 1)) (MonoidHom.id _) P.Pk
    (id_units_injective (t + 1)) (P.psiTrivialU (t + 1)) (StageRing (t + 1)) (P.place (t + 1))
    I.print)
  obtain ⟨bG, hbG⟩ := hall (I.hadmD hi) (I.hsplitD hi) (Tp := chainT P.pidx i) (p := P.pidx i)
    (I.classSupport_subset i) (I.classSupport_subset (i + 1)) (I.hSd i) (I.hSd (i + 1))
    (I.hm i) (I.hm (i + 1)) (I.hgood' i) (I.hgood' (i + 1)) I.d I.hθ (dvd_chainCond I.d P.ps i)
    (I.hpl i) (I.hpl (i + 1))
    (newPlace (P.place (t + 1) (P.pidx i, false)) (P.hwp (t + 1) (P.pidx i, false)))
    (newPlace (P.place (t + 1) (P.pidx i, true)) (P.hwp (t + 1) (P.pidx i, true)))
    (P.places (t + 1) i hi).above (hanti hi) (I.hwd hi)
  refine ⟨bG, ?_⟩
  rw [← stepFactor_eq hi]
  exact hbG

section UrInst

attribute [local instance] ZInQ.Contrib.CloudB3E2.NormCochain.mcoefModuleK

/-- The unramified representations of lane E2's construction are discrete modules (PROVED;
lane RC28's `urRep_continuousSMul`, with lane E2's module structure over the stage ring). -/
theorem urContU (jj : P.ι × Bool) : ContinuousSMul (GUr C.K (P.place (t + 1) jj).1)
    (urRep (StageRing (t + 1)) (Mcoef C.K (P.S₀ (t + 1)) ((Ecurve ℓ).baseChange C.K) (t + 1)
      (alphaStage (Δ := (Acoef (t + 1))ˣ) (t + 1) (P.sh (t + 1)) (P.hs (t + 1)) (P.hs0 (t + 1))
        (P.piU (t + 1)) (MonoidHom.id _)))
      (newPlace (P.place (t + 1) jj) (P.hwp (t + 1) jj))).V :=
  urRep_continuousSMul (StageRing (t + 1)) _ (newPlace (P.place (t + 1) jj) (P.hwp (t + 1) jj))

end UrInst

/-- **The local lifts of the classes** (PROVED: lane E2's `exists_ux`; tex 3471–3487,
4169–4171). -/
theorem hloc (j : ℕ) :
    ∃ u : (piCx (presCondS C.K (P.S₀ (t + 1)) (P.S (t + 1)) (StageRing (t + 1))
        (famM P (t + 1) (t + 1)) (famConds P (t + 1) (t + 1)) (P.place (t + 1))
        (famX P (t + 1) (t + 1)) (famEU P (t + 1) (t + 1)) (chainT P.pidx j)).U).X 1,
      (piMap (presCondS C.K (P.S₀ (t + 1)) (P.S (t + 1)) (StageRing (t + 1))
        (famM P (t + 1) (t + 1)) (famConds P (t + 1) (t + 1)) (P.place (t + 1))
        (famX P (t + 1) (t + 1)) (famEU P (t + 1) (t + 1)) (chainT P.pidx j)).i).f 1 1 rfl u =
      (resS (StageRing (t + 1)) (GKS C.K (P.S (t + 1)))
        (presGv C.K (P.S₀ (t + 1)) (P.S (t + 1)) (P.place (t + 1)))
        (presLoc C.K (P.S₀ (t + 1)) (P.S (t + 1)) (P.place (t + 1)))
        (famM P (t + 1) (t + 1))).f 1 1 rfl (I.g j) := by
  let _ := Classical.decEq (Places C.K (P.S₀ (t + 1)))
  have : NeZero (chainCond I.d P.ps j) := ⟨(I.chainCond_pos j).ne'⟩
  have : ∀ jj : P.ι × Bool, ContinuousSMul (GUr C.K (P.place (t + 1) jj).1)
      (urRep (MonoidAlgebra ℤ (Acoef (t + 1))ˣ)
        (ZInQ.Contrib.CloudB3E2.NormCochain.shapMod₀ (Δ := (Acoef (t + 1))ˣ)
          ((Ecurve ℓ).baseChange C.K) (t + 1)
          (P.sh (t + 1)) (P.hs (t + 1)) (P.hs0 (t + 1)) (P.piU (t + 1)))
        (newPlace (P.place (t + 1) jj) (P.hwp (t + 1) jj))).V := fun jj =>
    urRep_continuousSMul (MonoidAlgebra ℤ (Acoef (t + 1))ˣ)
      (ZInQ.Contrib.CloudB3E2.NormCochain.shapMod₀ (Δ := (Acoef (t + 1))ˣ)
          ((Ecurve ℓ).baseChange C.K) (t + 1)
        (P.sh (t + 1)) (P.hs (t + 1)) (P.hs0 (t + 1)) (P.piU (t + 1)))
      (newPlace (P.place (t + 1) jj) (P.hwp (t + 1) jj))
  have := fun jj => urContU (P := P) (t := t) jj
  have h0 := exists_ux (Δ := (Acoef (t + 1))ˣ) (P.hS (t + 1)) (P.hS (t + 1))
    (Set.Subset.refl (P.S (t + 1))) ((Ecurve ℓ).baseChange C.K) (t + 1) (P.sh (t + 1))
    (P.hs (t + 1)) (P.hs0 (t + 1)) (HasFullTwoTorsion.full (t + 1)) (P.piU (t + 1))
    (MonoidHom.id _) P.Pk (id_units_injective (t + 1)) (P.psiTrivialU (t + 1))
    (StageRing (t + 1)) (P.place (t + 1)) (P.hwp (t + 1))
  have h := h0 (famEU P (t + 1) (t + 1)) (famEU_i P (t + 1) (t + 1)) (I.actualPt j)
  exact h
end E2ChainInputsS

/-- **Lane E2's classes of the actual Heegner points as a class provider at the stage `t + 1` of
the staged presentation** (tex 2914–2936, 3080–3084, 4142–4194, 4157–4172). Kind: definition. -/
def e2ProviderS (P : StagedPresentation C D Fam x G.toFamily) (t : ℕ) (I : E2ChainInputsS P t) :
    StageClassesAtS P (t + 1) where
  g := I.g
  hG := I.hG
  hloc j _ := I.hloc j

end E2Inputs

end ZInQ.Manuscript.RC.Wiring
