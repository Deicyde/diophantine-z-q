import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate21Oriented
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19Leaf
import ZInQKernel.Contrib.CloudB3E2Norm.E2ChainGood
import ZInQKernel.Contrib.CloudB3E2Norm.FamilyCoef

/-!
# The staged common-coordinate leaf with the presentation oriented and lane E2's inputs built

Manuscript `diophantine_zq.tex`, tex 2595–2603, 2678–2680, 2720–2741, 2778–2795, 2847–2855,
2914–2936, 3455–3463, 4142–4194, 4385–4451.

**`CommonCoordinateInputsGenuineO D`** is lane RC32's `CommonCoordinateInputsGenuineS`
(`CommonCoordinate19Leaf.lean`) with three of its inputs replaced by their constructions, and the
same free retention (lane RC30's `StepRetention`, a free GLUE field of `StageChainsS`):

* the coefficient datum is lane E2's `quadTateCoef ℓ s₀` (`K = ℚ(s₀)`, `s₀² = k`, the shape of
  lane E2's `exists_leafCoef`);
* the presentation is an `OrientedPresentation` (`CommonCoordinate21Oriented.lean`), with the
  family's moving supports exactly the places above the moving primes: `xiFrob` is PROVED from the
  family's `orient_one`, and `xiConj` by lane E1's `xiConj_family'` (no print);
* at every retained stage lane E2's chain inputs are CONSTRUCTED (`e2ChainInputsS_ofCompanion`):
  lane E2's `e2ChainInputsS_of_actual'` with the three companion facts of `k` it uses (`k < 0`,
  squarefree, `k ≡ 1 (mod 4)`; ELLIOT: the facts of `RCSteps.companion` for the final companion,
  tex 2595–2603) in place of a whole `RCSteps D`, which contains
  (4.7) itself (`RCSteps.common_coordinate`) and so cannot be an input of a leaf for (4.7). The
  body is lane E2's. Its other inputs are: Cai–Chen–Liu (GLUE: read through the modular
  parametrization and joined with lane E2's full anchor), once per coefficient datum; the primes of
  `2N` in the fixed support (`hS2N`, stated by the text; it follows from lane E1's `LevelPrimesBad`,
  GLUE: Carayol, and `PreDataSpec.support_base`); `r_s ∤ k` (`hrk`, stated by the text);
  the places of the conductor in the stage supports (`hQS0`, stated by the text); no step prime `3`
  (`hQ3`) and the places above `3ℓ` in the stage supports (`h3ℓ`, formalization requirements; good
  reduction outside the support is lane E2's `hgood_of_support`); admissibility is the final
  family's (`FinalFamilyAt`).

* `e2ChainInputsS_ofCompanion`, `actualInputsO` (definitions);
* **`commonCoordinateInputsGenuineS_of_O`**, **`commonCoordinateInputsNF_of_genuineO`**,
  **`commonCoordinateTarget_of_genuineO`** (PROVED).

The starting models of `C_∅` and their ranks are as in `CommonCoordinateInputsGenuineS` (ELLIOT):
lane E2's `st0Shape_of_inputs` / `exists_genuine_st0_of_inputs` are stated over one support for all
stages, not over the staged supports `S₀ s`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion MilneADT_I_2_8)
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Local (IwasawaGenerators genuineCochainsInjective_proved)
open ZInQ.Manuscript.RC.PrintsArith (CCLThm2_15Applied)
open ZInQ.Contrib.CloudB3E2.NormCochain (CSTParam FullAnchor)
open ZInQ.Manuscript.RC.CoefModules (acoefTop acoefTop_discrete)
open ZInQ.Contrib.CloudB3E2.NormCochain (stageIsoA)
open ZInQ.Contrib.CloudB3RC53.CST (newformLevel)
open ZInQ.Contrib.CloudB3E2.ChainActual (prime_dvd_chainCond natCast_mem_of_card not_two_primes
  coprime_two_N_disc hgood_of_support)
open ZInQ.Contrib.CloudB3E2.FamilyCoef (quadTateCoef)
open scoped PowerSeries.WithPiTopology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} {G : GenuineFamilyMovingCharacter C.K ℓ Fam.Q}

section Constructor

attribute [local instance] acoefTop acoefTop_discrete stageIsoA

/-- **The actual chain inputs from the companion facts** (tex 2595–2603, 2678–2680, 2720–2741,
2847–2855, 2914–2936, 3455–3463, 4142–4146): lane E2's `e2ChainInputsS_of_actual` with the
companion facts `k < 0`, `k` squarefree, `k ≡ 1 (mod 4)` (`hk`; ELLIOT: the facts of
`RCSteps.companion` for the final companion, tex 2595–2603) in place of a whole `RCSteps D`; the
other inputs are lane E2's (Cai–Chen–Liu, GLUE, with the full anchor; admissibility; `hS2N`,
`hrk`, `hQS0` stated by the text; `hpidx`, `hQ3` formalization requirements; `hgood` GLUE,
Néron–Ogg–Shafarevich). The body is lane E2's.
Kind: definition. -/
def e2ChainInputsS_ofCompanion (P : StagedPresentation C D Fam x G.toFamily) (t : ℕ)
    (cp : CSTParam (Ecurve ℓ)) (emb : ZInQ.Manuscript.RC.PrintsArith.Qbar →ₐ[ℚ] ℂ)
    (κ : ZInQ.Manuscript.RC.PrintsArith.Qbar ≃ₐ[ℚ] AlgebraicClosure C.K)
    (print : CCLThm2_15Applied (Ecurve ℓ) (FullAnchor (Ecurve ℓ) C.K cp emb κ))
    (hk : D.kfin < 0 ∧ Squarefree D.kfin ∧ D.kfin % 4 = 1) (hAdm : Fam.Admissible D.S D.kfin)
    (hS2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ D.S)
    (hrk : ¬ ((G.r (t + 1) : ℕ) : ℤ) ∣ D.kfin)
    (hQS0 : ∀ q ∈ Fam.Q, Fam.lam q x = 1 → ∀ v : HeightOneSpectrum (𝓞 C.K),
      ((q : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ P.S₀ (t + 1))
    (hpidx : ∀ p : P.ι, ∃ j < P.ps.length, P.pidx j = p) (hQ3 : ∀ q ∈ unusedAt Fam x, q ≠ 3)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 C.K), v ∉ P.S₀ (t + 1) →
      ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt ((Ecurve ℓ).baseChange C.K) v) :
    E2ChainInputsS P t :=
  have hk0 : D.kfin < 0 := hk.1
  have hksq : Squarefree D.kfin := hk.2.1
  have hk4 : D.kfin % 4 = 1 := hk.2.2
  have hdisc : discr C.K = D.kfin := discr_of_sqrt P.hr P.hgen hk0 hksq hk4
  have hr := G.r_prime (t + 1)
  { cp := cp
    emb := emb
    κ := κ
    print := print
    hk0 := hk0
    hksq := hksq
    hk4 := hk4
    d := thetaCond Fam x (G.r (t + 1))
    hd := Nat.pos_of_ne_zero (thetaCond_ne_zero Fam x hr P.hprime)
    hd2 := by
      rw [hdisc]
      refine Nat.Coprime.mul_left (coprime_two_N_disc hr (G.r_not_twoN (t + 1)) hrk) ?_
      refine Nat.Coprime.prod_left fun q hq => ?_
      have hqQ := Finset.mem_of_mem_filter q hq
      obtain ⟨hqp, -, hqS, -, -⟩ := hAdm q hqQ
      exact coprime_two_N_disc hqp (fun h => hqS (hS2N q hqp h)) (P.split q hqQ).1
    hfd := dvd_refl _
    hdS0 := by
      intro v hv
      have hv' : ((G.r (t + 1) : ℕ) : 𝓞 C.K) *
          ((∏ q ∈ Fam.Q.filter (fun q => Fam.lam q x = 1), q : ℕ) : 𝓞 C.K) ∈ v.asIdeal := by
        simpa [thetaCond, Nat.cast_mul] using hv
      rcases v.isPrime.mem_or_mem hv' with h1 | h1
      · apply P.hSr (t + 1)
        apply G.toFamily.Sr_r (t + 1)
        change (((G.r (t + 1) : ℕ) : ℤ) : 𝓞 C.K) ∈ v.asIdeal
        exact_mod_cast h1
      · rw [Nat.cast_prod] at h1
        obtain ⟨q, hq, hqv⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 h1
        exact hQS0 q (Finset.mem_of_mem_filter q hq) (Finset.mem_filter.1 hq).2 v hqv
    htwo := by
      have := P.full (t + 1)
      exact ZInQ.Contrib.CloudB3RC53.Finiteness.h2_of_hasFullTwoTorsion_proof
        ((Ecurve ℓ).baseChange C.K)
    hgood := hgood
    hsep := by
      intro i hi p c hp hmem
      obtain ⟨j, hj, rfl⟩ := hpidx p
      have hij : j ≠ i := fun h => hp (h ▸ rfl)
      have hsp := P.places (t + 1) j hj
      have hjmem : ((P.ps.getD j 1 : ℕ) : 𝓞 C.K) ∈ (P.pl (P.pidx j, c)).asIdeal := by
        cases c
        · exact natCast_mem_of_card hsp.card
        · exact natCast_mem_of_card hsp.card'
      have hne : P.ps.getD i 1 ≠ P.ps.getD j 1 := by
        rw [List.getD_eq_getElem P.ps 1 hi, List.getD_eq_getElem P.ps 1 hj]
        exact fun h => hij ((P.hnd.getElem_inj_iff).1 h).symm
      exact not_two_primes (P.ps_getD_prime hi) (P.ps_getD_prime hj) hne hmem hjmem
    hq := by
      intro i hi h
      have hqp := P.ps_getD_prime hi
      obtain ⟨hqQ, hun⟩ := mem_unusedAt.mp (P.mem_unused hi)
      obtain ⟨-, -, hqS, -, -⟩ := hAdm _ hqQ
      rw [hdisc] at h
      rcases (Nat.Prime.dvd_mul hqp).1 h with h1 | h1
      · rcases (Nat.Prime.dvd_mul hqp).1 h1 with h2 | h2
        · rcases (Nat.Prime.dvd_mul hqp).1 h2 with h3 | h3
          · have h6 : P.ps.getD i 1 ∣ 2 * 3 := h3
            rcases (Nat.Prime.dvd_mul hqp).1 h6 with h4 | h4
            · exact (P.hprime _ hqQ).2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1 h4)
            · exact hQ3 _ (P.mem_unused hi)
                ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).1 h4)
          · rcases prime_dvd_chainCond hqp _ _ i h3 with h4 | ⟨m, hm, h4⟩
            · rcases (Nat.Prime.dvd_mul hqp).1 h4 with h5 | h5
              · have := (Nat.prime_dvd_prime_iff_eq hqp hr).1 h5
                exact G.r_notQ (t + 1) (this ▸ hqQ)
              · obtain ⟨q', hq', h6⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).1 h5
                have hq'p := (P.hprime q' (Finset.mem_of_mem_filter q' hq')).1
                have heq := (Nat.prime_dvd_prime_iff_eq hqp hq'p).1 h6
                have h1' := (Finset.mem_filter.1 hq').2
                rw [← heq, hun] at h1'
                exact zero_ne_one h1'
            · have hmi : m < P.ps.length := lt_trans hm hi
              have hpm := P.ps_getD_prime hmi
              have heq := (Nat.prime_dvd_prime_iff_eq hqp hpm).1 h4
              rw [List.getD_eq_getElem P.ps 1 hi, List.getD_eq_getElem P.ps 1 hmi] at heq
              exact (ne_of_gt hm) ((P.hnd.getElem_inj_iff).1 heq)
        · exact hqS (hS2N _ hqp (h2.trans (dvd_mul_left _ _)))
      · exact (P.split _ hqQ).1 (Int.natCast_dvd.mpr h1) }

/-- **The actual chain inputs at the retained stages** (tex 2729–2741, 2914–2936, 4385–4451): at
the stage `t + 1` the inputs `e2ChainInputsS_ofCompanion` with the stage's `hrk`, `hQS0`, and good
reduction outside the stage support from the places above `3ℓ` in it (lane E2's
`hgood_of_support`). Kind: definition. -/
def actualInputsO (P : StagedPresentation C D Fam x G.toFamily) {Gs : Set ℕ}
    (cp : CSTParam (Ecurve ℓ)) (emb : ZInQ.Manuscript.RC.PrintsArith.Qbar →ₐ[ℚ] ℂ)
    (κ : ZInQ.Manuscript.RC.PrintsArith.Qbar ≃ₐ[ℚ] AlgebraicClosure C.K)
    (print : CCLThm2_15Applied (Ecurve ℓ) (FullAnchor (Ecurve ℓ) C.K cp emb κ))
    (hk : D.kfin < 0 ∧ Squarefree D.kfin ∧ D.kfin % 4 = 1) (hAdm : Fam.Admissible D.S D.kfin)
    (hS2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ D.S)
    (hrk : ∀ s, ¬ ((G.r s : ℕ) : ℤ) ∣ D.kfin)
    (hQS0 : ∀ s, ∀ q ∈ Fam.Q, Fam.lam q x = 1 → ∀ v : HeightOneSpectrum (𝓞 C.K),
      ((q : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ P.S₀ s)
    (hpidx : ∀ p : P.ι, ∃ j < P.ps.length, P.pidx j = p) (hQ3 : ∀ q ∈ unusedAt Fam x, q ≠ 3)
    (h3ℓ : ∀ s, ∀ v : HeightOneSpectrum (𝓞 C.K), ((3 * ℓ : ℕ) : 𝓞 C.K) ∈ v.asIdeal →
      v ∈ P.S₀ s) :
    ∀ t, t + 1 ∈ Gs → E2ChainInputsS P t :=
  fun t _ => e2ChainInputsS_ofCompanion P t cp emb κ print hk hAdm hS2N (hrk (t + 1))
    (hQS0 (t + 1)) hpidx hQ3 (hgood_of_support P t (h3ℓ (t + 1)))

end Constructor

/-- **The staged common-coordinate inputs with the presentation oriented and lane E2's chain
inputs built** (tex 2595–2603, 2678–2680, 2729–2741, 2778–2795, 2914–2936, 3455–3463,
4142–4194, 4385–4451). Kind: definition. -/
structure CommonCoordinateInputsGenuineO {ℓ : ℕ} (D : RCData ℓ) : Prop where
  /-- `E_ℓ` is elliptic (definition) -/
  elliptic : (Ecurve ℓ).IsElliptic
  /-- PRINT + GLUE: Milne, *Arithmetic Duality Theorems*, Theorem I.2.8 (quoted at its
  definition); the reading of the printed bound and the comparison with the cochain model are
  GLUE (tex 3470–3487) -/
  milne : MilneADT_I_2_8
  /-- ELLIOT-uncited classical + GLUE: Iwasawa 1955, the tame quotient, joined with the splitting
  over the wild inertia (tex 3470–3480) -/
  iwasawa : IwasawaGenerators
  /-- the primes of `2N` lie in the fixed support (stated by the text, tex 2678–2680, 4234–4237;
  not recorded in `RCData`; it follows from lane E1's `LevelPrimesBad` (GLUE: Carayol) and
  `PreDataSpec.support_base`, `hS2N_of_levelPrimesBad`) -/
  hS2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ D.S
  /-- the coefficient datum `quadTateCoef ℓ s₀` (`K = ℚ(s₀)`, `s₀² = k`; lane E2's
  `exists_leafCoef`) with Cai–Chen–Liu (Trans. AMS 370 (2018), Theorem 2.15; GLUE: read through the
  modular parametrization and joined with lane E2's full anchor; tex 2914–2936); per final family
  the companion facts of `k` (ELLIOT: the facts of `RCSteps.companion` for the final companion,
  tex 2595–2603; a discharge chooses that companion in both branches), one nonprincipal
  ultrafilter (tex 4401–4404), one moving character (lane RC0's `GenuineFamilyMovingCharacter`;
  tex 2729–2737, 3500–3702) with moving supports exactly the places above the moving primes (lane
  E2's `exists_familyCoef` (per admissible family, with exact moving supports, from
  `RCSteps.companion`, `hS2N`, `SerreThm3` and `CMjInteger`; it does not produce `hrk`)) and moving
  primes not dividing `k` (definition: stated by the text,
  tex 2920–2921, 4268–4270); at every address an oriented presentation (tex 2720–2760,
  2778–2795, 3455–3498, 4142–4146), the places of the conductor's primes `q` with `λ_q(x) = 1` and
  the places above `3ℓ` in the stage supports (definitions: stated by the text, tex 3455–3463,
  2729–2741; the latter a formalization requirement for good reduction), no step prime `3`
  (definition: a formalization requirement of `q ∤ 6 d N D_K`, tex 2920–2921; derivable from
  admissibility and `PreDataSpec.support_base`), and the genuine
  stage chains with lane E2's classes (data, ELLIOT, GLUE; the retention is free, so the paired
  functionals are free; given `hprim`, `htildeE` is exactly the target; tex 4142–4194,
  4385–4451) -/
  chains : ∃ (s₀ : ZInQ.Manuscript.RC.PrintsArith.Qbar)
    (_ : s₀ ^ 2 = algebraMap ℚ ZInQ.Manuscript.RC.PrintsArith.Qbar D.kfin)
    (C : TateCoef (Ecurve ℓ)) (_ : C = quadTateCoef ℓ s₀) (cp : CSTParam (Ecurve ℓ))
    (emb : ZInQ.Manuscript.RC.PrintsArith.Qbar →ₐ[ℚ] ℂ)
    (κ : ZInQ.Manuscript.RC.PrintsArith.Qbar ≃ₐ[ℚ] AlgebraicClosure C.K)
    (print : CCLThm2_15Applied (Ecurve ℓ) (FullAnchor (Ecurve ℓ) C.K cp emb κ)),
    ∀ Co Ce : ℤ, ∀ F : Family, ∀ hF : D.FinalFamilyAt Co Ce F,
      ∃ (hk : D.kfin < 0 ∧ Squarefree D.kfin ∧ D.kfin % 4 = 1) (U : Ultrafilter ℕ)
        (hU : (U : Filter ℕ) ≤ cofinite) (G : GenuineFamilyMovingCharacter C.K ℓ F.Q)
        (hEq : ∀ i, G.C.Sr (G.r i) =
          {u : HeightOneSpectrum (𝓞 C.K) | ((G.r i : ℤ) : 𝓞 C.K) ∈ u.asIdeal})
        (hrk : ∀ s, ¬ ((G.r s : ℕ) : ℤ) ∣ D.kfin),
        ∀ x : Addr F.b, ∃ (O : OrientedPresentation C D F x G)
          (_ : ∀ s, DecidableEq (Places C.K ((O.toStaged hk.1 hEq).S₀ s))) (Gs : Set ℕ)
          (hQS0 : ∀ s, ∀ q ∈ F.Q, F.lam q x = 1 → ∀ v : HeightOneSpectrum (𝓞 C.K),
            ((q : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ (O.toStaged hk.1 hEq).S₀ s)
          (hQ3 : ∀ q ∈ unusedAt F x, q ≠ 3)
          (h3ℓ : ∀ s, ∀ v : HeightOneSpectrum (𝓞 C.K), ((3 * ℓ : ℕ) : 𝓞 C.K) ∈ v.asIdeal →
            v ∈ (O.toStaged hk.1 hEq).S₀ s),
          Nonempty (GenuineStageSTUS (O.toStaged hk.1 hEq) milne iwasawa
            genuineCochainsInjective_proved U hU Gs
            (e2ProviderOnS (O.toStaged hk.1 hEq)
              (actualInputsO (O.toStaged hk.1 hEq) (Gs := Gs) cp emb κ print hk hF.1 hS2N hrk
                hQS0 O.hpidx hQ3 h3ℓ)))

/-- **The leaf on the staged presentation from the oriented leaf with the built inputs**
(tex 2729–2737, 2778–2795, 2914–2936, 4142–4194, 4385–4451): the staged presentation of the
oriented one and the inputs `actualInputsO`. Kind: PROVED. -/
theorem commonCoordinateInputsGenuineS_of_O {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuineO D) : CommonCoordinateInputsGenuineS D := by
  obtain ⟨hE, h28, hI, hS2N, s₀, hs₀, C, hC, cp, emb, κ, print, hch⟩ := h
  refine ⟨hE, h28, hI, C, fun Co Ce F hF => ?_⟩
  obtain ⟨hk, U, hU, G, hEq, hrk, hx⟩ := hch Co Ce F hF
  refine ⟨U, hU, G, fun x => ?_⟩
  obtain ⟨O, hdec, Gs, hQS0, hQ3, h3ℓ, ⟨S⟩⟩ := hx x
  exact ⟨O.toStaged hk.1 hEq, hdec, Gs, _, ⟨S⟩⟩

/-- **The current leaf from the oriented leaf with the built inputs** (tex 4142–4194,
4385–4451): the replacement of `CommonCoordinateInputsNF` in the leaves. Kind: PROVED. -/
theorem commonCoordinateInputsNF_of_genuineO {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuineO D) : CommonCoordinateInputsNF D :=
  commonCoordinateInputsNF_of_genuineS (commonCoordinateInputsGenuineS_of_O h)

/-- **(4.7) from the oriented leaf with the built inputs** (tex 4142–4194, 4385–4451):
`RCSteps.common_coordinate`. Kind: PROVED. -/
theorem commonCoordinateTarget_of_genuineO {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuineO D) : CommonCoordinateTarget D :=
  commonCoordinateTarget_of_genuineS (commonCoordinateInputsGenuineS_of_O h)

end ZInQ.Manuscript.RC.Wiring
