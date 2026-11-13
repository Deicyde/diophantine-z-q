import ZInQKernel.Contrib.GZTheta.NewCMProof
import ZInQKernel.Contrib.GZTheta.New32
import ZInQKernel.Contrib.GZTheta.Final
import ZInQKernel.Contrib.GZDecomp.Decomp
import ZInQKernel.Contrib.TYZGenus.RingClassBridge

/-!
# frontier: the top of the chain to `ZInQ.FrozenTarget`, checked over fork main

`frozenTarget_of_open_main` derives `ZInQ.FrozenTarget` from H (`ZInQ.SixContactMin`), the open
TYZ Props of the finest reduction in a Contrib module on fork main
(`RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD`) and the two open GZ Props
(`GZDecomp.FHNonvanishing`, `GZDecomp.GrossZagierHeegner`).

`newCM` and `heckeThetaNewform` are verbatim copies of task atkin-li's proofs
(`ZInQKernel/Contrib/GZTheta/NewCMFinal.lean`, branch wip/atkin-li 6f77abb1), recompiled here
against fork main's modules (NewCMFinal imports only `NewCMProof` and `New32`, which are the same
on fork main), in the namespace `ZInQ.GZTheta.Frontier` so that they do not clash with atkin-li's.
-/

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 ModularForm Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace ZInQ.GZTheta.Frontier

open ZInQ.Contrib.HeckeFE ZInQ.GZDecomp

/-- **Newness of the theta series of `ψ_d` at level `32 d²`.** -/
theorem newCM : NewCM := by
  intro d _ hd4 hsq F hF
  have hc : ∀ n, (qExpansion 1 (cmForm etaForm32 d)).coeff n = heckeCoeff d n :=
    qExpansion_cmForm_coeff qExpansion_etaForm32_coeff d
  have hFeq : F = cmForm etaForm32 d := by
    apply CuspForm.qExpansion_injective one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _)
    ext n
    show (qExpansion 1 F).coeff n = (qExpansion 1 (cmForm etaForm32 d)).coeff n
    rw [hF, hc]
  rw [hFeq]
  obtain ⟨E, hE, hEχ⟩ := exists_eigenformAway_cmForm qExpansion_etaForm32_coeff d hd4 hsq
  obtain ⟨M, hM0, hMN, g, hgχ, hgev⟩ :=
    Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul
      E.mem_charSpace E.ne_zero (a := fun p hp hpN => E.eigenvalue ⟨p, hp.pos⟩ hpN)
      (fun p hp hpN => E.heckeTCuspNat_eq_eigenvalue_smul hp hpN)
  have hg1 : g.χ = 1 := by
    rw [hEχ] at hgχ
    ext u
    obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hMN u
    have := congrArg (fun φ => ((φ v : ℂˣ) : ℂ)) hgχ
    simpa using this
  have hE1 : (qExpansion 1 E.toCuspForm).coeff 1 = 1 := by rw [hE, hc 1, heckeCoeff_one]
  have hgood : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * d → coeff g p = heckeCoeff d p := by
    intro p hp hp2d
    have hpN : Nat.Coprime p (32 * d ^ 2) := by
      by_contra h
      exact hp2d ((dvd_two_mul_iff_not_coprime hp).mpr h)
    have e1 := g.qExpansion_coeff_eq_eigenvalue g.isNorm ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hMN)
    have e2 := E.qExpansion_coeff_eq_eigenvalue hE1 ⟨p, hp.pos⟩ hpN
    rw [hE, hc] at e2
    change coeff g p = _ at e1
    rw [e1, hgev p hp hpN]
    exact e2.symm
  have hMeq : M = 32 * d ^ 2 := level_eq_of_assoc hd4 hsq hMN g hg1 hgood
  subst hMeq
  have hmem : cmForm etaForm32 d ∈ cuspFormCharSpace 2 g.χ := by
    rw [hg1, ← hEχ, ← hE]; exact E.mem_charSpace
  have hfg := g.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul hmem
    (fun p hp hpN => by
      have := E.heckeTCuspNat_eq_eigenvalue_smul hp hpN
      rw [hE] at this
      rw [this, ← hgev p hp hpN])
  rw [hfg, hc 1, heckeCoeff_one, one_smul]
  exact g.isNew

/-- **The leaf `HeckeThetaNewform`** (L1 of gz-decomp), with no hypotheses. -/
theorem heckeThetaNewform : ZInQ.GZDecomp.HeckeThetaNewform :=
  heckeThetaNewform_of_newCM newCM

end ZInQ.GZTheta.Frontier

namespace ZInQ.Frontier

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus.Package ZInQ.Contrib.TYZGenus.RingClass

/-- **The top of the chain over fork main.** `ZInQ.FrozenTarget` from H, the open Props of the
finest TYZ reduction in a Contrib module on fork main, and the two open GZ Props. -/
theorem frozenTarget_of_open_main (hH : ZInQ.SixContactMin)
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hcm : ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition ringClassFieldD)
    (hs : TYZSigmaFixesZn) (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves hH
    (ZInQ.Contrib.TYZGenus.RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD
      h11 h1 h29 hcm hs h318 hG)
    ZInQ.GZTheta.Frontier.heckeThetaNewform hL2 hL3

end ZInQ.Frontier

#print axioms ZInQ.GZTheta.Frontier.newCM
#print axioms ZInQ.GZTheta.Frontier.heckeThetaNewform
#print axioms ZInQ.Frontier.frozenTarget_of_open_main
