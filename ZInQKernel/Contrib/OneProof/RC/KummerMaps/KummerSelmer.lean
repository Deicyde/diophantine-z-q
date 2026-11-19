import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerMilne
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.CycloInfl

/-!
# Lane RC29 (round 2, item 1): the Kummer Selmer duality with the Kummer places discharged

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality` (tex 2761–2830) with Lemma
`ex:arith-local-kummer` (tex 3413–3468), (4.3) at tex 3455–3463 and tex 3483–3498.

Round 1 proved `OrthogonalComplementsT` for the actual conditions `kummerCondA`, `kummerCondB` —
the genuine Kummer condition at the places of `P`, given conditions at the other places of `S₀`,
the unramified condition at `S − S₀` — from per-place inputs `hiso`, `hperf` at every place of
`S₀` (`orthogonalComplementsT_kummerCond`, `OrthKummer.lean`). At the places of `P` these inputs
were ELLIOT. This file discharges them there by `KummerMilne.lean` (PRINTs
`MilneLocalTateDualityKummerCharZero`, `NekovarProp524`), keeping them as hypotheses only at the
places of `S₀ − P`, whose conditions are not Kummer conditions:

* `kummerCond_isotropic_of_milne`: the isotropy input at every place of `S₀`;
* `kummerCond_perf_of_milne`: the per-place quasi-isomorphism at every place of `S₀`;
* **`orthogonalComplementsT_kummerCond_of_milne`**: `OrthogonalComplementsT` for the actual
  Kummer-type conditions;
* **`orthSelmerDuality_kummerCond_of_milne`**: the finite Selmer duality
  `C_U(M_i) ≃ RHom(C_{U⊥}(M_i^*(1)), A_i)[−3]` for them, with the round-1 GLUE `hT` now PROVED
  (`cycloInfl_isCyclotomicTwist_tate1`).

Kinds: PROVED from the named PRINTs (`MilneLocalTateDualityKummerCharZero`, `NekovarProp524`,
`NekovarProp756`, `NekovarProp543T`), the GLUE `FullTorsion` (lane RC28), the trace hypotheses of
lane RC26 (Nekovář 5.4.1; `InducesIsoH2`, `hsum`, `InducesIsoH3`), and the per-place inputs at the
non-Kummer places of `S₀`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.Duality (MilneLocalTateDualityKummerCharZero LocalTruncIsotropy)
open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  (P : Set (HeightOneSpectrum (𝓞 K)))
  [NeZero i] [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α] (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  (hα : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)
  (c : ∀ v : Places K S, v.1 ∈ S₀ → v.1 ∉ P → CondAt K S (Acoef i) (MinS hS W i α) v)
  (c' : ∀ v : Places K S, v.1 ∈ S₀ → v.1 ∉ P → CondAt K S (Acoef i) (MinS hS W i (charInv α)) v)
  (hc : ∀ v hv hP, OrthConcentratedAt (c v hv hP))
  (hc' : ∀ v hv hP, OrthConcentratedAt (c' v hv hP))
  (trv : ∀ v : Places K S, (localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
  (htrv : ∀ v z, trv v ((localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)

/-- PROVED. At a place of `P`, the condition `kummerCondA` is the actual Kummer condition. -/
theorem kummerCondA_of_mem {v : Places K S} (hv : v.1 ∈ S₀) (hP : v.1 ∈ P) :
    kummerCondA hS W i s hs hs0 hFull P α hα c v hv =
      actualKummerAtS hS W i s hs hs0 α hFull v (hα v.1 hP) := by
  unfold kummerCondA kummerCondFun
  exact dite_eq_left hP

/-- PROVED. At a place of `P`, the condition `kummerCondB` is the actual Kummer condition of the
dual module. -/
theorem kummerCondB_of_mem {v : Places K S} (hv : v.1 ∈ S₀) (hP : v.1 ∈ P) :
    kummerCondB hS W i s hs hs0 hFull P α hα c' v hv =
      actualKummerAtS hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv (hα v.1 hP)) := by
  unfold kummerCondB kummerCondFun
  exact dite_eq_left hP

/-- PROVED. Outside `P`, `kummerCondA` is the given condition. -/
theorem kummerCondA_of_not_mem {v : Places K S} (hv : v.1 ∈ S₀) (hP : v.1 ∉ P) :
    kummerCondA hS W i s hs hs0 hFull P α hα c v hv = c v hv hP := by
  unfold kummerCondA kummerCondFun
  exact dite_eq_right hP

/-- PROVED. Outside `P`, `kummerCondB` is the given condition. -/
theorem kummerCondB_of_not_mem {v : Places K S} (hv : v.1 ∈ S₀) (hP : v.1 ∉ P) :
    kummerCondB hS W i s hs hs0 hFull P α hα c' v hv = c' v hv hP := by
  unfold kummerCondB kummerCondFun
  exact dite_eq_right hP

include htrv in
/-- PROVED from the PRINT `MilneLocalTateDualityKummerCharZero` at the places of `P` (tex
3418–3419) and the hypothesis `hisoRest` at the other places of `S₀`. **The isotropy inputs of
the actual Kummer-type conditions.** -/
theorem kummerCond_isotropic_of_milne (hM : MilneLocalTateDualityKummerCharZero)
    (htrvP : ∀ v : Places K S, v.1 ∈ P → InducesIsoH2 (trv v))
    (hisoRest : ∀ v hv (hP : v.1 ∉ P), OrthIsotropicAt
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (c v hv hP) (c' v hv hP)) :
    ∀ v hv, OrthIsotropicAt (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (kummerCondA hS W i s hs hs0 hFull P α hα c v hv)
      (kummerCondB hS W i s hs hs0 hFull P α hα c' v hv) := by
  intro v hv
  by_cases hP : v.1 ∈ P
  · rw [kummerCondA_of_mem hS W i s hs hs0 hFull P α hα c hv hP,
      kummerCondB_of_mem hS W i s hs hs0 hFull P α hα c' hv hP]
    exact kummerPerPlace_isotropic_of_milne hS W i s hs hs0 hFull v hμ₀ α hM (hα v.1 hP) (trv v)
      (htrv v) (htrvP v hP)
  · rw [kummerCondA_of_not_mem hS W i s hs hs0 hFull P α hα c hv hP,
      kummerCondB_of_not_mem hS W i s hs hs0 hFull P α hα c' hv hP]
    exact hisoRest v hv hP

/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero` and `NekovarProp524` at the
places of `P` (tex 3418–3419, 3442–3450) and the hypothesis `hperfRest` at the other places of
`S₀`. **The per-place quasi-isomorphisms of the actual Kummer-type conditions**, with the zero
isotropy homotopies, in the form of the round-1 hypothesis `hperf` of
`orthogonalComplementsT_kummerCond`. -/
theorem kummerCond_perf_of_milne (hM : MilneLocalTateDualityKummerCharZero)
    (h524 : NekovarProp524 K) (hK : IsTotallyComplex K) (hSfin : S.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (htrvP : ∀ v : Places K S, v.1 ∈ P → InducesIsoH2 (trv v))
    (hisoRest : ∀ v hv (hP : v.1 ∉ P), OrthIsotropicAt
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (c v hv hP) (c' v hv hP))
    (hperfRest : ∀ v hv (hP : v.1 ∉ P), QuasiIso (GHom.toCC (orthLocalMap (c v hv hP).i
      (c' v hv hP).i (orthUrPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α)
        (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α) v)
      (orthZeroIsotropy (hc v hv hP) (hc' v hv hP) (hisoRest v hv hP)) (trv v) (htrv v)))) :
    ∀ (v : Places K S) (hv : v.1 ∈ S₀), QuasiIso (GHom.toCC (orthLocalMap
      (kummerCondA hS W i s hs hs0 hFull P α hα c v hv).i
      (kummerCondB hS W i s hs hs0 hFull P α hα c' v hv).i
      (orthUrPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α)
        (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α) v)
      (orthZeroIsotropy (kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc v hv)
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
          (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc' v hv)
        (kummerCond_isotropic_of_milne hS W i s hs hs0 hFull P α hμ₀ hα c c' trv htrv hM htrvP
          hisoRest v hv))
      (trv v) (htrv v))) := by
  intro v hv
  by_cases hP : v.1 ∈ P
  · have hAe := kummerCondA_of_mem hS W i s hs hs0 hFull P α hα c hv hP
    have hBe := kummerCondB_of_mem hS W i s hs hs0 hFull P α hα c' hv hP
    have hA₀ : OrthConcentratedAt (actualKummerAtS hS W i s hs hs0 α hFull v (hα v.1 hP)) := by
      rw [← hAe]
      exact kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc v hv
    have hB₀ : OrthConcentratedAt (actualKummerAtS hS W i s hs hs0 (charInv α) hFull v
        (isLocallyQuadAt_charInv (hα v.1 hP))) := by
      rw [← hBe]
      exact kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
        (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc' v hv
    have hi₀ := kummerPerPlace_isotropic_of_milne hS W i s hs hs0 hFull v hμ₀ α hM (hα v.1 hP)
      (trv v) (htrv v) (htrvP v hP)
    exact orthQuasiIso_congr _ _ hAe hBe _ (orthZeroIsotropy hA₀ hB₀ hi₀) (trv v) (htrv v) hA₀ hB₀
      (kummerPerPlace_perf_of_milne hS W i s hs hs0 hFull v hμ₀ α hM h524 hK hSfin h2₀
        (cycloInfl_isCyclotomicTwist_tate1 hS i hμ₀) (hα v.1 hP) (trv v) (htrv v) (htrvP v hP) _)
  · exact orthQuasiIso_congr _ _ (kummerCondA_of_not_mem hS W i s hs hs0 hFull P α hα c hv hP)
      (kummerCondB_of_not_mem hS W i s hs hs0 hFull P α hα c' hv hP) _
      (orthZeroIsotropy (hc v hv hP) (hc' v hv hP) (hisoRest v hv hP)) (trv v) (htrv v)
      (hc v hv hP) (hc' v hv hP) (hperfRest v hv hP)

/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero`, `NekovarProp524`,
`NekovarProp756`, the GLUE `FullTorsion`, the trace hypotheses of lane RC26 and the per-place
inputs at the non-Kummer places of `S₀` (tex 2761–2830, 3413–3423, 3483–3498).
**`OrthogonalComplementsT` for the actual Kummer-type conditions**: the round-1 theorem
`orthogonalComplementsT_kummerCond` with its ELLIOT inputs at the Kummer places `P` discharged. -/
theorem orthogonalComplementsT_kummerCond_of_milne [Fintype (Places K S)]
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K) (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v))
    (hisoRest : ∀ v hv (hP : v.1 ∉ P), OrthIsotropicAt
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (c v hv hP) (c' v hv hP))
    (hperfRest : ∀ v hv (hP : v.1 ∉ P), QuasiIso (GHom.toCC (orthLocalMap (c v hv hP).i
      (c' v hv hP).i (orthUrPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α)
        (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α) v)
      (orthZeroIsotropy (hc v hv hP) (hc' v hv hP) (hisoRest v hv hP)) (trv v) (htrv v))))
    (tr : (galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (kummerCondA hS W i s hs hs0 hFull P α hα c)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α))
          (kummerCondB hS W i s hs hs0 hFull P α hα c')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α)
        (kummerCondA hS W i s hs hs0 hFull P α hα c) (kummerCondB hS W i s hs hs0 hFull P α hα c')
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc)
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
          (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc')
        (kummerCond_isotropic_of_milne hS W i s hs hs0 hFull P α hμ₀ hα c c' trv htrv hM
          (fun v _ => htrv2 v) hisoRest))).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (kummerCondA hS W i s hs hs0 hFull P α hα c)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α))
          (kummerCondB hS W i s hs hs0 hFull P α hα c')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α)
        (kummerCondA hS W i s hs hs0 hFull P α hα c) (kummerCondB hS W i s hs hs0 hFull P α hα c')
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc)
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
          (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc')
        (kummerCond_isotropic_of_milne hS W i s hs hs0 hFull P α hμ₀ hα c c' trv htrv hM
          (fun v _ => htrv2 v) hisoRest))).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (InflMod hS (Tate1 (Acoef i) hμ₀))).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v)) :
    OrthogonalComplementsT K (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (kummerCondA hS W i s hs hs0 hFull P α hα c)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α))
          (kummerCondB hS W i s hs hs0 hFull P α hα c')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α)
        (kummerCondA hS W i s hs hs0 hFull P α hα c) (kummerCondB hS W i s hs hs0 hFull P α hα c')
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc)
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
          (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc')
        (kummerCond_isotropic_of_milne hS W i s hs hs0 hFull P α hμ₀ hα c c' trv htrv hM
          (fun v _ => htrv2 v) hisoRest)) tr htr :=
  orthogonalComplementsT_kummerCond hS W i s hs hs0 hFull P α hμ₀ hα c c' hc hc' h756 hK hS₀fin h2₀
    (kummerCond_isotropic_of_milne hS W i s hs hs0 hFull P α hμ₀ hα c c' trv htrv hM
      (fun v _ => htrv2 v) hisoRest) trv htrv (fun v _ => htrv2 v)
    (kummerCond_perf_of_milne hS W i s hs hs0 hFull P α hμ₀ hα c c' hc hc' trv htrv hM h524 hK hSfin
      h2₀ (fun v _ => htrv2 v) hisoRest hperfRest) tr htr hsum

/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero`, `NekovarProp524`,
`NekovarProp756`, `NekovarProp543T` (Nekovář 5.4.3 with 6.3–6.4), the GLUE `FullTorsion`, the trace
hypotheses of lane RC26 and the per-place inputs at the non-Kummer places of `S₀` (tex 2761–2830,
3413–3423, 3455–3463, 3483–3498). **The finite Selmer duality for the actual Kummer-type
conditions** `C_U(M_i) ≃ RHom(C_{U⊥}(M_i^*(1)), A_i)[−3]`: lane RC26's Selmer duality map is a
quasi-isomorphism. The round-1 GLUE `hT` is PROVED (`cycloInfl_isCyclotomicTwist_tate1`) and the
ELLIOT inputs at the Kummer places are discharged. -/
theorem orthSelmerDuality_kummerCond_of_milne [Fintype (Places K S)]
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K) (h543 : NekovarProp543T K)
    (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v))
    (hisoRest : ∀ v hv (hP : v.1 ∉ P), OrthIsotropicAt
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (c v hv hP) (c' v hv hP))
    (hperfRest : ∀ v hv (hP : v.1 ∉ P), QuasiIso (GHom.toCC (orthLocalMap (c v hv hP).i
      (c' v hv hP).i (orthUrPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α)
        (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α) v)
      (orthZeroIsotropy (hc v hv hP) (hc' v hv hP) (hisoRest v hv hP)) (trv v) (htrv v))))
    (tr : (galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (kummerCondA hS W i s hs hs0 hFull P α hα c)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α))
          (kummerCondB hS W i s hs hs0 hFull P α hα c')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α)
        (kummerCondA hS W i s hs hs0 hFull P α hα c) (kummerCondB hS W i s hs hs0 hFull P α hα c')
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc)
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
          (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc')
        (kummerCond_isotropic_of_milne hS W i s hs hs0 hFull P α hμ₀ hα c c' trv htrv hM
          (fun v _ => htrv2 v) hisoRest))).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (kummerCondA hS W i s hs hs0 hFull P α hα c)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α))
          (kummerCondB hS W i s hs hs0 hFull P α hα c')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α)
        (kummerCondA hS W i s hs hs0 hFull P α hα c) (kummerCondB hS W i s hs hs0 hFull P α hα c')
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc)
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
          (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc')
        (kummerCond_isotropic_of_milne hS W i s hs hs0 hFull P α hμ₀ hα c c' trv htrv hM
          (fun v _ => htrv2 v) hisoRest))).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (InflMod hS (Tate1 (Acoef i) hμ₀))).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v))
    (htr3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (kummerCondA hS W i s hs hs0 hFull P α hα c)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α))
          (kummerCondB hS W i s hs hs0 hFull P α hα c')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α)
        (kummerCondA hS W i s hs hs0 hFull P α hα c) (kummerCondB hS W i s hs hs0 hFull P α hα c')
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc)
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
          (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc')
        (kummerCond_isotropic_of_milne hS W i s hs hs0 hFull P α hμ₀ hα c c' trv htrv hM
          (fun v _ => htrv2 v) hisoRest))) tr htr)) :=
  orthSelmerDuality_urOutside hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α)
    (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α) (kummerCondA hS W i s hs hs0 hFull P α hα c)
    (kummerCondB hS W i s hs hs0 hFull P α hα c')
    (kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc)
    (kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
      (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc')
    (kummerCond_isotropic_of_milne hS W i s hs hs0 hFull P α hμ₀ hα c c' trv htrv hM
      (fun v _ => htrv2 v) hisoRest) trv htrv h543 h756 2
    (nekovarFiniteSetting_acoef K hK S₀ hS₀fin h2₀ i)
    (nekovarFiniteSetting_acoef K hK S hSfin (fun v hv => hS (h2₀ v hv)) i)
    (weilPairingM_bijective (S := S₀) W hμ₀ (Acoef i) α hFull)
    (weilPairingM_flip_bijective (S := S₀) W hμ₀ (Acoef i) α hFull)
    (isCyclotomicTwist_tate1 (Acoef i) hμ₀) (cycloInfl_isCyclotomicTwist_tate1 hS i hμ₀)
    (fun v _ => htrv2 v)
    (kummerCond_perf_of_milne hS W i s hs hs0 hFull P α hμ₀ hα c c' hc hc' trv htrv hM h524 hK hSfin
      h2₀ (fun v _ => htrv2 v) hisoRest hperfRest) tr htr hsum htr3

end ZInQ.Manuscript.RC.KummerMaps
