import ZInQKernel.Contrib.OneProof.RC.KummerMaps.ActualComplements
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.UrMilneActual

/-!
# Lane RC29 (round 3): the actual local complements with Milne I.2.6 at the unramified places

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer` (tex 3413–3468) and the support
change (tex 3483–3498: the unramified condition at the new places `S − S₀`).

`ActualComplements.lean` proves the local complement criterion for the actual data with the PRINT
`NekovarProp756` (Nekovář 7.5.6 with 7.5.5) at the unramified places `S − S₀`. This file gives the
same results with Milne's theorem instead: `H¹_ur` is its own exact annihilator for unramified
coefficients of order prime to the residue characteristic (Milne, *Arithmetic Duality Theorems*,
2nd ed., Ch. I, Theorem 2.6, p. 30; PRINT `MilneADT_I_2_6`, `UrMilne.lean`). On the actual data the
two prints have the same scope (`|M_i|` is a power of `2`, so "order prime to the residue
characteristic" is `w ∤ 2`, Nekovář's tame case; both need `w ∉ S₀`). The per-place statement at
`w ∈ S − S₀` is `urM_quasiIso_actual` (`UrMilneActual.lean`: Milne's `ℤ`-duality matched to the
`A_i`-duality by the top coefficient of `A_i` as generating character, used only as an annihilator
test, never as the trace, tex 3465–3467).

* `actLPerf_milne`: the per-place local duality map of the actual conditions is a
  quasi-isomorphism at every place of `S`, for every isotropy homotopy (Kummer places: Milne I.2.3
  etc. with Nekovář 5.2.4; full/zero places: no print; unramified places: Milne I.2.6 with
  Nekovář 5.2.4).
* **`actualLocalComplements_milne`**: lane RC26's `OrthogonalComplementsT` for the actual data,
  without `NekovarProp756`.
* `actualSelmerDuality_milne_packet`, **`actualSelmerDuality_milne_of_prints`**: the finite Selmer
  duality for the actual data (`ActLDuality`), for a packet of local traces and from the trace print.

Kinds: PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero`, `MilneADT_I_2_6`,
`NekovarProp524`, for the global duality also `NekovarProp543T` and `NekovarFiniteTraces`; GLUE
`FullTorsion`; ELLIOT `hα`.
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
  (trv : ∀ v : Places K S, (localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
  (htrv : ∀ v z, trv v ((localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)

open scoped Classical in
/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero`, `NekovarProp524` (at the Kummer
places) and `MilneADT_I_2_6` with `NekovarProp524` (at the unramified places), the GLUE
`FullTorsion` and the ELLIOT `hα`. **The per-place local duality map of the actual conditions is a
quasi-isomorphism at every place of `S`**, for every isotropy homotopy; as `actLPerf`, with Milne
I.2.6 in place of Nekovář 7.5.6. -/
theorem actLPerf_milne (hM : MilneLocalTateDualityKummerCharZero) (hM26 : MilneADT_I_2_6)
    (h524 : NekovarProp524 K) (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v)) (v : Places K S)
    (J : LocalTruncIsotropy (actLCondA hS W i s hs hs0 hFull P α hα v).i
      (actLCondB hS W i s hs hs0 hFull P α hα v).i
      (orthGaloisPair K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀) v)) :
    QuasiIso (GHom.toCC (orthLocalMap (actLCondA hS W i s hs hs0 hFull P α hα v).i
      (actLCondB hS W i s hs hs0 hFull P α hα v).i
      (orthGaloisPair K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀) v) J (trv v)
      (htrv v))) := by
  by_cases hv : v.1 ∈ S₀
  · by_cases hP : v.1 ∈ P
    · exact actLPerf_congr _ _ (actLCondA_of_P hS W i s hs hs0 hFull P α hα hv hP)
        (actLCondB_of_P hS W i s hs hs0 hFull P α hα hv hP) (trv v) (htrv v)
        (fun J₀ => kummerPerPlace_perf_of_milne hS W i s hs hs0 hFull v hμ₀ α hM h524 hK hSfin h2₀
          (cycloInfl_isCyclotomicTwist_tate1 hS i hμ₀) (hα v.1 hP) (trv v) (htrv v) (htrv2 v) J₀) J
    · exact actLPerf_congr _ _ (actLCondA_of_notP hS W i s hs hs0 hFull P α hα hv hP)
        (actLCondB_of_notP hS W i s hs hs0 hFull P α hα hv hP) (trv v) (htrv v)
        (actLPerf_full_zero _ _ v (trv v) (htrv v)) J
  · exact actLPerf_congr _ _ (actLCondA_of_notS0 hS W i s hs hs0 hFull P α hα hv)
      (actLCondB_of_notS0 hS W i s hs hs0 hFull P α hα hv) (trv v) (htrv v)
      (fun J₀ => urM_quasiIso_actual (hS := hS) (i := i) (hμ₀ := hμ₀) hM26 h524 hK hS₀fin hSfin h2₀
        W α hFull v hv J₀ (trv v) (htrv v) (htrv2 v)) J

/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero` (Milne, *ADT* 2nd ed., I.2.3,
I.3.2, I.3.4, I.3.5), `MilneADT_I_2_6` (Milne, *ADT* 2nd ed., I.2.6, p. 30) and `NekovarProp524`
(Nekovář 5.2.4), the GLUE `FullTorsion`, the ELLIOT `hα` and the traces of lane RC26 (tex
2754–2756, 2810–2816, 3080–3085, 3413–3468, 3483–3498). **The local complement criterion for the
actual Selmer data at every place of `S`, with Milne I.2.6 at the unramified places**: lane RC26's
`OrthogonalComplementsT` (the hypothesis `horth` of `genuineSelmerDualityT`) for the actual
conditions and their orthogonal conditions; the conclusion of `actualLocalComplements` without the
print `NekovarProp756`. -/
theorem actualLocalComplements_milne [Fintype (Places K S)]
    (hM : MilneLocalTateDualityKummerCharZero) (hM26 : MilneADT_I_2_6) (h524 : NekovarProp524 K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v))
    (tr : (actLTT hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((actLTT hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (InflMod hS (Tate1 (Acoef i) hμ₀))).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v)) :
    OrthogonalComplementsT K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀)
      (actLDeltaA hS W i s hs hs0 hFull P α hα) (actLDeltaB hS W i s hs hs0 hFull P α hα)
      (actLTrunc hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2) tr htr :=
  orthogonalComplementsT_ofCondAt K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀)
    (actLCondA hS W i s hs hs0 hFull P α hα) (actLCondB hS W i s hs hs0 hFull P α hα)
    (actLIso hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM htrv2) trv htrv tr htr hsum
    (fun v => actLPerf_milne hS W i s hs hs0 hFull P α hμ₀ hα trv htrv hM hM26 h524 hK hSfin hS₀fin
      h2₀ htrv2 v _)

/-- PROVED from the PRINTs of `actualLocalComplements_milne` and `NekovarProp543T`. **The actual
local complements and the finite Selmer duality for a packet of local traces** and a global trace
normalized by it, inducing `H³_c ≅ A_i`, with Milne I.2.6 at the unramified places. -/
theorem actualSelmerDuality_milne_packet [Fintype (Places K S)]
    (hM : MilneLocalTateDualityKummerCharZero) (hM26 : MilneADT_I_2_6) (h524 : NekovarProp524 K)
    (h543 : NekovarProp543T K) (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (tr : (actLTT hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((actLTT hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso).d 2 3 rfl
      z) = 0)
    (hN : L.Normalizes tr) (h3 : InducesIsoH3 tr) :
    ActLDuality hS W i s hs hs0 hFull P α hμ₀ hα hM L tr htr := by
  have hloc := actualLocalComplements_milne hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM hM26
    h524 hK hSfin hS₀fin h2₀ L.iso tr htr hN
  have : Finite (MinS hS W i α) := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  have : Finite (MinS hS W i (charInv α)) := inferInstanceAs (Finite (Mcoef K S₀ W i (charInv α)))
  exact ⟨hloc, genuineSelmerDualityT K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀)
    (actLDeltaA hS W i s hs hs0 hFull P α hα) (actLDeltaB hS W i s hs hs0 hFull P α hα)
    (actLTrunc hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso) tr htr h543 2
    (nekovarFiniteSetting_acoef K hK S hSfin (fun v hv => hS (h2₀ v hv)) i)
    (weilPairingM_bijective (S := S₀) W hμ₀ (Acoef i) α hFull)
    (weilPairingM_flip_bijective (S := S₀) W hμ₀ (Acoef i) α hFull)
    (cycloInfl_isCyclotomicTwist_tate1 hS i hμ₀) h3 hloc⟩

/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero`, `MilneADT_I_2_6`,
`NekovarProp524`, `NekovarProp543T` and `NekovarFiniteTraces`, the GLUE `FullTorsion` and the ELLIOT
`hα`. **The actual local complements and the finite Selmer duality, with the traces of the packet
and Milne I.2.6 at the unramified places**: as `actualSelmerDuality_of_prints`, without
`NekovarProp756`. No per-place input is left. -/
theorem actualSelmerDuality_milne_of_prints [Fintype (Places K S)]
    (hM : MilneLocalTateDualityKummerCharZero) (hM26 : MilneADT_I_2_6) (h524 : NekovarProp524 K)
    (h543 : NekovarProp543T K) (hTr : NekovarFiniteTraces K) (hK : IsTotallyComplex K)
    (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∃ (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
      (tr : (actLTT hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso).X 3 →ₗ[Acoef i]
        Acoef i)
      (htr : ∀ z, tr ((actLTT hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso).d 2 3 rfl
        z) = 0),
      InducesIsoH3 tr ∧ L.Normalizes tr ∧ ActLDuality hS W i s hs hs0 hFull P α hμ₀ hα hM L tr htr := by
  have hset := nekovarFiniteSetting_acoef K hK S hSfin (fun v hv => hS (h2₀ v hv)) i
  have hT := cycloInfl_isCyclotomicTwist_tate1 hS i hμ₀
  obtain ⟨L, hL⟩ := @hTr S 2 (Acoef i) _ _ hset _ (InflMod hS (Tate1 (Acoef i) hμ₀)) _ _ _ _ _ _ _ hT
  refine ⟨L, ?_⟩
  have h1 := hL (MinS hS W i α) (MinS hS W i (charInv α))
    (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀)
    (actLDeltaA hS W i s hs hs0 hFull P α hα) (actLDeltaB hS W i s hs hs0 hFull P α hα)
    (actLTrunc hS W i s hs hs0 hFull P α hμ₀ hα L.trv L.htrv₁ hM L.iso)
  exact h1.imp fun tr => Exists.imp fun htr hP => ⟨hP.1, hP.2,
    actualSelmerDuality_milne_packet hS W i s hs hs0 hFull P α hμ₀ hα hM hM26 h524 h543 hK hSfin
      hS₀fin h2₀ L tr htr hP.2 hP.1⟩

end ZInQ.Manuscript.RC.KummerMaps
