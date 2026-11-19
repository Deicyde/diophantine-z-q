import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerSelmer
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.TracePacket

/-!
# Lane RC29 (round 2, items 1–2): the Kummer Selmer duality from the prints

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality` (tex 2761–2830), Lemma
`ex:arith-local-kummer` (tex 3413–3468; tex 3454–3456: "The global Selmer duality theorem
[Nekovář, Sections 5.1, 5.2.4, 5.4.3 and 6.3.4] is applied to these actual local maps and
homotopies"), tex 3483–3498.

`KummerSelmer.lean` proves the finite Selmer duality for the actual Kummer-type conditions from
given local traces `tr_v` and a given global trace `tr` normalized by them (lane RC26's
hypotheses). This file takes the traces from the trace packet of `TracePacket.lean` (PRINT
`NekovarFiniteTraces`, Nekovář 5.1.3, 5.1.5, 5.2.1, 5.4.1): one family `L` of local traces for
`A_i(1)` over `G_{K,S}` and, for the actual data, a global trace normalized by `L`.

* `kTrIso`: the isotropy data of the actual Kummer-type conditions for a packet `L`.
* **`orthSelmerDuality_kummerCond_of_prints`** (PROVED from PRINTs): there are local traces `L`
  and a global trace `tr` (killing coboundaries, inducing `H³_c ≅ A_i`, normalized by `L`) for which
  lane RC26's Selmer duality map of the actual Kummer-type conditions is a quasi-isomorphism.

Kinds: PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero`, `NekovarProp524`,
`NekovarProp543T`, `NekovarProp756`, `NekovarFiniteTraces`, the GLUE `FullTorsion` (lane RC28), and
the per-place inputs at the non-Kummer places of `S₀` (for every packet of local traces).
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

/-- Definition. The actual Kummer-type local conditions on `M_i(α)` (`kummerCondA` at `S₀`, the
unramified condition at `S − S₀`), in the format of lane RC26's Galois Selmer data. -/
def kTrA : GaloisLocalConditions K S (Acoef i) (MinS hS W i α) :=
  ofCondAt K S (Acoef i) (MinS hS W i α)
    (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (kummerCondA hS W i s hs hs0 hFull P α hα c))

/-- Definition. The actual Kummer-type local conditions on `M_i(α⁻¹)`. -/
def kTrB : GaloisLocalConditions K S (Acoef i) (MinS hS W i (charInv α)) :=
  ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
    (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α))
      (kummerCondB hS W i s hs hs0 hFull P α hα c'))

/-- Definition. **The isotropy data of the actual Kummer-type conditions** for a packet `L` of
local traces: the zero homotopies at `S₀` (isotropy from `kummerCond_isotropic_of_milne` with the
traces of `L`) and the unramified data at `S − S₀`. -/
def kTrIso (hM : MilneLocalTateDualityKummerCharZero)
    (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (hisoRest : ∀ v hv (hP : v.1 ∉ P), OrthIsotropicAt
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (c v hv hP) (c' v hv hP)) :
    GaloisTruncIsotropyData K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (kTrA hS W i s hs hs0 hFull P α hα c) (kTrB hS W i s hs hs0 hFull P α hα c') :=
  orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α)
    (kummerCondA hS W i s hs hs0 hFull P α hα c) (kummerCondB hS W i s hs hs0 hFull P α hα c')
    (kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc)
    (kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
      (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc')
    (kummerCond_isotropic_of_milne hS W i s hs hs0 hFull P α hμ₀ hα c c' L.trv L.htrv₁ hM
      (fun v _ => L.iso v) hisoRest)

/-- Definition. The truncated compact cone of the actual Kummer-type data for a packet `L`. -/
abbrev kTrTT (hM : MilneLocalTateDualityKummerCharZero)
    (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (hisoRest : ∀ v hv (hP : v.1 ∉ P), OrthIsotropicAt
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (c v hv hP) (c' v hv hP)) :=
  galoisCompactTT K S (Acoef i)
    (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
    (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
    (kTrA hS W i s hs hs0 hFull P α hα c) (kTrB hS W i s hs hs0 hFull P α hα c')
    (kTrIso hS W i s hs hs0 hFull P α hμ₀ hα c c' hc hc' hM L hisoRest)

/-- PROVED (the restatement of `orthSelmerDuality_kummerCond_of_milne` for the traces of a packet
`L` and a global trace normalized by `L`). -/
theorem orthSelmerDuality_kummerCond_packet [Fintype (Places K S)]
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K) (h543 : NekovarProp543T K)
    (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hisoRest : ∀ v hv (hP : v.1 ∉ P), OrthIsotropicAt
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (c v hv hP) (c' v hv hP))
    (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (hperfRest : ∀ v hv (hP : v.1 ∉ P), QuasiIso (GHom.toCC (orthLocalMap (c v hv hP).i
        (c' v hv hP).i (orthUrPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α)
          (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α) v)
        (orthZeroIsotropy (hc v hv hP) (hc' v hv hP) (hisoRest v hv hP)) (L.trv v) (L.htrv₁ v))))
    (tr : (kTrTT hS W i s hs hs0 hFull P α hμ₀ hα c c' hc hc' hM L hisoRest).X 3 →ₗ[Acoef i]
      Acoef i)
    (htr : ∀ z, tr ((kTrTT hS W i s hs hs0 hFull P α hμ₀ hα c c' hc hc' hM L hisoRest).d 2 3 rfl
      z) = 0)
    (hN : L.Normalizes tr) (h3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (kTrA hS W i s hs hs0 hFull P α hα c) (kTrB hS W i s hs hs0 hFull P α hα c')
      (kTrIso hS W i s hs hs0 hFull P α hμ₀ hα c c' hc hc' hM L hisoRest)) tr htr)) :=
  orthSelmerDuality_kummerCond_of_milne hS W i s hs hs0 hFull P α hμ₀ hα c c' hc hc' L.trv
    L.htrv₁ hM h524 h543 h756 hK hSfin hS₀fin h2₀ L.iso hisoRest hperfRest tr htr hN h3

/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero` (Milne, *Arithmetic Duality
Theorems*, 2nd ed., I.2.3, I.3.2, I.3.4, I.3.5), `NekovarProp524` (Nekovář 5.2.4),
`NekovarProp543T` (5.4.3 with 6.3–6.4), `NekovarProp756` (7.5.6 with 7.5.5) and
`NekovarFiniteTraces` (5.1.3, 5.1.5, 5.2.1, 5.4.1), the GLUE `FullTorsion` (lane RC28) and the
per-place inputs at the non-Kummer places of `S₀` (tex 2761–2830, 3413–3468, 3483–3498).
**The finite Selmer duality for the actual Kummer-type conditions, with the traces of the
packet**: there are local traces `L` (one family for `A_i(1)` over `G_{K,S}`) and a global trace
`tr` killing coboundaries, inducing `H³_c(G_{K,S}, A_i(1)) ≅ A_i` and normalized by `L`, for which
lane RC26's Selmer duality map `C_U(M_i) → RHom(C_{U⊥}(M_i^*(1)), A_i)[−3]` is a
quasi-isomorphism. -/
theorem orthSelmerDuality_kummerCond_of_prints [Fintype (Places K S)]
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K) (h543 : NekovarProp543T K)
    (h756 : NekovarProp756 K) (hTr : NekovarFiniteTraces K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hisoRest : ∀ v hv (hP : v.1 ∉ P), OrthIsotropicAt
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (c v hv hP) (c' v hv hP))
    (hperfRest : ∀ (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀))) v hv
      (hP : v.1 ∉ P), QuasiIso (GHom.toCC (orthLocalMap (c v hv hP).i
        (c' v hv hP).i (orthUrPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α)
          (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α) v)
        (orthZeroIsotropy (hc v hv hP) (hc' v hv hP) (hisoRest v hv hP)) (L.trv v) (L.htrv₁ v)))) :
    ∃ (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
      (tr : (kTrTT hS W i s hs hs0 hFull P α hμ₀ hα c c' hc hc' hM L hisoRest).X 3 →ₗ[Acoef i]
        Acoef i)
      (htr : ∀ z, tr ((kTrTT hS W i s hs hs0 hFull P α hμ₀ hα c c' hc hc' hM L hisoRest).d 2 3 rfl
        z) = 0),
      InducesIsoH3 tr ∧ L.Normalizes tr ∧
        QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S (Acoef i)
          (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
          (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
          (kTrA hS W i s hs hs0 hFull P α hα c) (kTrB hS W i s hs hs0 hFull P α hα c')
          (kTrIso hS W i s hs hs0 hFull P α hμ₀ hα c c' hc hc' hM L hisoRest)) tr htr)) := by
  have hset := nekovarFiniteSetting_acoef K hK S hSfin (fun v hv => hS (h2₀ v hv)) i
  obtain ⟨L, hL⟩ := hTr S 2 (Acoef i) hset (InflMod hS (Tate1 (Acoef i) hμ₀))
    (cycloInfl_isCyclotomicTwist_tate1 hS i hμ₀)
  obtain ⟨tr, htr, h3, hN⟩ := hL (MinS hS W i α) (MinS hS W i (charInv α))
    (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
    (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
    (kTrA hS W i s hs hs0 hFull P α hα c) (kTrB hS W i s hs hs0 hFull P α hα c')
    (kTrIso hS W i s hs hs0 hFull P α hμ₀ hα c c' hc hc' hM L hisoRest)
  exact ⟨L, tr, htr, h3, hN, orthSelmerDuality_kummerCond_packet hS W i s hs hs0 hFull P α hμ₀ hα
    c c' hc hc' hM h524 h543 h756 hK hSfin hS₀fin h2₀ hisoRest L (hperfRest L) tr htr hN h3⟩

end ZInQ.Manuscript.RC.KummerMaps
