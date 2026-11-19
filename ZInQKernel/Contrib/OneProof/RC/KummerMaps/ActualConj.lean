import ZInQKernel.Contrib.OneProof.RC.KummerMaps.ConjComplements
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.ActualComplements

/-!
# Lane RC29 (round 3): the transported local complements with the traces of the packet

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality` (tex 2761–2830: "At a split
place `v`, the dual local condition is transported from the conjugate place `τv`. At a fixed place
it is transported by the actual local representative of conjugation. Kummer conditions at `2N` are
preserved by this transport. A full condition is paired with the zero condition"; the duality
`C_U(M_i) ≃ RHom_{R_i}(C_{U^⊥}(M_i^*(1)), R_i)[−3]` with `τ^*M_i ≃ M_i^*(1)` through
`(v, w) ↦ e₂(v, ρ_T(τ)w)`, tex 2798–2805).

`ConjComplements.lean` (lane RC29, round 3) proves that the transported dual conditions are the
orthogonal complements of the actual conditions (`conjActualLocalComplements`, round 2's gap D4)
and the finite Selmer duality in the text's transported form (`conjActualSelmerDuality`), for given
local traces and a given normalized global trace. This file takes the traces from the trace packet
of `TracePacket.lean` (PRINT `NekovarFiniteTraces`):

* `actCDeltaA`, `actCDeltaB`, `actCTrunc`, `actCTT`: the transported data, packaged;
* `ActCDuality`: orthogonal complements and the Selmer duality quasi-isomorphism;
* **`conjActualSelmerDuality_of_prints`**: there are local traces and a normalized global trace for
  which the actual conditions and their transported duals are orthogonal complements and the Selmer
  duality map is a quasi-isomorphism — no per-place input, only PRINTs.

Kinds: definitions and PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero`,
`NekovarProp524`, `NekovarProp543T`, `NekovarProp756`, `NekovarFiniteTraces`, the GLUE `FullTorsion`
and the ELLIOT hypotheses of `ConjComplements.lean` (`κ`-stability of `S₀` and `P`, `κ h = h`,
`W^κ = W`, `α_i^τ = α_i^{-1}`, `IsLocallyQuadAt` at `P`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.Duality (MilneLocalTateDualityKummerCharZero)
open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (hS : S₀ ⊆ S)
  (hS₀ : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) → (v ∈ S₀ ↔ w ∈ S₀))
  (W : WeierstrassCurve K) [W.IsElliptic] (hW : W.map (C.κ : K →+* K) = W) (i : ℕ)
  (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hκh : C.κ h = h) (hFull₀ : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α] (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  (hα₀ : ∀ σ, α ((conjInflConj C hS₀).conj σ) = (α σ)⁻¹)
  (P : Set (HeightOneSpectrum (𝓞 K)))
  (hP : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) → (v ∈ P ↔ w ∈ P))
  (hαP : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)

/-- Definition. The actual conditions (Kummer at `P`, full at `S₀ − P`, unramified at `S − S₀`) on
`M_i`, as lane RC26's Galois local conditions. -/
def actCDeltaA : GaloisLocalConditions K S (Acoef i) (MinS hS W i α) :=
  ofCondAt K S (Acoef i) (MinS hS W i α) (conjCFamA hS W i s hs hs0 hFull₀ α P hαP)

/-- Definition. The transported dual conditions on `τ^*M_i = Infl(τ₀^*M_{i,0})`, as lane RC26's
Galois local conditions. -/
def actCDeltaB : GaloisLocalConditions K S (Acoef i)
    (InflMod hS (PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α))) :=
  ofCondAt K S (Acoef i) _ (conjCFamB C hS hS₀ W i s hs hs0 hFull₀ α P hαP)

/-- Definition. The `τ≥2` isotropy data of the transported pair for a packet of local traces. -/
def actCTrunc (hM : MilneLocalTateDualityKummerCharZero)
    (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀))) :
    GaloisTruncIsotropyData K S (Acoef i) (conjCβ C hS hS₀ W hW i α hμ₀)
      (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀) (actCDeltaA hS W i s hs hs0 hFull₀ α P hαP)
      (actCDeltaB C hS hS₀ W i s hs hs0 hFull₀ α P hαP) :=
  conjCTrunc C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP L.trv L.htrv₁ L.iso hM

/-- Definition. The truncated compact cone of the transported data, the domain of the global
trace. -/
abbrev actCTT (hM : MilneLocalTateDualityKummerCharZero)
    (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀))) : GCx (Acoef i) :=
  galoisCompactTT K S (Acoef i) (conjCβ C hS hS₀ W hW i α hμ₀)
    (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀) (actCDeltaA hS W i s hs hs0 hFull₀ α P hαP)
    (actCDeltaB C hS hS₀ W i s hs hs0 hFull₀ α P hαP)
    (actCTrunc C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP hM L)

/-- Definition. **The conclusion for the transported data, a packet `L` and a global trace `tr`**:
the actual conditions and their transported duals are orthogonal complements and lane RC26's Selmer
duality map is a quasi-isomorphism. -/
def ActCDuality (hM : MilneLocalTateDualityKummerCharZero)
    (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (tr : (actCTT C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP hM L).X 3 →ₗ[Acoef i]
      Acoef i)
    (htr : ∀ z, tr ((actCTT C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP hM L).d 2 3 rfl
      z) = 0) : Prop :=
  OrthogonalComplementsT K (conjCβ C hS hS₀ W hW i α hμ₀) (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀)
      (actCDeltaA hS W i s hs hs0 hFull₀ α P hαP) (actCDeltaB C hS hS₀ W i s hs hs0 hFull₀ α P hαP)
      (actCTrunc C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP hM L) tr htr ∧
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S (Acoef i)
      (conjCβ C hS hS₀ W hW i α hμ₀) (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀)
      (actCDeltaA hS W i s hs hs0 hFull₀ α P hαP) (actCDeltaB C hS hS₀ W i s hs hs0 hFull₀ α P hαP)
      (actCTrunc C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP hM L)) tr htr))

/-- PROVED from the PRINTs of `ConjComplements.lean` and `NekovarProp543T`: **the transported local
complements and Selmer duality for a packet of local traces** and a global trace normalized by it,
inducing `H³_c ≅ A_i`. -/
theorem conjActualSelmerDuality_packet [Fintype (Places K S)] [NeZero i]
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K) (h543 : NekovarProp543T K)
    (h756 : NekovarProp756 K) (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (tr : (actCTT C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP hM L).X 3 →ₗ[Acoef i]
      Acoef i)
    (htr : ∀ z, tr ((actCTT C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP hM L).d 2 3 rfl
      z) = 0)
    (hN : L.Normalizes tr) (h3 : InducesIsoH3 tr) :
    ActCDuality C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP hM L tr htr :=
  ⟨conjActualLocalComplements C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP L.trv
      L.htrv₁ L.iso hM h524 h756 hK hSfin hS₀fin h2₀ tr htr hN,
    conjActualSelmerDuality C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP L.trv L.htrv₁
      L.iso hM h524 h756 h543 hK hSfin hS₀fin h2₀ tr htr h3 hN⟩

/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero`, `NekovarProp524`,
`NekovarProp543T`, `NekovarProp756` and `NekovarFiniteTraces` (Nekovář 5.1.3, 5.1.5, 5.2.1, 5.4.1),
the GLUE `FullTorsion` and the ELLIOT hypotheses of `ConjComplements.lean` (tex 2761–2830,
3413–3468, 3483–3498). **The transported local complements and the finite Selmer duality in the
text's form `C_U(M_i) ≃ RHom(C_{U⊥}(τ^*M_i), A_i)[−3]`, with the traces of the packet**: there are
local traces `L` and a global trace `tr` killing coboundaries, inducing `H³_c ≅ A_i` and normalized
by `L`, for which `ActCDuality` holds. No per-place input is left. -/
theorem conjActualSelmerDuality_of_prints [Fintype (Places K S)] [NeZero i]
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K) (h543 : NekovarProp543T K)
    (h756 : NekovarProp756 K) (hTr : NekovarFiniteTraces K) (hK : IsTotallyComplex K)
    (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∃ (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
      (tr : (actCTT C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP hM L).X 3 →ₗ[Acoef i]
        Acoef i)
      (htr : ∀ z, tr ((actCTT C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP hM L).d 2 3
        rfl z) = 0),
      InducesIsoH3 tr ∧ L.Normalizes tr ∧
        ActCDuality C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP hM L tr htr := by
  have hset := nekovarFiniteSetting_acoef K hK S hSfin (fun v hv => hS (h2₀ v hv)) i
  have hT := cycloInfl_isCyclotomicTwist_tate1 hS i hμ₀
  obtain ⟨L, hL⟩ := @hTr S 2 (Acoef i) _ _ hset _ (InflMod hS (Tate1 (Acoef i) hμ₀)) _ _ _ _ _ _ _ hT
  refine ⟨L, ?_⟩
  have h1 := hL (MinS hS W i α) (InflMod hS (PullMod (conjInflConj C hS₀).conj (Mcoef K S₀ W i α)))
    (conjCβ C hS hS₀ W hW i α hμ₀) (conjCβ_smul C hS hS₀ W hW i α hμ₀ hα₀)
    (actCDeltaA hS W i s hs hs0 hFull₀ α P hαP) (actCDeltaB C hS hS₀ W i s hs hs0 hFull₀ α P hαP)
    (actCTrunc C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP hM L)
  exact h1.imp fun tr => Exists.imp fun htr hQ => ⟨hQ.1, hQ.2,
    conjActualSelmerDuality_packet C hS hS₀ W hW i s hs hs0 hκh hFull₀ α hμ₀ hα₀ P hP hαP hM h524
      h543 h756 hK hSfin hS₀fin h2₀ L tr htr hQ.2 hQ.1⟩

end ZInQ.Manuscript.RC.KummerMaps
