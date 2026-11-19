import ZInQKernel.Contrib.OneProof.RC.KummerMaps.Iota
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthActual

/-!
# Lane RC29 (Kummer maps), part 6: the genuine Kummer conditions in the orthogonality assembly

Manuscript `diophantine_zq.tex` (11/5), Lemma `ex:arith-conjugate-duality` (tex 2761–2830: "With
the conjugate places, actual orthogonal local conditions and their isotropy homotopies, finite
Selmer duality gives `C_U(M_i) ≃ RHom_{R_i}(C_{U^⊥}(M_i^*(1)), R_i)[−3]`") and Lemma
`ex:arith-local-kummer` (tex 3413–3423: "Its Kummer image is its exact local annihilator, and the
comparison has integral isotropy homotopies").

This file puts the genuine Kummer conditions of `Iota.lean` into the orthogonality assembly of
`OrthActual.lean`:

* `isLocallyQuadAt_charInv`: the dual character `α⁻¹` is again `χ_h` on the decomposition group
  (`χ_h = ±1`), so the dual module `M_i(α⁻¹) ≅ M_i^*(1)` carries the same kind of genuine Kummer
  condition (PROVED).
* `kummerCondFun`: the conditions at the coefficient support `S₀` of `kummerSelData` — the genuine
  Kummer condition `actualKummerAtS` at the places of `P ⊆ S₀` (above `2N`,
  where the moving character is locally trivial), given conditions elsewhere in `S₀`;
  `kummerCondFun_concentrated` (PROVED: degrees `0, 1`).
* **`orthogonalComplementsT_kummerCond`**: Nekovář's orthogonality (`OrthogonalComplementsT`,
  lane RC26's `τ≥2` form) for these conditions on `M_i` against the same conditions on
  `M_i(α⁻¹)`, with the unramified conditions at `S − S₀`, through the inflated Weil pairing —
  PROVED from the PRINT `NekovarProp756` (Nekovář 7.5.6, the unramified places), lane RC28's GLUE
  `FullTorsion`, and the per-place inputs at `S₀`: the isotropy `hiso` and the per-place
  quasi-isomorphisms `hperf`, which at the Kummer places are Elliot's Lemma
  `ex:arith-local-kummer` (ELLIOT, tex 3418–3419, 3442–3450), and the trace hypotheses of lane
  RC26.

Kinds: PROVED from the hypotheses named (their kinds are in the docstrings).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}

/-- PROVED (tex 2798–2805: the dual coefficients `M_i(α_i⁻¹)`). **The inverse character is again
`χ` on the decomposition group** when `α` is (`χ` takes values `±1`, which are their own
inverses). -/
theorem isLocallyQuadAt_charInv {i : ℕ} {α : GKS K S →* (Acoef i)ˣ} {χ : GKS K S →* ℤˣ}
    {v : HeightOneSpectrum (𝓞 K)} (hα : IsLocallyQuadAt i α χ v) :
    IsLocallyQuadAt i (charInv α) χ v := by
  intro σ
  rw [charInv_apply, hα σ, ← map_inv, Int.units_inv_eq_self]

variable (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  (P : Set (HeightOneSpectrum (𝓞 K)))

open scoped Classical in
/-- Definition (tex 2754–2756, 3413–3438). **The conditions at the coefficient support `S₀`** of
`kummerSelData`: the genuine Kummer condition at the places of `P`, the given condition `c`
at the other places of `S₀`. -/
def kummerCondFun (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
    (hα : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)
    (c : ∀ v : Places K S, v.1 ∈ S₀ → v.1 ∉ P → CondAt K S (Acoef i) (MinS hS W i α) v) :
    ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v :=
  fun v hv => if hP : v.1 ∈ P then actualKummerAtS hS W i s hs hs0 α hFull v (hα v.1 hP)
    else c v hv hP

/-- PROVED. `kummerSelData` is lane RC28's `actualSelData` of `kummerCondFun`. -/
theorem kummerSelData_eq_actualSelData (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
    (hα : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)
    (c : ∀ v : Places K S, v.1 ∈ S₀ → v.1 ∉ P → CondAt K S (Acoef i) (MinS hS W i α) v) :
    kummerSelData hS W i s hs hs0 α hFull P hα c =
      actualSelData hS W i α (kummerCondFun hS W i s hs hs0 hFull P α hα c) :=
  rfl

open scoped Classical in
/-- PROVED. The conditions `kummerCondFun` are concentrated in degrees `0, 1` when the given ones
are (the Kummer condition is, `orth_kummerAt_concentrated`). -/
theorem kummerCondFun_concentrated (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
    (hα : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)
    (c : ∀ v : Places K S, v.1 ∈ S₀ → v.1 ∉ P → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hc : ∀ v hv hP, OrthConcentratedAt (c v hv hP)) (v : Places K S) (hv : v.1 ∈ S₀) :
    OrthConcentratedAt (kummerCondFun hS W i s hs hs0 hFull P α hα c v hv) := by
  unfold kummerCondFun
  split
  · rename_i hP
    have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    exact orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
      (kummerIotaS hS W i s hs hs0 α hFull v) (kummerIotaS_smul hS W i s hs hs0 α hFull v (hα v.1 hP))
  · exact hc v hv ‹_›

variable [NeZero i] [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α] (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  (hα : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)
  (c : ∀ v : Places K S, v.1 ∈ S₀ → v.1 ∉ P → CondAt K S (Acoef i) (MinS hS W i α) v)
  (c' : ∀ v : Places K S, v.1 ∈ S₀ → v.1 ∉ P → CondAt K S (Acoef i) (MinS hS W i (charInv α)) v)
  (hc : ∀ v hv hP, OrthConcentratedAt (c v hv hP))
  (hc' : ∀ v hv hP, OrthConcentratedAt (c' v hv hP))

/-- The genuine Kummer conditions on `M_i` at `S₀` (`kummerCondFun`). -/
abbrev kummerCondA : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v :=
  kummerCondFun hS W i s hs hs0 hFull P α hα c

/-- The genuine Kummer conditions on the dual module `M_i(α⁻¹) ≅ M_i^*(1)` at `S₀`. -/
abbrev kummerCondB : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i (charInv α)) v :=
  kummerCondFun hS W i s hs hs0 hFull P (charInv α) (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c'

/-- Orthogonality for the constructed finite Kummer conditions and supplied old conditions
concentrated in degrees zero and one, with unramified conditions outside S₀. The Kummer-place
isotropy and local quasi-isomorphism are ELLIOT inputs (tex 3418–3419, 3442–3456); the
unramified comparison uses Nekovář 7.5.6. The hypotheses `hc` and `hc'` exclude a genuine full
condition with nonzero coefficients. This theorem therefore does not instantiate the complete
primitive/relaxed old-condition package, which retains full active and moving conditions
(tex 2865–2867, 5055–5061). Full/zero places require their separate local comparison and an
assembly allowing arbitrary old conditions. PROVED from the displayed hypotheses.

Lane RC29's later rounds supply both: round 2's `orthogonalComplementsT_kummerCond_of_milne`
(`KummerSelmer.lean`) derives the Kummer-place inputs from the PRINTs
`MilneLocalTateDualityKummerCharZero` and `NekovarProp524`, and round 3's `actualLocalComplements`
(`ActualComplements.lean`) is the assembly with the full conditions at the active and moving primes
paired with the zero condition, through the arbitrary-condition per-place assembly
`orthogonalComplementsT_ofCondAt`, the zero homotopy of `ActLTZ`/`ofTruncZero` and the full/zero
comparison `orthLocalMap_full_zero_quasiIso`. -/
theorem orthogonalComplementsT_kummerCond [Fintype (Places K S)] (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hiso : ∀ v hv, OrthIsotropicAt (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (kummerCondA hS W i s hs hs0 hFull P α hα c v hv)
      (kummerCondB hS W i s hs hs0 hFull P α hα c' v hv))
    (trv : ∀ v : Places K S, (localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ v z, trv v ((localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)
    (htrv2 : ∀ v : Places K S, v.1 ∉ S₀ → InducesIsoH2 (trv v))
    (hperf : ∀ (v : Places K S) (hv : v.1 ∈ S₀), QuasiIso (GHom.toCC (orthLocalMap
      (kummerCondA hS W i s hs hs0 hFull P α hα c v hv).i
      (kummerCondB hS W i s hs hs0 hFull P α hα c' v hv).i
      (orthUrPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α)
        (weilPairingM_smul W hμ₀ (Acoef i) α) v)
      (orthZeroIsotropy (kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc v hv)
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
          (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc' v hv) (hiso v hv))
      (trv v) (htrv v))))
    (tr : (galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (kummerCondA hS W i s hs hs0 hFull P α hα c)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α))
          (kummerCondB hS W i s hs hs0 hFull P α hα c')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (kummerCondA hS W i s hs hs0 hFull P α hα c) (kummerCondB hS W i s hs hs0 hFull P α hα c')
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc)
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
          (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc') hiso)).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (kummerCondA hS W i s hs hs0 hFull P α hα c)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α))
          (kummerCondB hS W i s hs hs0 hFull P α hα c')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (kummerCondA hS W i s hs hs0 hFull P α hα c) (kummerCondB hS W i s hs hs0 hFull P α hα c')
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc)
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
          (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc') hiso)).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (InflMod hS (Tate1 (Acoef i) hμ₀))).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v)) :
    OrthogonalComplementsT K (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (kummerCondA hS W i s hs hs0 hFull P α hα c)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α))
          (kummerCondB hS W i s hs hs0 hFull P α hα c')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (kummerCondA hS W i s hs hs0 hFull P α hα c) (kummerCondB hS W i s hs hs0 hFull P α hα c')
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc)
        (kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
          (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc') hiso) tr htr :=
  orthogonalComplementsT_urOutside hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α)
    (weilPairingM_smul W hμ₀ (Acoef i) α) (kummerCondA hS W i s hs hs0 hFull P α hα c)
    (kummerCondB hS W i s hs hs0 hFull P α hα c')
    (kummerCondFun_concentrated hS W i s hs hs0 hFull P α hα c hc)
    (kummerCondFun_concentrated hS W i s hs hs0 hFull P (charInv α)
      (fun v hv => isLocallyQuadAt_charInv (hα v hv)) c' hc') hiso trv htrv h756 2
    (nekovarFiniteSetting_acoef K hK S₀ hS₀fin h2₀ i)
    (weilPairingM_bijective W hμ₀ (Acoef i) α hFull)
    (weilPairingM_flip_bijective W hμ₀ (Acoef i) α hFull)
    (isCyclotomicTwist_tate1 (Acoef i) hμ₀) htrv2 hperf tr htr hsum

end ZInQ.Manuscript.RC.KummerMaps
