import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerPerPlace
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.IotaWeil
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.CompKummer

/-!
# Lane RC29 (round 2, item 1): the Kummer per-place inputs from Milne's local duality

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer`, tex 3418–3419 and 3439–3450:
"The local finite dualities [Milne I.2.3, I.3.2–I.3.5] make the Kummer map adjoint to
`H¹(F, B[2^a]) → H¹(F, B)[2^a]`. The latter has Kummer image as kernel, so the Kummer image is its
exact annihilator."

`KummerPerPlace.lean` derives the round-1 per-place inputs `hisoK`, `hperfK` from lane RC26's
PRINT `NekovarProp524` and the exact annihilator `KummerExactAnn ψ₀` for the coefficient pairing
`ψ₀(t₁, t₂) = weilS(e t₁, e t₂)` that the Kummer coefficient maps `ι_v` induce. This file derives
`KummerExactAnn ψ₀` from the existing print of the other group (`MilneLocalTateDualityKummerCharZero`,
Milne, *Arithmetic Duality Theorems*, 2nd ed., Ch. I, Cor. 2.3, Thm. 3.2, Cor. 3.4, Rem. 3.5),
following the text:

* `compKummerAnnihilator_adicCompletion` (`CompKummer.lean`): the print, moved to the genuine
  continuous cochains of lanes RC26/RC28 and made trace-free, gives `KummerExactAnn` for the Weil
  pairing `e^B : B(K̄_v)[2^i] × B(K̄_v)[2^i] → μ_{2^i}(K̄_v)` of the local twist `B = E^{(h)}`.
* `iotaWeil_weilS_eq`, `iotaWeilTwist_invariance`, `iotaWeilLog_smul` (`IotaWeil.lean`): **`ι_v`
  respects the Weil pairing** — `ψ₀ = ℓ_v ∘ e^B` for the discrete logarithm `ℓ_v` at the primitive
  root `j(ζ)` (the twist identification is a change of variables, which preserves the Weil
  pairing), and `ℓ_v` is `G_{K_v}`-equivariant into `ℤ/2^i(1)`.
* `kmilneF`: the equivariant isomorphism `ℓ_v : μ_{2^i}(K̄_v) ≃ ℤ/2^i(1)`;
  **`kummerExactAnn_kannPsi`** (PROVED from the PRINT): `KummerExactAnn ψ₀`.
* **`kummerPerPlace_isotropic_of_milne`, `kummerPerPlace_perf_of_milne`** (PROVED from the PRINTs
  `MilneLocalTateDualityKummerCharZero` and `NekovarProp524`): the round-1 inputs `hisoK`, `hperfK`
  at every place where the character of `M_i` is `χ_h` on the decomposition group.

Kinds: definitions and PROVED (from the named PRINTs and the round-1 GLUE `FullTorsion`, `hT`).
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
  (v : Places K S) (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))

/-- Definition. **The equivariant isomorphism `ℓ_v : μ_{2^i}(K̄_v) ≃ ℤ/2^i(1)`**, the discrete
logarithm at `j(ζ)` (`iotaWeilLog`), with values in the local module `ℤ/2^i(1)` (inflated from
`S₀`). -/
def kmilneF : MuAlg (v.1.adicCompletion K) (2 ^ i) ≃+
    ResMod (locMap K S v.1) (InflMod hS (Tate1 (ZMod (2 ^ i)) hμ₀)) :=
  iotaWeilLog (S := S₀) hμ₀ v.1

theorem kmilneF_apply (w : MuAlg (v.1.adicCompletion K) (2 ^ i)) :
    kmilneF hS i v hμ₀ w = iotaWeilLog (S := S₀) hμ₀ v.1 w :=
  rfl

/-- PROVED. **`ℓ_v` is `G_{K_v}`-equivariant** into `ℤ/2^i(1)` (`iotaWeilLog_smul`, lane RC26's
`locMap_compat`). -/
theorem kmilneF_smul (σ : Gloc K v.1) (w : MuAlg (v.1.adicCompletion K) (2 ^ i)) :
    kmilneF hS i v hμ₀ (σ • w) = σ • kmilneF hS i v hμ₀ w := by
  have hw : (σ • w : MuAlg (v.1.adicCompletion K) (2 ^ i)) =
      Additive.ofMul (restrictRootsOfUnity (iotaWeilGal v.1 σ) (2 ^ i) w.toMul) := by
    apply muAlg_ext
    rw [coe_smul_muAlg]
    change σ.toAlgHom _ = ((restrictRootsOfUnity (iotaWeilGal v.1 σ) (2 ^ i) w.toMul :
      (AlgebraicClosure (v.1.adicCompletion K))ˣ) : AlgebraicClosure (v.1.adicCompletion K))
    rw [restrictRootsOfUnity_coe_apply]
    rfl
  change iotaWeilLog (S := S₀) hμ₀ v.1 (σ • w) =
    algebraMap (ZMod (2 ^ i)) (ZMod (2 ^ i)) (cycS hμ₀ (inflMap K hS (locMap K S v.1 σ))) *
      iotaWeilLog (S := S₀) hμ₀ v.1 w
  rw [hw, iotaWeilLog_smul, locMap_compat K hS v.1 σ, Algebra.algebraMap_self, RingHom.id_apply]

/-- PROVED (tex 3442–3444). **`ψ₀ = ℓ_v ∘ e^B`**: the coefficient pairing of the Kummer maps is the
Weil pairing of `B = E^{(h)}` over `K̄_v` read through `ℓ_v` (`iotaWeil_weilS_eq`, and the
invariance of the Weil pairing under the twist identification, `iotaWeilTwist_invariance`). -/
theorem kannPsi_eq_kmilneF [DecidableEq (v.1.adicCompletion K)] [(localTwist W h v.1).IsElliptic]
    (t₁ t₂ : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    kannPsi hS W i s hs hs0 hFull v hμ₀ t₁ t₂ =
      kmilneF hS i v hμ₀ (compWeil (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) t₁ t₂) := by
  have h1 : kannPsi hS W i s hs hs0 hFull v hμ₀ t₁ t₂ =
      iotaWeilFormE (S := S₀) W i s hs hs0 v.1 hμ₀ t₁ t₂ := by
    change weilS (S := S₀) W hμ₀ ((compTorsEquiv W (2 ^ i) hFull v.1).symm _)
      ((compTorsEquiv W (2 ^ i) hFull v.1).symm _) = _
    rw [iotaWeil_weilS_eq W hμ₀ v.1, ← compTorsEquiv_apply W _ hFull,
      ← compTorsEquiv_apply W _ hFull, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    rfl
  rw [h1, iotaWeilFormE_apply, iotaWeilTwist_invariance, kmilneF_apply]
  rfl

open scoped Classical in
/-- PROVED from the PRINT `MilneLocalTateDualityKummerCharZero` (the other group's; Milne,
*Arithmetic Duality Theorems*, 2nd ed., Ch. I, Cor. 2.3, Thm. 3.2, Cor. 3.4, Rem. 3.5; tex
3439–3445). **The exact annihilator for the coefficient pairing `ψ₀` of the Kummer maps**:
`compKummerAnnihilator_adicCompletion` (the print in the genuine continuous cochains, trace-free)
for `e^B`, transported along `ℓ_v` (`kummerExactAnn_transport`, `kannPsi_eq_kmilneF`). -/
theorem kummerExactAnn_kannPsi (hM : MilneLocalTateDualityKummerCharZero) :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    KummerExactAnn (kannPsi hS W i s hs hs0 hFull v hμ₀) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  refine kummerExactAnn_transport (compWeil (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i))
    (kannPsi hS W i s hs hs0 hFull v hμ₀) (kmilneF hS i v hμ₀)
    (kmilneF_smul hS i v hμ₀) (kannPsi_eq_kmilneF hS W i s hs hs0 hFull v hμ₀)
    (fun y hy => ?_)
  exact compKummerAnnihilator_adicCompletion hM K v.1 (localTwist W h v.1) i y hy

variable [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]

open scoped Classical in
/-- PROVED from the PRINT `MilneLocalTateDualityKummerCharZero` (tex 3418–3419, 3439–3448).
**The round-1 input `hisoK`**: at a place `v` where the character `α` of `M_i` is `χ_h` on the
decomposition group, the actual Kummer conditions on `M_i(α)` and `M_i(α⁻¹)` are isotropic for the
inflated Weil pairing, for any local trace inducing `H²(G_{K_v}, A_i(1)) ≅ A_i`. -/
theorem kummerPerPlace_isotropic_of_milne (hM : MilneLocalTateDualityKummerCharZero)
    (hα : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v.1)
    (trv : (locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ z, trv ((locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)
    (h2 : InducesIsoH2 trv) :
    OrthIsotropicAt (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (actualKummerAtS hS W i s hs hs0 α hFull v hα)
      (actualKummerAtS hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv hα)) :=
  kummerPerPlace_isotropic hS W i s hs hs0 hFull v hμ₀ α hα
    (kummerExactAnn_kannPsi hS W i s hs hs0 hFull v hμ₀ hM) trv htrv h2

open scoped Classical in
/-- PROVED from the PRINTs `MilneLocalTateDualityKummerCharZero` and `NekovarProp524`, with the
round-1 GLUE `FullTorsion` and `hT` (tex 3418–3419, 3439–3450). **The round-1 input `hperfK`**: at a
place `v` where the character `α` of `M_i` is `χ_h` on the decomposition group, the per-place local
duality map of the actual Kummer pair is a quasi-isomorphism, for every isotropy homotopy. -/
theorem kummerPerPlace_perf_of_milne [NeZero i] (hM : MilneLocalTateDualityKummerCharZero)
    (h524 : NekovarProp524 K) (hK : IsTotallyComplex K) (hSfin : S.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hT : IsCyclotomicTwist K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (hα : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v.1)
    (trv : (localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ z, trv ((localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)
    (h2 : InducesIsoH2 trv)
    (J : LocalTruncIsotropy (actualKummerAtS hS W i s hs hs0 α hFull v hα).i
      (actualKummerAtS hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv hα)).i
      (orthUrPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α)
        (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α) v)) :
    QuasiIso (GHom.toCC (orthLocalMap (actualKummerAtS hS W i s hs hs0 α hFull v hα).i
      (actualKummerAtS hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv hα)).i
      (orthUrPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α)
        (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α) v) J trv htrv)) :=
  kummerPerPlace_perf hS W i s hs hs0 hFull v hμ₀ α h524 hK hSfin h2₀ hT hα
    (kummerExactAnn_kannPsi hS W i s hs hs0 hFull v hμ₀ hM) trv htrv h2 J

end ZInQ.Manuscript.RC.KummerMaps
