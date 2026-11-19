import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerAnnActual
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthLocalDuality

/-!
# Lane RC29 (round 2, item 1): the per-place Kummer inputs from local duality

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer`, tex 3418–3419 ("Its Kummer image is
its exact local annihilator, and the comparison has integral isotropy homotopies") and the proof
at tex 3439–3450.

Round 1 of this lane assumed, at the places `v` where the Kummer condition is used, the per-place
isotropy (`hisoK`) and the per-place quasi-isomorphism (`hperfK`) for the actual Kummer conditions
`actualKummerAtS` on `M_i(α)` and `M_i(α⁻¹)` (ELLIOT). This file derives both, following the text:

* `KummerExactAnn ψ` (predicate): **the Kummer image of `B(F)` is its own exact annihilator** for a
  coefficient pairing `ψ : B(F̄)[m] × B(F̄)[m] → T`, in the trace-free form on genuine continuous
  cochains: a `1`-cocycle is a Kummer cocycle up to a coboundary iff its cup products with all
  Kummer cocycles are coboundaries. Transport along isomorphisms of targets
  (`kummerExactAnn_transport`) and under negation (`kummerExactAnn_neg`); isotropy
  (`KummerExactAnn.iso`); non-vacuity (`kummerExactAnn_one`).
* `kannPsi0_flip`: the coefficient pairing `ψ₀(t₁, t₂) = weilS(e t₁, e t₂)` is alternating
  (lane RC28's `weilBar_skew`), so `ψ₀ᵗ = −ψ₀`.
* **`kummerPerPlace_annihilator`** (PROVED): from `KummerExactAnn ψ₀` and a local trace inducing
  `H² ≅ A_i`, the actual Kummer pair satisfies the annihilator condition of
  `OrthLocalDuality.lean` (via the coefficient extension of `KummerAnn.lean`, the decomposition
  data of `KummerAnnActual.lean`, and the bridge `orthKummerAnnihilator_of_cup`).
* **`kummerPerPlace_isotropic`** (PROVED): the round-1 input `hisoK` at `v`.
* **`kummerPerPlace_perf`** (PROVED from PRINT `NekovarProp524`): the round-1 input `hperfK` at
  `v`, for every isotropy homotopy.

The remaining input `KummerExactAnn ψ₀` is Milne's local duality for `B[2^i]` (tex 3439–3441);
`KummerMilne.lean` derives it from the existing print.

Kinds: definitions and PROVED; the hypotheses are the PRINT `NekovarProp524` (lane RC26), the
GLUE `hT` and `FullTorsion` as in round 1, and `KummerExactAnn ψ₀` (from Milne's print).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs
open scoped TensorProduct

/-! ### The exact annihilator, trace-free -/

section ExactAnn

variable {F : Type} [Field F] [CharZero F] [DecidableEq F] {B : WeierstrassCurve F} [B.IsElliptic]
  {m : ℕ} [NeZero m]
  {T : Type} [AddCommGroup T] [DistribMulAction (Field.absoluteGaloisGroup F) T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (Field.absoluteGaloisGroup F) T]

/-- Hypothesis predicate (tex 3423, 3439–3445). **The Kummer image of `B(F)` is its own exact
annihilator for the coefficient pairing `ψ`**, in the trace-free form on genuine continuous
cochains (lanes RC26, RC28): a continuous `1`-cocycle `y` with values in `B(F̄)[m]` is a Kummer
cocycle `κ_P` up to a coboundary iff all cup products `κ_P ∪_ψ y` are coboundaries. -/
def KummerExactAnn (ψ : TorsAlg F B m →ₗ[ℤ] TorsAlg F B m →ₗ[ℤ] T) : Prop :=
  ∀ y : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1,
    contD ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 y = 0 →
      ((∃ P : B.toAffine.Point,
          y - kummerCocycle F B m P ∈ contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m)) ↔
        ∀ P : B.toAffine.Point, kannCup ψ (kummerCocycle F B m P) y ∈
          LinearMap.range (contD ℤ (Field.absoluteGaloisGroup F) T 1))

/-- PROVED. **Isotropy of the Kummer image** from the exact annihilator. -/
theorem KummerExactAnn.iso {ψ : TorsAlg F B m →ₗ[ℤ] TorsAlg F B m →ₗ[ℤ] T}
    (h : KummerExactAnn ψ) (P Q : B.toAffine.Point) :
    kannCup ψ (kummerCocycle F B m P) (kummerCocycle F B m Q) ∈
      LinearMap.range (contD ℤ (Field.absoluteGaloisGroup F) T 1) :=
  (h _ (kummerCocycle_isCocycle F B m Q)).1 ⟨Q, by rw [sub_self]; exact Submodule.zero_mem _⟩ P

/-- PROVED. **Transport of the exact annihilator** along an equivariant isomorphism of targets. -/
theorem kummerExactAnn_transport {T' : Type} [AddCommGroup T']
    [DistribMulAction (Field.absoluteGaloisGroup F) T'] [TopologicalSpace T'] [DiscreteTopology T']
    [ContinuousSMul (Field.absoluteGaloisGroup F) T']
    (e₁ : TorsAlg F B m →ₗ[ℤ] TorsAlg F B m →ₗ[ℤ] T)
    (e₂ : TorsAlg F B m →ₗ[ℤ] TorsAlg F B m →ₗ[ℤ] T') (f : T ≃+ T')
    (hf : ∀ (g : Field.absoluteGaloisGroup F) (w : T), f (g • w) = g • f w)
    (he : ∀ s t, e₂ s t = f (e₁ s t)) (h : KummerExactAnn e₁) : KummerExactAnn e₂ := by
  intro y hy
  rw [h y hy]
  exact forall_congr' fun P => (kann_cup_range_transport e₁ e₂ f hf he _ y).symm

/-- PROVED. **The exact annihilator is unchanged by negating the pairing.** -/
theorem kummerExactAnn_neg (e₁ e₂ : TorsAlg F B m →ₗ[ℤ] TorsAlg F B m →ₗ[ℤ] T)
    (he : ∀ s t, e₂ s t = -e₁ s t) (h : KummerExactAnn e₁) : KummerExactAnn e₂ := by
  intro y hy
  rw [h y hy]
  exact forall_congr' fun P => (kann_cup_range_neg e₁ e₂ he _ y).symm

end ExactAnn

/-- PROVED. **Non-vacuity of `KummerExactAnn`**: for `m = 1` (where `B(F̄)[1] = 0`) it holds for
every pairing. -/
theorem kummerExactAnn_one {F : Type} [Field F] [CharZero F] [DecidableEq F]
    {B : WeierstrassCurve F} [B.IsElliptic] {T : Type} [AddCommGroup T]
    [DistribMulAction (Field.absoluteGaloisGroup F) T] [TopologicalSpace T] [DiscreteTopology T]
    [ContinuousSMul (Field.absoluteGaloisGroup F) T]
    (ψ : TorsAlg F B 1 →ₗ[ℤ] TorsAlg F B 1 →ₗ[ℤ] T) : KummerExactAnn ψ := by
  have h0 : ∀ t : TorsAlg F B 1, t = 0 := fun t => by
    have := kann_torsAlg_nsmul t
    rwa [one_smul] at this
  intro y _
  have hy0 : ∀ c : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B 1) 1, c = 0 :=
    fun c => Subtype.ext (funext fun g => h0 _)
  refine ⟨fun _ P => ⟨0, ?_⟩, fun _ => ⟨0, ?_⟩⟩
  · rw [map_zero]
    apply Subtype.ext
    funext g
    change (0 : T) = cupFun ψ 1 1 2 rfl (cfun (kummerCocycle F B 1 P)) (cfun y) g
    rw [cupFun_one_one_apply, h0 (cfun (kummerCocycle F B 1 P) fun _ => g 0), map_zero,
      LinearMap.zero_apply]
  · rw [hy0 (y - kummerCocycle F B 1 0)]
    exact Submodule.zero_mem _

/-! ### The actual Kummer pair at a place where `α = χ_h` -/

section Actual

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy)

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  (v : Places K S) (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))

/-- PROVED. **`ψ₀` is alternating**, hence `ψ₀ᵗ = −ψ₀` (lane RC28's `weilBar_skew`). -/
theorem kannPsi_flip (t₁ t₂ : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    (kannPsi hS W i s hs hs0 hFull v hμ₀).flip t₁ t₂ = -kannPsi hS W i s hs hs0 hFull v hμ₀ t₁ t₂ := by
  change weilS (S := S₀) W hμ₀ (kannE W i s hs hs0 hFull v t₂) (kannE W i s hs hs0 hFull v t₁) =
    -weilS (S := S₀) W hμ₀ (kannE W i s hs hs0 hFull v t₁) (kannE W i s hs hs0 hFull v t₂)
  rw [weilS_apply, weilS_apply, weilBar_skew, map_neg]

variable [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]

open scoped Classical in
/-- PROVED (tex 3418–3419, 3423, 3439–3445). **The annihilator condition for the actual Kummer
pair at `v`**, from the exact annihilator for `ψ₀` (Milne's local duality for `B[2^i]`, in the
trace-free form) and a local trace killing coboundaries and inducing `H²(G_{K_v}, A_i(1)) ≅ A_i`:
the input `OrthKummerAnnihilator` of the per-place duality of `OrthLocalDuality.lean`. -/
theorem kummerPerPlace_annihilator
    (hα : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v.1)
    (hA : haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      KummerExactAnn (kannPsi hS W i s hs hs0 hFull v hμ₀))
    (trv : (locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ z, trv ((locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)
    (h2 : InducesIsoH2 trv) :
    OrthKummerAnnihilator (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (actualKummerAtS hS W i s hs hs0 α hFull v hα)
      (actualKummerAtS hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv hα)) trv := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  have hannF := kummerExactAnn_neg _ _ (kannPsi_flip hS W i s hs hs0 hFull v hμ₀) hA
  exact orthKummerAnnihilator_of_cup _ _ v (localTwist W h v.1) (localTwist W h v.1) (2 ^ i)
    (kummerIotaS hS W i s hs hs0 α hFull v) (kummerIotaS_smul hS W i s hs hs0 α hFull v hα)
    (kummerIotaS hS W i s hs hs0 (charInv α) hFull v)
    (kummerIotaS_smul hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv hα))
    trv htrv h2
    (fun u hu u' hu' => kannActual_iso hS W i s hs hs0 hFull v hμ₀ α hα
      (fun P Q => hA.iso P Q) hu hu')
    (fun y hy hall => kannActual_ann hS W i s hs hs0 hFull v hμ₀ α hα
      (fun y' hy' hcup => (hannF y' hy').2 hcup) y hy
      (fun Q => hall _ (Submodule.mem_sup_left (kummerCocycleIn_mem _ (1 : Acoef i) Q))))

open scoped Classical in
/-- PROVED (tex 3418–3419). **The round-1 input `hisoK` at `v`**: the actual Kummer pair is
isotropic for the inflated Weil pairing (`OrthIsotropicAt`, lane RC26's `τ≥2` form), from the exact
annihilator for `ψ₀` and a local trace inducing `H² ≅ A_i`. -/
theorem kummerPerPlace_isotropic
    (hα : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v.1)
    (hA : haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      KummerExactAnn (kannPsi hS W i s hs hs0 hFull v hμ₀))
    (trv : (locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ z, trv ((locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)
    (h2 : InducesIsoH2 trv) :
    OrthIsotropicAt (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (actualKummerAtS hS W i s hs hs0 α hFull v hα)
      (actualKummerAtS hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv hα)) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact orthLD_isotropicAt _ _ _ _ trv
    (orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
      (kummerIotaS hS W i s hs hs0 α hFull v) (kummerIotaS_smul hS W i s hs hs0 α hFull v hα))
    (orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
      (kummerIotaS hS W i s hs hs0 (charInv α) hFull v)
      (kummerIotaS_smul hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv hα)))
    (kummerPerPlace_annihilator hS W i s hs hs0 hFull v hμ₀ α hα hA trv htrv h2) h2

open scoped Classical in
/-- PROVED from the PRINT `NekovarProp524` (Nekovář, *Selmer complexes*, 5.2.4) and GLUE as in
round 1 (tex 3418–3419, 3442–3450). **The round-1 input `hperfK` at `v`**: the per-place local
duality map of the actual Kummer pair is a quasi-isomorphism, for every isotropy homotopy `J`. -/
theorem kummerPerPlace_perf [NeZero i] (h524 : NekovarProp524 K) (hK : IsTotallyComplex K)
    (hSfin : S.Finite) (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hT : IsCyclotomicTwist K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (hα : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v.1)
    (hA : haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      KummerExactAnn (kannPsi hS W i s hs hs0 hFull v hμ₀))
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
        (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α) v) J trv htrv)) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  have hset := nekovarFiniteSetting_acoef K hK S hSfin (fun v hv => hS (h2₀ v hv)) i
  have := hset.selfInjective
  have : Finite (MinS hS W i α) := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  have : Finite (MinS hS W i (charInv α)) :=
    inferInstanceAs (Finite (Mcoef K S₀ W i (charInv α)))
  exact orthPerPlace_of_localDuality _ _ (actualKummerAtS hS W i s hs hs0 α hFull v hα)
    (actualKummerAtS hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv hα)) J trv htrv
    (h524 S 2 (Acoef i) hset (MinS hS W i α) (MinS hS W i (charInv α))
      (InflMod hS (Tate1 (Acoef i) hμ₀))
      (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α))
      (weilPairingM_bijective (S := S₀) W hμ₀ (Acoef i) α hFull)
      (weilPairingM_flip_bijective (S := S₀) W hμ₀ (Acoef i) α hFull) hT v trv htrv h2)
    (orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
      (kummerIotaS hS W i s hs hs0 α hFull v) (kummerIotaS_smul hS W i s hs hs0 α hFull v hα))
    (orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
      (kummerIotaS hS W i s hs hs0 (charInv α) hFull v)
      (kummerIotaS_smul hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv hα)))
    (orth_kummerAt_h01 v (localTwist W h v.1) (2 ^ i)
      (kummerIotaS hS W i s hs hs0 α hFull v) (kummerIotaS_smul hS W i s hs hs0 α hFull v hα))
    (orth_kummerAt_h01 v (localTwist W h v.1) (2 ^ i)
      (kummerIotaS hS W i s hs hs0 (charInv α) hFull v)
      (kummerIotaS_smul hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv hα)))
    (kummerPerPlace_annihilator hS W i s hs hs0 hFull v hμ₀ α hα hA trv htrv h2)

end Actual

end ZInQ.Manuscript.RC.KummerMaps
