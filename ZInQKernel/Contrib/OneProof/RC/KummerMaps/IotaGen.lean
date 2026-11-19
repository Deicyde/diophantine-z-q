import ZInQKernel.Contrib.OneProof.RC.KummerMaps.NonVacuity

/-!
# Lane RC29 (Kummer maps), round 2: the Kummer coefficient maps over an arbitrary coefficient ring

Manuscript `diophantine_zq.tex` (11/5):

* tex 2724–2730: "`A_i = (ℤ/2^iℤ)[t]/t^i`, `M_i = (T_2E ⊗ A_i)(χ_hΨ_i)`. For a fixed binary group
  `G`, use `A_i[G]` and the universal quadratic character."
* tex 2790–2796: "Let `R_i = A_i` in the scalar construction and `R_i = A_i[G]` in the binary
  construction. Write `α_i = χ_hΨ_i`, respectively `α_i = χ_0εΨ_i`, where `ε : G_K → G` is the
  restriction of the universal rational quadratic character."
* Lemma `ex:arith-local-kummer`, tex 3413–3440: the actual derived Kummer condition of the local
  twist `B = E^{(h)}` over `F = K_v`, extended to the coefficient ring ("derived coefficient
  extension defines the scalar `A_i` condition for this actual twist"; "The `A_i[G]` Kummer
  condition and its null-homotopy are consequently derived scalar extensions of the fixed local
  data").

Round 1 (`Iota.lean`, `KummerImage.lean`) built the Kummer coefficient map `ι_v` and the actual
Kummer condition for the scalar ring `R_i = A_i` (lane RC10's `Acoef i`) at the level `2^i`. The
binary construction needs the same maps over `R_i = A_i[G]`. This file generalizes them, with the
same proofs, to an arbitrary commutative coefficient ring `A` and an arbitrary level `N` (with
`E[N] ⊂ E(K_S)`, lane RC28's `FullTorsion`):

* `IsLocallyQuadAtGen A α χ v`: the character `α : G_{K,S} → A^×` of the coefficient module is
  `χ` (read in `A^×` through `ℤ^× → A^×`) on the decomposition group at `v`;
  `isLocallyQuadAtGen_acoef_iff`: for `A = A_i` it is round 1's `IsLocallyQuadAt`;
  `IsLocallyQuadAtGen.map` (transport along a ring map), `isLocallyQuadAtGen_charMul` (a factor
  that is trivial on the decomposition group does not change it), `isLocallyQuadAtGen_charInv`
  (the inverse character, as for the dual module), `isLocallyQuadAtGen_intUnitsTo` (the character
  `χ` itself; non-vacuity for every ring).
* `genIotaBase`, `genIota`: **the Kummer coefficient map `ι_v : B(K̄_v)[N] → (A ⊗ E(K_S)[N])(α)`,
  `t ↦ 1 ⊗ j⁻¹(φ_q t)`** (`φ_q = twistTors`, `j = compTorsEquiv`, `1 ⊗ − = oneTmul`, all landed in
  round 1, `q = j(s)` the local square root of `h`); `genIotaBase_smul`, `genIota_smul`:
  **`G_{K_v}`-equivariance** under `IsLocallyQuadAtGen A α χ_h v` (the hypothesis `hι` of lane
  RC28's `kummerAt`); `genIotaBase_injective` (given a ring map `A → ℤ/N`).
* `genKummerAt`: **the Kummer condition over `A`**, lane RC28's `kummerAt` with this `ι_v`;
  `genKummerAt_isInjective`, `genKummerAt_isIso_H0` (all of `H⁰`), `genKummerAt_mono_H1`,
  `genKummerMap` (the local Kummer map `B(K_v) → H¹(K_v, (A ⊗ E[N])(α))`), `genKummerMap_nsmul`,
  **`genKummerAt_range_eq_span`** (the `H¹`-image of the condition is the `A`-span of the image
  of the local Kummer map).
* `genIotaS`, `genIotaS_smul`, `genKummerAtS`: the same for the module built over `G_{K,S₀}` and
  inflated to the Selmer support `S ⊇ S₀` (lane RC28's `InflMod`).
* **Agreement with round 1** (all PROVED by `rfl`): `genIotaBase_acoef` (`= kummerIotaBase`),
  `genIota_acoef` (`= kummerIota`), `genKummerAt_acoef` (`= actualKummerAt`),
  `genKummerMap_acoef` (`= actualKummerMap`), `genIotaS_acoef` (`= kummerIotaS`),
  `genKummerAtS_acoef` (`= actualKummerAtS`).
* Non-vacuity: `genKummerAt_nonvacuous` (over `ℚ`, for every coefficient ring `A`, with
  `α = χ_1` read in `A^×`, the curve `E_1` of round 1, `N = 2`).

Kinds: definitions and PROVED, from lane RC28's `FullTorsion` (GLUE, as in round 1). No new
ELLIOT input: the local hypothesis is the predicate `IsLocallyQuadAtGen`, discharged for the scalar
and binary characters in `Binary.lean`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve TensorProduct
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
  ZInQ.Manuscript.RC.TwistDictionary ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-! ### The character of the coefficient module on the decomposition group -/

/-- Hypothesis predicate (tex 2790–2796, 3429–3440: at `v ∣ 2N` the moving character, and in the
binary construction also the universal character, are trivial on `G_{K_v}`). **The character
`α : G_{K,S} → A^×` of the coefficient module is `χ` on the decomposition group at `v`**:
`α(p_v σ) = χ(p_v σ)` for `σ ∈ G_{K_v}` (`χ` with values `±1`, read in `A^×`). For `A = A_i` this
is round 1's `IsLocallyQuadAt` (`isLocallyQuadAtGen_acoef_iff`). -/
def IsLocallyQuadAtGen (A : Type) [CommRing A] (α : GKS K S →* Aˣ) (χ : GKS K S →* ℤˣ)
    (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ σ : Gloc K v, α (locMap K S v σ) = intUnitsTo A (χ (locMap K S v σ))

/-- PROVED. For the scalar ring `A_i` the generic predicate is round 1's `IsLocallyQuadAt`. -/
theorem isLocallyQuadAtGen_acoef_iff (i : ℕ) (α : GKS K S →* (Acoef i)ˣ) (χ : GKS K S →* ℤˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    IsLocallyQuadAtGen (Acoef i) α χ v ↔ IsLocallyQuadAt i α χ v :=
  Iff.rfl

/-- PROVED. `ℤ^× → A^× → B^×` is `ℤ^× → B^×`, for a ring map `f : A → B`. -/
theorem units_map_intUnitsTo {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : ℤˣ) :
    Units.map f.toMonoidHom (intUnitsTo A u) = intUnitsTo B u :=
  Units.ext (map_intCast f (u : ℤ))

/-- PROVED. **Transport along a ring map**: if `α = χ` on the decomposition group, the same holds
for `α` read in `B^×` through a ring map `f : A → B` (e.g. `A_i → A_i[G]`, `a ↦ a[1]`). -/
theorem IsLocallyQuadAtGen.map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    {α : GKS K S →* Aˣ} {χ : GKS K S →* ℤˣ} {v : HeightOneSpectrum (𝓞 K)}
    (hα : IsLocallyQuadAtGen A α χ v) :
    IsLocallyQuadAtGen B ((Units.map f.toMonoidHom).comp α) χ v := fun σ => by
  rw [MonoidHom.comp_apply, hα σ, units_map_intUnitsTo]

/-- PROVED. **A factor trivial on the decomposition group does not change the local character**:
if `α = χ` and `β = 1` on `G_{K_v}`, then `αβ = χ` there (tex 3429–3437: the moving character, and
the universal character in the binary construction, are trivial on `G_{K_v}` at `v ∣ 2N`). -/
theorem isLocallyQuadAtGen_charMul {A : Type} [CommRing A] {α β : GKS K S →* Aˣ}
    {χ : GKS K S →* ℤˣ} {v : HeightOneSpectrum (𝓞 K)} (hα : IsLocallyQuadAtGen A α χ v)
    (hβ : ∀ σ : Gloc K v, β (locMap K S v σ) = 1) : IsLocallyQuadAtGen A (charMul α β) χ v :=
  fun σ => by rw [charMul_apply, hα σ, hβ σ, mul_one]

/-- PROVED. **The inverse character** (the character of the dual module `M^*(1)` up to the
cyclotomic factor): if `α = χ` on the decomposition group, so is `α⁻¹` (`χ = χ⁻¹`, values `±1`). -/
theorem isLocallyQuadAtGen_charInv {A : Type} [CommRing A] {α : GKS K S →* Aˣ}
    {χ : GKS K S →* ℤˣ} {v : HeightOneSpectrum (𝓞 K)} (hα : IsLocallyQuadAtGen A α χ v) :
    IsLocallyQuadAtGen A (charInv α) χ v := fun σ => by
  rw [charInv_apply, hα σ, ← map_inv, Int.units_inv_eq_self]

/-- PROVED (non-vacuity of `IsLocallyQuadAtGen` over every ring). The character `χ` itself, read
in `A^×`, is `χ` on every decomposition group. -/
theorem isLocallyQuadAtGen_intUnitsTo (A : Type) [CommRing A] (χ : GKS K S →* ℤˣ)
    (v : HeightOneSpectrum (𝓞 K)) : IsLocallyQuadAtGen A ((intUnitsTo A).comp χ) χ v :=
  fun _ => rfl

/-! ### The Kummer coefficient map `ι_v` over an arbitrary coefficient ring -/

section Gen

variable (A : Type) [CommRing A] (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ) [NeZero N]
  (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
  (α : GKS K S →* Aˣ) (hFull : FullTorsion K S W N) (v : HeightOneSpectrum (𝓞 K))

/-- Definition (tex 3413–3440, 2790–2796). **The Kummer coefficient map over the coefficient ring
`A`**, before the restriction of the action to `G_{K_v}`: `t ↦ 1 ⊗ j⁻¹(φ_q(t))`, from the
`N`-torsion of the local twist `B = E^{(h)}` over `K_v` into `(A ⊗ E(K_S)[N])(α)` (lane RC28's
`CoefMod`); `φ_q` is the twist identification at `q = j(s)` (`twistTors`), `j⁻¹` the inverse of the
comparison along the fixed embedding (`compTorsEquiv`), `t ↦ 1 ⊗ t` is `oneTmul`. For `A = A_i`,
`N = 2^i` it is round 1's `kummerIotaBase` (`genIotaBase_acoef`). -/
def genIotaBase :
    TorsAlg (v.adicCompletion K) (localTwist W h v) N →+ CoefMod A α (TorsS K S W (N : ℤ)) :=
  (oneTmul A α (TorsS K S W (N : ℤ))).comp
    ((compTorsEquiv W N hFull v).symm.toAddMonoidHom.comp
      (twistTors (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
        two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v) N).toAddMonoidHom)

/-- PROVED. The value of the Kummer coefficient map: `t ↦ 1 ⊗ j⁻¹(φ_q t)`. -/
theorem genIotaBase_apply (t : TorsAlg (v.adicCompletion K) (localTwist W h v) N) :
    genIotaBase A W N s hs hs0 α hFull v t =
      oneTmul A α (TorsS K S W (N : ℤ))
        ((compTorsEquiv W N hFull v).symm
          (twistTors (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
            two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v) N t)) :=
  rfl

/-- PROVED (tex 3413–3440). **Equivariance of the Kummer coefficient map over `A`**:
`ι_v(σ t) = p_v(σ) • ι_v(t)`, when the character `α` is `χ_h` on the decomposition group
(`IsLocallyQuadAtGen`). The proof is round 1's, with the landed `twistTors_smul`,
`compTorsEquiv_symm_smul`, `twistSign_localSqrt` and `smul_oneTmul`. -/
theorem genIotaBase_smul (hα : IsLocallyQuadAtGen A α (quadChar s hs hs0) v) (σ : Gloc K v)
    (t : TorsAlg (v.adicCompletion K) (localTwist W h v) N) :
    genIotaBase A W N s hs hs0 α hFull v (σ • t) =
      locMap K S v σ • genIotaBase A W N s hs hs0 α hFull v t := by
  rw [genIotaBase_apply, genIotaBase_apply, twistTors_smul, map_zsmul,
    compTorsEquiv_symm_smul, twistSign_localSqrt s hs hs0 v σ, map_zsmul,
    smul_oneTmul A α _ (locMap K S v σ) _ (quadChar s hs hs0 (locMap K S v σ)) (hα σ)]

/-- PROVED. **The Kummer coefficient map is injective** when `A` has a ring map to `ℤ/N` (for
`A_i` the constant coefficient `acoefConst`, for `A_i[G]` composed with the augmentation). -/
theorem genIotaBase_injective (ε : A →+* ZMod N) :
    Function.Injective (genIotaBase A W N s hs hs0 α hFull v) := by
  have hT : ∀ t : TorsS K S W (N : ℤ), N • t = 0 := fun t => by
    have := AddSubgroup.torsionBy.nsmul_iff.1 t.2
    exact Subtype.ext this
  intro t t' htt
  rw [genIotaBase_apply, genIotaBase_apply] at htt
  have h1 := oneTmul_injective A ε α _ hT htt
  exact (twistTors _ _ _ _ _ _).injective ((compTorsEquiv W N hFull v).symm.injective h1)

/-- Definition (tex 3413–3440). **The Kummer coefficient map `ι_v` over `A`**, with `G_{K_v}`
acting on `(A ⊗ E(K_S)[N])(α)` through `p_v` (`ResMod (locMap K S v)`, the format of lane RC28's
`kummerAt`). -/
def genIota :
    TorsAlg (v.adicCompletion K) (localTwist W h v) N →+
      ResMod (locMap K S v) (CoefMod A α (TorsS K S W (N : ℤ))) :=
  (toResModAdd (locMap K S v) (CoefMod A α (TorsS K S W (N : ℤ)))).comp
    (genIotaBase A W N s hs hs0 α hFull v)

/-- PROVED. The value of `ι_v`. -/
theorem genIota_apply (t : TorsAlg (v.adicCompletion K) (localTwist W h v) N) :
    genIota A W N s hs hs0 α hFull v t =
      toResModAdd (locMap K S v) (CoefMod A α (TorsS K S W (N : ℤ)))
        (genIotaBase A W N s hs hs0 α hFull v t) :=
  rfl

/-- PROVED (tex 3413–3440). **`ι_v` over `A` is `G_{K_v}`-equivariant** (lane RC28's hypothesis
`hι` of `kummerAt`), when `α = χ_h` on the decomposition group. -/
theorem genIota_smul (hα : IsLocallyQuadAtGen A α (quadChar s hs hs0) v) (σ : Gloc K v)
    (t : TorsAlg (v.adicCompletion K) (localTwist W h v) N) :
    genIota A W N s hs hs0 α hFull v (σ • t) = σ • genIota A W N s hs hs0 α hFull v t := by
  rw [genIota_apply, genIota_apply, smul_toResModAdd,
    genIotaBase_smul A W N s hs hs0 α hFull v hα σ t]

end Gen

/-- PROVED (`rfl`). **For `A = A_i` and `N = 2^i` the generic map is round 1's
`kummerIotaBase`.** -/
theorem genIotaBase_acoef (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (α : GKS K S →* (Acoef i)ˣ)
    (hFull : FullTorsion K S W (2 ^ i)) (v : HeightOneSpectrum (𝓞 K)) :
    genIotaBase (Acoef i) W (2 ^ i) s hs hs0 α hFull v = kummerIotaBase W i s hs hs0 α hFull v :=
  rfl

/-- PROVED (`rfl`). **For `A = A_i` and `N = 2^i` the generic `ι_v` is round 1's `kummerIota`.** -/
theorem genIota_acoef (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (α : GKS K S →* (Acoef i)ˣ)
    (hFull : FullTorsion K S W (2 ^ i)) (v : HeightOneSpectrum (𝓞 K)) :
    genIota (Acoef i) W (2 ^ i) s hs hs0 α hFull v = kummerIota W i s hs hs0 α hFull v :=
  rfl

/-! ### The Kummer condition over `A` -/

section GenCond

variable (A : Type) [CommRing A] (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ) [NeZero N]
  (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
  (α : GKS K S →* Aˣ) [IsOpenKer α] (hFull : FullTorsion K S W N) (v : Places K S)
  (hα : IsLocallyQuadAtGen A α (quadChar s hs hs0) v.1)

open scoped Classical in
/-- Definition (tex 2754–2756, 3413–3440). **The Kummer local condition at `v ∈ S` over the
coefficient ring `A`**: lane RC28's `kummerAt` (the finite-level subcomplex `U⁰ = C⁰`,
`U¹ = span_A(ι_v ∘ κ_P) + B¹`, `Uⁿ = 0` of `C^•_cont(G_{K_v}, (A ⊗ E[N])(α))`) for the local
twist `B = E^{(h)}` and the coefficient map `ι_v` over `A`. -/
def genKummerAt : CondAt K S A (CoefMod A α (TorsS K S W (N : ℤ))) v :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  kummerAt v (localTwist W h v.1) N (genIota A W N s hs hs0 α hFull v.1)
    (genIota_smul A W N s hs hs0 α hFull v.1 hα)

open scoped Classical in
/-- PROVED. The Kummer condition over `A` is a subcomplex of the local cochains. -/
theorem genKummerAt_isInjective : (genKummerAt A W N s hs hs0 α hFull v hα).IsInjective :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  kummerAt_isInjective v (localTwist W h v.1) N (genIota A W N s hs hs0 α hFull v.1)
    (genIota_smul A W N s hs hs0 α hFull v.1 hα)

open scoped Classical in
/-- PROVED (tex 3415–3417, degree zero). **The Kummer condition over `A` has all of `H⁰`**. -/
theorem genKummerAt_isIso_H0 :
    IsIso (HomologicalComplex.homologyMap
      (GHom.toCC (genKummerAt A W N s hs hs0 α hFull v hα).i) 0) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact kummerConditionIn_isIso_homologyMap_zero A (genIota A W N s hs hs0 α hFull v.1)
    (genIota_smul A W N s hs hs0 α hFull v.1 hα)

open scoped Classical in
/-- PROVED (tex 3415–3418, degree one). **The Kummer condition over `A` injects on `H¹`**. -/
theorem genKummerAt_mono_H1 :
    Mono (HomologicalComplex.homologyMap
      (GHom.toCC (genKummerAt A W N s hs hs0 α hFull v hα).i) 1) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact cocycleCondition_mono_homologyMap_one _ _

open scoped Classical in
/-- Definition (tex 3413–3418, 3442–3445). **The local Kummer map of `B = E^{(h)}` over `K_v` with
coefficients in `(A ⊗ E[N])(α)`**: `B(K_v) → H¹(K_v, (A ⊗ E[N])(α))`, `P ↦ ι_{v,*}[κ_P]`
(`kummerMapIn` for the coefficient map over `A`). -/
def genKummerMap :
    (localTwist W h v.1).toAffine.Point →+
      (locAt K S A (CoefMod A α (TorsS K S W (N : ℤ))) v).toCC.homology 1 :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  kummerMapIn A (genIota A W N s hs hs0 α hFull v.1) (genIota_smul A W N s hs hs0 α hFull v.1 hα)

open scoped Classical in
/-- PROVED (tex 3415–3418). **The local Kummer map over `A` factors through `B(K_v)/N B(K_v)`**. -/
theorem genKummerMap_nsmul (P' : (localTwist W h v.1).toAffine.Point) :
    genKummerMap A W N s hs hs0 α hFull v hα (N • P') = 0 := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact kummerMapIn_nsmul A (genIota A W N s hs hs0 α hFull v.1)
    (genIota_smul A W N s hs hs0 α hFull v.1 hα) P'

open scoped Classical in
/-- PROVED (tex 3415–3418, 3429–3440: "`B(F)/2^aB(F)` in degree one", "derived coefficient
extension"). **The Kummer condition over `A`, in `H¹`, is the `A`-span of the image of the local
Kummer map**: `range(H¹(U_v) → H¹(K_v, (A ⊗ E[N])(α))) = span_A {ι_{v,*}[κ_P] : P ∈ B(K_v)}`. -/
theorem genKummerAt_range_eq_span :
    LinearMap.range (HomologicalComplex.homologyMap
      (GHom.toCC (genKummerAt A W N s hs hs0 α hFull v hα).i) 1).hom =
      Submodule.span A (Set.range (genKummerMap A W N s hs hs0 α hFull v hα)) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact range_homologyMap_kummerConditionIn A (genIota A W N s hs hs0 α hFull v.1)
    (genIota_smul A W N s hs hs0 α hFull v.1 hα)

end GenCond

open scoped Classical in
/-- PROVED (`rfl`). **For `A = A_i` and `N = 2^i` the Kummer condition over `A` is round 1's
`actualKummerAt`.** -/
theorem genKummerAt_acoef (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (α : GKS K S →* (Acoef i)ˣ)
    [IsOpenKer α] (hFull : FullTorsion K S W (2 ^ i)) (v : Places K S)
    (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v.1) :
    genKummerAt (Acoef i) W (2 ^ i) s hs hs0 α hFull v hα =
      actualKummerAt W i s hs hs0 α hFull v hα :=
  rfl

open scoped Classical in
/-- PROVED (`rfl`). **For `A = A_i` and `N = 2^i` the local Kummer map over `A` is round 1's
`actualKummerMap`.** -/
theorem genKummerMap_acoef (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (α : GKS K S →* (Acoef i)ˣ)
    [IsOpenKer α] (hFull : FullTorsion K S W (2 ^ i)) (v : Places K S)
    (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v.1) :
    genKummerMap (Acoef i) W (2 ^ i) s hs hs0 α hFull v hα =
      actualKummerMap W i s hs hs0 α hFull v hα :=
  rfl

/-! ### The module built over `G_{K,S₀}`, inflated to the Selmer support `S ⊇ S₀` -/

section GenInflated

variable {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (A : Type) [CommRing A]
  (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ) [NeZero N] (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (α : GKS K S₀ →* Aˣ)
  (hFull : FullTorsion K S₀ W N)

/-- Definition (tex 3413–3440 with (4.3), tex 3455–3463). **The Kummer coefficient map over `A`
into the inflated module** `InflMod hS (A ⊗ E[N])(α)` (built over `G_{K,S₀}`, inflated to
`G_{K,S}`), at a place `v ∈ S`. -/
def genIotaS (v : Places K S) :
    TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) N →+
      ResMod (locMap K S v.1) (InflMod hS (CoefMod A α (TorsS K S₀ W (N : ℤ)))) :=
  (toResModAdd (locMap K S v.1) (InflMod hS (CoefMod A α (TorsS K S₀ W (N : ℤ))))).comp
    ((toResModAdd (inflMap K hS) (CoefMod A α (TorsS K S₀ W (N : ℤ)))).comp
      (genIotaBase (S := S₀) A W N s hs hs0 α hFull v.1))

/-- PROVED (lane RC26's `locMap_compat`). **The inflated Kummer coefficient map over `A` is
`G_{K_v}`-equivariant.** -/
theorem genIotaS_smul (v : Places K S)
    (hα : IsLocallyQuadAtGen (S := S₀) A α (quadChar s hs hs0) v.1) (σ : Gloc K v.1)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) N) :
    genIotaS hS A W N s hs hs0 α hFull v (σ • t) = σ • genIotaS hS A W N s hs hs0 α hFull v t := by
  change toResModAdd (locMap K S v.1) (InflMod hS (CoefMod A α (TorsS K S₀ W (N : ℤ))))
      (toResModAdd (inflMap K hS) (CoefMod A α (TorsS K S₀ W (N : ℤ)))
        (genIotaBase (S := S₀) A W N s hs hs0 α hFull v.1 (σ • t))) =
    σ • toResModAdd (locMap K S v.1) (InflMod hS (CoefMod A α (TorsS K S₀ W (N : ℤ))))
      (toResModAdd (inflMap K hS) (CoefMod A α (TorsS K S₀ W (N : ℤ)))
        (genIotaBase (S := S₀) A W N s hs hs0 α hFull v.1 t))
  rw [smul_toResModAdd, smul_toResModAdd, locMap_compat K hS v.1 σ,
    genIotaBase_smul (S := S₀) A W N s hs hs0 α hFull v.1 hα σ t]

open scoped Classical in
/-- Definition (tex 2754–2756, 3413–3440). **The Kummer local condition over `A` at `v ∈ S` for the
inflated module**: lane RC28's `kummerAt` with the inflated coefficient map. -/
def genKummerAtS [IsOpenKer α] (v : Places K S)
    (hα : IsLocallyQuadAtGen (S := S₀) A α (quadChar s hs hs0) v.1) :
    CondAt K S A (InflMod hS (CoefMod A α (TorsS K S₀ W (N : ℤ)))) v :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  kummerAt v (localTwist W h v.1) N (genIotaS hS A W N s hs hs0 α hFull v)
    (genIotaS_smul hS A W N s hs hs0 α hFull v hα)

open scoped Classical in
/-- PROVED. The inflated Kummer condition over `A` is a subcomplex of the local cochains. -/
theorem genKummerAtS_isInjective [IsOpenKer α] (v : Places K S)
    (hα : IsLocallyQuadAtGen (S := S₀) A α (quadChar s hs hs0) v.1) :
    (genKummerAtS hS A W N s hs hs0 α hFull v hα).IsInjective :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  kummerAt_isInjective v (localTwist W h v.1) N (genIotaS hS A W N s hs hs0 α hFull v)
    (genIotaS_smul hS A W N s hs hs0 α hFull v hα)

end GenInflated

/-- PROVED (`rfl`). For `A = A_i` and `N = 2^i` the inflated generic map is round 1's
`kummerIotaS`. -/
theorem genIotaS_acoef {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
    (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (α : GKS K S₀ →* (Acoef i)ˣ)
    (hFull : FullTorsion K S₀ W (2 ^ i)) (v : Places K S) :
    genIotaS hS (Acoef i) W (2 ^ i) s hs hs0 α hFull v = kummerIotaS hS W i s hs hs0 α hFull v :=
  rfl

open scoped Classical in
/-- PROVED (`rfl`). For `A = A_i` and `N = 2^i` the inflated Kummer condition over `A` is round
1's `actualKummerAtS`. -/
theorem genKummerAtS_acoef {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
    (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (α : GKS K S₀ →* (Acoef i)ˣ)
    [IsOpenKer α] (hFull : FullTorsion K S₀ W (2 ^ i)) (v : Places K S)
    (hα : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v.1) :
    genKummerAtS hS (Acoef i) W (2 ^ i) s hs hs0 α hFull v hα =
      actualKummerAtS hS W i s hs hs0 α hFull v hα :=
  rfl

/-! ### Non-vacuity -/

/-- PROVED. A character `χ : G_{K,S} → ℤ^×` with open kernel, read in `A^×`, has open kernel. -/
instance genIsOpenKer_intUnitsTo (A : Type) [CommRing A] (χ : GKS K S →* ℤˣ) [IsOpenKer χ] :
    IsOpenKer ((intUnitsTo A).comp χ) :=
  isOpenKer_map χ (intUnitsTo A)

open scoped Classical in
/-- PROVED (non-vacuity of the hypotheses of `genIota_smul` and `genKummerAt`, for every
coefficient ring `A`). Over `ℚ`, for every `S` and every `v ∈ S`, with `h = 1` (`s = 1`), the
character `α = χ_1` read in `A^×` (open kernel, `IsLocallyQuadAtGen` everywhere), the curve
`E_1 : y² = x(x − 1)(x + 3)` and `N = 2^1` (lane RC28's `FullTorsion` instance), the Kummer
condition over `A` exists and is a subcomplex of the local cochains. -/
theorem genKummerAt_nonvacuous (A : Type) [CommRing A] (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    (v : Places ℚ S) :
    ∃ c : CondAt ℚ S A (CoefMod A ((intUnitsTo A).comp
        (quadChar (1 : KS ℚ S) (one_sq_KS S) one_ne_zero))
        (TorsS ℚ S (ZInQ.Manuscript.RC.CoefModules.curveEll (1 : ℚ)) ((2 ^ 1 : ℕ) : ℤ))) v,
      c.IsInjective := by
  have := isElliptic_curveEll (K := ℚ) one_ne_zero
  exact ⟨genKummerAt A (curveEll 1) (2 ^ 1) 1 (one_sq_KS S) one_ne_zero _
      (fullTorsion_curveEll_one S) v (isLocallyQuadAtGen_intUnitsTo A _ v.1),
    genKummerAt_isInjective A (curveEll 1) (2 ^ 1) 1 (one_sq_KS S) one_ne_zero _
      (fullTorsion_curveEll_one S) v (isLocallyQuadAtGen_intUnitsTo A _ v.1)⟩

end ZInQ.Manuscript.RC.KummerMaps
