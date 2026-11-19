import ZInQKernel.Contrib.OneProof.RC.KummerMaps.Twist
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.LocalGlobal

/-!
# Lane RC29 (Kummer maps), part 3: the Kummer coefficient maps `ι_v` and the actual Kummer condition

Manuscript `diophantine_zq.tex` (11/5):

* tex 2724–2727: `A_i = (ℤ/2^iℤ)[t]/t^i`, `M_i = (T_2E ⊗ A_i)(χ_hΨ_i)`;
* Definition `ex:arith-data`, tex 2754–2756: "The primitive and relaxed complexes use the actual
  derived Kummer, unramified, full and orthogonal local conditions specified below, with their
  maps and homotopies";
* Lemma `ex:arith-local-kummer`, tex 3413–3438: "For the actual local twist `B = E^{(h)}` over
  `F = K_v`, the condition `U_F = B(F)^∧_2[−1] → RΓ(F, T_2B)` … At `v ∣ 2N`, `Ψ_i` is trivial, so
  derived coefficient extension defines the scalar `A_i` condition for this actual twist."
  "These are the local maps used in the Selmer-cone duality above."
* tex 2729: "The character `Ψ_i` is finite, trivial at `2N`, ramified at a moving conductor prime
  `r_i`"; tex 2733–2736: "Apply Proposition `ex:arith-moving-character` to an orientation above
  every `q ∈ Q`, prescribing `ξ_i(Fr_q) = 1` at each finite stage"; Proposition
  `ex:arith-moving-character`, tex 3500–3506: the moving character is "trivial on the local
  decomposition groups at `2N`"; tex 3431: "At `v ∣ 2N`, `Ψ_i` is trivial".

The coefficient map of the text is the composite of three identifications at finite level,
`B(K̄_v)[2^i] ≅ E(K̄_v)[2^i](χ_h) ≅ E(K_S)[2^i](χ_h) → M_i`, `t ↦ 1 ⊗ t`:

* `localTwist W h v`: the actual local twist `B = E^{(h)}` over `K_v` (lane RC18's `twistK` of
  `W ×_K K_v` by `h`; `localTwist_eq_baseChange`: the base change of the global twist);
  `isElliptic_localTwist` for `h ≠ 0`.
* `localSqrt s v = j(s)`: the image in `K̄_v` of the square root `s ∈ K_S` of `h` defining lane
  RC28's `quadChar s` (`χ_h`) under the fixed embedding `j` (`LocalGlobal.lean`);
  `twistSign_localSqrt`: **the local quadratic character is `χ_h ∘ p_v`** (PROVED).
* `IsLocallyQuadAt i α χ v`: `α ∘ p_v = χ ∘ p_v` on `G_{K_v}` (the character of `M_i` is `χ_h` on
  the decomposition group); `isLocallyQuadAt_alphaChar`: it holds for lane RC28's
  `α_i = alphaChar i χ_h ξ` as soon as `ξ` is trivial on the decomposition group at `v` (ELLIOT).
  The text supplies this at `v ∣ 2N` (tex 2729, 3430–3432, 3503–3506). At graph primes it instead
  prescribes additive exponent one, hence Frobenius value `1+t` (tex 2733–2736, 4275–4277); this
  hypothesis is not supplied there.
* **`kummerIotaBase`, `kummerIota`: the Kummer coefficient map `ι_v : B(K̄_v)[2^i] → M_i`**,
  `t ↦ 1 ⊗ j⁻¹(φ_q(t))` (`φ_q = twistTors`, `j = compTorsEquiv`), with values in `M_i`, resp. in
  `M_i` with `G_{K_v}` acting through `p_v` (`ResMod (locMap K S v)`, the format of lane RC28's
  `kummerAt`); **`kummerIotaBase_smul`, `kummerIota_smul`: it is `G_{K_v}`-equivariant** —
  exactly lane RC28's hypothesis `hι` of `kummerAt` (PROVED, from `FullTorsion`, GLUE as in lane
  RC28); `kummerIotaBase_injective`: it is injective for `i ≠ 0` (through the constant
  coefficient `acoefConst : A_i → ℤ/2^i` and `oneTmul_injective`).
* `actualKummerAt`: **the actual Kummer local condition at `v`** — lane RC28's `kummerAt` with the
  genuine `ι_v`; `actualKummerAt_isInjective`.
* `kummerIotaS`, `actualKummerAtS`: the same for the module `M_i` built over `G_{K,S₀}` and
  inflated to the Selmer support `S ⊇ S₀` (lane RC28's `MinS`), through lane RC26's
  `locMap_compat`; `kummerSelData`: **the actual Selmer data with the genuine Kummer conditions**
  at a set `P ⊆ S₀` of places where the moving character is locally trivial (the places above
  `2N`), any given conditions at the rest of `S₀`, the unramified condition at `S − S₀` (lane
  RC28's `actualSelData`); `isGaloisSelData_kummerSelData` (PROVED).
* Non-vacuity: `kummerIota_nonvacuous` (`ℚ`, `E_ℓ`, `i = 1`, `h = 1`, `ξ = 1`).

Kinds: definitions and PROVED, from lane RC28's `FullTorsion` (GLUE) and the ELLIOT hypothesis
that `ξ` is trivial on the decomposition group (only in `isLocallyQuadAt_alphaChar`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open NumberField IsDedekindDomain WeierstrassCurve TensorProduct ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.TwistDictionary
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-! ### The actual local twist -/

/-- Definition (tex 3413–3416: "the actual local twist `B = E^{(h)}` over `F = K_v`"). **The local
twist**: lane RC18's quadratic twist `twistK` of `W ×_K K_v` by `h`. -/
abbrev localTwist (W : WeierstrassCurve K) (h : K) (v : HeightOneSpectrum (𝓞 K)) :
    WeierstrassCurve (v.adicCompletion K) :=
  twistK (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)

/-- PROVED. The local twist is the base change to `K_v` of the global twist `E^{(h)}`
(lane RC18's `twistK_map`). -/
theorem localTwist_eq_baseChange (W : WeierstrassCurve K) (h : K) (v : HeightOneSpectrum (𝓞 K)) :
    localTwist W h v = (twistK W h).baseChange (v.adicCompletion K) :=
  (twistK_map W (algebraMap K (v.adicCompletion K)) h).symm

/-- PROVED. A quadratic twist of an elliptic curve by a nonzero parameter is elliptic
(`Δ(twistK W d) = d⁶ Δ(W)`, lane RC18's `twistK_Δ`). -/
theorem isElliptic_twistK {L : Type*} [Field L] (h2 : (2 : L) ≠ 0) (W : WeierstrassCurve L)
    [W.IsElliptic] {d : L} (hd : d ≠ 0) : (twistK W d).IsElliptic :=
  ⟨by rw [twistK_Δ W h2 d]; exact (IsUnit.mk0 _ (pow_ne_zero 6 hd)).mul W.isUnit_Δ⟩

/-- PROVED. The local twist of an elliptic curve by `h ≠ 0` is elliptic. -/
theorem isElliptic_localTwist (W : WeierstrassCurve K) [W.IsElliptic] {h : K} (hh : h ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) : (localTwist W h v).IsElliptic :=
  isElliptic_twistK two_ne_zero _ ((map_ne_zero _).2 hh)

/-! ### The local square root and the local quadratic character -/

section Sqrt

variable (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
  (v : HeightOneSpectrum (𝓞 K))

/-- Definition. **The local square root** `q = j(s) ∈ K̄_v` of `h`, the image of lane RC28's square
root `s ∈ K_S` (the one defining `χ_h = quadChar s`) under the fixed embedding `j`. -/
def localSqrt : AlgebraicClosure (v.adicCompletion K) := embS K S v s

include hs in
/-- PROVED. `j(s)² = h` in `K̄_v`. -/
theorem localSqrt_sq :
    localSqrt s v ^ 2 =
      algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
        (algebraMap K (v.adicCompletion K) h) := by
  rw [localSqrt, ← map_pow, hs, AlgHom.commutes]
  rfl

include hs0 in
/-- PROVED. `j(s) ≠ 0`. -/
theorem localSqrt_ne_zero : localSqrt s v ≠ 0 :=
  (map_ne_zero (embS K S v).toRingHom).2 hs0

omit [NumberField K] in
include hs hs0 in
/-- PROVED. `h ≠ 0`. -/
theorem ne_zero_of_sqrt : h ≠ 0 := by
  rintro rfl
  rw [map_zero, sq_eq_zero_iff] at hs
  exact hs0 hs

/-- PROVED (tex 3431–3433). **The local quadratic character of `K_v(√h)/K_v` is `χ_h ∘ p_v`**:
for `σ ∈ G_{K_v}`, `twistSign (j s) σ = quadChar s (p_v σ)`. -/
theorem twistSign_localSqrt (σ : Gloc K v) :
    twistSign (localSqrt s v) σ = quadChar s hs hs0 (locMap K S v σ) := by
  have h1 := twistSign_spec (algebraMap K (v.adicCompletion K) h) (localSqrt_sq s hs v) σ
  have h2 : σ.toAlgHom (localSqrt s v) =
      ((quadChar s hs hs0 (locMap K S v σ) : ℤˣ) : ℤ) • localSqrt s v := by
    rw [localSqrt, ← embS_locMap K S v σ s, quadChar_spec s hs hs0, map_zsmul]
  rw [h1] at h2
  have hq := localSqrt_ne_zero s hs0 v
  have h3 : (((twistSign (localSqrt s v) σ : ℤˣ) : ℤ) : AlgebraicClosure (v.adicCompletion K)) =
      (((quadChar s hs hs0 (locMap K S v σ) : ℤˣ) : ℤ) : AlgebraicClosure (v.adicCompletion K)) := by
    rw [zsmul_eq_mul, zsmul_eq_mul] at h2
    exact mul_right_cancel₀ hq h2
  exact Units.ext (Int.cast_injective h3)

end Sqrt

/-! ### The character of `M_i` on the decomposition group -/

/-- Hypothesis predicate (tex 3431: "At `v ∣ 2N`, `Ψ_i` is trivial"; tex 2729, 2733–2736,
3500–3506). **The character `α` of `M_i` is `χ` on the decomposition group at `v`**: `α(p_v σ) = χ(p_v σ)` for `σ ∈ G_{K_v}`
(`χ` with values `±1`, read in `A_i^×`). -/
def IsLocallyQuadAt (i : ℕ) (α : GKS K S →* (Acoef i)ˣ) (χ : GKS K S →* ℤˣ)
    (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ σ : Gloc K v, α (locMap K S v σ) = intUnitsTo (Acoef i) (χ (locMap K S v σ))

/-- PROVED from ELLIOT. For `α_i = χ_h Ψ_i`, `α_i = χ_h` on the decomposition group at `v`
when `ξ_i` is trivial there. The text supplies this at `v ∣ 2N` (tex 2729, 3430–3432,
3503–3506). At graph primes it instead prescribes additive exponent one, hence Frobenius value
`1+t` (tex 2733–2736, 4275–4277); this hypothesis is not supplied there. -/
theorem isLocallyQuadAt_alphaChar (i : ℕ) (χ : GKS K S →* ℤˣ)
    (ξ : GKS K S →* Multiplicative (ZMod (2 ^ (2 * i)))) (v : HeightOneSpectrum (𝓞 K))
    (hξ : ∀ σ : Gloc K v, ξ (locMap K S v σ) = 1) :
    IsLocallyQuadAt i (alphaChar i χ ξ) χ v := by
  intro σ
  rw [alphaChar, charMul_apply, MonoidHom.comp_apply]
  have : movingCharS i ξ (locMap K S v σ) = 1 := by
    rw [movingCharS, HeegnerAlgebra.movingChar, MonoidHom.comp_apply, hξ σ, map_one]
  rw [this, mul_one]

/-! ### The coefficient map `t ↦ 1 ⊗ t` -/

/-- Definition (tex 2726, 3430–3432: `T_2E ⊗ A_i`, coefficient extension). **`t ↦ 1 ⊗ t`**,
`T → (A ⊗_ℤ T)(α)` (lane RC28's `CoefMod`). -/
def oneTmul (A : Type) [CommRing A] {G : Type} [Group G] (α : G →* Aˣ) (T : Type)
    [AddCommGroup T] : T →+ CoefMod A α T :=
  (CoefMod.equiv A α T).toAddEquiv.toAddMonoidHom.comp (TensorProduct.mk ℤ A T 1).toAddMonoidHom

theorem oneTmul_apply (A : Type) [CommRing A] {G : Type} [Group G] (α : G →* Aˣ) (T : Type)
    [AddCommGroup T] (t : T) : oneTmul A α T t = CoefMod.equiv A α T ((1 : A) ⊗ₜ t) :=
  rfl

/-- PROVED (tex 3429–3432). On the decomposition group, where `α = χ` with `χ = ±1`:
`g • (1 ⊗ t) = χ(g) • (1 ⊗ g t)`. -/
theorem smul_oneTmul (A : Type) [CommRing A] {G : Type} [Group G] (α : G →* Aˣ) (T : Type)
    [AddCommGroup T] [DistribMulAction G T] (g : G) (t : T) (u : ℤˣ)
    (hg : α g = intUnitsTo A u) :
    g • oneTmul A α T t = ((u : ℤˣ) : ℤ) • oneTmul A α T (g • t) := by
  rw [oneTmul_apply, CoefMod.smul_tmul, hg, oneTmul_apply, mul_one,
    ← map_zsmul (CoefMod.equiv A α T)]
  congr 1
  rw [TensorProduct.smul_tmul', zsmul_eq_mul, mul_one]
  rfl

/-- Definition (tex 2724–2725). **The constant coefficient** `A_i → ℤ/2^i`, `t ↦ 0` (for `i ≠ 0`). -/
def acoefConst (i : ℕ) (hi : i ≠ 0) : Acoef i →+* ZMod (2 ^ i) :=
  Ideal.Quotient.lift _ Polynomial.constantCoeff (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have hX : Polynomial.constantCoeff (Polynomial.X : Polynomial (ZMod (2 ^ i))) = 0 :=
      Polynomial.coeff_X_zero
    rw [map_mul, map_pow, hX, zero_pow hi, mul_zero])

/-- PROVED. **`t ↦ 1 ⊗ t` is injective on an `n`-torsion group** `T`, for a ring `A` with a ring
map `A → ℤ/n` (a retraction: `a ⊗ t ↦ ε(a) t`). -/
theorem oneTmul_injective (A : Type) [CommRing A] {n : ℕ} [NeZero n] (ε : A →+* ZMod n)
    {G : Type} [Group G] (α : G →* Aˣ) (T : Type) [AddCommGroup T] (hT : ∀ t : T, n • t = 0) :
    Function.Injective (oneTmul A α T) := by
  let _ : Module (ZMod n) T := AddCommGroup.zmodModule hT
  let β : A →ₗ[ℤ] T →ₗ[ℤ] T := LinearMap.mk₂ ℤ (fun a t => ε a • t)
    (fun a b t => by rw [map_add, add_smul])
    (fun c a t => by rw [map_zsmul, smul_assoc])
    (fun a t t' => smul_add _ _ _)
    (fun c a t => smul_comm _ _ _)
  intro t t' h
  have h1 := congrArg (TensorProduct.lift β) h
  change TensorProduct.lift β ((1 : A) ⊗ₜ t) = TensorProduct.lift β ((1 : A) ⊗ₜ t') at h1
  rw [TensorProduct.lift.tmul, TensorProduct.lift.tmul] at h1
  simpa [β] using h1

/-- Definition. The identity of `M`, as an additive map into the restricted module `ResMod φ M`
(lane RC26's `ResMod`, the same group with the action through `φ`). -/
def toResModAdd {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    (φ : H →ₜ* G) (M : Type) [AddCommGroup M] : M →+ ResMod φ M :=
  AddMonoidHom.id M

/-- PROVED. `h • m = φ(h) • m` in the restricted module. -/
theorem smul_toResModAdd {G H : Type} [Group G] [Group H] [TopologicalSpace G]
    [TopologicalSpace H] (φ : H →ₜ* G) (M : Type) [AddCommGroup M] [DistribMulAction G M] (h : H)
    (m : M) : h • toResModAdd φ M m = toResModAdd φ M (φ h • m) :=
  rfl

/-! ### The Kummer coefficient map `ι_v` -/

section Iota

variable (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (α : GKS K S →* (Acoef i)ˣ)
  (hFull : FullTorsion K S W (2 ^ i)) (v : HeightOneSpectrum (𝓞 K))

/-- Definition (tex 3413–3438). **The Kummer coefficient map with values in `M_i`**, before the
restriction of the action to `G_{K_v}`: `t ↦ 1 ⊗ j⁻¹(φ_q(t))`, for the local twist
`B = E^{(h)}` over `K_v`: `φ_q : B[2^i] ≅ E[2^i]` the twist identification over `K̄_v` at
`q = j(s)` (`twistTors`), `j⁻¹ : E(K̄_v)[2^i] ≅ E(K_S)[2^i]` the inverse of the comparison along
the fixed embedding (`compTorsEquiv`, from `FullTorsion`), and `t ↦ 1 ⊗ t` into
`M_i = (E[2^i] ⊗ A_i)(α)` (`oneTmul`). -/
def kummerIotaBase :
    TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i) →+ Mcoef K S W i α :=
  (oneTmul (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ))).comp
    ((compTorsEquiv W (2 ^ i) hFull v).symm.toAddMonoidHom.comp
      (twistTors (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
        two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v) (2 ^ i)).toAddMonoidHom)

/-- PROVED. The value of the Kummer coefficient map: `t ↦ 1 ⊗ j⁻¹(φ_q t)`. -/
theorem kummerIotaBase_apply (t : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    kummerIotaBase W i s hs hs0 α hFull v t =
      oneTmul (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ))
        ((compTorsEquiv W (2 ^ i) hFull v).symm
          (twistTors (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
            two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v) (2 ^ i) t)) :=
  rfl

/-- PROVED (tex 3413–3438). **Equivariance of the Kummer coefficient map**:
`ι_v(σ t) = p_v(σ) • ι_v(t)` in `M_i`, when the character `α` of `M_i` is `χ_h` on the
decomposition group (`IsLocallyQuadAt`). -/
theorem kummerIotaBase_smul (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v) (σ : Gloc K v)
    (t : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    kummerIotaBase W i s hs hs0 α hFull v (σ • t) =
      locMap K S v σ • kummerIotaBase W i s hs hs0 α hFull v t := by
  rw [kummerIotaBase_apply, kummerIotaBase_apply, twistTors_smul, map_zsmul,
    compTorsEquiv_symm_smul, twistSign_localSqrt s hs hs0 v σ, map_zsmul,
    smul_oneTmul (Acoef i) α _ (locMap K S v σ) _ (quadChar s hs hs0 (locMap K S v σ)) (hα σ)]

/-- PROVED. **The Kummer coefficient map is injective** (for `i ≠ 0`): `φ_q` and `j⁻¹` are
isomorphisms, and `t ↦ 1 ⊗ t` is injective on the `2^i`-torsion (`oneTmul_injective`). In
particular `ι_v` is not degenerate. -/
theorem kummerIotaBase_injective (hi : i ≠ 0) :
    Function.Injective (kummerIotaBase W i s hs hs0 α hFull v) := by
  have hT : ∀ t : TorsS K S W ((2 ^ i : ℕ) : ℤ), (2 ^ i) • t = 0 := fun t => by
    have := AddSubgroup.torsionBy.nsmul_iff.1 t.2
    exact Subtype.ext this
  intro t t' htt
  rw [kummerIotaBase_apply, kummerIotaBase_apply] at htt
  have h1 := oneTmul_injective (Acoef i) (acoefConst i hi) α _ hT htt
  exact (twistTors _ _ _ _ _ _).injective ((compTorsEquiv W (2 ^ i) hFull v).symm.injective h1)

/-- Definition (tex 3413–3438; the coefficient maps of the actual Kummer condition). **The Kummer
coefficient map `ι_v : B(K̄_v)[2^i] → M_i`** with `G_{K_v}` acting on `M_i` through `p_v`
(`ResMod (locMap K S v)`, the format of lane RC28's `kummerAt`). -/
def kummerIota :
    TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i) →+
      ResMod (locMap K S v) (Mcoef K S W i α) :=
  (toResModAdd (locMap K S v) (Mcoef K S W i α)).comp (kummerIotaBase W i s hs hs0 α hFull v)

/-- PROVED. The value of `ι_v`: `ι_v t = 1 ⊗ j⁻¹(φ_q t)`. -/
theorem kummerIota_apply (t : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    kummerIota W i s hs hs0 α hFull v t =
      toResModAdd (locMap K S v) (Mcoef K S W i α) (kummerIotaBase W i s hs hs0 α hFull v t) :=
  rfl

/-- PROVED (tex 3413–3438: the local Kummer maps into `RΓ(K_v, M_i)` are maps of `G_{K_v}`-modules).
**`ι_v` is `G_{K_v}`-equivariant**, `ι_v(σ t) = σ ι_v(t)` with `G_{K_v}` acting on `M_i` through
`p_v` — lane RC28's hypothesis `hι` of `kummerAt` — when the character `α` of `M_i` is `χ_h` on
the decomposition group (`IsLocallyQuadAt`; for `α_i = χ_hΨ_i`: `ξ` trivial there,
`isLocallyQuadAt_alphaChar`). -/
theorem kummerIota_smul (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v) (σ : Gloc K v)
    (t : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    kummerIota W i s hs hs0 α hFull v (σ • t) = σ • kummerIota W i s hs hs0 α hFull v t := by
  rw [kummerIota_apply, kummerIota_apply, smul_toResModAdd, kummerIotaBase_smul W i s hs hs0 α
    hFull v hα σ t]

end Iota

/-! ### The actual Kummer condition -/

open scoped Classical in
/-- Definition (tex 2754–2756, 3413–3438; lane RC28's DEPARTURE 4 for the finite-level form).
**The actual Kummer local condition at `v ∈ S`**: lane RC28's `kummerAt` (the finite-level
subcomplex `U⁰ = C⁰`, `U¹ = span(ι_v ∘ κ_P) + B¹`, `Uⁿ = 0` of `C^•_cont(G_{K_v}, M_i)`) for the
actual local twist `B = E^{(h)}` and the genuine coefficient map `ι_v`. -/
def actualKummerAt (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (α : GKS K S →* (Acoef i)ˣ)
    [IsOpenKer α] (hFull : FullTorsion K S W (2 ^ i)) (v : Places K S)
    (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v.1) :
    CondAt K S (Acoef i) (Mcoef K S W i α) v :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  kummerAt v (localTwist W h v.1) (2 ^ i) (kummerIota W i s hs hs0 α hFull v.1)
    (kummerIota_smul W i s hs hs0 α hFull v.1 hα)

open scoped Classical in
/-- PROVED. The actual Kummer condition is a subcomplex of the local cochains (lane RC28's
`kummerAt_isInjective`). -/
theorem actualKummerAt_isInjective (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S)
    {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (α : GKS K S →* (Acoef i)ˣ)
    [IsOpenKer α] (hFull : FullTorsion K S W (2 ^ i)) (v : Places K S)
    (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v.1) :
    (actualKummerAt W i s hs hs0 α hFull v hα).IsInjective :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  kummerAt_isInjective v (localTwist W h v.1) (2 ^ i) (kummerIota W i s hs hs0 α hFull v.1)
    (kummerIota_smul W i s hs hs0 α hFull v.1 hα)



/-! ### The module built over `G_{K,S₀}`, inflated to the Selmer support `S ⊇ S₀` -/

section Inflated

variable {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h)
  (hs0 : s ≠ 0) (α : GKS K S₀ →* (Acoef i)ˣ) (hFull : FullTorsion K S₀ W (2 ^ i))

/-- Definition (tex 3413–3438 with (4.3), tex 3455–3463, and the support change of tex
3479–3498). **The Kummer coefficient map into lane RC28's inflated module** `MinS hS W i α`
(`M_i` built over `G_{K,S₀}`, inflated to `G_{K,S}`), at a place `v ∈ S`: the same map
`t ↦ 1 ⊗ j⁻¹(φ_q t)`, with `G_{K_v}` acting through `G_{K_v} → G_{K,S} → G_{K,S₀}`. -/
def kummerIotaS (v : Places K S) :
    TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) →+
      ResMod (locMap K S v.1) (MinS hS W i α) :=
  (toResModAdd (locMap K S v.1) (MinS hS W i α)).comp
    ((toResModAdd (inflMap K hS) (Mcoef K S₀ W i α)).comp
      (kummerIotaBase (S := S₀) W i s hs hs0 α hFull v.1))

/-- PROVED (lane RC26's `locMap_compat`: `infl ∘ p_v^S = p_v^{S₀}`). **The inflated Kummer
coefficient map is `G_{K_v}`-equivariant** — lane RC28's hypothesis `hι` for `MinS`. -/
theorem kummerIotaS_smul (v : Places K S)
    (hα : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v.1) (σ : Gloc K v.1)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    kummerIotaS hS W i s hs hs0 α hFull v (σ • t) = σ • kummerIotaS hS W i s hs hs0 α hFull v t := by
  change toResModAdd (locMap K S v.1) (MinS hS W i α)
      (toResModAdd (inflMap K hS) (Mcoef K S₀ W i α)
        (kummerIotaBase (S := S₀) W i s hs hs0 α hFull v.1 (σ • t))) =
    σ • toResModAdd (locMap K S v.1) (MinS hS W i α)
      (toResModAdd (inflMap K hS) (Mcoef K S₀ W i α)
        (kummerIotaBase (S := S₀) W i s hs hs0 α hFull v.1 t))
  rw [smul_toResModAdd, smul_toResModAdd, locMap_compat K hS v.1 σ,
    kummerIotaBase_smul (S := S₀) W i s hs hs0 α hFull v.1 hα σ t]

open scoped Classical in
/-- Definition (tex 2754–2756, 3413–3438). **The actual Kummer local condition at `v ∈ S` for the
inflated module** `MinS hS W i α`: lane RC28's `kummerAt` with the genuine `ι_v`. -/
def actualKummerAtS [IsOpenKer α] (v : Places K S)
    (hα : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v.1) :
    CondAt K S (Acoef i) (MinS hS W i α) v :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  kummerAt v (localTwist W h v.1) (2 ^ i) (kummerIotaS hS W i s hs hs0 α hFull v)
    (kummerIotaS_smul hS W i s hs hs0 α hFull v hα)

open scoped Classical in
/-- PROVED. The actual Kummer condition for the inflated module is a subcomplex. -/
theorem actualKummerAtS_isInjective [IsOpenKer α] (v : Places K S)
    (hα : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v.1) :
    (actualKummerAtS hS W i s hs hs0 α hFull v hα).IsInjective :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  kummerAt_isInjective v (localTwist W h v.1) (2 ^ i) (kummerIotaS hS W i s hs hs0 α hFull v)
    (kummerIotaS_smul hS W i s hs hs0 α hFull v hα)

open scoped Classical in
/-- Definition (tex 2754–2756, (4.3) at tex 3455–3463, tex 3479–3498). **The actual Selmer data
with the genuine Kummer conditions**: lane RC28's `actualSelData` with the actual Kummer condition
`actualKummerAtS` at the places of `P ⊆ S₀` (the places above `2N`, where the moving character is
locally trivial: `hα`), the given conditions `c` at the other places of `S₀` (the moving prime and
the active primes, whose conditions are not Kummer conditions), and the unramified condition at
`S − S₀`. -/
def kummerSelData [IsOpenKer α] (P : Set (HeightOneSpectrum (𝓞 K)))
    (hα : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)
    (c : ∀ v : Places K S, v.1 ∈ S₀ → v.1 ∉ P → CondAt K S (Acoef i) (MinS hS W i α) v) :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData (Acoef i) :=
  actualSelData hS W i α (fun v hv => if hP : v.1 ∈ P then
    actualKummerAtS hS W i s hs hs0 α hFull v (hα v.1 hP) else c v hv hP)

open scoped Classical in
/-- PROVED. **The actual Selmer data with the genuine Kummer conditions are genuine Galois Selmer
data** (lane RC28's `IsGaloisSelData`, the leaf's predicate) for finite `S` and injective `c`. -/
theorem isGaloisSelData_kummerSelData [IsOpenKer α] (hSfin : S.Finite)
    (P : Set (HeightOneSpectrum (𝓞 K)))
    (hα : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)
    (c : ∀ v : Places K S, v.1 ∈ S₀ → v.1 ∉ P → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hc : ∀ v hv hP, (c v hv hP).IsInjective) :
    ZInQ.Manuscript.RC.Wiring.IsGaloisSelData (kummerSelData hS W i s hs hs0 α hFull P hα c) := by
  refine isGaloisSelData_actual hS hSfin W i α _ fun v hv => ?_
  split
  · exact actualKummerAtS_isInjective hS W i s hs hs0 α hFull v _
  · exact hc v hv ‹_›

end Inflated

end ZInQ.Manuscript.RC.KummerMaps
