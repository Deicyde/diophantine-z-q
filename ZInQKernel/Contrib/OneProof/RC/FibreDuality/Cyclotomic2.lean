import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.TateLambda
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Weil

/-!
# Lane RC31, part 2: the `2`-adic cyclotomic character of `G_{K,S}`

Manuscript `diophantine_zq.tex`, tex 2798–2805 (the Weil pairing takes values in `R_i(1)`, "and
`e_2` transforms by the cyclotomic character"), at the characteristic-zero fibres of the switching
argument (tex 4976–5200): the coefficient twist `k(𝔭)(1) = k(𝔭) ⊗_{ℤ₂} ℤ₂(1)` of Nekovář 5.2.1.

* `HasTwoPowerRoots K S`: `K_S` contains a primitive `2^n`-th root of unity for every `n`
  (lane RC28's `HasRootsOfUnity` at every `2^n`); an instance under lane RC28's
  `HasFullTwoTorsion` (through the Weil pairing, `hasRootsOfUnity_of_fullTorsion`).
* `cyc2 K S : G_{K,S} → ℤ₂ˣ`: Mathlib's `2`-adic `cyclotomicCharacter` of the field `K_S`,
  composed with `G_{K,S} → Aut(K_S)`.
* `cyc2_spec`: `σ ζ = ζ ^ (cyc2 σ mod 2^n)` for every `2^n`-th root of unity `ζ ∈ K_S`;
  `toZModPow_cyc2`: the reduction of `cyc2` modulo `2^n` is lane RC28's `cycS` at level `2^n`;
  `continuous_cyc2`: `cyc2` is continuous (Mathlib's `cyclotomicCharacter.continuous`, Krull
  topology).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open NumberField IsDedekindDomain Filter Topology
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules (KS galS ringAutHom HasRootsOfUnity cycS
  hasRootsOfUnity_of_fullTorsion card_rootsOfUnity_KS)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion resN)

instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- **`μ_{2^∞} ⊆ K_S`**: `K_S` contains a primitive `2^n`-th root of unity for every `n`.
Kind: hypothesis (class); instance under `HasFullTwoTorsion`
(`hasTwoPowerRoots_of_fullTwoTorsion`). -/
class HasTwoPowerRoots : Prop where
  roots : ∀ n : ℕ, HasRootsOfUnity K S (2 ^ n)

/-- **`E[2^∞] ⊆ E(K_S)` gives `μ_{2^∞} ⊆ K_S`** (the Weil pairing at every level `2^n`; lane RC28's
`hasRootsOfUnity_of_fullTorsion`). Kind: PROVED. -/
theorem hasTwoPowerRoots_of_fullTwoTorsion (W : WeierstrassCurve K) [W.IsElliptic]
    [h : HasFullTwoTorsion K S W] : HasTwoPowerRoots K S :=
  ⟨fun n => hasRootsOfUnity_of_fullTorsion K S W (2 ^ n) (h.full n)⟩

/-- `K_S` has enough `2^i`-th roots of unity (a primitive root, and `μ_{2^i}(K_S)` is cyclic since
`K_S` is a field). Kind: PROVED. -/
instance hasEnoughRootsOfUnity_KS [h : HasTwoPowerRoots K S] (i : ℕ) :
    HasEnoughRootsOfUnity (KS K S) (2 ^ i) :=
  ⟨h.roots i, rootsOfUnity.isCyclic _ _⟩

/-- **The `2`-adic cyclotomic character** `G_{K,S} → ℤ₂ˣ`: Mathlib's `cyclotomicCharacter` of
`K_S` (`σ ζ = ζ^{χ(σ) mod 2^n}` on `μ_{2^n}(K_S)`), composed with `G_{K,S} → Aut(K_S)`. -/
def cyc2 : GKS K S →* ℤ_[2]ˣ :=
  (cyclotomicCharacter (KS K S) 2).comp (ringAutHom K S)

variable {K S}

omit [NumberField K] in
/-- **`σ ζ = ζ ^ (χ(σ) mod 2^n)`** for every `2^n`-th root of unity `ζ ∈ K_S`. Kind: PROVED. -/
theorem cyc2_spec [HasTwoPowerRoots K S] (σ : GKS K S) (n : ℕ) (ζ : KS K S) (hζ : ζ ^ (2 ^ n) = 1) :
    galS K S σ ζ = ζ ^ resN n (cyc2 K S σ : ℤ_[2]) :=
  cyclotomicCharacter.spec 2 (ringAutHom K S σ) ζ hζ

/-- **The reduction of `cyc2` modulo `2^n` is lane RC28's cyclotomic character at level `2^n`.**
Kind: PROVED. -/
theorem toZModPow_cyc2 [HasTwoPowerRoots K S] (n : ℕ) (hμ : HasRootsOfUnity K S (2 ^ n))
    (σ : GKS K S) :
    PadicInt.toZModPow n (cyc2 K S σ : ℤ_[2]) = ((cycS hμ σ : (ZMod (2 ^ n))ˣ) : ZMod (2 ^ n)) :=
  cyclotomicCharacter.toZModPow 2 (ringAutHom K S σ)

omit [NumberField K] in
/-- `ringAutHom` is Mathlib's action of `Gal(K_S/K)` on `K_S` by ring automorphisms. -/
theorem ringAutHom_eq_toRingAut (σ : GKS K S) :
    ringAutHom K S σ =
      MulSemiringAction.toRingAut (KS K S ≃ₐ[K] KS K S) (KS K S) (galS K S σ) :=
  RingEquiv.ext fun _ => rfl

omit [NumberField K] in
/-- **The `2`-adic cyclotomic character is continuous** (Krull topology on `G_{K,S}`; Mathlib's
`cyclotomicCharacter.continuous`). Kind: PROVED. -/
theorem continuous_cyc2 : Continuous (cyc2 K S) := by
  have h := cyclotomicCharacter.continuous 2 K (KS K S)
  have e : (cyc2 K S : GKS K S → ℤ_[2]ˣ) =
      fun σ => ((cyclotomicCharacter (KS K S) 2).comp
        (MulSemiringAction.toRingAut (KS K S ≃ₐ[K] KS K S) (KS K S))) (galS K S σ) := by
    funext σ
    change cyclotomicCharacter (KS K S) 2 (ringAutHom K S σ) = _
    rw [ringAutHom_eq_toRingAut]
    rfl
  rw [e]
  exact h

omit [NumberField K] in
/-- `σ ↦ χ(σ) ∈ ℤ₂` is continuous. Kind: PROVED. -/
theorem continuous_coe_cyc2 : Continuous fun σ : GKS K S => (cyc2 K S σ : ℤ_[2]) :=
  Units.continuous_val.comp continuous_cyc2

omit [NumberField K] in
/-- **`χ(σ) ≡ 1 mod 2^n` near `1`.** Kind: PROVED. -/
theorem eventually_cyc2_sub_one_mem (n : ℕ) :
    ∀ᶠ σ in 𝓝 (1 : GKS K S), (cyc2 K S σ : ℤ_[2]) - 1 ∈ Ideal.span {(2 : ℤ_[2]) ^ n} := by
  have hc : Tendsto (fun σ : GKS K S => (cyc2 K S σ : ℤ_[2])) (𝓝 1) (𝓝 1) := by
    have := (continuous_coe_cyc2 (K := K) (S := S)).tendsto 1
    simpa using this
  have hmem : {y : ℤ_[2] | y - 1 ∈ Ideal.span {(2 : ℤ_[2]) ^ n}} ∈ 𝓝 (1 : ℤ_[2]) := by
    have hopen : IsOpen ((Ideal.span {(2 : ℤ_[2]) ^ n} : Ideal ℤ_[2]) : Set ℤ_[2]) :=
      ZInQ.Manuscript.RC.LambdaCoef.isOpen_span_two_pow n
    have h0 : ((Ideal.span {(2 : ℤ_[2]) ^ n} : Ideal ℤ_[2]) : Set ℤ_[2]) ∈ 𝓝 (0 : ℤ_[2]) :=
      hopen.mem_nhds (Submodule.zero_mem _)
    have := (continuous_sub_right (1 : ℤ_[2])).tendsto 1
    rw [sub_self] at this
    exact this h0
  exact hc hmem

end ZInQ.Manuscript.RC.FibreDuality
