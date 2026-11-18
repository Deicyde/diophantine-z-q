import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Defs

/-!
# GenusOdd: the textbook GLUE behind (3.4) (stated here; current status of each below)

The proof of (3.4) (tex L2427–2439) cites Cai–Shu–Tian Theorem 1.1 twice (the printed leaf
`CST.CSTThm11Split` of `Prints`) and then compares the two outputs. Between the print as it is stated
over Lean objects (`Prints/CST.lean`) and that comparison, five standard facts are used that are
neither in Mathlib nor in Tau Ceti. Each is stated here as a `Prop`, in the most standard form that
suffices, with a docstring saying why it is true and where it enters; they were introduced as GLUE.
**Current status:** `NeronTateTwist`, `TwistDescent` and `SplittingCriterion` are PROVED;
`GenusTheory` is no longer needed on the current route (`Artin34.lean`: `genusRoots_proof` and the
normal-closure form of Elliot's step); `ArtinFactorization` is PROVED from lane RC8's
`HasseConvergence` (GLUE) and `ModularNewform` (PRINT) and the local GLUE `LocalFactorInert`
(`artinFactorization_of_newform`, `LocalFinal.lean`). None is a step of Elliot's argument: Elliot's step (the index-at-most-two comparison,
tex L2433–2435) is PROVED in `GenusLower.lean` from these.

* `ArtinFactorization` (tex L2432 "The two Rankin products have the common factor `L(E^{(h)},s)`"):
  `L(E/K, χ_{d₁} ∘ N, s) = L(E^{(d₁)}, s) L(E^{(d₂)}, s)` for `d₁ d₂ = disc(K) c²`. Reduced to the
  inert clause `LocalFactorInert` with `HasseConvergence` and `ModularNewform`
  (`artinFactorization_of_newform`, `LocalFinal.lean`).
* `NeronTateTwist` (implicit at tex L2433–2436, mcheck K3 item (d)): the Néron–Tate height of the
  image of a rational point of the twist `E^{(d)}` in `E(H)` is `[H : ℚ]` times its height.
  **PROVED** from lane RC19's height results in `HeightDischarge.lean` (`neronTateTwist_proof`).
* `TwistDescent` (tex L8313–8314 "the standard twist identification"): a point of `E(H)` on which
  `Gal(H/ℚ)` acts through the character of `√d` comes from `E^{(d)}(ℚ)`. **PROVED** in
  `TwistDescentProof.lean` (`twistDescent_proof`); no longer an input.
* `GenusTheory` (tex L8211–8215, L8257–8259 "The conductor-one genus character … cuts out
  `F_D = ℚ(√D, √h_*)`"): the ring class field is Galois over `ℚ` and contains `√d₁`, `√d₂`, on
  which `Gal(H_c/K)` acts by `χ`, and complex conjugation fixes one and negates the other.
  Reduced to `RingClassGalois` and `GenusRoots` (`genusTheory_of`, `GenusTheoryReduction.lean`;
  `GenusRoots` PROVED); not needed on the route of `Artin34.lean`.
* `SplittingCriterion` (tex L2428 "All level primes split", from the squareclass conditions of
  tex L2405–2406, L2350–2352): a prime `p ∤ disc K` at which `disc K` is a square splits in `K`.
  **PROVED** in the Splitting area (`Splitting.splittingCriterion_proof`).
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain Complex

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

/-- **Artin factorization of the ring-class `L`-function** (GLUE, textbook: Artin formalism for
`Ind_K^ℚ (χ_{d₁} ∘ N) = χ_{d₁} ⊕ χ_{d₁} χ_{disc K}`, with the Euler factors compared prime by prime;
tex L2432). For an imaginary quadratic `K` of odd discriminant in which every prime of the level
splits, `c ≥ 1` prime to `disc K`, `d₁ ≡ 1 (mod 4)` squarefree with `c ∣ d₁`, `d₁ d₂ = disc(K) c²`
prime to the level, and `χ = χ_{d₁} ∘ N_{K/ℚ}` on `Pic(O_c)`: the Euler product of `E/K` twisted
by `χ` (CST's `twistedLFunction`, `χ(𝔭) = 0` at `𝔭 ∣ c`) is `L(E^{(d₁)}, s) L(E^{(d₂)}, s)` on
`Re s > 3/2`. At `𝔭 ∣ c` both sides have trivial factor (`E^{(d₁)}`, `E^{(d₂)}` are additive there);
at a ramified `𝔭 ∤ c` the factor of `E/K` matches the good one of the unramified twist. In the two
uses: genus point `c = 1`, `d₁ = h_*`, `d₂ = h`; ring-class point `c = |h|`, `d₁ = h`,
`d₂ = h k'`. Status: reduced (`artinFactorization_of_newform`, `LocalFinal.lean`) to lane RC8's
`HasseConvergence` (GLUE) and `ModularNewform` (PRINT) and the inert clause `LocalFactorInert`. -/
def ArtinFactorization : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K],
    Module.finrank ℚ K = 2 → IsTotallyComplex K → Odd (discr K) →
    (∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p) →
    ∀ (c : ℕ) [NeZero c] (d₁ d₂ : ℤ), d₁ * d₂ = discr K * c ^ 2 → d₁ % 4 = 1 → Squarefree d₁ →
      (c : ℤ) ∣ d₁ → Nat.Coprime c (discr K).natAbs →
      Nat.Coprime (d₁ * d₂).natAbs (newformLevel E) →
    ∀ χ : Pic (conductorOrder K c) →* ℂˣ, IsQuadRingClassChar K c d₁ χ →
    ∀ s : ℂ, 3 / 2 < s.re →
      LSeries (twistedLFunction E (chiAt (conductorOrder K c) χ)) s =
        (qtwist E d₁).LSeries s * (qtwist E d₂).LSeries s

/-- **Néron–Tate height of a twisted rational point** (stated here as GLUE; PROVED in
`HeightDischarge.lean`, `neronTateTwist_proof`, from lane RC19. Textbook: the canonical height is
invariant under isomorphism over `H` and multiplies by `[H : F]` under base change, heights being
relative to the field; Silverman VIII.9). For `E` with `a₁ = a₃ = 0`, `s ∈ H` with `s² = d ≠ 0`
and `P ∈ E^{(d)}(ℚ)`: `ĥ_H(ψ_s P) = [H : ℚ] ĥ_ℚ(P)` (Tau Ceti's canonical heights, Mathlib's
admissible absolute values of the number fields `H` and `ℚ`). -/
def NeronTateTwist : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) (d : ℚ),
    ∀ (H : Type) [Field H] [NumberField H] [DecidableEq H] (s : H) (hs : s ≠ 0)
      (hsd : s ^ 2 = algebraMap ℚ H d) (P : (qtwist E d).toAffine.Point),
      (twistEmb E d s (twistVC_smul E h₁ h₃ hs hsd) P).canonicalHeight =
        (Module.finrank ℚ H : ℝ) * P.canonicalHeight

/-- **Galois descent for the twist** (stated here as a GLUE statement; PROVED in
`TwistDescentProof.lean`, `twistDescent_proof`. Textbook: Galois descent of points, as in Tau Ceti's
`GaloisDescent` for quadratic extensions; Silverman X.2). Let `H/ℚ` be finite Galois containing a
quadratic field `K`, `ρ ∈ Gal(H/ℚ)` not `K`-linear (so `Gal(H/K)` and `ρ` generate `Gal(H/ℚ)`),
and `s ∈ H` with `s² = d ≠ 0`. A point `x ∈ E(H)` with `g x = ε_s(g) x` for `g ∈ Gal(H/K)` and for
`g = ρ`, where `ε_s(g) = g(s)/s ∈ {±1}`, is `ψ_s P` for some `P ∈ E^{(d)}(ℚ)`: under the variable
change `twistVC s` the twisted action becomes the plain action of `Gal(H/ℚ)` on
`E^{(d)}(H)`, whose fixed points are `E^{(d)}(ℚ)`. -/
def TwistDescent : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (H : Type) [Field H] [DecidableEq H] [Algebra K H] [Algebra ℚ H] [IsScalarTower ℚ K H]
      [FiniteDimensional ℚ H] [IsGalois ℚ H] (d : ℚ) (s : H) (hs : s ≠ 0)
      (hsd : s ^ 2 = algebraMap ℚ H d) (ρ : H ≃ₐ[ℚ] H),
      (¬ ∃ σ : H ≃ₐ[K] H, ∀ z, σ z = ρ z) →
      ∀ x : (E.baseChange H).toAffine.Point,
        (∀ σ : H ≃ₐ[K] H,
          WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) x =
            if σ s = s then x else -x) →
        WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ρ.toAlgHom x =
            (if ρ s = s then x else -x) →
        ∃ P : (qtwist E d).toAffine.Point, twistEmb E d s (twistVC_smul E h₁ h₃ hs hsd) P = x

/-- **Genus theory for the ring class field** (GLUE, class field theory: `H_c/ℚ` is Galois with
generalized dihedral group, and the quadratic character `χ = χ_{d₁} ∘ N` of `Pic(O_c)` corresponds
under the Artin map to the Kummer character of `√d₁` (equivalently of `√d₂`, as
`√(d₁ d₂) = c √(disc K) ∈ K`); complex conjugation fixes the real one of `√d₁`, `√d₂` and negates
the imaginary one, since `d₁ d₂ < 0`). Hypotheses as in `ArtinFactorization`. Used for the genus
field `F_D = ℚ(√D, √h_*)` of tex L8257–8259 and for `K(√h) ⊆ H_{|h|}`. Status: follows from
`RingClassGalois` (GLUE) and `GenusRoots` (PROVED) by `genusTheory_of`; not needed on the route of
`Artin34.lean`. -/
def GenusTheory : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    Odd (discr K) →
    ∀ (c : ℕ) [NeZero c] (d₁ d₂ : ℤ), d₁ * d₂ = discr K * c ^ 2 → d₁ % 4 = 1 → Squarefree d₁ →
      (c : ℤ) ∣ d₁ → Nat.Coprime c (discr K).natAbs →
    ∀ χ : Pic (conductorOrder K c) →* ℂˣ, IsQuadRingClassChar K c d₁ χ →
      IsGalois ℚ (ringClassField (conductorOrder K c)) ∧
      ∃ s₁ s₂ : ringClassField (conductorOrder K c),
        s₁ ^ 2 = (d₁ : ringClassField (conductorOrder K c)) ∧
        s₂ ^ 2 = (d₂ : ringClassField (conductorOrder K c)) ∧
        (∀ σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
          σ s₁ = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) * s₁ ∧
          σ s₂ = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) * s₂) ∧
        ∃ ρ : ringClassField (conductorOrder K c) ≃ₐ[ℚ] ringClassField (conductorOrder K c),
          (ρ s₁ = s₁ ∧ ρ s₂ = -s₂) ∨ (ρ s₁ = -s₁ ∧ ρ s₂ = s₂)

/-- **The splitting criterion** (GLUE, textbook: Dedekind–Kummer for `𝓞_K = ℤ[(1 + √D)/2]`, or
`K ⊗ ℚ_p ≅ ℚ_p(√D)`): a prime `p` at which the discriminant `D` of the quadratic field `K` is a
unit square (`SquareAt p D`: `p ∤ D` and `D` a square mod `p`, or `D ≡ 1 mod 8` at `p = 2`) splits
in `K`. Status: **PROVED** (`Splitting.splittingCriterion_proof`, `Splitting/Criterion.lean`). -/
def SplittingCriterion : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ p : ℕ, p.Prime → SquareAt p (discr K) → SplitsIn K p

/-- The GLUE of (3.4), bundled. -/
structure Glue34 : Prop where
  artin : ArtinFactorization
  height : NeronTateTwist
  descent : TwistDescent
  genus : GenusTheory
  split : SplittingCriterion

end ZInQ.Contrib.CloudB3RC53.GenusOdd
