# shimura-modfn: `Shimura.ShimuraReciprocityModFn` and the main theorem of CM for `j`

Task shimura-modfn, 2026-11-14. Branch `wip/shimura-modfn` (base 71dc3f1b). Lean:
`scratch/shimura-modfn/ModFn.lean` (imports the built `ZInQKernel.Contrib.TYZGenus.ShimuraMain`; no
`sorry`, no `axiom`). Numerics: `scratch/shimura-modfn/jpair_check.py` → `jpair_check.out`,
`isolated_check.py` → `isolated_check.out` (plain Python, double precision: this host has no
PARI or mpmath, and no network). Log: `scratch/shimura-modfn/log.md`.
Marks: **VERIFIED** (compiled, computed, or read in a named file), **STANDARD** (published, exact
reference), **SPECULATIVE**, **UNVERIFIED** (theorem numbers from memory; there is no network on
this host).

## 0. Verdict

1. **The statement is right.** `ShimuraReciprocityModFn` follows from published theorems and is no
   stronger than they are: the main theorem of CM with its action on torsion (Shimura 1971,
   Thm. 5.4) plus the canonical model of `X₀(N)` over `ℚ` as the coarse moduli space of pairs
   `(E, C)` (Shimura 1971, §6.7; Deligne–Rapoport), or equivalently Shimura's reciprocity law for
   values of modular functions at CM points (Shimura 1971, Thm. 6.31), specialized to `ℚ(X₀(N))`.
   All theorem numbers are UNVERIFIED. Gross 1984 §1–§3 states the Heegner-point form
   `σ_𝔟(O, 𝔫, [𝔞]) = (O, 𝔫, [𝔞𝔟⁻¹])` for his Heegner points, i.e. pairs where both lattices have
   the same order and `O/𝔫 ≅ ℤ/N` (his exact conditions, including whether `(f, N) = 1` is
   required, are recalled from memory and UNVERIFIED). The Lean statement assumes no such
   condition (e.g. `Q = [32, 10, 1]` has `f = 2 ∣ 32`), so for the general case cite Shimura's
   theorem. Every hypothesis was checked against the published form (§1); none is missing.
2. **The weaker `CMValueRingClass` is not enough for every use.** It gives
   `CM.CMFieldOfDefinition` and `CMAlgebraic`. But `TYZSigmaFixesZn` (through `ShimuraZn`, class of
   `𝔟 = (3+2√−n)𝓞_K ∩ O_{n,4}`) and `TYZThm36Seven` (cm-bridge §14, class `[𝔭₂]^{−5}`) apply
   `ShimuraReciprocityPic` to non-trivial ideal classes. The headline
   `tyzThm35ReadingA_of_lcal_shimuraModFn_…` (cm-bridge) needs both, so it needs the full Gross
   form (VERIFIED by reading `ShimuraMain.lean`, `ShimuraTheta.lean`,
   `scratch/cm-bridge/Bridge.lean` §14–§15).
3. **Reducing to the main theorem of CM for `j` alone is impossible by the `ℚ(j, j_N)` route,
   and the obstruction appears in the cases the project uses.** Proved in Lean (§2):
   * `MainTheoremCMj` (new CM leaf, stated over Mathlib's `E₄`, `Δ`, Tau Ceti's ring class field
     and Artin map), together with
   * `RatX0Rep` (new non-CM leaf: `ℚ(X₀(N)) = ℚ(j, j_N)` with Euler's conductor bound),

   implies `ShimuraReciprocityModFn` at every Heegner point that is an *isolated* point of the
   plane model `(j, j_N)` of `X₀(N)` (`j(Nτ)` a simple root of `Φ_N(j(τ), Y)`). The remaining
   part, `ShimuraReciprocityModFnSingular` (the same statement at non-isolated points), is the
   level-structure content of the main theorem of CM. It cannot come from `j`-values: at
   `Q = [32, 10, 1]`, `D = −28`, we have `j(τ_Q) = j(32τ_Q) = 255³ ∈ ℚ` but `x(τ_Q) = −1 + √−7`
   (VERIFIED computed). The points the project uses include such cases: TYZ's class-7 forms
   `tyzForm7 n`, `tyzForm7' n` (used in `TYZThm36Seven`) are non-isolated for `n = 7, 15, 47`
   (VERIFIED computed, §3).

   So the honest decomposition is
   `ShimuraReciprocityModFn ⇐ MainTheoremCMj ∧ RatX0Rep ∧ ShimuraReciprocityModFnSingular`
   (`shimuraReciprocityModFn_of_split`, compiled). The last conjunct is a restriction of the
   original leaf and stays a CM leaf with the original sources. **Recommendation: keep
   `ShimuraReciprocityModFn` as the single CM leaf for the announcement.** Its standard source is
   Shimura's Thm. 5.4 *with torsion*, i.e. Thm. 6.31, not the `j`-form. The split is useful
   because it isolates exactly which part of the leaf goes beyond the `j`-form.

## 1. Check of the statement against the published theorem

The statement (verbatim copy `ShimuraModFnTask.ShimuraReciprocityModFn`, `rfl`-equal to tyz-cm's,
VERIFIED compiled):

```lean
def ShimuraReciprocityModFn : Prop :=
  ∀ (N : ℕ) (g : UpperHalfPlane → ℂ), IsRatModFn N g →
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
    ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) →
    ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ),
      (∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass J) x)) →
    ∀ (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm N D) (c : ℂ),
      idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
      idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
      ∃ a a' : Qbar, ιC a = g Q.tauH ∧ ιC a' = g Q'.tauH ∧ ρ a = a'
```

Derivation from Shimura's Thm. 5.4 (all steps STANDARD; numbers UNVERIFIED):

* `τ_Q` is the point `(ℂ/L, L_N/L)` of `Y₀(N)` with `L = ⟨1, τ_Q⟩` and `L_N = ⟨1/N, τ_Q⟩`.
  `L_N/L ≅ ℤ/N` is cyclic. `L` is a proper `O_D`-ideal because `Q` is primitive. `L_N` is stable
  under an order `O_N ⊇ O_D`: every subgroup of the cyclic `O`-module `L_N/L` is `O`-stable
  (Lean: `kappa_mul_mem_latN_gen`, tyz-cm).
* `ρ` fixes `e(K)`, since `Art(𝔟) ∈ Gal(H_O/K)`. Extend it to `σ ∈ Aut(ℂ/K)` through `ιC`.
  Take an idele `s` with `[s, K] = σ|_{K^{ab}}`. `[s, K]|_{H_O} = Art([J ∩ O])`, so `s` lies in
  `s_J·K^×·Ô^×·ℂ^×`, where `s_J` generates `J` locally. `Ô^×` fixes both `L` and `L_N`, since
  `Ô^× ⊆ Ô_N^×`. So `s⁻¹(L, L_N)` is homothetic to `𝔟⁻¹(L, L_N)` with `𝔟 = J ∩ O`. Here `𝔟` is
  invertible because `J` is prime to `f`.
* Main theorem of CM (Shimura Thm. 5.4, including the clause on torsion points
  `ξ(u)^σ = ξ'(s⁻¹u)`): `(ℂ/L, L_N/L)^σ ≅ (ℂ/s⁻¹L, s⁻¹L_N/s⁻¹L)`.
* The hypotheses give `L' = c·𝔟⁻¹L` and `L'_N = c·(𝔟O_N)⁻¹L_N`. To get these, multiply by
  `𝔟⁻¹`, using that `L'` and `L'_N` are `O`-stable (`Q'` is a Heegner form of discriminant `D`)
  and that `(𝔟L' : 𝔟L') = (L' : L')`. So `σ(τ_Q) = τ_{Q'}` in `Y₀(N)(ℂ)`.
* `X₀(N)_ℚ`, with function field the functions that have rational `q`-expansion at `∞`, is the
  coarse moduli space with `τ ↦ (ℂ/⟨1, τ⟩, ⟨1/N⟩)`. Hence `σ(g(x)) = g(σx)` for every
  `g ∈ ℚ(X₀(N))` regular at `x` (Shimura §6.7; Diamond–Shurman Ch. 7). `IsRatModFn N g` is
  exactly "`g ∈ ℚ(X₀(N))` with no poles on `ℍ`". `N = 0` is vacuous, because `HeegnerForm 0 D` is
  empty (`heegnerForm_N_pos`, compiled). The convention matches the `ℚ`-structure: under
  `ℂ/⟨1, τ⟩ ≅ ℂ^×/q^ℤ`, `z ↦ e^{2πiz}`, the subgroup `⟨1/N⟩` goes to `μ_N ⊂ Tate(q)`, which is
  defined over `ℚ((q))`. So the cusp `∞` is `ℚ`-rational and "rational `q`-expansion at `∞`" is the
  `ℚ`-structure of this moduli problem (STANDARD, Katz–Mazur / Diamond–Shurman §7.?). With
  `⟨τ/N⟩` (↦ `q^{1/N}`) one would get the other cusp, which is rational only over `ℚ(ζ_N)`.
* Normalization: Tau Ceti's Artin map is arithmetic, and Shimura's `[s, K]` sends a uniformizer at
  `𝔭` to the arithmetic Frobenius, giving `j(𝔞)^{Frob_𝔭} = j(𝔭⁻¹𝔞)` (Cox Cor. 11.37:
  `σ_𝔭 j(𝔞) = j(𝔭̄𝔞)`, `𝔭̄ ∼ 𝔭⁻¹`). cm-numeric and cm-bridge checked the direction numerically
  (`Art(𝔞)` sends the Heegner point of `[𝔟]` to that of `[𝔟𝔞⁻¹]`).

Nothing in the statement is stronger than this: no Heegner condition is assumed or needed, `J` is
prime to `f`, `ρ` fixes `K`, and the values are algebraic. **Conclusion: a consequence of Shimura
Thm. 5.4 + §6.7 (equivalently Thm. 6.31). It is not the j-form of the main theorem.**

## 2. What is proved (Lean, `scratch/shimura-modfn/ModFn.lean`)

Namespace `ZInQ.Contrib.TYZGenus.ShimuraModFnTask`.

```lean
-- §1 definitions over Mathlib
def jInv (τ : UpperHalfPlane) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ
def latH (τ : UpperHalfPlane) : Submodule ℤ ℂ := Submodule.span ℤ {1, (τ : ℂ)}
def IsOStable (m f : ℕ) [NeZero m] [NeZero f] (L : Submodule ℤ ℂ) : Prop :=
  ∀ o ∈ (conductorOrder (QNeg m) f).toSubalgebra, ∀ x ∈ L, kappa m o * x ∈ L
def scaleH (N : ℕ) (τ : UpperHalfPlane) : UpperHalfPlane      -- N·τ

-- Leaf CM-J (main theorem of CM for j, ideal-class form)
def MainTheoremCMj : Prop :=
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
    ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) →
    ∀ τ : UpperHalfPlane, IsOStable m f (latH τ) →
      (∃ x : ringClassField (conductorOrder (QNeg m) f), ιC (e x) = jInv τ) ∧
      ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ),
        (∀ x : ringClassField (conductorOrder (QNeg m) f),
          ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
            ((conductorOrder (QNeg m) f).picClass J) x)) →
        ∀ (τ' : UpperHalfPlane) (c : ℂ), IsOStable m f (latH τ') →
          idealLat m f J * latH τ' = (latH τ).map (LinearMap.mulLeft ℤ c) →
          ∃ a a' : Qbar, ιC a = jInv τ ∧ ιC a' = jInv τ' ∧ ρ a = a'

-- Non-CM leaf RAT-X0
def RatX0Rep : Prop :=
  ∀ N : ℕ, 0 < N → ∀ g : UpperHalfPlane → ℂ, IsRatModFn N g →
    ∃ A B : MvPolynomial (Fin 2) ℚ, (∀ τ, evalJ N B τ * g τ = evalJ N A τ) ∧
      ∀ τ, IsIsolated N τ → evalJ N B τ ≠ 0

-- glue theorems (proved)
theorem jPair_reciprocity (hj : MainTheoremCMj) … :        -- ρ j(τ_Q) = j(τ_Q'), ρ j(Nτ_Q) = j(Nτ_Q')
theorem reciprocity_of_rep (hj : MainTheoremCMj) g A B (hrep : ∀ τ, evalJ N B τ * g τ = evalJ N A τ)
    … (hB : evalJ N B Q.tauH ≠ 0) : ∃ a a' : Qbar, ιC a = g Q.tauH ∧ ιC a' = g Q'.tauH ∧ ρ a = a'
theorem shimuraReciprocityModFn_isolated (hj : MainTheoremCMj) (hR : RatX0Rep) : … IsIsolated N Q.tauH → …
theorem shimuraReciprocityModFn_of_split (hj : MainTheoremCMj) (hR : RatX0Rep)
    (hS : ShimuraReciprocityModFnSingular) : ShimuraReciprocityModFn
theorem singular_of_shimuraReciprocityModFn : ShimuraReciprocityModFn → ShimuraReciprocityModFnSingular
theorem isIsolated_one (τ) : IsIsolated 1 τ                 -- so for N = 1 the singular part is empty

-- §5 q-expansion bookkeeping (proved): j and j_N are in the leaf's function class
theorem jInv_smul (γ : SL(2, ℤ)) (τ) : jInv (γ • τ) = jInv τ
theorem jInv_qexp : ∃ a : ℕ → ℚ, ∀ τ, HasSum (fun n => (a n : ℂ) * q τ ^ n) (q τ ^ 1 * jInv τ)
theorem jInv_bound : ∃ C, ∀ τ, 1 ≤ τ.im → ‖jInv τ‖ ≤ C * Real.exp (2 * π * τ.im)
theorem isRatModFn_jInv (N : ℕ) : IsRatModFn N jInv
theorem isRatModFn_jN (hN : 0 < N) : IsRatModFn N fun τ => jInv (scaleH N τ)
theorem jPair_of_modFn (hS : ShimuraReciprocityModFn) … :    -- the j-part, from tyz-cm's leaf
    (ρ j(τ_Q) = j(τ_Q')) ∧ (ρ j(Nτ_Q) = j(Nτ_Q'))
```

Methods for §5. `SL₂(ℤ)`-invariance comes from Mathlib's slash invariance of `E₄` (weight 4) and
tyz-cm's `eta_pow_smul` (`Δ = η²⁴`, weight 12). The rational `q`-expansion is
`q·j = E₄(q)³/∏(1 − qⁿ)²⁴`: `E₄(q)` is Mathlib's `cuspFunction 1 E₄`, with rational Taylor
coefficients from Mathlib's `E_qExpansion_coeff` (`−(8/B₄)σ₃(n) = 240σ₃(n)`); `Δ = q·pd 1 q²⁴`
uses tyz-cm's `eta_eq_prodF`. These are combined with tyz-cm's `IsRatAt` calculus and
`exists_rat_hasSum` (`ShimuraQExp.lean`). The growth bound `|j(τ)| ≤ C e^{2π Im τ}` holds for
`Im τ ≥ 1` because `Gj` is bounded on the compact disc `|q| ≤ e^{−2π}`. For `j_N`:
`Γ₀(N)`-invariance uses `γ' = [[a, Nb], [c/N, d]]`. Growth at every cusp uses tyz-cm's Hermite
decomposition `exists_smul_decomp`, with `Nγτ = γ'w` and `Im w ≥ Im τ/N`. The `q`-expansion is
reindexed along `n ↦ Nn` (`Function.Injective.hasSum_iff`). **Consequence (`jPair_of_modFn`): on
Heegner lattices, `MainTheoremCMj` asks for nothing that tyz-cm's leaf does not already give.**

Here `evalJ N P τ = P(j(τ), j(Nτ))`. `IsIsolated N τ` means exactly one of the `ψ(N)` values
`j((aτ+b)/d)` (`ad = N`, `0 ≤ b < d`, `gcd(a, b, d) = 1`) equals `j(Nτ)`.

Statement notes.
* `MainTheoremCMj` is a consequence of the published `j`-form (Shimura Thm. 5.4 for `j`;
  Cox Thm. 11.1 and Cor. 11.37; Lang, *Elliptic functions*, Ch. 10–11; UNVERIFIED numbers) and
  of the functoriality `Art_O(𝔟)|_{H_{O'}} = Art_{O'}(𝔟O')`, for lattices whose order `O'`
  contains `O`. **Pitfall found while stating it:** the hypothesis that `⟨1, τ'⟩` is
  `κ(O)`-stable is needed. Without it, `κ(𝔟)·L' = c·L` only determines `O·L'`. Example: `𝔟 = O`,
  `c = 1`, `L = O`, `L' = ⟨1, 2τ⟩` gives `O·L' = L` but `j(L') ≠ j(L)`, which would make the leaf
  false. In `ShimuraReciprocityModFn` this hypothesis holds automatically, since `Q'` has
  discriminant `D`.
* `RatX0Rep` is true. Take `B = ∂Φ_N/∂Y`. `Φ_N(j(τ), Y) = ∏(Y − j((aτ+b)/d))`, so
  `B(j(τ), j(Nτ)) ≠ 0` exactly at isolated points. `g` is integral over `ℚ[j]`.
  `ℚ(X₀(N)) = ℚ(j, j_N)`. Euler's lemma gives `R ⊆ R^∨ ⊆ ℚ[j][j_N]^∨ = Φ_N'(j_N)⁻¹ℚ[j][j_N]`.
  Sources are in the docstring: Cox Thm. 11.18, Shimura Prop. 6.9, Diamond–Shurman §7.5–7.7,
  Serre *Local fields* III §6 (UNVERIFIED numbers). It is a combination of three textbook facts
  with no CM input. Neither Mathlib nor the project has modular polynomials or function fields of
  modular curves, so for now it is a leaf.

## 3. Why the `j`-form cannot replace the leaf (numerics)

`jpair_check.out` (VERIFIED computed, double precision, `x, y` from x0-32's eta quotients):

| `Q` (level 32) | `D` | `j(τ_Q)` | `j(32τ_Q)` | `x(τ_Q)` | `y(τ_Q)` |
|---|---|---|---|---|---|
| `[32, 10, 1]` | −28 | 16581375 = 255³ | 16581375 | `−1 + 2.6457513111 i` (= `−1+√−7`) | 4 |
| `[32, −10, 1]` | −28 | 255³ | 255³ | `−1 − √−7` | 4 |
| `[32, 18, 3]` | −60 | 4137.798… (real) | 3.7018…·10¹⁰ (real) | `−4.2360679775 − 1.7320508076 i` | non-real |

In the first two rows, `(j, j₃₂)` takes the same rational value at two points of `X₀(32)` that
complex conjugation swaps. No representation `x = A(j, j₃₂)/B(j, j₃₂)` over `ℚ` can have
`B(255³, 255³) ≠ 0`. The same symmetry, `𝔫 ↔ 𝔫̄` when the relevant classes have order at most 2,
persists at every higher level `32M`. Lifting to `X₀(32M)` does not separate the two points either:
for `h = 1` all `O`-stable cyclic `32M`-isogenies of `L` have the same `j`.

`isolated_check.out` (VERIFIED computed: multiplicity of `j(32τ)` among the 48 roots of
`Φ₃₂(j(τ), Y)`, compared through reduced points of the fundamental domain):

* non-isolated: `[32,10,1]`, `[32,18,3]`, `[32,4,1]`, `[32,6,1]`, and TYZ's class-7 forms
  `tyzForm7 n`, `tyzForm7' n` for `n = 7, 15, 47` (exactly the `n` with `[𝔭₂]^{10} = 1`);
* isolated: TYZ's class-5 forms `tyzForm n`, `tyzForm' n` for `n = 5, 13, 21, 29, 37, 53, 61`, and
  class-7 for `n = 23, 31, 39, 55`.

So `TYZThm36Seven`, through `ShimuraReciprocityPic` at `tyzForm7`, needs the singular part.

The class-7 singular set is finite. For `tyzForm7 n` (`O = 𝓞_K`, 2 split), the only `O`-stable
cyclic 32-isogenies of `L` are `𝔭₂⁻⁵L` and `𝔭̄₂⁻⁵L`. The others have different orders, hence
different `j`. So the point is non-isolated iff `[𝔭₂]^{10} = 1`, iff `𝔭₂^{10} = (α)` with
`(a² + nb²)/4 = 2^{10}` and `b ≠ 0`, which forces `n ≤ 4096`. `class7_singular.out` (VERIFIED
computed) lists the 32 values `n = 7, 15, 47, 79, 103, 119, 127, 143, 159, 303, 319, 415, 455, 615,
1495, 1695, 1887, 2071, 2247, 2415, 3007, 3135, 3255, 3367, 3471, 3567, 3655, 3927, 4015, 4047,
4071, 4087`. The direct multiplicity count agrees for 12/12 values `71 ≤ n ≤ 167`
(`class7_crosscheck.out`). So `TYZThm36Seven` needs the level-structure part only at these 32
values of `n`, but for those it is needed. The
class-5 uses (`CMFieldOfDefinitionTYZ`, `TYZSigmaFixesZn`) were isolated in every sampled case. A
proof of isolatedness for all `n` is not available (SPECULATIVE whether it holds), and it would
need lower bounds on differences of CM `j`-values.

## 4. What remains

* `MainTheoremCMj`: CM leaf (textbook).
* `RatX0Rep`: non-CM leaf (textbook combination). It could become glue once modular polynomials
  and `ℚ(X₀(N))` exist in Lean, which is a large project.
* `ShimuraReciprocityModFnSingular`: CM leaf, the level-structure part of Shimura Thm. 5.4 (or
  Thm. 6.31). It is a restriction of `ShimuraReciprocityModFn`, with the same sources.
* Not done: the Frobenius-at-primes form of `MainTheoremCMj` and its passage to the class form
  (factorization of `J`, multiplicativity of `J ↦ J ∩ O` for ideals prime to `f`, products of
  Artin symbols). The class form stated here is Shimura's standard form, so this passage is
  optional.
