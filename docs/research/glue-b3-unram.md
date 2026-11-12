# glue-b3-unram: the kernel field `L'` of B3 is unramified outside `T`

Status: research note (task glue-b3-unram, 2026-11-11). Scope: B3 (v) of
`docs/research/glue-descent.md`, which is N5 = `diophantine_zq.tex` L702-712. Lean file:
`scratch/glue-b3-unram/Unram.lean` (511 lines, self-contained, `import Mathlib`). Log:
`scratch/glue-b3-unram/log.md`. No file under `ZInQKernel/`, `blueprint/` or other tasks' notes was
edited.

## 1. Main result

**(VERIFIED, compiled; axioms `propext`, `Classical.choice`, `Quot.sound`.)**
`GlueB3Unram.unramified_outside` proves B3 (v) in Lean from four leaves stated over Mathlib
objects. The input is the output of glue-descent's `b2_of_leaves` and `inflatedNormalized_of`:
- a finite Galois `L ⊆ ℚ̄` unramified outside a finite set `T` with `2 ∈ T`;
- a sign 2-cocycle `ε` that equals 1 as soon as one argument lies in `G_L`;
- a Dirichlet character `χ` mod `N` whose prime divisors lie in `T`;
- a locally constant `β : G_ℚ → ℂ^×` with `β² = χ` (through the cyclotomic character) and
  `dβ = ε`.

The theorem produces a finite set `Q` of primes outside `T` and the locally constant quadratic
character `η = ∏_{q∈Q} η_q` of `G_ℚ`, where `η_q` is the Legendre character mod `q` composed with
the cyclotomic character mod `q`. Every `L'` with `G_{L'} = {σ ∈ G_L : β(σ)η(σ) = 1}` is then
unramified outside `T`. This `L'` is the kernel field that `b3_of_leaves` builds for this `η`.

`Q` is the set of primes `p ∉ T` at which `β` is ramified at some place over `p`. This is N5's
"product of those odd primes". `Q` contains no 2 because `2 ∈ T`.

`2 ∈ T` holds in the application (VERIFIED): `T = ramSet S u ⊇ S_mul ⊇ heightPrimes`, which is
the set of primes below 325 (`ZInQKernel/Compiler/Precision/HeightConstant.lean:116`,
`HeightMin.lean:85`). N5 L707 also says `2 ∈ T`.

## 2. Definitions (all over Mathlib, nothing invented)

| Name | Definition |
| --- | --- |
| `GQ`, `cyc N`, `galChar χ` | copied verbatim from `scratch/glue-descent/B2Glue.lean` (`Field.absoluteGaloisGroup ℚ`, Mathlib's `modularCyclotomicCharacter`) |
| `LiesOver w p` | `w : ValuationSubring ℚ̄` with `w.valuation p < 1` |
| `inertiaGQ w` | image in `G_ℚ` of Mathlib's `ValuationSubring.inertiaSubgroup ℚ w`, the elements of the decomposition group of `w` that act trivially on its residue field (same convention as pkg-I2's `IsInertia`) |
| `GalUnramifiedOutside L' T` | for every prime `p ∉ T` and every `w` over `p`, `inertiaGQ w ≤ L'.fixingSubgroup` |
| `legChar p`, `etaP p` | `quadraticChar (ZMod p)` cast to `ℂ`, as a Dirichlet character; `etaP p = galChar (legChar p)` (`1` if `p` is not prime) |

## 3. Leaves

| Leaf | Lean | Statement | Source | Proved? |
| --- | --- | --- | --- | --- |
| L-B3a | `LeafB3a` | for an odd prime `p` and `w` over `p`: two nontrivial, locally constant characters `inertiaGQ w →* ℂ^×` of square 1 are equal | wild inertia is pro-`p` and tame inertia is `∏_{ℓ≠p} ℤ_ℓ(1)` (Serre, *Corps locaux* IV §2; Neukirch–Schmidt–Wingberg Ch. VII §5; UNVERIFIED locators) | no (deep: needs local class field theory or the structure of tame inertia) |
| L-B3b | `LeafB3b` | for an odd prime `p` and `w` over `p`: `etaP p` is nontrivial on `inertiaGQ w` | `ℚ(√p*)` has discriminant `p* = ±p`, so it is ramified at `p`; equivalently `ℚ(ζ_p)` is totally ramified at `p` (STANDARD; Washington, *Cyclotomic fields*, Lemma 1.4, UNVERIFIED locator) | no, see §5 |
| L-conj | `LeafConj` | if `w, w'` lie over the same `p`, then `σ⁻¹ I_{w'} σ ≤ I_w` for some `σ ∈ G_ℚ` | `G_ℚ` acts transitively on the extensions of `v_p` to `ℚ̄` (Neukirch, *ANT* II.9.1, with a compactness argument for `ℚ̄`; UNVERIFIED locator), and `I_{σw} = σ I_w σ⁻¹` | no |
| L-finram | `LeafFinRam` | an open subgroup `H ≤ G_ℚ` contains `inertiaGQ w` for every `w` over every prime outside a finite set | `H ⊇ G_K` for a number field `K`, which is ramified only at primes dividing its discriminant (Neukirch III.2.12, UNVERIFIED locator) | no |

*Faithfulness* (checked by reading the statements; SPECULATIVE only where marked):
- Each leaf is a consequence of the cited theorem and never stronger.
  - L-B3a: a locally constant character of `I_w` into `{±1}` is continuous. Continuous
    quadratic characters of `I_w ≅ I(ℚ̄_p/ℚ_p)` factor through the maximal pro-2 quotient of
    tame inertia, `ℤ_2(1)`, so there is exactly one nontrivial one.
  - L-B3a requires local constancy. Without it the statement would be false: `I_w` has
    uncountably many discontinuous quadratic characters. For this reason glue-descent's
    abstract `twist_kills_inertia` (whose `unique` hypothesis quantifies over all homomorphisms)
    is not used. The argument is redone here with locally constant characters.
- `LiesOver`: a valuation subring `w` of `ℚ̄` with `v_w(p) < 1` meets `ℚ` in `ℤ_(p)`. Since
  `ℚ̄/ℚ` is algebraic, `w` is the valuation ring of an extension of `v_p`. So `inertiaGQ w` is
  the usual inertia group at a place over `p` (STANDARD).
- L-B3b is the prime-conductor case of "a quadratic Dirichlet character is ramified exactly at
  the primes dividing its conductor". The converse direction ("unramified at `p ∤ N`") is glue
  and is proved (`cycUnram`, §4). The product `η = ∏ η_q` replaces N5's "quadratic character of
  conductor `P`". It has the same ramification outside 2 (and none at 2), so no CRT or Jacobi
  symbol is needed.
- L-conj and L-finram are not new inputs to N5's argument. They are what N5's "at only finitely
  many primes" and the well-definedness of "β is ramified at `p`" use implicitly.

## 4. Glue proved in Lean (all compiled)

| Lemma | Content |
| --- | --- |
| `cycUnram` | **the cyclotomic character mod `N` is trivial on `inertiaGQ w` for `w` over `p ∤ N`**. Proof: for `t ∈ μ_N`, `ζ = s(t)/t` lies in `w` and has residue 1. If `ζ ≠ 1`, then `∑_{i<N} ζ^i = 0` reduces to `N = 0` in the residue field. That is impossible: `p` maps to 0 there, and `ap + bN = 1`. |
| `galChar_unram`, `etaP_unram` | hence `galChar χ` is unramified at `p ∤ N`, and `η_q` is unramified at `p ≠ q` |
| `etaP_sq`, `etaP_isLocallyConstant`, `prod_isLocallyConstant` | `η` is quadratic and locally constant |
| `kerSub`, `beta_mul_left`, `beta_one`, `beta_conj` | `K = {σ ∈ G_L : β σ = 1}` is a subgroup, open, and normal in `G_ℚ` (it uses only `ε = 1` on `G_L`-arguments and `G_L ⊴ G_ℚ`) |
| `unramified_outside_of_leaves` | the twist argument at a place `w` over `p ∉ T` (proof sketch below) |
| `unramified_outside` | the same theorem with `cycUnram` discharged: four leaves only |

Proof sketch of `unramified_outside_of_leaves`, at a place `w` over `p ∉ T`:
- `I_w ≤ G_L`, so `β|_{I_w}` is a homomorphism. It is quadratic because `β² = χ` and `p ∤ N`.
- If `I_w ≤ K`, then by L-conj and the normality of `K`, `β` is unramified at every place over
  `p`, so `p ∉ Q` and `η|_{I_w} = 1`.
- Otherwise `p ∈ Q` and `p` is odd. By `cycUnram`, `η|_{I_w} = η_p|_{I_w}`, which is nontrivial
  by L-B3b. L-B3a then gives `β = η` on `I_w`, so `βη = η² = 1` there.

## 5. What remains

- **Bridge between the two notions of unramified (glue, not formalized).** glue-descent states
  "L unramified at `p`" ideal-theoretically (`UnramifiedAt`: `e(P|p) = 1` for all `P | p` in
  `𝓞 L`). This note uses the Galois form `GalUnramifiedOutside`. Integration needs both
  directions:
  - `UnramifiedAt L p ⇒ I_w ≤ G_L`, to feed `L` in;
  - the converse for `L'`, if downstream steps want `UnramifiedAt L' p`.

  Both are the standard equality `|I(P|p)| = e(P|p)` for Galois extensions of number fields
  (Mathlib has inertia groups of Dedekind extensions), plus the restriction of `inertiaGQ w` to
  the inertia group of `P = w ∩ 𝓞 L`. Cost estimate 150-300 lines (SPECULATIVE).
- **Integration with `b3_of_leaves` (restructuring, easy).** `b3_of_leaves` takes `η` before
  calling `b2_of_leaves`. Here `η` depends on `β₁`, the output of B2. The integrated proof must:
  1. call `b2_of_leaves`;
  2. apply `unramified_outside` to `β₁`;
  3. build `L'` as in `b3_of_leaves`, with `β = β₁η`. The characterization
     `G_{L'} = {σ ∈ G_L : β σ = 1}` is exactly the hypothesis on `L'` here.
- **L-B3b is not proved.** It is classical, but a proof over this API needs:
  - the total ramification of `ℚ(ζ_p)` at `p` (Mathlib has cyclotomic ramification results at
    the ideal level);
  - the bridge above.

  So it is "elementary" only after the bridge. It stays a leaf.
- L-B3a, L-conj and L-finram are deep or need infrastructure (local Galois theory of `ℚ̄_p`)
  that Mathlib lacks. L-finram becomes glue after the bridge, using Mathlib's discriminant
  results (SPECULATIVE).

## 6. Findings

1. **(VERIFIED, Lean.)** B3 (v) follows from L-B3a, L-B3b, L-conj and L-finram plus proved
   glue. glue-descent counted only L-B3a and L-B3b. Two more inputs are used implicitly by N5
   L703-707: the conjugacy of places over `p` (so that "β is ramified at `p`" makes sense) and
   the finiteness of ramification.
2. **(VERIFIED, Lean.)** The unramified direction of "a Dirichlet character ramifies only at its
   conductor" (`cycUnram`) is elementary glue over valuation subrings, about 85 lines.
3. **(VERIFIED, reading.)** glue-descent's `twist_kills_inertia` has a `unique` hypothesis over
   all homomorphisms `I_v →* U`. For the real (profinite) inertia groups that hypothesis is
   false, so it could never be discharged. The theorem is not wrong, but it cannot be applied.
   The version proved here restricts to locally constant characters, which matches the published
   statement. This is a faithfulness fix for the integration.
