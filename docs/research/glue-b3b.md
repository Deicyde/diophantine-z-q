# glue-b3b: L-B3b is glue; B3 (v) now rests on L-B3a alone

Status: research note (task glue-b3b, 2026-11-12). Lean: `scratch/glue-b3b/B3b.lean`
(self-contained, `import Mathlib`, 1617 lines). Log: `scratch/glue-b3b/log.md`.

## Verdict

1. **(VERIFIED, compiled.)** `GlueB3Unram.leafB3b : LeafB3b` is proved in Lean. The statement is
   glue-b3-unram's text, unchanged (the md5 sums of the `def` blocks of `LeafB3b`, `LeafB3a`,
   `LiesOver`, `inertiaGQ`, `etaP`, `legChar`, `galChar`, `cyc` match across
   `scratch/glue-b3-unram/Unram.lean`, `scratch/glue-conj/UnramConj.lean` and `B3b.lean`): for an
   odd prime `p` and every place `w` of `ℚ̄` over `p`, the Legendre character mod `p` (as a
   character of `G_ℚ` through the cyclotomic character) is nontrivial on the inertia group `I_w`.
2. **(VERIFIED, compiled.)** `GlueB3Unram.unramified_outside_b3a (hA : LeafB3a) ...` proves B3 (v)
   (N5 L702-712: the twisted kernel field `L'` is unramified outside `T`). It has the same
   hypotheses on `L` and the same conclusion as glue-conj's `unramified_outside_final`, but assumes
   **only `LeafB3a`**: the body is `unramified_outside_final hA leafB3b ...`.
3. **(VERIFIED, compiled.)** A bonus: `GlueB3Unram.t32b : LeafPush.T32b_QuadraticRamification`.
   This is leaf **T32(b)** of the synthesis bundle (`TextbookLeaves.t32b` in
   `scratch/h-decomposition/Leaves.lean`). Its statement is copied verbatim from
   `scratch/leaf-push/Push.lean`, and `diff` shows it identical to Leaves.lean L11903-11916, with
   the defs `GQ`, `IsAtPrime`, `inertiaQ` identical to L11877-11888. It says: for squarefree
   `d ≡ 1 mod 4`, a square root `s` of `d` and `w` over `ℤ_(p)` (any prime `p`, including 2), some
   element of `I_w` moves `s` iff `p ∣ d`. So T32(b) is glue, not a leaf.
4. Every `#print axioms` line in `B3b.lean` (12 theorems, among them `exists_inertia_neg`,
   `leafB3b`, `unramified_outside_b3a`, `t32b` and the 8 glue-b3-unram/glue-conj theorems) reads
   `[propext, Classical.choice, Quot.sound]`. The file has no `sorry` and no `axiom`, and
   `lake env lean` takes 20 s.
5. **L-B3a is not proved** (and neither is T32(a), its leaf-push form). It needs the structure of
   tame inertia, which Mathlib lacks; see "What remains".

## The method (no discriminants, no ramification indices)

The glue-conj agent's guess was SPECULATIVE: it suggested using Mathlib's cyclotomic discriminant
or ramification results. The proof does not use them. Instead it builds the inertia element
directly from Mathlib's profinite invariant theory. All steps are compiled.

- **Gauss sum** (`gaussP`, `gaussP_sq`, `gaussP_transform`). In `ℚ̄`, set
  `g = ∑ₐ (a/p) ζ^a` with `ζ` a primitive `p`-th root of unity. Mathlib's `gaussSum_sq` gives
  `g² = (-1/p) p = ±p`. From `modularCyclotomicCharacter.spec` and `gaussSum_mulShift_eq`,
  `s(g) = (cyc_p(s)/p) · g` for `s ∈ G_ℚ`. So `etaP p s = 1 ⇒ s g = g`.
- **The core theorem** (`exists_inertia_neg`). Suppose `α ∈ ℚ̄` with `α² = c ∈ ℤ`,
  `v_w(c) = v_w(p)`, and some `σ ∈ G_ℚ` with `σ α = -α`. Then some `s ∈ I_w` has `s α = -α`.
  Proof:
  - Let `H = Stab(α)`: open, hence closed, hence compact. Let `B` be the algebraic integers,
    `A = FixedPoints.subalgebra ℤ B H` (`= 𝓞_{ℚ(α)}`, never computed), and `Q` the center of `w`
    on `B`.
  - (i) `σQ` and `Q` lie over the same prime of `A`.
  - (ii) Mathlib's `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` (over `A`, group
    `H`) gives `h ∈ H` with `τ = hσ` stabilizing `Q`, and still `τ α = -α`.
  - (iii) `τ` induces an `A/(Q∩A)`-algebra automorphism of `B/Q`.
  - (iv) `Ideal.Quotient.stabilizerHom_surjective_of_profinite` (over `A`, group `H`) gives
    `h' ∈ Stab_H(Q)` acting on `B/Q` like `τ`.
  - (v) `s = h'⁻¹τ` stabilizes `Q`, acts trivially on `B/Q` and negates `α`. Then
    `mem_inertia_of_center` shows `s ∈ I_w`, using glue-conj's center lemma `le_of_center` and
    writing elements of `w` as `n/d` with `n, d ∈ B`, `v(d) = 1`.
  - The arithmetic input for (i) and (iii) is "the residue extension of `ℚ(α)` at `w` is
    trivial". It is replaced by the valuation lemma `val_sub_lt_one`: if `a, b` are `w`-integral
    and `(a - b)α ∈ ℤ`, then `v(a - b) < 1`. The reason is that `v(α)` lies strictly between
    `v(p)` and `1`, while an integer has valuation `1` or `≤ v(p)`. The other ingredient is
    `exists_int_anti`: for `a ∈ A`, `(a - σa)α` is `G_ℚ`-invariant and integral, hence lies in
    `ℤ`.
- **`leafB3b`** combines the two with `c = ±p`. The irrationality of `g` comes from
  `not_isSquare_of_squarefree`.
- **`t32b`**:
  - (⇐) `p ∣ d` squarefree gives `v(d) = v(p)`, then apply `exists_inertia_neg`.
  - (⇒) If `p ∤ d` and `σ ∈ I_w` had `σ s = -s`, take `t = (1+s)/2`. It is integral, as a root
    of `X² - X - (d-1)/4`, so inertia gives `v(σt - t) = v(-s) < 1`. That contradicts
    `v(s)² = v(d) = 1`.
  - `IsAtPrime O p` together with `w ∩ ℚ = O` gives `LiesOver w p` (`liesOver_of_isAtPrime`).

`exists_inertia_neg` holds for every prime `p`, including 2; it does not need `p` odd. Mathlib
inputs used (VERIFIED by compilation against Mathlib v4.35.0):

- `gaussSum_sq`, `gaussSum_mulShift_eq`, `AddChar.zmodChar_primitive_of_primitive_root`;
- `quadraticChar_ne_one`, `quadraticChar_dichotomy`, `MulChar.IsQuadratic.inv`;
- `modularCyclotomicCharacter.spec`, `stabilizer_isOpen_of_isIntegral`;
- `InfiniteGalois.mem_bot_iff_fixed`;
- `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`,
  `Ideal.Quotient.stabilizerHom_surjective_of_profinite`;
- `IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq`.

## File layout (`scratch/glue-b3b/B3b.lean`)

- Lines 1-918: `scratch/glue-conj/UnramConj.lean` verbatim through `end Conj` (glue-b3-unram
  plus glue-conj's `leafConj`), after an 8-line header comment. Sections from line 929; `t32b` at line 1542.
- Sections `B3b` (valuation lemmas, `exists_int_anti`, `exists_frac`, `mem_inertia_of_center`),
  `B3bMain` (`exists_inertia_neg`) and `B3bGauss` (Gauss sum, `leafB3b`).
- glue-conj's `unramified_outside_final`, unchanged, followed by the new `unramified_outside_b3a`.
- Namespace `LeafPush` (verbatim T32(b) defs), then `GlueB3Unram.t32b`.

## Effect on the decomposition

- B3 (v): the leaves were L-B3a, L-B3b and L-conj (glue-b3-unram). glue-conj made it L-B3a and
  L-B3b. Now it is **L-B3a only**.
- Synthesis bundle: T32(b) can be dropped from `TextbookLeaves` and supplied by `t32b`, once the
  file is integrated. T32(a) remains.
- No file under `ZInQKernel/` or `blueprint/` was edited. For integration,
  `ZInQKernel/HDecomp/` would need glue-b3-unram's and glue-conj's material (the prefix of
  `B3b.lean`) as a module, with this task's sections appended.

## What remains: L-B3a (unique quadratic character of tame inertia)

Not proved. `LeafB3a` says that two nontrivial locally constant characters `I_w → ℂˣ` of order
dividing 2 are equal, for `p` odd. Given `leafB3b`, it is equivalent to: every such character is
trivial on `I_w ∩ Stab(√p*)`. The text gives two routes (both SPECULATIVE):

1. **Finite level.** The image of `I_w` in `Gal(F/ℚ)`, for `F` finite Galois, has a normal
   `p`-subgroup with cyclic quotient. This is `G₀/G₁ ↪ k^×` with `G₁` a `p`-group (Serre,
   *Corps locaux* IV §2, Cor. 1-4, locator UNVERIFIED). Mathlib has no higher ramification groups.
   A search of Mathlib for files mentioning `inertia` together with `IsCyclic`/`tame` found none
   (VERIFIED).
2. **Kummer.** A quadratic character of `I_w = Gal(ℚ̄/E)`, with `E` the inertia field, is
   `s ↦ s(√u)/√u` for some `u ∈ E`. Then one needs `v(E^×) = v(ℚ^×)` (`E/ℚ` unramified at `w`) and
   that `√(unit)` is fixed by inertia (p odd). The first point needs the identification
   `|I_P| = e`, which Mathlib has (`Ideal.card_inertia_eq_ramificationIdxIn`, used by
   glue-b3-unram's bridge), plus surjectivity of `I_w` onto the finite-level inertia group and
   infinite Kummer theory.

Either route is a project of several hundred lines (SPECULATIVE estimate). It is beyond this
task's remaining time, so L-B3a stays a leaf (published: Serre, *Corps locaux* IV §2;
Neukirch–Schmidt–Wingberg 7.5; locators UNVERIFIED).
