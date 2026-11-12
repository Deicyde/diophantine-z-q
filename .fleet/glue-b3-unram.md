# glue-b3-unram (2026-11-12)

**Result.** B3 (v), "the twisted kernel field `L'` is unramified outside `T`" (N5 L702-712),
is now a Lean theorem: `GlueB3Unram.unramified_outside_final` in
`scratch/glue-b3-unram/Unram.lean`.
- The file is 673 lines, self-contained, and checked with `lake env lean` in about 10 s.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- The theorem rests on three leaves stated as `def … : Prop` over Mathlib objects.
- Inertia groups of `G_ℚ` are images of Mathlib's `ValuationSubring.inertiaSubgroup` for
  valuation subrings `w ⊂ ℚ̄` over `p`, the same convention as pkg-I2.

The three leaves:
- `LeafB3a` (L-B3a): at an odd `p`, the inertia group has at most one nontrivial locally constant
  quadratic character (from the structure of tame inertia; Serre, *Corps locaux* IV §2,
  UNVERIFIED locator).
- `LeafB3b` (L-B3b): the Legendre character mod an odd `p`, composed with `cyc p`, is nontrivial
  on every inertia group over `p` (`ℚ(√p*)` is ramified at `p`; STANDARD).
- `LeafConj`: places of `ℚ̄` over `p` are `G_ℚ`-conjugate. This is a new leaf that N5 uses
  implicitly: without it, "β is ramified at `p`" is not well defined.

**Proved glue.**
- `cycUnram`: a Dirichlet character is unramified at `p ∤ N`.
- `inertia_le_of_unramifiedAt`: glue-descent's ideal-theoretic `UnramifiedAt L p` gives
  `I_w ≤ G_L`. The proof uses Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn`.
- `finRam`: an open subgroup contains almost all inertia groups. The proof uses Mathlib's
  discriminant criterion and normal closures. This was planned as a leaf and is now glue.
- The twist argument itself.

The hypotheses are exactly the outputs of glue-descent's `b2_of_leaves` and
`inflatedNormalized_of`, including `UnramifiedAt` and `2 ∈ T`. `2 ∈ T` holds in the application:
`heightPrimes ⊆ S_mul`.

**Faithfulness fix.** glue-descent's `twist_kills_inertia` assumes uniqueness over *all*
quadratic homomorphisms of inertia. That assumption is false for the real profinite inertia
groups, so it could never be discharged. The version proved here uses locally constant
characters.

**What remains.**
1. Integration. B3 must call `b2_of_leaves` first, then this theorem (`η` depends on `β₁`),
   then build `L'` as in `b3_of_leaves`. The definitions copied from glue-descent must be
   unified.
2. The converse bridge (Galois-unramified `L'` ⇒ `UnramifiedAt L'`), needed only if downstream
   wants the ideal form.
3. L-B3a, L-B3b and L-conj are unproved leaves. L-B3b and L-conj would become glue once the
   converse bridge (lifting inertia from a finite level to `ℚ̄`) exists.

Report: `docs/research/glue-b3-unram.md`. Log: `scratch/glue-b3-unram/log.md`.
