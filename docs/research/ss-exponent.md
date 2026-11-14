# ss-exponent: `SupersingularExponentA` is a theorem (Mathlib only)

**Verdict.** The textbook leaf `SupersingularExponentA` from tyz-318 is **proved** in Lean, with no
hypotheses, no `sorry`, and only the axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED, compiled):

    theorem ZInQ.Contrib.SSExponent.supersingularExponentA : SupersingularExponentA

Source file: `scratch/ss-exponent/SSExponent.lean`. It imports `Mathlib` and
`ZInQKernel.Model.Field.ShortWeierstrass`, and `lake env lean` checks it in about 7 s.
The statement is copied verbatim from `scratch/tyz-318/Lemma318.lean` §1. `diff` confirms the
`def` text is identical (VERIFIED). It uses the fully qualified `ZInQ.shortCurve`, so it does not
depend on any opened namespace:

```lean
def SupersingularExponentA : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 3 → ∀ (k : Type) [Field k] [CharP k p] [DecidableEq k],
    (∀ r : k, r ^ (p ^ 2) = r) → ∀ P : (ZInQ.shortCurve (4 : k)).toAffine.Point, (p + 1) • P = 0
```

No leaf and no glue Prop remain. The proof is elementary. It does not use the characteristic
polynomial of Frobenius, the Hasse bound, isogenies, `#E(F_{p²})` or Tau Ceti. The statement is not
vacuous: the file applies the theorem to `GaloisField 3 2` (every point killed by 4) and to `ZMod 7`
(every point killed by 8) (VERIFIED, compiled).

**Context.** tyz-318 later proved Lemma `torsion2` from the weak exponent `2(p + 1)` and stopped using
this leaf (`docs/research/tyz-318.md`, final section). So this result removes no hypothesis from the
current headline chain. What it does:

* it closes tyz-318's original route, `lemma318Literal_HHprime_of_ss_sqrtTwo`, outright;
* it gives the sharp statement `Ã(F_{p²}) = Ã[p + 1]` as a Lean theorem, for any later use.

## 1. Proof

Write `E : y² = x³ + 4x`, `p ≡ 3 (mod 4)`, and `k` a field of characteristic `p` with `r^{p²} = r`
for every `r ∈ k`.

1. **`#E(F_p) = p + 1`.** This is tyz-318's `card_W1`, copied: a character sum, using `x ↦ −x` and the
   fact that `−1` is a non-square mod `p`.
2. **Frobenius.** `π = Point.map (frobeniusAlgHom)` on `E(k)` satisfies `π² = 1`. A `π`-fixed point
   has `F_p`-rational coordinates, so it lies in the image of the injective map `E(F_p) → E(k)`
   (Mathlib `Point.map_injective`). Therefore every subgroup of `π`-fixed points has order dividing
   `p + 1`, by Lagrange in `E(F_p)`.
3. **`k` without `√−1`.** Then `k = F_p`: if `s = r − r^p ≠ 0` for some `r`, then `s^p = −s`, and so
   `(s^{(p−1)/2})² = −1`. Every point is then `π`-fixed, and step 2 applies.
4. **`k` with `ι² = −1`.** `[i](x, y) = (−x, ιy)` is additive, `[i]² = −1` and `π[i] = −[i]π` (tyz-318,
   copied). The new abstract lemma (§4 of the file) finishes the proof:

   > `nsmul_eq_zero_of_frob`. Let `G` be a finite abelian group with an involution `π` and an
   > endomorphism `i` such that `i² = −1` and `π i = −i π`. Suppose every `π`-fixed subgroup has
   > order dividing `N = 2^v m`, with `m` odd. Then `N • G = 0`.

   Proof of the abstract lemma:
   * **Weak exponent.** `P + πP` and `i(P − πP)` are `π`-fixed, so `2N • G = 0`. This is tyz-318's
     argument.
   * **Bound on `M = G[2^{v+1}]`.** The map `1 − π` sends `M` into the anti-fixed part `M_B`, with
     kernel the fixed part `M_A`. Also `i` maps `M_B` injectively into `M_A`. `#M_A` divides `N`, and
     by Cauchy it is a power of 2, so `#M_A` divides `2^v`. Hence `#M ≤ #M_A · #M_B ≤ 2^{2v}`.
   * **Chain of kernels.** Put `j = 1 + i`. The kernels `ker j^n` increase with `n`, and once two
     consecutive ones are equal the chain stays constant. Since `j² = 2i`, `ker j^{2v+2} = M`.
     If `ker j^{2v} ≠ M`, the first `2v + 2` kernels would increase strictly. Then
     `#ker j^{2v+1} ≥ 2^{2v+1} > #M`, which is impossible.
   * **Conclusion.** So `j^{2v} = 2^v i^v` kills `M`, and `2^v` kills `M`. For any `P`,
     `m • P ∈ M` by the weak exponent, so `N • P = 2^v • (m • P) = 0`.

   Step 2 gives the hypothesis with `N = p + 1`.

## 2. What compiles, what remains

* Compiles: `scratch/ss-exponent/SSExponent.lean`, the whole file, with no errors; `#print axioms`
  is standard. §1–§3 are tyz-318's proved count, `[i]` and Frobenius lemmas, copied under the new
  namespace `ZInQ.Contrib.SSExponent`.
* Remains: nothing for this target.
* Integration note: the file could become a `ZInQKernel/Contrib/` module unchanged. Its only project
  import is `ZInQKernel.Model.Field.ShortWeierstrass`. tyz-318's `Lemma318.lean` could then drop the
  leaf hypothesis from `lemma318Literal_HHprime_of_ss_sqrtTwo` and `lemma318_at_single`.

Log: `scratch/ss-exponent/log.md`.
