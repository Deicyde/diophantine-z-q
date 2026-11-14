# ss-exponent results log

Target: `SupersingularExponentA` (verbatim from scratch/tyz-318/Lemma318.lean §1, merged origin/wip/tyz-318).

## Compile outcomes
- [VERIFIED, compiled, 2026-11-14 00:10] `scratch/ss-exponent/Abstract.lean`: abstract group lemma
  `nsmul_eq_zero_of_frob`: finite abelian `G`, `π` involution, `i² = −1`, `π i = −i π`, every `π`-fixed subgroup
  has order dividing `N = 2^v m` (`m` odd) ⟹ `N • G = 0`. No sorry. (Proof: weak exponent `2N` as in tyz-318;
  `#G[2^{v+1}] ≤ #(fixed part)·#(anti-fixed part) ≤ 2^v·2^v`; the chain `ker (1+i)^n` strictly increases until it
  stabilizes, `(1+i)² = 2i`, so `(1+i)^{2v} = 2^v i^v` kills `G[2^{v+1}]`.)
- [VERIFIED, compiled, 2026-11-14 00:20] `scratch/ss-exponent/SSExponent.lean` (imports `Mathlib`,
  `ZInQKernel.Model.Field.ShortWeierstrass`; `lake env lean`, ~7 s): **`supersingularExponentA :
  SupersingularExponentA`**, no hypotheses; `#print axioms` = [propext, Classical.choice, Quot.sound]; no sorry.
  The abstract lemma (formerly Abstract.lean, now §4) is merged in; Abstract.lean deleted.
- [VERIFIED, `diff`] the `def SupersingularExponentA` text is identical to scratch/tyz-318/Lemma318.lean §1
  (both use the fully qualified `ZInQ.shortCurve`, no opened-namespace dependence).
- [VERIFIED, compiled] non-vacuity instances: `GaloisField 3 2` (points killed by 4) and `ZMod 7` (killed by 8),
  both by applying `supersingularExponentA`.

## Statement
- `SupersingularExponentA` (was LEAF, textbook, in tyz-318): ∀ p prime, p % 4 = 3, ∀ field k, CharP k p,
  [DecidableEq k], (∀ r, r^(p²) = r) → ∀ P : (shortCurve (4:k)).toAffine.Point, (p+1)•P = 0.
  Now a THEOREM (glue-free: Mathlib only). No leaf remains.

## Proof route (all VERIFIED by compilation)
1. `#E(F_p) = p + 1` (tyz-318 `card_W1`, character sum + `x ↦ −x`).
2. `π` (p-power Frobenius on `E(k)`), `π² = 1`; `π`-fixed points = image of the injective `E(F_p) → E(k)`,
   so every `π`-fixed subgroup has order dividing `p + 1` (Lagrange in `E(F_p)`).
3. If `k` has no `√−1`: every `r` has `r^p = r` (else `s = r − r^p`, `s^p = −s`, `(s^{(p−1)/2})² = −1`), so all
   points are `π`-fixed: done by 2.
4. If `ι² = −1` in `k`: `[i](x,y) = (−x, ιy)` additive, `[i]² = −1`, `π[i] = −[i]π` (tyz-318); the abstract
   lemma `nsmul_eq_zero_of_frob` with `p + 1 = 2^v m` gives `(p+1)•P = 0`.
- Not used: characteristic polynomial of Frobenius, Hasse bound, isogenies, `#E(F_{p²})`, Tau Ceti.
