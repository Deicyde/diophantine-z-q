# h-map: map of the height hypothesis H (SixContactMin)

Full note: `docs/research/h-map.md`. Scripts and log: `scratch/h-map/`.

**Three findings that matter most**

1. **What the proof uses (VERIFIED in Lean).** The proof uses one inequality,
   `h(u) ≤ H₆(D)·M_{S_mul}(u)²⁴` on `ℚ \ 𝒞`, at two points:
   - the precision step (`ratHeight_le_bound_of_test`);
   - the finite box of multiplication (`slope_height_le`).

   At each point `u` is an adversarial witness. There is huge slack in the constant (a tower
   budget), in the exponent (anything below the test valuation 25) and, for the precision use
   only, in the shape (any `NExpr`). There is **none** in effectivity or in uniformity over `u`.
   So narrowing the statement cannot make H easier: it is uniform effective Mordell for twists
   of a genus-17 curve, that is, for the compact Shimura curve `X⁶/W`.
2. **The weakest link is the manuscript itself.** The chain is Lean ⇐ Theorem 4.1 ⇐ refereed
   theorems plus 5 upstream supplements.
   - The new argument in Theorem 4.1 (scalar descent, the character β, the conductor bound
     `N ≤ QM²`, the transfer) has had only AI reviews (four Astra reviews and the repository
     notes).
   - The worst supplement is `b11-integral-model`: unpublished, unread, and not reproduced by
     any script.
   - Two inputs are uncited: I2 and the independence of `ℓ`.
   - GR14's non-circularity is unchecked.
3. **New route B1: drop the integral model.** Lemma PR ("`K` is unramified at `p ∉ S` when
   every contact valuation is even, and `A` has good reduction at every `v ∤ 3`") should follow
   from published results, with no model of `Y₃`:
   - Beckmann's specialization theorem (Crelle 1991; Grothendieck's tame specialization) for
     `Y₃ → P¹_j`, with monodromy of order `| 4·72` and branch data `(0,4), (∞,6), (−16/27,2)`;
   - Morita (QM surfaces have potentially good reduction everywhere);
   - Serre–Tate, with the full level-3 structure.

   Exact checks (`beckmann_check.py`, `o3_units.py`): for `p ∉ {2,3,5,7,11,13}` the branch
   multiplicities are `2v_p(u−c)`, `6v_p(G)` and `2v_p(H)`, and `J(∞)` is not a branch value.
   Together with B2-B5 (Pan applied directly, published sources for `a001`, `ly-d6` and
   `igusa-theta`, citations for I1 and I2, NoCM), this leaves **no supplement** in H's
   justification.

**Ratings**
- (a) Narrowing:
  - A1 `SixContactMin`: done.
  - A2, a consumer-shaped split: high feasibility, very low payoff.
  - A3, a subset of `u` or an ineffective constant: very low (ruled out).
- (b) Justification:
  - B1 Beckmann: **medium-high**.
  - B2 Pan applied directly: high (reviewed; repairs pending).
  - B3 the three computational supplements: high.
  - B4 citations for I1 and I2: high.
  - B5 NoCM: high.
  - B6 Khare–Wintenberger with Kisin, as a fallback: high (no gain in depth).
  - B7 GR14 non-circularity: medium.
- (c) Elimination by redesign: very low across the board (S-units, elliptic or genus-2
  families, per-curve Chabauty, other contact sets, trading H for CR₃, formalizing H).

**Next tasks**
1. **T1, route B1 as an audit record.** *First step:* pin Beckmann's exact hypotheses (G-cover
   over a number field, no vertical ramification when `p ∤ |G|` and the branch locus is étale),
   through Legrand's arXiv restatements if Crelle cannot be read, and match them to `Y₃ → P¹_j`.
2. **T2, adversarial review of N5 L631-716 and L796-857** (descent, β, conductor at 2 and at
   `p > R`). *First step:* recompute every inequality of the order bound for β and of the break
   bound line by line.
3. **T3, one supplement-free trust statement for H** (B2 + B3 + B4 + B5 + T1), then one review.
   *First step:* list a numbered published supplier for each step of Theorem 4.1.
