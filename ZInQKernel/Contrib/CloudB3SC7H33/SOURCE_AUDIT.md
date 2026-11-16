# TYZ Theorem 3.3: printed-source comparison

Evidence: **AI-READ**, 2026-11-16. This does not clear a human-reading flag and is not a kernel proof of an algebraic modular-curve dictionary.

## Editions actually opened

- Tian–Yuan–Zhang, *Genus periods, genus points and congruent number problem*, **arXiv:1411.4728v1**: https://arxiv.org/pdf/1411.4728v1 . The exact source response https://arxiv.org/src/1411.4728v1 contains `Period7.tex`, 147,063 decompressed bytes, 3,357 lines.
  - PDF SHA-256: `aa0b6791b0ccd186db488468168289d0182751aa77db41c455b77844191ad1f8`.
  - Source response SHA-256: `b295b1605f9760c8780fd0dc7f5429ecf2569510e4b0bbe28bd2f0b1bb81fed2`.
  - Decompressed TeX SHA-256: `18cee04cb4d63818119f4ffa547d07fc69467031bfbe521622da5a907ef36e32`.
- Authors' typeset journal copy, **Asian J. Math. 21 no.4 (August 2017), pp.721–774**: https://web.math.princeton.edu/~shouwu/publications/cn.pdf .
  - PDF SHA-256: `417f6bbe7f7b775f77a2593cc2f32cbab2f2782cf07d0ba0a15f2708b2475595`.
  - **Theorem 3.3: printed p.739 / PDF page19.** Setup: pp.736–739. Proposition3.2(4): p.738. Theorem3.6: p.741. Sign and Corollary3.9: p.744. Proof: pp.748–751. Explicit TheoremA.9: p.769.

Short verbatim statement quote, journal p.739: “The point Pχ is non-torsion only if χ is of the form”. The eligible decomposition and displayed point equality below it are unchanged from v1.

Read v1 source L311–407, L1159–1348, L1521–1600, L1846–2020 and L3021–3079, and the corresponding typeset statement/setup/proof pages. Other parts of the paper, the complete proof of A.9, and the underlying Yuan–Zhang–Zhang and Kolyvagin sources were not independently verified here.

## Exact statement and residual inputs

The new export proves the **unchanged** `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33`, with the two explicit premises:

- `T5Glue.ShimuraMainCM`, already a separate input of `frozenTarget`;
- `ZInQ.Contrib.TYZGenus.H33Dict.TYZThm33Printed`.

No new proof of either premise is claimed. `TYZProp324Used` is proved from the existing CM premise in the reused reduction; it is not an additional leaf.

**Source-content verdict:** the printed premise is faithful or weaker. The reduction to the old eta-coordinate/quantifier statement remains a conditional consequence. This is not an unconditional h33 or Hilbert10 result.

## Clause comparison

- Positive squarefree n and §3's standing n≡5,6,7 are retained with only the subcases n≡5,7 required. Zero is excluded. The eligible factors are odd, so the printed residue classes6 and2 add no instances.
- Journal p.736 fixes `(X0(32),∞) ≅ A:2y²=x³+x`. The scaling `(x,y)↦(2x,4y)` gives the existing `y²=x³+4x`, compatibly with `[i]`.
- The printed embeddings on p.737 have fixed equations exactly `[16(n+1),−8,1]` and `[(n+δ²)/4,δ,1]`, with δ²≡−n mod128. The fixed point P_n=[h,1] and z_n=f_n(P_n) are the intended CM points, not an arbitrary family.
- The sign is confirmed on p.744: α=−i and `f_n=f0∘[1−i]`. The class5 point is `(1−[i])i0(P_n)`; class7 uses i0(P_n).
- Cl_n, the representatives Φ and Pχ are those of pp.738–739. A ±1-valued Artin character is unchanged by inversion of the Artin convention. The radicand is d1 for n≡5 and d1*=(-1)^((d1−1)/2)d1 for n≡7.
- The same p.739 formula has factor `ε·2^h2(n)·L(d1)·P(d0)`. ε=±i exactly for (d0,d1)≡(5,3), and ±1 otherwise. Cleared equality modulo torsion is equality after tensoring with Q.
- `P(d0)=Q(d0)/m(d0)`, m>0, forgets the regulator-dependent coefficient: this is a weakening. Unused indices may use Q=0. The analytic-order>1 clause implies L(d)=0 and P(d)=0 in the printed definition; the Lean torsion requirement is its zero-vector consequence.
- Φ is fixed before Theorem3.3. The new premise chooses ε after Φ and χ, not before them. The reused proof obtains uniform ε using torsion independence of the lift family and uniqueness of each eligible quadratic character. This introduces no new unproved uniformity premise.
- The proof on pp.750–751 explicitly covers vanishing L-derivative products by zero vectors. Thus the Lean equality includes every eligible character, not only eligible non-torsion cases.
- Arbitrary integer sign choices of L on classes1,3 are absorbed into ε. The odd-case denominator `2^(2k−3)Ω_m` and the period definition agree with v1's introduction.

## Interpretation and non-vacuity boundaries

The reused Lean proves the eta coordinates satisfy `IsX0Identification`, including cusp bounds. It does **not** construct a scheme isomorphism or prove an equivalence with an algebraic pointed-Q-isomorphism predicate.

The standard interpretation is: `IsRatModFn` gives rational modular functions without poles on the upper half-plane; the curve equation gives a nonconstant map to the smooth cubic; the unique pole of X at∞ has order≤2; hence `deg X=2 deg i0≤2` forces degree1. Conversely every pointed identification has such pullbacks. Over Q the pointed identifications differ only by sign. This interpretation is mathematically valid setup over genuine definitions, not a new structure containing the desired Gross–Zagier conclusion; nevertheless it remains source interpretation, not a Lean scheme-equivalence theorem. The X_U/component interpretation likewise remains source reading.

The reused non-vacuity theorem establishes the X,Y,w hypotheses **given hCM**. The ℓ hypothesis separately depends on TYZ1.1 integer-square data. It is not an unconditional non-vacuity result for every premise.

If this analytic definition is accepted as the printed setup, the new open premise is one printed unread TYZ3.3 leaf while hCM is reused. No additional dictionary premise or glue-count rise is requested. AI-READ does not decide or clear a human-reading/rating flag; that ruling belongs to the maintainer.

## Minor typo in the source's proof

V1 L1978 and journal p.750's final d1=1 proof sentence print `(4P)^c=+4P` before concluding membership in the minus subgroup. The sign must be **−** there, by the preceding conjugation calculation after killing the torsion term. This is a proof-sentence typo, not a counterexample to Theorem3.3 or a change requested to the target.

## Bounded formal supplier search

Pinned server-side tree inventories and twelve complete candidate content reads were checked, without recursive checkout scans:

- FLT `6e837e75355538c7f80bab5b956861e86c4eacc2`: complete primary Definitions/Theorems/P2M indices; JZero height sources supply algebraic/log-height support, not the exact derivative/CM point formula.
- TauCeti `086028a6d8d186715b52fac7f3e7b23175ed2dc9`: complete tree; canonical height, L-function and regulator sources supply genuine prerequisites but no exact closed h33 proof was validated.
- Stacks `c496df0d9beea9deaeabcea8492605f9a0a2313b`: complete core; frontier enumeration was truncated. Adic L-function source concerns finite-field Frobenius Euler products, not number-field central derivatives.
- Mordell `82a30cb7857f6e3cfdb1be91f5533c0ccb57d493`: complete tree; Néron–Tate/Jacobian pairing support has no exact GZ supplier among the sources read.
- Jacobian-Challenge `c4254cce15b3e284a0a3ae1d73936f2ee195d272`: complete tree and entry; Picard/Albanese/Jacobian geometry is not the analytic GZ identity.
- Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`: complete tree; elliptic Euler products and naïve heights do not supply the exact h33 formula.

No repository-wide or global absence claim is made. No candidate was promoted to a closed proof and none is vendored. The remaining deep input is the printed TYZ3.3 formula itself: its proof uses Tunnell–Saito, explicit YZZ A.9, the derivative/height relation, rank one via Gross–Zagier–Kolyvagin and uniform cross-pair constants. The existing hL3/hFH/hCM tasks are not taken over.
