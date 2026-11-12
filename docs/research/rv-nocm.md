# Review rv-nocm: NoCM (step A10) and the branch indices of step A5 after the locator audit

Adversarial review of two arguments that `docs/research/locators.md` (below: *the audit*) may
affect. Labels: **VERIFIED** (read in a source named here, computed by
`scratch/rv-nocm/nocm_check.py`, or compiled in `scratch/rv-nocm/OrbifoldIndex.lean`),
**STANDARD** (published, reference given), **SPECULATIVE**, **UNVERIFIED** (a locator from memory
or from another note, not read here: González–Rotger, Baba–Granath and Elkies were not available
on this host, which has no network). The manuscript is `diophantine_zq.tex`; line numbers are
those of the file in this branch.

## Verdicts

**(1) NoCM (A10): HOLDS AFTER REPAIRS.** The repairs are to the statements of leaves, not to the
argument.

- Neither proof of NoCM uses the unqualified count `#CM(R) = h(R)`:
  - The proof of h-cm §4.1.4 uses `#CM(𝔬) = 2^b h(𝔬)`, together with simple transitivity of
    `W' × Pic(𝔬)`.
  - The shortened proof of rv-h-cm §7.2 (the one adopted by h-trust A10 and glue-repo A10) uses
    `#CM(R) = h(R)` only in the case `D(R) = 1`. There `b = 0`, so the orientation factor is
    `2⁰ = 1`.
  - VERIFIED by reading both proofs.
- The unqualified statement is nevertheless printed as the leaf R5 / L14 in four places:
  h-decomposition R5, glue-repo §A10 (row L14 of the table), `R05_GonzalezRotger` in
  `scratch/h-decomposition/Leaves.lean`, and hdec-elementary L3. It is **false** as stated:
  - 15 of the 24 non-elliptic rows of Elkies' table contradict it (§1.2).
  - It also fails at `ℤ[i]` itself: `h = 1`, but `X₆` has two `ℤ[i]`-CM points.
  - Such a statement must never become a Lean leaf, since a false leaf proves everything.
- Every field-of-definition claim in NoCM concerns points of `X₆ = X₀(6,1)`, González–Rotger's
  own curve. None concerns `X₆/W` or `Y₃`. The rational value `t(u)` on the quotient is used only
  to locate the fibre. The audit's discriminant `−24` example is consistent with this (§1.3).
- Repaired texts: §3.1.

**(2) Step A5 (Prop. TS, Lemma NV): HOLDS AFTER REPAIRS.** Again, only the supplier's wording
needs repair.

- A5 needs the ramification of the level-three cover `Y₃ → P¹_j`:
  - Prop. TS uses the inertia orders `e_b/gcd(e_b, m_b)` of `M = ℚ(Y^{(1)})` over `ℚ(j)`.
  - Lemma NV step 3 uses `I_𝔓 = I_{Q_i}`, cyclic of order `e_i`.
- For that cover the indices are the orbifold elliptic orders `(4, 6, 2)` of the normalizer group
  `Γ*`, because:
  - `Γ₃` is torsion-free (`−1 ∉ K₃`, and `1 + 3M₄(ℤ₃)` is torsion-free, N5 L468-470);
  - `Γ₃` is normal in `Γ*`;
  - the ramification index of a torsion-free normal cover equals the stabilizer order
    (`RvNocm.ramification_eq_orbifold_order`, compiled).
- The manuscript itself says that each geometric component of `Y₃` is a torsion-free cover of
  the norm-one orbifold (L480-482).
- The indices `(2, 2, 2)` belong to the degree-4 map `X₆ → X₆/W`. Lemma NV step 4 uses exactly
  those, and derives them internally, correctly.
- The audit's correction therefore hits the leaf texts. They say "`X₆/W` branched with indices
  4, 6, 2", which is wrong for the finite map `X₆ → X₆/W` and silent about `Y₃`. It does not hit
  the argument.
- Cross-checks (VERIFIED, computed and compiled):
  - Riemann–Hurwitz for a component of `Y₃` (degree 72 over `P¹_j`) gives genus 4 with indices
    `(4, 6, 2)`, and is impossible with `(2, 2, 2)`.
  - Of the six labellings of `{4, 6, 2}` on `(0, ∞, −16/27)`, only Baba–Granath's makes Lemma
    PR(i)'s conclusion true.
- Repaired texts: §3.2.

## 1. NoCM

### 1.1 What the arguments use (VERIFIED by reading)

| Source | Count used | Field claims used | On which curve |
|---|---|---|---|
| h-cm §4.1.4 (Cases A-C) | `#CM(𝔬) = 2^b h(𝔬)`, `W' × Pic(𝔬)` simply transitive (JGR) | `K·ℚ(x) = K(f)` (S) | `X⁶` |
| rv-h-cm §7.2 (adopted: h-trust A10, glue-repo A10, h-decomposition G6) | `#CM(R) = h(R)`, only in the case `D(R) = 1`, where `b = 0` | GR Thm 5.12: `ℚ(x) = H_R` if `D(R) ≠ 1`, `[H_R:ℚ(x)] = 2` if `D(R) = 1` | `X⁶` |
| rv-h-cm §2.3 (twist constants `c₀ = −1`, `c₁ = 3`) | none | fields of the points of `X⁶` over `t = 1, ∞, 0` (GR Thm 5.8/5.12) | `X⁶` |
| h-cm/rv-h-cm Step 1 (the fibre) | none | the residue field of the points of `X⁶` over `t(u)` is `ℚ(i)`, read off the model | `X⁶` |

Neither proof assigns a field of definition to a point of `X* = X⁶/W` or of `Y₃`.

- The quotient enters only through the rational coordinate `t = 1 + 27j/16`. This is the unique
  `ℚ`-coordinate on `X* ≅ P¹_ℚ` with values `0, 1, ∞` at the CM points of discriminants
  `−24, −4, −3`.
- It also enters through the fact that the map `X⁶ → X*` is `W`-Galois over `ℚ`.

The surface `A` of the manuscript lives on `Y₃`. Forgetting the level structure sends it to a
point of `X⁶` over `J(u)`. This does not change `End(A_ℚ̄)`, so `A` is CM exactly when that
point of `X⁶` is CM. NoCM is a statement about all four points of `X⁶` over `t(u)`.

There is one gap of exposition, in rv-h-cm §7.2, case `D(R) ≠ 1`. The step "`R = ℤ[i]`, so `x`
lies over `t = 1`" needs one of two justifications:

- `CM(ℤ[i])` has `2^1·1 = 2` points, by the corrected count, and both points of `X⁶` over
  `t = 1` are `ℤ[i]`-CM points (h-b1 M9). So `CM(ℤ[i])` is exactly the fibre over `t = 1`.
- Alternatively, an element of `𝒪` of reduced norm 2 in the image of `ℤ[i]` normalizes `𝒪` and
  acts as `w₂` fixing `x`. So `x` is a branch point with stabilizer `⟨w₂⟩`, i.e. it lies over
  `t = 1`.

With the unqualified count, this step would contradict the two points over `t = 1`.

### 1.2 The count with and without the orientation factor (VERIFIED, `nocm_check.py` Part A)

On the 24 non-elliptic rows of Elkies' Table 1, every row is a rational point of `X*` whose
fibre is a free `W`-orbit of 4 points. Recomputed independently here, in pure Python (class
numbers by reduced forms):

- (Emb) holds in every row: `(f, 6) = 1`, and neither 2 nor 3 splits.
- `2^b h(R) = 4` in every row.
- `h(R) = 4` holds in exactly the 9 rows with `b = 0`: `|D| = 84, 120, 132, 168, 228, 312, 372,
  408, 708`.
- In the other 15 rows the unqualified count is wrong. Examples: `|D| = 19, 43, 67, 163`
  (`h = 1`, `b = 2`) and `|D| = 40, 51, 52, 75, 88, 100, …` (`h = 2`, `b = 1`).
- Elliptic points: `|D| = 4` and `|D| = 3` have `h = 1`, `b = 1`, and 2 points each.
  `|D| = 24` has `h = 2`, `b = 0`, and 2 points.

This confirms the audit's R5 finding, including its example `D = −19` (4 points, `h = 1`).

### 1.3 Fields: on `X₆`, not on the quotient (VERIFIED, Parts B and C)

**Part B.** For all 24 rows the fibre field `ℚ(√−t, √(3(t−1)))` agrees with GR Thm 5.12 *on
`X₆`*:

- if `b ≥ 1`, it has degree `2h` and contains `K`;
- if `b = 0`, it has degree `h` and does not contain `K`;
- in both cases `[K·ℚ(x) : K] = h`;
- every quadratic subfield passes an unramified-outside-`f` consistency test over `K`.

**Part C, the audit's example.** For `D = −24`:

- `H_R = ℚ(√−6, √2)` has degree 4.
- The image `t = 0` (`j = −16/27`) on `X*` is rational, of index 4 in `H_R`.
- The two points of `X₆` over it have `ℚ(x) = ℚ(√−3)`, of index 2, as GR Thm 5.12 states for
  `D(R) = 1`.

So no index-2 statement holds on the quotient, and none is used. The twist-constant derivation
(rv-h-cm §2.3) uses exactly the `X₆`-field `ℚ(√−c₁) ∈ {ℚ(√2), ℚ(√−3)}` at `t = 0`.

### 1.4 What remains as stated before (not affected by the audit)

The audit does not touch NoCM's other inputs: (S)/GR Thm 5.8, (Emb), the model, and the
interface with A9. Their status is as in h-trust A10:

- GR numbering VERIFIED in arXiv:math/0612732 by rv-h-cm. The journal locators are Prop. 5.6,
  p. 943, and Thm 5.12, p. 946, per the audit (UNVERIFIED here).
- Vignéras is UNVERIFIED.

One more caution applies to the leaf. The audit reads GR's count as `2^{#{p | D(R)N(R)}} h(R)`.
At `N = 1`, with `D(R)` the product of the primes `p | 6` inert in `K`, this is the `2^b h(R)`
used here. It is valid only together with (Emb), as rv-h-cm R1(a) already noted.

## 2. Step A5: which cover, which indices

### 2.1 The cover A5 needs (VERIFIED by reading h-b1 §§1.2-3, §2 M2-M4, manuscript L421-528)

- **Prop. TS** (h-b1 §1.2) is applied to `M = ℚ(Y^{(1)})`, a `ℚ`-component of `Y₃`, Galois over
  `ℚ(j)` (M2). It uses the inertia generator `g_i` at the branch point `b_i` and its order
  `e_i`. The inertia of the fibre field at `p` is `⟨g_i^m⟩`, of order `e_i/gcd(e_i, m)`.
- **Lemma NV**:
  - Step 3 uses `I_𝔓 = I_{Q_i}`, cyclic of order `e_i` (M4), again for `Y₃ → P¹_j`.
  - Step 4 uses `e_∞ = 6`, `e_{−16/27} = 2` to get `|I_V| ∣ 2`. It then uses the image in
    `W = Gal(ℚ(X₆)/ℚ(j))`, whose inertia generators have order 2. These are derived from
    `W ≅ (ℤ/2)²`, from connectedness, and from at most three branch points.
- **The `p ≥ 17` case analysis** (`GlueRepo.PR.inertia_trivial_iff`) uses `(e₀, e_∞, e_{−16/27})
  = (4, 6, 2)` with `m₀ = 2v_p(F)`, `m_∞ = 6v_p(G)`, `m = 2v_p(H)`.
- **The manuscript** (L421-422) gives the "normalizer quotient … indices 4,6,2". At L480-482 it
  calls each geometric component of `Y₃` "a torsion-free cover of the norm-one orbifold". At
  L514-516 it applies tame normalization `e ↦ e/gcd(e, a)`, which leaves `2, 1, 1`. These are
  the indices of `Y₃ → P¹_j`.

So A5 needs the indices of `Y₃ → P¹_j`, and Lemma NV in addition needs the indices `2, 2, 2` of
`X₆ → P¹_j`.

### 2.2 The indices of `Y₃ → P¹_j` are the orbifold orders (VERIFIED: compiled lemma plus the inputs below)

On each geometric component, `Y₃ → P¹_j` is `Γ₃\ℍ → Γ*\ℍ`, where:

- `Γ* = N_{B⁺}(𝒪)/ℚ^*` is the normalizer group, of index 4 over `𝒪¹/±1`;
- `Γ₃` is the image of `𝒪¹ ∩ K₃`.

The ramification index at the image of `τ` is the order of the stabilizer of `Γ₃τ` in `Γ*/Γ₃`.
That stabilizer is `[S : Γ₃]`, with `S = {g : gτ ∈ Γ₃τ}`. The file
`scratch/rv-nocm/OrbifoldIndex.lean` proves, for any group action:

- `orbitStab_eq_sup`: `S = N ⊔ Stab(x)`, when `N` is normal;
- `relIndex_orbitStab`: `[S : N] = |Stab(x)|` when `N ⊓ Stab(x) = ⊥`;
- `inf_stabilizer_eq_bot`: torsion-free `N` and finite `Stab(x)` give `N ⊓ Stab(x) = ⊥`;
- `ramification_eq_orbifold_order`: the combination of the two.

The inputs, for this cover:

- **`Γ₃` is torsion-free.** `−1 ∉ K₃`, and a finite-order element of `1 + 3𝒪₃` is 1. The
  manuscript proves this at L468-470 via `1 + 3M₄(ℤ₃)`, and glue-repo proves it as
  `TorsionFree.matrix_padic_eq_one`. Elements of `B⁺ ∩ K₃` have reduced norm 1.
  Proved directly in Lean on the repository's `𝒪 ⊂ ℍ[ℚ,2,0,−3]`:
  `RvNocm.Neat.eq_zero_of_pow_eq_one` (`scratch/rv-nocm/Neat.lean`, compiled) says that
  `(1 + 3y)^m = 1` with `y ∈ 𝒪` and `m > 0` forces `y = 0`. The proof goes as follows:
  - `nrd ≡ 1 (mod 3)`, so `nrd = 1`;
  - then `trd = 2 − 9·nrd(y)`;
  - if `nrd(y) ≠ 0`, the Cayley–Hamilton recursion grows, and `x^m = 1` forces `x ∈ ℚ`;
  - otherwise anisotropy of the norm form gives `y = 0`.
- **`Γ₃` is normal in `Γ*`.** `N` normalizes `K₃` (N5 L425-426).
- **The orbifold orders of `Γ*`** are `4, 6, 2` at `j = 0, ∞, −16/27`, and there are no other
  elliptic points:
  - This is the signature `(0; 2, 4, 6)` of `X*(6)`. STANDARD: Baba–Granath §3.1, elliptic-order
    table, p. 740 per the audit (UNVERIFIED here); Elkies 1998 §3.1 (UNVERIFIED here).
  - It is consistent with h-b1 M9's complete list of elliptic elements of the normalizer: the
    types `(2,2)`, `(3,3)` and `(0,6)` have orders 4, 6 and 2 in `PGL₂`.
  - It is consistent with `−χ(Γ¹) = 1/3 = 4·(1/12) = 4·(−χ(Γ*))` (`RvNocm.euler_ratio`).

Consequently the indices are `4, 6, 2` over `0, ∞, −16/27` and `1` elsewhere (the stabilizer is
trivial). The geometric group has order `[Γ*:Γ₃] = 4·36/2 = 72`. Part D checks this:
`|(𝒪/3𝒪)^*| = 72`, and the image of `𝒪¹` is the kernel of `nrd mod 3`, of order 36. Two
components give `144`, which is h-b1 M3's order of `Γ'`. Riemann–Hurwitz then gives genus 4:

- `72·(1/12) = 6 = 2g − 2` (`rh_462`);
- with indices `(2,2,2)` it would give genus `−17` (`rh_222_impossible`).

This agrees with the manuscript's "genus at least two" (L481-482). The stabilizers of the three
points in `W = Γ*/Γ¹` have orders `4/2, 6/3, 2/1 = 2`, using the orders `2, 3, 1` of `Γ¹` at
those points. These are the audit's `(2,2,2)` for `V → V/W`.

### 2.3 Sensitivity (VERIFIED, compiled)

- `inertia_trivial_of_dvd`: the direction A5 needs ("`p ∤ M_S(u)` ⇒ unramified") holds for any
  indices dividing `(4, 6, 2)`. So it would survive even if the indices were smaller. The exact
  values matter only for the converse, i.e. the "iff" of `GlueRepo.PR.inertia_orders_eq_one_iff`.
- `labelling`: among the six permutations of `(4, 6, 2)`, only `(e₀, e_∞, e_{−16/27}) = (4, 6, 2)`
  makes the needed direction hold. So A5 depends on the labelling of the values (disc `−4 ↦ 0`,
  `−3 ↦ ∞`, `−24 ↦ −16/27`). That labelling is the content of `PkgI1.QMHauptmodul`, a composite
  of R2-R4, and of the audit's remark that Baba–Granath Thm 2.1/Lemma 3.1 alone do not fix the
  numerical `j`-normalization.

## 3. Exact repaired texts

### 3.1 For (1)

**h-decomposition R5** (replace the paragraph):

> **R5. González–Rotger.** Let `R` be an order of conductor `f`, `(f, 6) = 1`, in an imaginary
> quadratic field `k` in which neither 2 nor 3 splits. Let `CM(R) ⊂ X₆(ℚ̄)` be the points of
> `X₆ = X₀(6,1)` with CM by `R`, let `D(R)` be the product of the primes `p | 6` inert in `k`,
> and `b(R) = #{p | D(R)}`. Then (i) `#CM(R) = 2^{b(R)} h(R)`, and
> `⟨w_p : p | D(R)⟩ × Gal(H_R/k)` acts simply transitively on `CM(R)`; (ii) for `x ∈ CM(R)`,
> `ℚ(x) = H_R` if `D(R) ≠ 1`, and `[H_R : ℚ(x)] = 2` if `D(R) = 1`. Both parts concern points
> of `X₆` itself, not their images in `X₆/W` or points of `Y₃`. For example, `R = ℤ[√−6]` maps
> to the rational point `j = −16/27` of `X₆/W`, of index 4 in `H_R`. Ref: J. Math. Soc. Japan 58
> (2006), Prop. 5.6, Thm 5.12 (arXiv:math/0612732 numbering VERIFIED by rv-h-cm; journal
> pp. 943, 946 per locators.md). E (restricted to `(f,6) = 1`, `N = 1`). Lean: **no** (via R1).
> Step A10 (NoCM), which uses (i) only when `D(R) = 1`, where it reads `#CM(R) = h(R)`.

**glue-repo §A10, row L14** (and the row L14 of its leaf table): replace "`#CM(R) = h(R)` for
`(f,6) = 1`" by "`#CM(R) = 2^{b(R)} h(R)` for `(f,6) = 1` and neither 2 nor 3 split in `k`,
`b(R) = #{p | 6 inert in k}`; on `X₆ = X₀(6,1)`; used only for `b(R) = 0`".

**`R05_GonzalezRotger` docstring** in `scratch/h-decomposition/Leaves.lean`: replace
"`#CM(R) = h(R)` on `X₆`" by "`#CM(R) = 2^{b(R)} h(R)` on `X₆ = X₀(6,1)`, `b(R)` the number of
primes dividing 6 inert in `k`". Keep the field statement, and add "for points of `X₆`, not of
`X₆/W`".

**hdec-elementary L3(i)**: the same replacement of "`#CM(R) = h(R)`".

**h-trust A10 / rv-h-cm §7.2, case `D(R) ≠ 1`**: after "`R = ℤ[i]`", insert: "`CM(ℤ[i])` has
`2^1·1 = 2` points (GR Prop. 5.6). The two points of `X₆` over `t = 1` are `ℤ[i]`-CM points
(h-b1 M9), so `CM(ℤ[i])` is the fibre over `t = 1`." Then continue with "Then `x` lies over
`t = 1`, i.e. `F(u) = 0`, which is excluded."

### 3.2 For (2)

**h-decomposition R2** (replace the first sentence):

> **R2. Baba–Granath.** `X₆/W ≅ P¹_j` over `ℚ`. The orbifold `Γ*\ℍ` (`Γ* = Γ_W`, the
> normalizer group) has exactly three elliptic points, at `j = 0, ∞, −16/27`, of orders 4, 6, 2,
> the CM points of discriminants −4, −3, −24. Two QM surfaces with principal polarization of
> the fixed type have the same polarized moduli point iff their points of `X₆` are
> `W`-conjugate. Ref: Canad. J. Math. 60 (2008), Thm 2.1, Lemma 3.1, §3.1 elliptic-order table
> (p. 740 per locators.md); the numerical `j`-normalization of the labels needs Prop. 3.6/3.9-
> Cor. 3.11 or R3 (locators.md). The ramification indices are glue, not part of the leaf:
> `X₆ → X₆/W` has index 2 over each of the three values (stabilizers of order 4/2, 6/3, 2/1 in
> `W`). The level-three cover `Y₃ → P¹_j` has indices 4, 6, 2 there and is unramified
> elsewhere, because `Γ₃` is torsion-free and normal in `Γ*`
> (`RvNocm.ramification_eq_orbifold_order`).

**h-b1 §2, M4** (Value column): "`(0,4)`, `(∞,6)`, `(−16/27,2)`: the orbifold orders of `Γ*`
(Baba–Granath §3.1). They are the ramification indices of each geometric component
`Γ₃\ℍ → Γ*\ℍ`, since `Γ₃` is torsion-free (`−1 ∉ K₃`; N5 L468-470) and normal in `Γ*`
(`RvNocm.ramification_eq_orbifold_order`). They are not the indices of `X₆ → P¹_j`, which are
`2, 2, 2` (used in Lemma NV step 4)."

**h-trust A2** (Content): "The normalizer quotient `Γ*\ℍ` of the discriminant-six curve is
`P¹_j`. Its elliptic points are `0, ∞, −16/27`, of orbifold orders `4, 6, 2`, at the CM points of
discriminants `−4, −3, −24`. The degree-4 map `X₆ → P¹_j` has index 2 at each. A5 uses the
orbifold orders as the indices of the torsion-free normal cover `Y₃ → P¹_j`."

**glue-repo leaf table, row L2; `R02_BabaGranath` docstring; pkg-I1 row A2; hdec-faithful,
hdec-alt and hdec-elementary row A2**: replace "branched at / branch values … with indices
4, 6, 2" by "elliptic points … of orbifold orders 4, 6, 2 (indices of `Y₃ → P¹_j`; the map
`X₆ → X₆/W` has indices 2, 2, 2)".

## 4. What compiles, what remains

- **Compiles.** `scratch/rv-nocm/Neat.lean`: `RvNocm.Neat.eq_zero_of_pow_eq_one`, the
  torsion-freeness of `1 + 3𝒪`, which is the hypothesis `htf` of
  `ramification_eq_orbifold_order` for `Γ₃`.
- **Compiles.** `scratch/rv-nocm/OrbifoldIndex.lean` (`lake env lean`, no `sorry`; axioms
  `propext`, `Classical.choice`, `Quot.sound`) contains:
  - `orbitStab`, `orbitStab_eq_sup`, `relIndex_orbitStab`, `inf_stabilizer_eq_bot`,
    `ramification_eq_orbifold_order`;
  - `rh_462`, `rh_222_impossible`, `euler_ratio`, `labelling`, `inertia_trivial_of_dvd`.
- **Computed.** `scratch/rv-nocm/nocm_check.py` and its output, Parts A-D.
  - PARI/cypari2 was not available on this host (`~/pyenv` is absent), and no network install
    was attempted. All checks are pure Python with exact arithmetic.
  - The Part B unramifiedness test is a consistency test on square classes, not a computation
    of ring class fields.
- **Not checked here.**
  - The primary texts of González–Rotger, Baba–Granath and Elkies (no access). Their content
    enters through the audit and through rv-h-cm.
  - The statement that `Γ*` has no elliptic points besides the three. It follows from the
    signature `(0;2,4,6)` (STANDARD, UNVERIFIED locator) and is consistent with the Euler
    characteristic and with h-b1 M9.
  - The instantiation of `ramification_eq_orbifold_order` on the actual `Γ*` acting on `ℍ`. It
    needs R1's objects, so it cannot be stated in Lean today.
  - The repaired texts of §3 are not applied to other tasks' files (rule of this task).
