# Route B1: the integral model of the Shimura curve replaced by tame specialization (audit record)

Status: research note (task h-b1, 2026-11-11). This is task T1 of `docs/research/h-map.md`
(branch `wip/h-map`), §3.2, route B1. It proves Lemma PR of h-map from published theorems and
records the exact replacement for every place where the frozen 11/5 manuscript
(`diophantine_zq.tex`, "N5 L…") uses the integral model built in the unpublished supplement
`b11-integral-model`. Scripts and outputs are in `scratch/h-b1/`, with the work log in
`scratch/h-b1/log.md`.
Repaired (task h-b1-fix, 2026-11-11) per `docs/research/rv-h-b1.md` §8; see the changelog at the
end.

Marks:

- **VERIFIED**: checked against the manuscript or the repository, or by an exact computation in
  `scratch/h-b1/b1_checks.py`, whose output is saved beside it.
- **STANDARD**: a published theorem, with a reference. No source outside the repository could be
  read in this task. Every locator (theorem number, page) is therefore **UNVERIFIED** unless
  stated otherwise, and the place to check it is named.
- **PROVED HERE**: a short argument written in this note from STANDARD inputs. It has not been
  reviewed by anyone else.
- **SPECULATIVE**: an assessment.

## Summary

1. **Beckmann alone does not remove b11 (VERIFIED).** h-map's sketch assumed that a tame cover
   whose branch points stay distinct mod `p` has no vertical ramification at `p`. That is false
   in general. `y² = p·j(27j+16)` has group `ℤ/2`, its branch points `0` and `−16/27` stay
   distinct mod every `p ≥ 5`, and its fibre at `j = 1` is `ℚ(√(43p))`, which is ramified at `p`
   (checked for five primes `p > 324`, section D of the script). Beckmann's theorem lists "no
   vertical ramification" as a separate hypothesis. It holds only outside an unspecified finite
   set of primes. So route B1 needs one more input. F1 shows a little more (VERIFIED,
   `scratch/rv-h-b1/rv_checks.py` R5): its residue fields over the branch points are `ℚ`,
   unramified at `p`, and still `p` is vertically ramified, with `I₀ = I_{−16/27} = ℤ/2`. So
   unramified branch fibres (step 2 of Lemma NV) do not exclude vertical ramification by
   themselves, and the `W`-step of NV (step 4) is essential.
2. **That input is supplied here (Lemma NV, PROVED HERE).** For the cover `Y₃ → P¹_j`, vertical
   ramification at `p ≥ 5` is ruled out as follows. The fibres over the branch points are CM
   points. Shimura reciprocity makes them unramified at `p`. Abhyankar's lemma then forces the
   vertical inertia into the inertia groups at `∞` and at `−16/27`. The images of these in the
   Atkin–Lehner group `W ≅ (ℤ/2)²` differ, so the vertical inertia is trivial. No integral model
   of `Y₃` is used.
3. **Lemma PR is proved (§4).**
   - (i) For `p ∉ S`, `K` is unramified at `p` unless some `v_p(u−c)` is positive and odd. In
     fact this holds for every `p ≥ 17`.
   - (ii) `A` has good reduction at every place `v ∤ 3` of `K`.

   The inputs are:
   - Zariski–Nagata purity and Abhyankar's lemma (SGA 1);
   - Shimura reciprocity for the canonical model (Deligne);
   - the moduli interpretation of `Y₃` over `ℚ`;
   - Grothendieck's semistable reduction (SGA 7), which reproves Morita's potentially good
     reduction;
   - Serre–Tate.

   The specialization step is the special case of Beckmann's theorem (Prop. TS) that we need,
   and §1.2 proves it directly from SGA 1. Beckmann is therefore cited only for attribution.
4. **Replacements (§5).** Every use of the integral model in N5 L441-530, L557-558, L752-753,
   L781 and L847-850 has an exact replacement. L814 (at `v | 3`) uses only Raynaud's criterion, so it
   never needed b11.
5. **Verdict.** B1 removes `b11`, Buzzard 1997 (A002) and the stable-model and tame-quotient
   scheme theory (A078) from H's justification. In their place come published theorems plus one
   short new argument, Lemma NV, which needs one independent review. Rating: **high** that the
   argument is correct as written (SPECULATIVE). Overall rating of the route after this audit:
   **medium-high → high**, conditional on that review and on checking the locators listed in §6.

## 1. Beckmann's specialization theorem

### 1.1 Statement (from memory; text not read; UNVERIFIED)

S. Beckmann, *On extensions of number fields obtained by specializing branched coverings*,
J. reine angew. Math. 419 (1991), pp. 27–53 (page range UNVERIFIED). The main statement is
Proposition 4.2 there (number UNVERIFIED). Legrand restates it as the "Specialization Inertia
Theorem", for example in P. Legrand, *Specialization results and ramification conditions*, Israel
J. Math. (2016), §2. Dèbes and Legrand also restate it, in *Specialization results in Galois
theory*, Trans. AMS (2013). Both restatements are UNVERIFIED.

> Let `k` be a number field and `f: X → P¹_k` a Galois cover with group `G` defined over `k`
> (its function field is Galois over `k(T)`; Beckmann allows `X` not geometrically irreducible),
> with branch points `t₁,…,t_r` and ramification indices `e₁,…,e_r`. Let `g_i` be a generator of
> an inertia group at `t_i`. Let `𝔭` be a prime of `k` such that
> (a) `𝔭 ∤ |G|`;
> (b) no two branch points meet modulo `𝔭`;
> (c) `𝔭` is unramified in `k(t₁,…,t_r)/k`;
> (d) `𝔭` is not vertically ramified in `k(X)/k(T)`.
> Let `t₀ ∈ P¹(k)` not be a branch point. Then `𝔭` ramifies in the specialization `k(X)_{t₀}`
> only if `t₀` meets some `t_i` modulo `𝔭`. In that case the inertia group at `𝔭` is
> conjugate to `⟨g_i^{I_𝔭(t₀,t_i)}⟩`, where `I_𝔭` is the intersection multiplicity.

Beckmann also shows that only finitely many primes fail (a)-(d). Hypothesis (d) is genuinely
separate (VERIFIED by the counterexample in the Summary, item 1). What h-map attributed to
Beckmann, "no vertical ramification when `p ∤ |G|` and the branch locus is étale mod `p`", is
true only up to a twist. Grothendieck's tame specialization (SGA 1 Exp. XIII) gives good
reduction of the *geometric* cover over `𝒪_𝔭^{sh}`. The `k`-model can still differ from a model
with good reduction by a ramified twist. *To check:* the numbering and the exact form of (d) in
Beckmann §4-5, and Legrand's restatement.

### 1.2 The case used here, proved from SGA 1 (Prop. TS; PROVED HERE from STANDARD inputs)

Inputs:

- (P) Zariski–Nagata purity: a finite morphism from a normal scheme onto a regular scheme,
  étale in codimension one, is étale (SGA 1, Exp. X, Thm 3.1; UNVERIFIED locator).
- (Ab) Abhyankar's lemma: let `X` be regular, `D` a divisor with normal crossings, and `V` a
  normal finite cover of `X`, étale over `X − D` and tamely ramified along `D`. Then, étale
  locally at a point `x`, `V` is a disjoint union of quotients of Kummer covers
  `X[t₁^{1/n₁},…,t_s^{1/n_s}]`, where the `t_i` are local equations of the branches of `D`
  through `x` and the `n_i` are prime to the residue characteristic. Consequently the inertia
  group at a point of `V` over `x` is abelian and generated by the inertia groups of the
  height-one primes of `V` through it, over the branches of `D` (SGA 1, Exp. XIII, 5.3;
  Grothendieck–Murre, LNM 208; UNVERIFIED locators).

Set-up. Let `R` be the strict henselization of `ℤ_(p)`, `k_p = Frac R`, and let `M/ℚ(j)` be a
finite Galois extension with group `Γ_M`. Assume:

- `p ∤ |Γ_M|`;
- the branch points `b_i ∈ P¹(ℚ)` are pairwise distinct mod `p`;
- `Z`, the normalization of `P¹_R` in a factor field `M'` of `M ⊗ k_p`, is unramified over the
  generic point of the special fibre `V(p)`.

Write `D = ∪ D_i` for the closures of the `b_i`. Then:

- `Z → P¹_R` is finite: `R = ℤ_(p)^{sh}` is excellent (a henselization of an excellent ring
  is excellent; EGA IV 7.8.3 and 18.7.6, UNVERIFIED locators), so `P¹_R` is excellent and
  normalization in a finite extension of the function field is finite.
- `Z → P¹_R` is flat: `Z` is normal of dimension 2, hence Cohen–Macaulay (Serre's `S₂`), and a
  finite morphism from a Cohen–Macaulay scheme to a regular scheme of the same dimension is
  flat (miracle flatness, EGA IV 6.1.5 / Matsumura, *Commutative Ring Theory*, Thm 23.1;
  UNVERIFIED locators). So "unramified at a codimension-one point" upgrades to "étale" there.
- `Z → P¹_R` is étale outside `D` (by (P)). The only codimension-one points of `P¹_R` are the
  generic points of horizontal divisors, where the cover is étale off `D`, and the generic point
  of `V(p)`.
- `D ∪ V(p)` has normal crossings, because the `D_i` are sections that are disjoint mod `p`.
- The ramification is tame along `D` (residue characteristic 0) and along `V(p)` (degree prime
  to `p`, so the residue extension is separable).

Prop. TS. Let `j₀ ∈ P¹(ℚ)` not be a branch point, and `K_{j₀}` the residue field of `M` at a
place over `j₀`.

- If `j₀ mod p` is not any `b_i mod p`, then `K_{j₀}` is unramified at `p`.
- If `j₀ ≡ b_i mod p`, let `m = v_p(j₀ − b_i)`, using the coordinate `1/j` when `b_i = ∞`.
  Then the inertia group of `K_{j₀}` at `p` is conjugate to `⟨g_i^m⟩` and has order
  `e_i / gcd(e_i, m)`.

Proof.

- In the first case, the section `j₀: Spec R → P¹_R` stays inside the étale locus.
- In the second case, at `P_i = (b_i mod p)` the only branch of the branch locus is
  `D_i: z = 0`, with `z = j − b_i`. By (Ab), `Z` is étale locally a disjoint union of copies of
  `R_{P_i}^{sh}[z^{1/e_i}]`. Pulling back along `j₀` gives `R[(p^m w)^{1/e_i}]` with `w` a unit.
  The local generator then acts through its `m`-th power. ∎

This is Beckmann's conclusion in our case. Her hypothesis (c) holds because `b_i ∈ ℚ`, and (d)
is the assumption on `Z`.

## 2. Matching the hypotheses to `Y₃ → P¹_j`

Notation as in N5 L405-438:

- `B = (2,−3)` and `𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩`;
- `K₀ = 𝒪̂^*` and `K₃ = ker(K₀ → (𝒪/3𝒪)^*)`;
- `N` is the finite-adelic normalizer of `𝒪̂`;
- `Γ' = N/(𝔸_f^* K₃)`;
- `Y₃ = Sh_{K₃}` is the canonical model over `ℚ`;
- `X₆ = Sh_{K₀}`, `W = N/(𝔸_f^* K₀)`, and `X₆/W = X₆^* = P¹_j` in the Baba–Granath
  coordinate.

| # | Hypothesis / fact | Value for `Y₃ → P¹_j` | Mark |
| --- | --- | --- | --- |
| M1 | cover over a number field, with group action defined over it | `Γ'` acts on `Y₃` over `ℚ` (right translation by elements of `G(𝔸_f)` normalizing `K₃`, Hecke action on the canonical model), with quotient `P¹_j` (N5 L428-438) | STANDARD (Deligne 1979, §2.7 and §5 (UNVERIFIED locators); Milne, *Introduction to Shimura varieties*, §13) |
| M2 | Galois extension and its group | Let `Y^{(1)}` be a `ℚ`-irreducible component, `Γ₁` its stabilizer in `Γ'` and `κ₁` the kernel of `Γ₁` on it. Then `M := ℚ(Y^{(1)})` is Galois over `ℚ(j)` with group `Γ₁/κ₁` (Artin's theorem, since `Y^{(1)}/Γ₁ = P¹_j`). The points of `Y₃` over any `j₀` all have the residue field of `M` there, because `Γ'` is defined over `ℚ` | PROVED HERE |
| M3 | order of the group | `Γ'` has order `4·72/2 = 144 = 2⁴3²`: `(𝒪/3𝒪)^*` has 72 elements, the image of `ℤ̂^*` is `{±1}`, and the local normalizer index is 2 at each of the two division primes. So the order of `Γ₁/κ₁` divides 144, and `p` does not divide the order of `Γ_M` for any `p ≥ 5`. This refines h-map's "divides 4·72" and N5's `≤ 324` | VERIFIED (script §B) for 72 and `{±1}`; STANDARD for the local index (Vignéras, LNM 800, Ch. II) |
| M4 | branch points and indices | `(0,4)`, `(∞,6)`, `(−16/27,2)` | STANDARD (Baba–Granath, Canad. J. Math. 2008; Lin–Yang 2020; cited at N5 L418-419) |
| M5 | branch locus étale mod `p` | the pairwise differences of `0, ∞, −16/27` are supported on `{2,3}`, so the branch points are distinct mod every `p ≥ 5`, and they are rational, so Beckmann's (c) holds | VERIFIED (§A) |
| M6 | no vertical ramification at `p ≥ 5` | Lemma NV (§3) | PROVED HERE |
| M7 | the specialization point | `j₀ = J(u) = −57600F²/G⁶` is never a branch value for `u ∈ ℚ∖𝒞`: `F(u) ≠ 0`, `G` has no real root, and `H` has no rational root, since the discriminants of its three quadratic factors (10800, 43200, 43200) are not squares | VERIFIED (§A) |
| M8 | the fibre field | `Y₃` is étale over `j₀`, so the normalized pullback to `P¹_u` (N5 L509-523) is étale over `u`, and its fibre over `u` is the fibre of `Y₃` over `j₀`. Hence N5's `K` is the residue field `K_{j₀}` of `M` (M2), and it is Galois over `ℚ` | PROVED HERE |
| M9 | the fibres over the branch points (indeed over every elliptic point) are CM points whose CM order has conductor prime to every `p ≥ 5` | Complete enumeration of the elliptic elements of the normalizer (primitive `x ∈ 𝒪`, `nrd x ∣ 6`, finite order mod `ℚ^*`), by `(\|trd\|, nrd)`: `(0,1)` → `ℤ[i]`, image 1; `(1,1)` → `ℤ[ζ₃]`, image 1; `(2,2)` → `ℤ[i]`, image `w₂`; `(3,3)` → `ℤ[ζ₃]`, image `w₃`; `(0,3)` → `ℤ[ζ₃]` (not `ℤ[√−3]`), image `w₃`; `(0,6)` → `ℤ[√−6]`, image `w₆`. Type `(0,2)` is absent: `ℚ(√−2)` does not embed in `B` since 3 splits in it. So `ℚ(x) ∩ 𝒪` is always the maximal order of discriminant `−4`, `−3` or `−24` (conductor 1) | VERIFIED (§C here; complete list: `scratch/rv-h-b1/rv_checks.py` R2) |
| M10 | `X₆` is geometrically connected and `X₆ → P¹_j` is `W`-Galois | `nrd(K₀) = ℤ̂^*`, so `π₀ = ℚ^*_{>0}∖𝔸_f^*/ℤ̂^* = 1`, and `W`, of order 4, acts faithfully | STANDARD (Deligne 1971 §2 for `π₀` (UNVERIFIED locator); Baba–Granath for `X₆^* = X₆/W`) |

Remark on M2. N5's Galois closure "splitting field of the fibre" is the residue field of a Galois
extension at an unramified place. That is all that Prop. TS needs. We do not need `Γ'` to act
faithfully or freely.

## 3. Lemma NV: no vertical ramification (PROVED HERE)

**Lemma NV.** Let `p ≥ 5`. The normalization `Z` of `P¹_R` in `M'` (§1.2) is unramified over
the generic point of `V(p)`.

*Proof.*

1. *Tameness.* `|Γ_M|` divides 144 (M3), so `p ∤ |Γ_M|`. The set-up of §1.2 applies, except for
   the conclusion we are proving. Let `I_V` be the inertia group of a prime of `Z` over the
   generic point of `V(p)`. These primes are permuted transitively, so `I_V` is defined up to
   conjugacy. It is cyclic of order prime to `p`.
2. *The fibres over the branch points are unramified at `p`.*
   - Let `y ∈ Y₃` lie over `b_i`. The fibre is a `Γ'`-orbit and `Γ'` is defined over `ℚ`, so
     `ℚ(y) = ℚ(y₀)` for `y₀ = [τ_i, 1]`, where `τ_i` is fixed by an elliptic element of
     `N ∩ B^*_+`. Here we use `G(𝔸_f) = B^*_+ K₀`: class number one and surjectivity of `nrd`,
     STANDARD (Vignéras III.5, UNVERIFIED locator).
   - `τ_i` is a CM point, with CM field `E_i = ℚ(i)`, `ℚ(√−3)` or `ℚ(√−6)` for
     `b_i = 0, ∞, −16/27`.
   - What is needed is only: *the CM order `E_i ∩ 𝒪` has conductor prime to `p`.* Then
     `𝒪_{E_i} ⊗ ℤ_ℓ ⊂ 𝒪_ℓ` for every `ℓ` prime to the conductor, so
     `∏_{ℓ ∤ 3f} 𝒪_{E_i,ℓ}^* ⊂ K₃` with `f` the conductor, and the argument below gives
     `E_i(y₀)/E_i` unramified outside `3f`.
   - By the complete enumeration of M9, every elliptic element `x` of the normalizer has
     `ℚ(x) ∩ 𝒪` maximal, of discriminant `−4` (types `(0,1)`, `(2,2)`, `W`-images 1, `w₂`),
     `−3` (types `(1,1)`, `(3,3)`, `(0,3)`, `W`-images 1, `w₃, w₃`) or `−24` (type `(0,6)`,
     `W`-image `w₆`). So `f = 1` for every elliptic point, and this holds whatever the
     labelling of the branch values `0, ∞, −16/27` (Baba–Granath's labelling is not used).
   - Hence `𝒪_{E_i} ⊗ ℤ_ℓ ⊂ 𝒪_ℓ` for every `ℓ`, so `∏_{ℓ≠3} 𝒪_{E_i,ℓ}^* ⊂ K₃`.
   - By Shimura reciprocity on the canonical model, `σ_s[τ_i, 1] = [τ_i, r(s)]` for
     `s ∈ 𝔸_{E_i}^*`, where `r` is the identity or conjugation, depending on the convention.
     (STANDARD: Deligne 1971 (Bourbaki 389) §3; Milne, *Introduction to Shimura varieties*,
     §12-13; locators UNVERIFIED.)
   - So `y₀` is fixed by the Artin images of `E_i^* E_{i,∞}^* ∏_{ℓ∤3} 𝒪_{E_i,ℓ}^*`. Therefore
     `E_i(y₀)/E_i` is unramified outside 3, and since `E_i/ℚ` is ramified only at 2 and 3,
     `ℚ(y₀)` is unramified at every `p ≥ 5`.
3. *Local analysis at `P_i = (b_i mod p)`.*
   - Let `𝔓 ∈ Z` lie over `P_i`, and let `Q_i` be a height-one prime over `D_i` through `𝔓`. Its
     residue field `k(Q_i)` is `ℚ(y)k_p` for some `y` over `b_i` (M2), so `k(Q_i) = k_p` by
     step 2.
   - The closure of `Q_i` in `Z` is `Spec A'`, where `A'` is local (it lies over the strictly
     henselian `D_i ≅ Spec R`) and finite over `R`, with fraction field `k(Q_i) = k_p`. A local
     domain finite over the strictly henselian `R` with fraction field `Frac R` is strictly
     henselian and unibranch, and its branch at `𝔓` has residue degree 1 over `k_p`.
   - By (Ab), étale locally at `𝔓`, `Z` is a quotient `(R^{sh}_{P_i}[z^{1/n}, p^{1/n}])^H`
     of a Kummer cover. In this model there is a unique branch over `z = 0` through `𝔓`, the
     inertia `I_{Q_i}` is the image of `μ_n × 1`, and the residue degree of the branch of the
     closure of `Q_i` over `k_p` equals `[I_𝔓 : I_{Q_i}]` (its fraction field is
     `k_p(p^{1/c})`, `c = [I_𝔓 : I_{Q_i}]`). By the previous bullet this degree is 1, so
     `I_𝔓 = I_{Q_i}`, which is cyclic of order `e_i` (M4).
   - Existence of the primes: `Z → P¹_R` is flat (§1.2), so going-down holds; hence `𝔓`
     contains a height-one prime `Q_i` over `D_i` and a height-one vertical prime `q` over
     `V(p)`. Inclusion of inertia: if `σ ≡ id mod q` then `σ ≡ id mod 𝔓` (as `q ⊂ 𝔓`), so
     `I_q ⊂ I_𝔓`. The group `I_q` is a conjugate of `I_V`. Hence a conjugate of `I_V` lies in
     `I_{Q_i}`.
4. *Conclusion.*
   - Steps 3 at `b = ∞` (`e = 6`) and at `b = −16/27` (`e = 2`) give `|I_V| ∣ 2`.
   - Suppose `|I_V| = 2`. Then a conjugate of `I_V` is the subgroup of order 2 of a conjugate of
     `I_{Q_∞}`. Its image in `W = Gal(ℚ(X₆)/ℚ(j))` is `⟨σ_∞^3⟩ = ⟨σ_∞⟩`, where `σ_b` generates
     the inertia of `X₆ → P¹_j` at `b`. Likewise, from `−16/27`, the image is `⟨σ_{−16/27}⟩`.
     (`M ⊇ ℚ(X₆)`, because `Y^{(1)} → X₆` is dominant. Images of inertia groups are inertia
     groups.)
   - `W` is abelian, so conjugate subgroups have the same image. Hence
     `⟨σ_∞⟩ = ⟨σ_{−16/27}⟩`.
   - But `X₆ → P¹_j` is a connected `(ℤ/2)²`-cover branched at most at three points (M10). Its
     inertia generators satisfy `σ₀σ_∞σ_{−16/27} = 1` and generate `W`. So all three are
     nontrivial and pairwise distinct. (This matches M9: `w₂, w₃, w₆`.) Contradiction.
   - So `I_V = 1`. ∎

Remark. The argument uses only two branch points and the abelian quotient `W`. It does not need
the exact group `Γ_M`, only `p ∤ |Γ_M|`. It does not depend on the Baba–Granath labelling of
the branch values either: any pair of branch points gives the contradiction (at the order-4 point
`g₀² ↦ 1`, so pairing it with either other point also works).

Independent support on the `W`-layer (VERIFIED, `scratch/rv-h-b1/rv_checks.py` R7). Elkies'
model `ℚ(X₆) = ℚ(j)(√j, √(−(27j+16)))` (checked in `docs/research/rv-h-cm.md` §2) has constants
`−1` and `3`, so `X₆ → P¹_j` has no vertical ramification at any `p ≥ 5`: NV's conclusion on the
`W`-quotient, from Elkies' computation rather than from NV. On 30 samples `(j₀, p)`,
`5 ≤ p < 400`, ramification of `p` in the biquadratic fibre agrees with Prop. TS in every case.

## 4. Lemma PR

**Lemma PR.** Let `S ⊇ {p ≤ 324}`, let `u ∈ ℚ∖𝒞`, and let `K` be the splitting field of the
fibre over `u` (N5 L524). Let `A/K` be the abelian surface of a point `x ∈ Y₃(K)` over `J(u)`.
Then:

- (i) for `p ∉ S`, `K` is unramified at `p` unless some `v_p(u−c)`, `c ∈ 𝒞`, is positive and
  odd;
- (ii) `A` has good reduction at every finite place `v ∤ 3` of `K`.

*Proof of (i).* Let `p ≥ 17`. This covers every `p ∉ S`.

1. By M8, `K = K_{j₀}` with `j₀ = J(u)`. By Lemma NV and M3, M5, Prop. TS applies at `p`.
2. Suppose `v_p(u) ≥ 0`.
   - The resultants of `F, G, H` and the discriminants are supported on `{2,3,5}`, and the
     leading coefficients of `G` and `H` on `{7}` and `{11,13}` (VERIFIED, §A). So at most one
     of `F(u), G(u), H(u)` is divisible by `p`, and at most one contact `c` has `v_p(u−c) > 0`.
     The contact differences are supported on `{2,3,5}`.
   - If `v_p(F(u)) = v_p(u−c) = v > 0`, then `j₀` meets `0` with multiplicity `2v`. The inertia
     has order `4/gcd(4,2v)`, which is 1 exactly when `v` is even.
   - If `v_p(G(u)) = w > 0`, then `j₀` meets `∞` with multiplicity `6w`, and the inertia is
     trivial.
   - If `v_p(H(u)) = w > 0`, then `j₀ + 16/27 = 16H²/(27G⁶)` (VERIFIED) meets `−16/27` with
     multiplicity `2w`, and the inertia is trivial (`e = 2`).
   - Otherwise `j₀` is a `p`-unit with `j₀ ≢ −16/27`, so it meets nothing, and `K` is
     unramified at `p`.
3. Suppose `v_p(u) < 0`. `F²` and `G⁶` have degree 12 and leading coefficients 1 and `7⁶`, so
   `j₀ ≡ J(∞) = −57600/7⁶ (mod p)`. Both `J(∞)` and `J(∞) + 16/27 = 2⁴11²13²/(3³7⁶)` are
   `p`-units (VERIFIED), so `j₀` meets nothing.
4. A sample check of 30 cases agrees with this case analysis in every case (VERIFIED, §E):
   contact, `G`-root, `H`-root, negative valuation and generic `u`, at primes 331-5000. ∎

*Proof of (ii).*

1. **Moduli interpretation (STANDARD).** `Y₃` is the fine moduli scheme over `ℚ` of quadruples
   `(A, ι: 𝒪 → End A, λ, η)`. Here `λ` is a principal polarization of the type fixed by `μ`
   (N5 L407-418), and `η: 𝒪/3𝒪 ≅ A[3]` is an `𝒪`-linear isomorphism.
   - The level `K₃` is neat (`1 + 3M₄(ℤ₃)` is torsion-free, N5 L468-470).
   - References: Shimura, Ann. of Math. 85 (1967); Deligne 1971 §4 (moduli for PEL type and
     the canonical model); Milne, *Introduction*, §8 and §14; Kottwitz, JAMS 5 (1992) §5.
     Locators UNVERIFIED.
   - N5 needs this already over `ℚ` ("choose a fibre `A/K`", L528). Only its integral extension
     came from b11.
   - The four inputs behind this identification (canonical model = moduli, uniqueness of the
     `μ`-principal polarization, Weil-pairing compatibility, level-3 rigidity), and the fact
     that NV, PR(ii) and Baba–Granath's `j` use one `ℚ`-structure, are listed in §4A.
   - So `x ∈ Y₃(K)` gives `ι` defined over `K` and `η` defined over `K`, that is,
     `A[3] ⊂ A(K)`.
2. **Potentially good reduction (Morita, PROVED HERE from STANDARD inputs).**
   - By Grothendieck (SGA 7, Exp. IX, Thm 3.6), `A` has semistable reduction over a finite
     extension `K'`.
   - The connected special fibre of the Néron model is an extension of an abelian variety by a
     torus `T` of dimension `t ≤ 2`.
   - By the Néron mapping property, `End A` acts on the Néron model, hence on the character
     group `X(T)` (functoriality of the toric part, SGA 7 IX §2; UNVERIFIED locator).
   - This gives a unital map `B = 𝒪⊗ℚ → End(X(T)⊗ℚ) = M_t(ℚ)`. Then `ℚ^t` is a module over
     the division algebra `B`, of dimension 4, so `4 ∣ t`, and `t = 0`.
   - (Morita, Hokkaido Math. J. 10 (1981), proves the same; locator UNVERIFIED.)
3. **Good reduction at `v ∤ 3`.**
   - Let `ρ: G_{K_v} → GL(T₃A) ≅ GL₄(ℤ₃)`, with `3` different from the residue characteristic.
   - Potentially good reduction means `ρ(I_v)` is finite (Serre–Tate, Ann. of Math. 88 (1968),
     Thm 2).
   - `A[3]` is rational, so `ρ(I_v) ⊂ 1 + 3M₄(ℤ₃)`, which is torsion-free (N5 L468-470; also
     Serre–Tate §4). So `ρ(I_v) = 1`.
   - By Néron–Ogg–Shafarevich (Serre–Tate, Thm 1), `A` has good reduction at `v`. ∎

At `v | 3` the same argument with `ℓ = 5` gives good reduction over `K_v(A[5])`. This is not
needed: see L814 below.

## 4A. The one `ℚ`-structure on `Y₃ = Sh_{K₃}`

Three parts of the argument use a rational structure on `Y₃`, and they must use the same one:

- **Lemma NV** (step 2, and M1) uses the *canonical model* `Sh_{K₃}(B^*, H^±)` over `ℚ`: Shimura
  reciprocity at CM points and the Hecke action of `Γ'` over `ℚ`.
- **Lemma PR(ii)** (step 1) uses the *moduli problem*: a `K`-point gives `(A, ι, λ, η)` over
  `K`, so `A[3] ⊂ A(K)`.
- **N5** uses *Baba–Granath's `j`* on `X₆/W = P¹_j` (L418-419), whose `ℚ`-structure comes from
  their work on the QM moduli, and defines `Y₃` only as "the level-three curve with all its
  determinant components" (L434-435). Its only identification of `Y₃` with the full-three moduli
  problem is b11's sentence at L476-477, which B1 deletes.

So the identification must be cited directly. It follows from four STANDARD inputs. None could
be read in this task; each is **UNVERIFIED**, with the place to check it.

1. **Canonical model = moduli scheme.** The moduli scheme over `ℚ` of QM abelian
   surfaces `(A, ι, λ, η)` with `K`-level structure is the canonical model `Sh_K(B^*, H^±)`, and
   there are no extra copies since `ker¹(ℚ, B^*) = 1` (Hasse principle for `B^*`).
   - Shimura, *Construction of class fields and zeta functions of algebraic curves*, Ann. of
     Math. 85 (1967), 58–159: the QM moduli give the canonical model (check the sections on
     "models over `ℚ`" of curves attached to quaternion algebras, §§2-3 and the main theorem).
   - Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §4–6: PEL moduli and the canonical
     model; check §4.13–4.21 and §6.
   - Milne, *Introduction to Shimura varieties*, §8 (PEL Shimura varieties as moduli) and §14
     (canonical models of PEL type); Kottwitz, JAMS 5 (1992), §5 and §8 (the `ker¹` count).
2. **The polarization adds no data.** For the maximal order `𝒪` and `μ² = −6`, a QM surface
   `(A, ι)` carries a unique principal polarization whose Rosati involution is `x ↦ μ^{-1} x̄ μ`.
   - Rotger, *Quaternions, polarizations and class numbers*, J. reine angew. Math. 561 (2003),
     and *Modular Shimura varieties and forgetful maps*, Trans. AMS 356 (2004): check the
     statement counting principal polarizations of a given Rosati type on a QM surface with
     maximal order (expected: exactly one for discriminant 6 and this `μ`). Also Milne, *Introduction*, §8 (uniqueness up to the
     similitude).
   - VERIFIED (`scratch/rv-h-b1/rv_checks.py` R1): N5's form `Trd(μ^{-1} x ȳ)` has the matrix
     printed at N5 L414-416 and determinant 1, so it is the principal polarization of that type.
3. **The level structure is the `K₃`-structure, compatibly with the Weil pairing.**
   - A `K₃`-structure is an `𝒪`-linear `η: 𝒪/3𝒪 ≅ A[3]`. This uses that `T_ℓA` is free of rank
     one over `𝒪_ℓ`: at `ℓ = 3` by N5 L454-459, at `ℓ ∤ 6` because `𝒪_ℓ = M₂(ℤ_ℓ)` (Morita
     equivalence; check Milne §8 or Deligne §4 on lattices).
   - Compatibility of `η` with the Weil pairing up to a scalar is automatic: the `λ`-Weil pairing
     is `ψ(x, y) = Trd(μ^{-1} x ȳ)` up to a unit, and `ψ(xu, yu) = nrd(u)·ψ(x, y)`. So the PEL
     similitude condition imposes nothing beyond `𝒪`-linearity (check Milne §8, the PEL datum
     with `G = B^*`, `ν = nrd`).
4. **Representability (level-3 rigidity).** `K₃` is neat: an automorphism of a polarized abelian
   variety acting trivially on `A[n]`, `n ≥ 3`, is the identity (Serre's lemma; Mumford, *Abelian
   varieties*, §21, Thm 5, or Milne, *Abelian varieties*, Prop. 17.5; also N5 L466-470,
   `1 + 3M₄(ℤ₃)` torsion-free; neatness VERIFIED in `rv_checks.py` R6). So the moduli problem is
   fine, a `K`-point gives `(A, ι, λ, η)` over `K`, and the fibre of the universal family over
   `x` is N5's "fibre `A/K`" (L528).

**Consequence.** By 1-4 the moduli scheme, the canonical model and N5's `Y₃ = Sh_{K₃}` are one
`ℚ`-scheme with one `Γ'`-action (the Hecke action of Deligne is the action by change of level
structure, `η ↦ η∘g`). Baba–Granath's `j` is a coordinate on the quotient of this same
`ℚ`-scheme by `N` (they compute on the QM moduli, i.e. on input 1's canonical model at level
`K₀`; check Baba–Granath, Canad. J. Math. 60 (2008), §2-3 for the model over `ℚ` they use). So
NV, PR(ii) and N5 use one and the same `ℚ`-structure. This is a citation task, not a gap
(SPECULATIVE); it is the main remaining risk of B1 (rv-h-b1, "most serious issue").

## 5. Exact replacements in the manuscript

| N5 lines | What b11 / the integral model supplied there | Replacement |
| --- | --- | --- |
| L441-478 | smooth projective `X₃₅` over `ℤ[1/30]` via Buzzard's `V₁(5)`; free quotient by `G₅`; descent of the universal abelian scheme | Delete. Use only the generic fibre: §4(ii) step 1 (STANDARD moduli interpretation of `Y₃` over `ℚ`) |
| L480-482 | the components have genus `≥ 2` (for stable models) | Delete (not used elsewhere) |
| L482-507 | normalizer action on the stable model; tame quotient; three disjoint branch sections; integral `P¹_{ℤ_p}` in the coordinate `j` | M1-M5 plus Lemma NV (§3) and Prop. TS (§1.2) |
| L509-523 | pullback by `J`, tame normalization, local form `u − c = z²` | M7, M8 and §4(i) steps 2-3. The normalized cover of `P¹_u` is not needed, because its fibre over `u` equals the fibre of `Y₃` over `J(u)` |
| L524-528 | `K` normal, `[K:ℚ] ≤ 324!`, unramified outside `T = S ∪ supp M_S(u)` | Degree: unchanged (generic fibre, L436-438; in fact `[K:ℚ]` is at most the order of `Γ_M`, which divides 144 (M2-M3)). Unramified outside `T`: Lemma PR(i) |
| L529-530 | "the proper model and its universal abelian scheme give good reduction outside the places over `S`" | Lemma PR(ii) |
| L557-558 | every conjugate has good reduction at primes outside `T` | the conjugates are `σA = A_{σx}` with `σx ∈ Y₃(K)` (`K` is Galois), so Lemma PR(ii) applies (`3 ∈ T`) |
| L752-753 | `r_ℓ` unramified outside `T ∪ {ℓ}`, since there `A` has good reduction | Lemma PR(ii) at places over primes `∉ T ∋ 3` |
| L778-781 | for `p ∉ T ∪ {3,5}`, `A` has good reduction at `v` (Frobenius comparison of `Ā_v` with the reduction of `^σA`) | Lemma PR(ii), since `v ∤ 3` |
| L847-850 | `p > R`: the surface has good reduction | Lemma PR(ii), since `p > R ≥ 10¹² > 3` |
| L814 | `p = 3`: adjoin `A[5]` | no change. Semistability over `L_v(A[5])` comes from Raynaud's criterion (Silverberg–Zarhin Thm 3.5), not from b11. h-map's "L814 for `v` over 3" needs no replacement |

The numerals `F₀ = 324!`, `D`, `E₀` and `H₆` are unchanged. Nothing downstream of L530 uses the
integral model itself (VERIFIED by reading L530-972; `grep` for "integral model / proper model" in
N5 finds only L443, L529 and the unrelated L2963). Downstream lines use only its *conclusion*,
good reduction of `A` (and its conjugates) at places outside `T ∋ 3`: these are exactly L557-558,
L752-753, L781 and L848-849, each covered by Lemma PR(ii) in the table above (VERIFIED by
rv-h-b1's grep of N5 L1-1200 for "good reduction", "stable model", "semistable", "potentially
good" and related phrases, and re-read in this repair). At L848-849 the prime `p > R` may lie
in `supp M_S(u) ⊂ T`, where `K` can ramify; PR(ii) still applies, since it covers every `v ∤ 3`.
L814 never used b11 (confirmed by rv-h-b1 §6 and re-read here): it adjoins `A[3]` (`A[5]` at
`p = 3`) and invokes Raynaud's criterion; no model enters.

## 6. What remains unpublished or unchecked after B1

1. **Lemma NV, Prop. TS and the M2/M8 bookkeeping are PROVED HERE and unreviewed.** They need
   one independent review. Its focus should be §3 step 3 (the residue field of the prime over
   `D_i` versus `[I_𝔓 : I_{Q_i}]`) and step 4.
2. **Locators not read (UNVERIFIED):**
   - Beckmann Prop. 4.2 (attribution only);
   - SGA 1 X 3.1 and XIII 5.3, and Grothendieck–Murre;
   - SGA 7 IX 3.6 and the toric functoriality;
   - Serre–Tate Thms 1-2 and the torsion lemma;
   - Deligne 1971 and 1979 (reciprocity, `π₀`, Hecke action);
   - Shimura 1967 and Kottwitz 1992 (moduli), and the other §4A inputs: Rotger 2003/2004
     (polarization), Mumford §21 (rigidity), Baba–Granath §2-3 (their `ℚ`-model);
   - EGA IV 7.8.3/18.7.6 (excellence) and miracle flatness (§1.2);
   - Vignéras (local normalizers, class number one);
   - Morita 1981.

   All of these are classical. The risk is in the numbering, not in the content (SPECULATIVE).
3. **Sign and normalization conventions** for reciprocity (`r = id` or conjugation). The
   argument is insensitive to them, because the unit group used is conjugation-stable.
4. **Branch data M4** still rests on Baba–Granath and Lin–Yang, as before. B1 adds no new
   dependence on them.
5. **Not touched by B1:**
   - W1, the manuscript's scalar descent, conductor bound and transfer (task T2);
   - W3, I1, I2 and the independence of `ℓ`;
   - W4, GR14 non-circularity;
   - the identification of N5's "level-three curve with all determinant components" with the
     moduli problem of §4(ii) step 1. That identification is standard but is stated in N5 only
     through b11's construction. **Repaired:** §4A now lists the four STANDARD inputs that give
     the agreement of N5's `Y₃` (defined as `Sh_{K₃}`) with the moduli scheme, including the
     polarization type; their locators remain UNVERIFIED (Shimura 1967, Deligne 1971 §4-6,
     Milne §8/§14, Kottwitz 1992, Rotger 2003/2004, Mumford §21, Baba–Granath §2-3).
6. **Scripts:** `scratch/h-b1/b1_checks.py`, with output `b1_checks.output.txt`, covering
   sections A-E. Each was run once, in about 1 minute of CPU.

## 7. Verdict

B1, as amended here, removes `b11-integral-model` from the justification of H, together with
Buzzard 1997 (A002) and the stable-model and tame-quotient theory (A078). After the amendment,
Theorem 4.1's good-reduction step (N5 L441-530, L557-558, L752-753, L781, L847-850) rests on:

- SGA 1 (purity and Abhyankar);
- the canonical model with Shimura reciprocity (Deligne);
- the classical moduli interpretation over `ℚ`, with the one `ℚ`-structure of §4A;
- SGA 7 semistable reduction, or Morita;
- Serre–Tate;
- Baba–Granath and Lin–Yang;

plus the exact computations of `scratch/h-b1`, and one new half-page argument (Lemma NV). The
amendment is essential: Beckmann's theorem by itself leaves vertical ramification open (Summary,
item 1).

Rating: **high** (SPECULATIVE) that Lemma PR holds as proved here. **Medium-high** that the
record survives review unchanged, mainly because of Lemma NV step 3. Payoff: it closes h-map's
W2. Combined with B2-B5, no supplement is left in H's justification.

## Changelog

Task h-b1-fix (2026-11-11), applying `docs/research/rv-h-b1.md` §8 (work log
`scratch/h-b1-fix/log.md`). None of these changes the argument.

1. **Repair 1 (table, rv T1/T2).** §5: the conjugate good-reduction line is N5 L557-558, not
   L563-566 (L563-566 is the Milne Hodge-endomorphism paragraph). Added rows L752-753 (`r_ℓ`
   unramified outside `T ∪ {ℓ}`) and L778-781 (good reduction at `p ∉ T ∪ {3,5}` for the
   Frobenius comparison), both covered by PR(ii). The paragraph after the table names all
   downstream uses of the conclusion and keeps the finding that L814 never used b11. Summary
   item 4 and §7 line ranges updated. Locators re-read in N5.
2. **Repair 2 (NV step 3; Prop. TS).** §3 step 3 now gives the full argument (closure of `Q_i`
   is local, finite over `R` with fraction field `k_p`, hence strictly henselian and unibranch,
   residue degree 1 = `[I_𝔓 : I_{Q_i}]` in the Kummer model; going-down by flatness; `I_q ⊂ I_𝔓`).
   §1.2 adds finiteness (`R` excellent) and flatness (normal of dimension 2 over regular).
3. **Repair 3 (M9, NV step 2).** M9 cites the complete enumeration of elliptic normalizer types
   (rv R2) with CM orders and `W`-images; NV step 2 is stated with "conductor prime to `p`" and
   the CM orders of discriminant `−3`, `−4`, `−24`, all maximal, with their `W`-images.
4. **Repair 4 (Summary item 1).** F1 also shows that unramified branch fibres are not enough, so
   NV's `W`-step is essential (rv R5).
5. **Repair 5 (§4A, new).** The one `ℚ`-structure on `Y₃ = Sh_{K₃}` shared by NV, PR(ii) and
   N5 (Baba–Granath's `j`), with the four STANDARD inputs (canonical model = moduli; uniqueness
   of the `μ`-principal polarization; Weil-pairing compatibility; level-3 rigidity), each
   UNVERIFIED with where to check it. Pointers added in §4(ii) step 1, §6 items 2 and 5, §7.
6. **Repair 6 (optional, done).** §3 remark: the `W`-layer check (Elkies constants `−1`, `3`; rv
   R7) as independent support for NV, and robustness to the branch labelling.
7. **Scripts rerun.** `scratch/h-b1/b1_checks.py` and `scratch/rv-h-b1/rv_checks.py`: outputs
   byte-identical to the saved ones (copies in `scratch/h-b1-fix/`).
