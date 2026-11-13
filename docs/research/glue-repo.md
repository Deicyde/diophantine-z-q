# glue-repo: the repository's replacement arguments and bookkeeping in Part A of H

Status: research note (task glue-repo, 2026-11-11). Scope: the steps A1, A3, A5, A6, A7, A8 and
A10 of `docs/research/h-trust.md` §1 (the quaternion datum, the degree bound `≤ 324`, Lemma
PR(i)-(ii) of `docs/research/h-b1.md`, the conjugates, the Hom field, NoCM of
`docs/research/rv-h-cm.md` §7.2). For each step this note states what is used, splits it into
**leaves** (published theorems) and **glue** (arguments the project must prove), decides whether
each piece can be stated in Lean today over genuine definitions, and records what is now proved
in Lean. Lean drafts: `scratch/glue-repo/` (`A1Quaternion.lean`, `TorsionFree.lean`,
`PRArith.lean`, `Numerics.lean`); scripts `compute.py`, `bezout.py` (output
`bezout.output.txt`); log `scratch/glue-repo/log.md`. No file under `ZInQKernel/`, `blueprint/`
or another note was edited.

Marks: **VERIFIED** = read in a source, computed, or compiled in Lean; **STANDARD** = a published
theorem with a reference (locators are those of h-trust / h-b1 / rv-h-cm and are UNVERIFIED
unless stated, since no source outside the repository could be read); **SPECULATIVE** = an
assessment. "N5 Lnnn" is a line of `diophantine_zq.tex`.

Kinds used in the tables:

- **LEAF**: a published theorem, to be stated as a Lean Prop and taken as an input.
- **GLUE-proved**: elementary content, now proved in Lean (no `sorry`; `#print axioms` gives
  only `propext`, `Classical.choice`, `Quot.sound`; VERIFIED by compilation with
  `lake env lean`).
- **GLUE-open**: an argument the project must prove, statable in Lean today, not yet proved.
- **GLUE-blocked**: an argument the project must prove that cannot be stated in Lean today,
  because its objects (Shimura curves, abelian varieties, Néron models, Tate modules of abelian
  varieties) are not in Mathlib (`docs/research/prereq-survey.md` §1, rows A1-A10).

## Summary

1. **All the elementary content of A1, A3, A5-A8 and A10 is now proved in Lean** (VERIFIED,
   four files, about 1400 lines, no `sorry`). Highlights:
   - A1: the order `𝒪 ⊂ ℍ[ℚ,2,0,−3]` as a genuine `Subring` of Mathlib's quaternion algebra; N5's
     Gram matrix and determinant 1; the Rosati identity `E(ax,y) = E(x, μ⁻¹āμ y)`; positivity of
     the Rosati involution (`Trd(a a†) = 2x₀²+4x₁²+2(3x₂−4x₃)²+4x₃² > 0`).
   - A3: `|(𝒪/3𝒪)^*| = 72`, and `4·72 ≤ 4·81 = 324`.
   - A5: the whole valuation case analysis of Lemma PR(i): for every prime `p ≥ 17` and
     `u ∈ ℚ ∖ 𝒞`, the three inertia orders `e_b/gcd(e_b, m_b)` predicted by Prop. TS at
     `b = 0, ∞, −16/27` are all 1 iff `p ∤ M_S(u)` (stated with the project's own
     `ZInQ.contactSupport`); `J(u)` is finite, nonzero and not a branch value; `[K:ℚ] ≤ 324!`.
   - A6: `1 + 3M_r(ℤ₃)` is torsion-free; `B` is a division algebra, so the toric part of
     PR(ii) step 2 vanishes.
   - A8: Minkowski's bound (a finite subgroup of `GL_r(ℤ)` injects into `GL_r(𝔽₃)`, so has order
     `≤ 3^{r²}`) and `[EK:ℚ] ≤ F₀·3^{r²} ≤ D`.
   - A10: the fibre of Elkies' model over `t(u)` is four points `(±iH/G³, ±540iF/G³)`, a free
     `W`-orbit with no real coordinate, and complex conjugation acts as `w₃`.
   - For Lemma NV and NoCM (h-b1 M9): `ℚ(√−2)` does not embed in `B`, and a type-(0,3) element
     `x` of `𝒪` has `(1+x)/2 ∈ 𝒪`.
2. **No new error was found** in A1, A3, A5-A8 or A10. Every arithmetic claim that was checked
   in Lean agrees with the notes (h-b1 M3, M5, M7, M9, §4(i); rv-h-cm §1.4, §2.4; N5 L414-416,
   L440, L468-470, L551-555). One refinement: h-b1 proves PR(i) "for every `p ≥ 17`". The Lean
   proof confirms the arithmetic half in exactly that range: `p ∤ 2·3·5` (resultants) and
   `p ∤ 7·11·13` (leading coefficients of `G` and `H`) are the only conditions used.
3. **The leaves of this cluster.** There are 14, listed in §3: Deligne's Hecke action and the
   Baba–Granath quotient, the moduli interpretation (A4), Vignéras' local normalizers, Prop. TS
   (Beckmann; or SGA 1 purity and Abhyankar), Shimura reciprocity at CM points, Grothendieck's
   semistable reduction with the functoriality of the toric part (or Morita), Serre–Tate
   Thms 1-2, Mumford's rank bound, Baba–Granath / Lin–Yang on the polarized moduli point, Elkies'
   model of `X⁶ → X*`, and González–Rotger Thm 5.12 and Prop. 5.6. Only two of them can be stated
   faithfully in Lean today: Vignéras' local normalizer index, which is in fact elementary
   (GLUE-open), and Prop. TS, a statement about Galois extensions of `ℚ(T)` (statable over
   Mathlib's Dedekind-domain ramification API, with real effort). The rest are about the
   Shimura curve `X₆`, its level-3 cover `Y₃` and the abelian surfaces it parametrizes.
4. **Biggest obstacle (SPECULATIVE assessment).** Every non-elementary input of Part A is a
   statement about `Y₃`, `X₆` or the fibre surface `A`. None of these exists in Mathlib, so
   neither the leaves nor the glue that connects them (A3's quotient, Lemma NV, PR(ii), A7, A8)
   can be stated over genuine definitions. The Lean glue proved here is the elementary core that
   any future formalization of Part A needs. It does not yet connect to `SixContactMin`, because
   the objects in between cannot be stated.

## 1. The steps, one by one

### A1. The quaternion datum and the Riemann form (N5 L405-418)

**Statement.** `B = (2,−3)` over `ℚ`; `𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩` is a maximal order;
`μ = 2j + ij`, `μ² = −6`; `E(x,y) = Trd(μ⁻¹xȳ)` is alternating, `ℤ`-valued and unimodular on `𝒪`,
with Gram matrix `[[0,0,−1,1],[0,0,1,−2],[1,−1,0,0],[−1,2,0,0]]`; its Rosati involution is
`a† = μ⁻¹āμ`, which is a positive involution and preserves `𝒪`.

| Piece | Kind | Supplier | Lean |
| --- | --- | --- | --- |
| `𝒪` is an order (closed under products, conjugation and `†`), reduced discriminant 6 | GLUE-proved | `form_check.py` | `A1.O` (a `Subring`), `comb_mul`, `star_mem`, `ros_mem`, `det_trace_form` (`det Trd(eₐe_b) = −36`) |
| `μ² = −6`, Gram matrix, `det = 1`, `E` integral and alternating | GLUE-proved | `form_check.py` | `μ_mul_μ`, `gram_E`, `det_gram_E`, `E_comb`, `E_self`, `E_antisymm` |
| `E(ax,y) = E(x,a†y)`; `†` is an anti-involution | GLUE-proved | `form_check.py` (on a basis) | `E_ros`, `ros_ros`, `ros_mul`, `ros_add` (for all `a, x, y`) |
| `†` is positive: `Trd(a a†) > 0` for `a ≠ 0` | GLUE-proved | new here (`compute.py` §1: minors 2, 8, 144, 576) | `trd_mul_ros`, `trd_mul_ros_pos` |
| `𝒪` maximal | GLUE-proved | discriminant 6 = disc `B`, a squarefree product of the ramified primes | `det_trace_form`; that discriminant equal to `disc B` implies maximality is STANDARD (Vignéras Ch. III) and was not formalized |
| Riemann-form convention (which form on `H₁` is the polarization) | convention, not a theorem | Lin–Yang 2020 eq. (3), Lemma 3 | — |

A1 has **no leaf**. Lin–Yang's equation (3) fixes a convention. That this form is a Riemann form
for the complex structure of a given point, and that the polarization is unique, belongs to A4
(the moduli interpretation; h-trust A4 item 2).

### A3. Level three, the normalizer action, the degree (N5 L419-441)

**Statement.** Let `K₀ = 𝒪̂^*`, `K₃ = ker(K₀ → (𝒪/3𝒪)^*)`, `N` the normalizer of `𝒪̂` in
`(B ⊗ 𝔸_f)^*`, and `Γ' = N/(𝔸_f^*K₃)`.
- (a) `|N/(𝔸_f^*K₀)| = 4`.
- (b) `𝔸_f^*` acts trivially on `Y₃ = Sh_{K₃}`.
- (c) `Γ'` acts on `Y₃` over `ℚ`, with quotient `P¹_j`.
- (d) `deg(Y₃ → P¹_j) ≤ |Γ'| ≤ 4·|(𝒪/3𝒪)^*| = 288 ≤ 324`; in fact `|Γ'| = 4·72/2 = 144 = 2⁴3²`
  (h-b1 M3).

| Piece | Kind | Supplier | Lean |
| --- | --- | --- | --- |
| (a) local normalizers: `N(𝒪_p) = ℚ_p^*𝒪_p^*` at split `p`, index 2 at `p = 2, 3` | GLUE-open (or LEAF L3) | Vignéras, LNM 800, Ch. II (UNVERIFIED). Elementary: at `p | 6`, `B_p` is a division algebra, `𝒪_p = {x : nrd x ∈ ℤ_p}`, `N(𝒪_p) = B_p^*` and `B_p^*/ℚ_p^*𝒪_p^* ≅ ℤ/2` via `v_p(nrd) mod 2`; at split `p`, `N(M₂(ℤ_p)) = ℚ_p^*GL₂(ℤ_p)` | statable now over `ℍ[ℚ_[p],2,0,−3]`; not done. The global ingredient `nrd x = 0 ⇒ x = 0` is proved (`A1.nrd_ne_zero`) |
| (b) central ideles act trivially | GLUE-open | `𝔸_f^* = ℚ^*_{>0}·ℤ̂^*` and `ℤ̂^* ∩ (1+3ℤ̂) ⊂ K₃` up to sign (N5 L428-433) | statable with Mathlib's `FiniteAdeleRing`; not done |
| (c) Hecke action of `Γ'` on the canonical model over `ℚ`; `X₆/W = P¹_j` | LEAF (L1, L2) | Deligne 1979 §2.7, §5; Baba–Granath 2008 (UNVERIFIED) | not statable (no Shimura curves) |
| `deg ≤ |Γ'|` (the quotient by a group of order `|Γ'|`, acting possibly non-faithfully) | GLUE-blocked | Artin's theorem on the function field (h-b1 M2) | not statable |
| `|(𝒪/3𝒪)^*| = 72` | GLUE-proved | `form_check.py`, `b1_checks.py` §B | `A1.card_units_mod3`, with `red3_mul` (reduction of coordinates is multiplicative) and `isUnit3_iff` (unit iff `nrd ≢ 0 mod 3`) |
| `4·72 ≤ 4·81 = 324`, `4·72/2 = 144 = 2⁴3²` | GLUE-proved | arithmetic | `Numerics.a3_numerals` |

The index computation `|Γ'| = |N/𝔸_f^*K₀| · |K₀/ℤ̂^*K₃|` is finite group theory. It was not
formalized: Mathlib's `relIndex_sup_*` lemmas need normality in the ambient group, which fails
here (`K₃` is normal in `N`, not in `(B⊗𝔸_f)^*`). With (a), (b) and the count it gives
`|Γ'| = 4·36 = 144`.

### A5. Lemma PR(i): the fibre field (replaces N5 L443-528; h-b1 §§1-4)

**Statement.** For `S ⊇ {p ≤ 324}` and `u ∈ ℚ ∖ 𝒞`, let `K` be the residue field of
`M = ℚ(Y^{(1)})` at a place over `j₀ = J(u)` (h-b1 M2, M8). Then `K/ℚ` is Galois,
`[K:ℚ] ≤ 324!` (in fact `[K:ℚ]` divides 144), and for `p ∉ S`, `K` is unramified at `p` unless
some `v_p(u − c)`, `c ∈ 𝒞`, is positive and odd.

| Piece | Kind | Supplier | Lean |
| --- | --- | --- | --- |
| Prop. TS: tame specialization, inertia order `e_i/gcd(e_i, m_i)` at `p` under (a) `p ∤ |Γ_M|`, (b) branch points distinct mod `p`, (c) rational branch points, (d) no vertical ramification | LEAF (L4) | Beckmann, J. reine angew. Math. 419 (1991), Prop. 4.2 (UNVERIFIED); or h-b1 §1.2 from SGA 1 X 3.1 (purity) and XIII 5.3 (Abhyankar) | statable in principle over `RatFunc ℚ`, integral closures and `Ideal.ramificationIdx`; no draft. Stacks (Axiom) has purity and Abhyankar, unreviewed (prereq-survey row A5) |
| Lemma NV (hypothesis (d) at `p ≥ 5`) | GLUE-blocked, over LEAF L5 (Shimura reciprocity at CM points: Shimura 1967, Deligne 1971 §3) and L2 (`W ≅ (ℤ/2)²`, Baba–Granath) | h-b1 §3 | not statable (the cover `Y₃ → P¹_j` cannot be defined) |
| NV step 2 input: every elliptic element of the normalizer has a maximal CM order (types `(0,1), (1,1), (2,2), (0,3), (3,3), (0,6)`; `(0,2)` absent) | GLUE, partly proved | `b1_checks.py` §C, `rv_checks.py` R2 | proved: `A1.half_one_add_mem` (type `(0,3)`: `(1+x)/2 ∈ 𝒪`, so the order has discriminant −3) and `A1.no_trd_zero_nrd_two` (no `x ∈ B` with `Trd x = 0`, `nrd x = 2`). Open: the list of types from `Trd² / nrd ∈ {0,1,2,3}` and the maximality of `ℤ[x]` for discriminants −3, −4, −24 |
| M1-M3, M10 (Galois structure of the cover, `|Γ_M|` divides 144, `X₆` connected and `W`-Galois over `P¹_j`) | LEAF / GLUE-blocked | Deligne; Baba–Granath; A3 | not statable |
| M5: branch points distinct mod every `p ≥ 5` | GLUE-proved (trivially) | differences of `0, ∞, −16/27` supported on `{2,3}` | implicit in `PRArith` (the case analysis needs only `p ≥ 17`) |
| M7: `j₀` is finite, nonzero and not a branch value | GLUE-proved | `branch_check.py`; h-b1 M7 | `PR.J_ne_zero`, `PR.J_ne_branch`, `PR.Hq_ne_zero` (the quadratic factors of `H` have discriminants `10800, 43200, 43200`, of odd 3-adic valuation), `PR.Gq_ne_zero` |
| The case analysis at `p ≥ 17` (h-b1 §4(i) steps 2-3) | GLUE-proved | `b1_checks.py` §§A, E | `PR.inertia_trivial_iff`: for every prime `p ≥ 17` and `u ∉ 𝒞`, `(4 ∣ m₀ ∧ 6 ∣ m_∞ ∧ 2 ∣ m_{−16/27}) ↔ ¬∃ c ∈ 𝒞, v_p(u−c) > 0 odd`, with `m₀ = v_p(j₀)⁺`, `m_∞ = (−v_p(j₀))⁺`, `m_{−16/27} = v_p(j₀+16/27)⁺`. `PR.inertia_orders_eq_one_iff`: the same with Prop. TS's `e/gcd(e,m) = 1` and with `¬ p ∣ ZInQ.contactSupport S u` for `p ∉ S ⊇ {primes ≤ 324}` |
| Identities `G⁶ − 97200F² = H²`, `J + 16/27 = 16H²/(27G⁶)` | GLUE-proved | N5 L513-515 | `PR.G6_sub_F2`, `PR.J_add` |
| Bezout certificates: `Res(F,G)`, `Res(F,H)`, `Res(G,H)` are `{2,3,5}`-units | GLUE-proved | `bezout.py` (homogeneous certificates with `N = 2¹⁰3⁸5⁶, 2¹⁷3¹²5¹⁰, 2¹¹3⁹5⁶`) | `PR.bez_FG`, `PR.bez_FH`, `PR.bez_GH` (checked by `ring`) |
| `[K:ℚ] ≤ 324!` | GLUE-proved, given that `K` is the splitting field of a separable polynomial of degree `≤ 324` | Galois group ↪ permutations of the roots | `Numerics.splitting_degree_le` |

How the proved pieces enter. Prop. TS reduces PR(i) at `p` to the three numbers
`e_b/gcd(e_b, m_b)`, once (a)-(d) hold at `p`. For `p ∉ S` we have `p > 324`, so (a) holds
whatever `|Γ_M| ≤ 324` is. (b) and (c) hold by M5, and (d) is Lemma NV. `inertia_orders_eq_one_iff`
then turns the three numbers into `p ∤ M_S(u)`. So PR(i) = Prop. TS (leaf) + Lemma NV
(blocked) + `inertia_orders_eq_one_iff` (proved).

### A6. Lemma PR(ii): good reduction away from 3 (replaces N5 L529-530)

**Statement.** The abelian surface `A/K` of a point of `Y₃(K)` over `j₀` has good reduction at
every finite place `v ∤ 3` of `K`; so do its conjugates.

| Piece | Kind | Supplier | Lean |
| --- | --- | --- | --- |
| `A[3] ⊂ A(K)` (the level structure is rational) | LEAF (L6: A4's moduli interpretation) | Shimura 1967; Deligne 1971 §4; Kottwitz 1992 (UNVERIFIED) | not statable |
| Semistable reduction over a finite extension | LEAF (L7) | SGA 7 I, Exp. IX, Thm 3.6 | not statable (no abelian varieties or Néron models in Mathlib) |
| `End A` acts on the character group `X(T)` of the toric part | LEAF (L7, same source) | SGA 7 IX §2 (functoriality of the toric part) | not statable |
| A unital `B`-module of `ℚ`-dimension `t ≤ 2` is zero, so `T = 0` and the reduction is potentially good | GLUE-proved | h-b1 §4(ii) step 2 (`4 ∣ t`) | `A1.module_eq_zero` (any `V` with `Module B V`, `IsScalarTower ℚ B V`, `dim_ℚ V < 4` is zero), from `A1.nrd_ne_zero` (`B` is a division algebra: 3-adic descent on `x₀² − 2x₁² + 3x₂² − 6x₃² = 0`) and `A1.inv_mul_self` |
| Alternative to the two rows above: potentially good reduction of QM surfaces | LEAF (L7') | Morita, Hokkaido Math. J. 10 (1981) (UNVERIFIED) | not statable |
| Potentially good ⇔ `ρ_ℓ(I_v)` finite; Néron–Ogg–Shafarevich | LEAF (L8) | Serre–Tate, Ann. of Math. 88 (1968), Thms 2 and 1 (UNVERIFIED) | not statable for abelian varieties (Tau Ceti has elliptic curves only) |
| A finite subgroup of `1 + 3M₄(ℤ₃)` is trivial | GLUE-proved | N5 L468-470 | `TorsionFree.matrix_padic_eq_one`, `TorsionFree.padic_subgroup_trivial` (via the general `eq_one_of_pow_eq_one` and Krull's intersection theorem) |
| Conjugates: `σA = A_{σx}` with `σx ∈ Y₃(K)`, `K` Galois | GLUE-blocked | h-b1 §5 | not statable |

### A7. The conjugates of `A` are geometrically isomorphic (N5 L532-543)

**Statement.** For `σ ∈ G_ℚ`, `σA ≅ A` over `ℚ̄` (polarized and with `𝒪`-action up to `W`),
because both have the same polarized moduli point, determined by `j = J(u) ∈ ℚ`.

| Piece | Kind | Supplier | Lean |
| --- | --- | --- | --- |
| `V_ℤ = V/W`; on the finite nonzero `j`-locus the polarized point is determined by `[J₂:J₄:J₆:J₁₀] = [12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]` | LEAF (L9) | Baba–Granath 2008 Thm 2.1; Lin–Yang 2020 eqs. (13)-(14), Exs. 29-30 (`igusa_check.py`) | not statable (no moduli of genus-2 curves or QM surfaces) |
| `j = J(u)` rational, finite, nonzero | GLUE-proved | `F(u) ≠ 0`, `disc G = −10800 < 0` | `PR.J_ne_zero`, `PR.Gq_ne_zero` |
| Alternative: the conjugates are Hecke translates, hence isogenous; an isogeny suffices downstream | GLUE-blocked | h-trust A7 remark (SPECULATIVE simplification) | not statable |

### A8. The Hom field `L` (N5 L544-563)

**Statement.** `W₀ = Res_{K/ℚ}A` has geometric endomorphism rank `r ≤ 16F₀²`; `G_ℚ` acts on
`End(W₀,ℚ̄)` through a finite group `G ↪ GL_r(ℤ)` with kernel field `E`; `L = EK` is normal over
`ℚ`, `[L:ℚ] ≤ F₀·3^{r²} ≤ D`, and `L` is unramified outside `T`.

| Piece | Kind | Supplier | Lean |
| --- | --- | --- | --- |
| `rank Hom(A, A') ≤ 4 dim A dim A'` | LEAF (L10) | Mumford, *Abelian varieties* (1970), §19 Thm 3 (UNVERIFIED) | not statable |
| `r ≤ [K:ℚ]²·16 ≤ 16F₀²` | GLUE-proved | arithmetic | `Numerics.a8_rank` |
| A finite subgroup of `GL_r(ℤ)` injects into `GL_r(𝔽₃)`, so `|G| ≤ 3^{r²}` | GLUE-proved | Minkowski | `TorsionFree.injective_mod_three`, `TorsionFree.card_le_three_pow` |
| `[E:ℚ] = |G|` (the kernel field of a finite Galois action) | GLUE-open | Galois theory | statable in Mathlib (fixed field of the kernel of a continuous action of `Gal(ℚ̄/ℚ)`); not done |
| `[EK:ℚ] ≤ [E:ℚ][K:ℚ] ≤ F₀·3^{r²} ≤ F₀·3^{256F₀⁴} = D` | GLUE-proved | arithmetic and compositum degree | `Numerics.a8_degree`, `Numerics.a8_field` (`IntermediateField.finrank_sup_le`); stated for variables `F₀, D` with `D = F₀·3^{256F₀⁴}`, because the kernel cannot unfold `ZInQ.heightD` (memory note on huge constants; `HeightConstant.lean`) |
| `L` unramified outside `T`: inertia acts trivially on `T_ℓ W₀`, hence on `End W₀` | LEAF (L8: NOS) with A5, A6 | Serre–Tate Thm 1 | not statable |

### A10. NoCM: `End⁰(A_ℚ̄) = B` for rational `u ∉ 𝒞` (replaces N5 L578-631; rv-h-cm §7.2)

**Statement.** For `u ∈ ℚ ∖ 𝒞`, no point `x ∈ X⁶(ℚ̄)` over `j = J(u)` is a CM point.

| Piece | Kind | Supplier | Lean |
| --- | --- | --- | --- |
| `t = 1 + 27j/16` takes the values `0, 1, ∞` at discriminants `−24, −4, −3` | LEAF (L2) | Baba–Granath (labelling of `j`) | not statable |
| Elkies' model `ℚ(X⁶) = ℚ(t)(√(−t), √(3(t−1)))` with `w₂, w₆, w₃` negating `y₂, y₁`, both | LEAF (L11) plus GLUE | shape: `W`-action over `ℚ` (González–Rotger §5); constants `c₀ = −1`, `c₁ = 3`: Shimura reciprocity at the elliptic points (rv-h-cm §2.3, `check.py` B); Elkies, ANTS-III (1998) §3, cross-check | not statable |
| `t(u) = H²/G⁶`, `t(u) − 1 = −3(180F/G³)²` | GLUE-proved | rv-h-cm §1.4 | `PR.t_eq`, `PR.t_sub_one` |
| The fibre over `t(u)` is `(±iH/G³, ±540iF/G³)`: four distinct points, a free `W`-orbit, no real coordinate (so no `ℚ`-rational point; residue field `ℚ(i)`), complex conjugation acts as `w₃` | GLUE-proved (in the model) | rv-h-cm §2.4, `check.py` | `PR.fibre_iff`, `PR.fibre_free`, `PR.h₁_ne_zero`, `PR.h₂_ne_zero` |
| (Emb): an imaginary quadratic `K` embeds in `B` iff neither 2 nor 3 splits in `K` | LEAF (L12) | Vignéras Ch. III (UNVERIFIED) | not formalized in general; the instance `K = ℚ(√−2)` is proved (`A1.no_trd_zero_nrd_two`). Splitting criteria for quaternion algebras exist in Tau Ceti (prereq-survey row A1) |
| `ℚ(x) = H_R ⊇ K` if `D(R) ≠ 1`; `[H_R:ℚ(x)] = 2` if `D(R) = 1` | LEAF (L13) | González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (numbering of arXiv:math/0612732 VERIFIED by rv-h-cm; journal UNVERIFIED) | not statable |
| `#CM(R) = h(R)` for `(f,6) = 1` | LEAF (L14) | González–Rotger, Prop. 5.6 | not statable |
| The case split (`|W·x| = 4 > 2 = #CM(R)`; `K = ℚ(i)`, `h = 1`, `R = ℤ[i]` forces `F(u) = 0`) | GLUE-blocked (trivial once the leaves are stated) | rv-h-cm §7.2 | not statable |

## 2. Lean: what compiles

All four files compile with `lake env lean scratch/glue-repo/<file>.lean`, with no `sorry`
(the only occurrence of the word is in a docstring). Every `#print axioms` at the ends of the
files reports `[propext, Classical.choice, Quot.sound]` (VERIFIED, 2026-11-11).

| File | Imports | Main theorems |
| --- | --- | --- |
| `A1Quaternion.lean` | Mathlib | `O` (a `Subring ℍ[ℚ,2,0,−3]`), `gram_E`, `det_gram_E`, `det_trace_form`, `E_ros`, `ros_ros`, `ros_mul`, `ros_mem`, `trd_mul_ros_pos`; `nrd_mul`, `half_one_add_mem`, `no_trd_zero_nrd_two`; `red3_mul`, `isUnit3_iff`, `card_units_mod3`; `norm_descent`, `nrd_ne_zero`, `inv_mul_self`, `module_eq_zero` |
| `TorsionFree.lean` | Mathlib | `CommCore.eq_one_of_pow_eq_one`, `eq_one_of_pow_eq_one`, `matrix_eq_one`, `matrix_int_eq_one`, `matrix_padic_eq_one`, `padic_subgroup_trivial`, `injective_mod_three`, `card_le_three_pow` |
| `PRArith.lean` | `ZInQKernel.Hypotheses.Height` (for `contactSet`, `contactSupport`, `prime_dvd_contactSupport_iff`; `Jmap` is copied verbatim from `JHeight.lean`, which scratch files cannot import in a worktree) | `G6_sub_F2`, `J_add`, `t_eq`, `t_sub_one`, `Hq_ne_zero`, `J_ne_zero`, `J_ne_branch`, `bez_FG`, `bez_FH`, `bez_GH`, `inertia_trivial_iff`, `inertia_trivial_iff_not_dvd`, `inertia_orders_eq_one_iff`, `fibre_iff`, `fibre_free` |
| `Numerics.lean` | `ZInQKernel.Hypotheses.Height` | `a3_numerals`, `splitting_degree_le`, `a8_rank`, `a8_degree`, `a8_field` |

Notes for reuse.
- `inertia_orders_eq_one_iff` is stated in terms of `ZInQ.contactSupport`, the Lean `M_S(u)` of
  `SixContactEstimate`. So once Prop. TS and Lemma NV are available as Props about a concrete
  cover, PR(i) follows by rewriting with it.
- The torsion-freeness core is proved for any ring in which 3 is a non-zero-divisor and
  `⋂ 3ⁿ = 0`. The same lemma gives A4's neatness (Serre's lemma at level 3) once Tate modules
  exist.
- Two Lean pitfalls met here. (i) `linarith [(by exact_mod_cast h : T)]` failed where
  `have : T := by exact_mod_cast h; linarith` succeeded. (ii) Statements mentioning
  `heightF0 = 324!` or `heightD` directly hit "maximum recursion depth" or "kernel refused to
  evaluate Nat.pow". Hence the variable form of `a8_*`.

## 3. The leaf list (brief)

Exact statements as used; all locators UNVERIFIED unless stated. "Statable" means statable in
Lean today over genuine Mathlib definitions.

| # | Leaf | Used in | Statable? |
| --- | --- | --- | --- |
| L1 | Deligne 1979 §2.7, §5: Hecke operators of `N` act on the canonical model `Sh_{K₃}` over the reflex field `ℚ` | A3(c), M1 | no (Shimura varieties) |
| L2 | Baba–Granath, Canad. J. Math. 60 (2008), §2-3; Lin–Yang 2020 Ex. 30: `X₆/W ≅ P¹_j`, branch values `0, ∞, −16/27` of indices 4, 6, 2 at CM discriminants −4, −3, −24; `W ≅ (ℤ/2)²` | A3, A5 (M4, M10, NV), A10 | no |
| L3 | Vignéras, LNM 800, Ch. II: normalizers of maximal orders in local quaternion algebras | A3(a) | yes; and elementary (GLUE-open) |
| L4 | Prop. TS = Beckmann 1991 Prop. 4.2 in the case of rational branch points; or SGA 1 X 3.1 + XIII 5.3 via h-b1 §1.2 | A5 | yes in principle (function fields, Dedekind ramification); no draft |
| L5 | Shimura reciprocity for CM points on the canonical model: `σ_s[τ,1] = [τ, r(s)]` (Shimura 1967; Deligne 1971 §3) | A5 (NV), A10 (constants) | no |
| L6 | Canonical model = fine moduli scheme of `(A, ι, λ, η)` over `ℚ` (Shimura 1967; Deligne 1971 §4; Kottwitz 1992 §5, §8; Rotger 2003/2004 for the polarization) — this is step A4, cluster of another task | A5-A8 | no |
| L7 | SGA 7 IX Thm 3.6 (semistable reduction) and IX §2 (functoriality of the toric part); or L7' Morita 1981 | A6 | no |
| L8 | Serre–Tate 1968 Thm 1 (Néron–Ogg–Shafarevich) and Thm 2 (potentially good ⇔ finite inertia image) | A6, A8 | no (for abelian varieties) |
| L9 | Baba–Granath Thm 2.1 with Lin–Yang eqs. (13)-(14): the polarized moduli point on the finite nonzero `j`-locus is determined by `j` | A7 | no |
| L10 | Mumford 1970 §19 Thm 3: `rank Hom(A,A') ≤ 4 dim A dim A'` | A8 | no |
| L11 | The `W`-action on `X⁶` over `ℚ` (González–Rotger §5) and Elkies 1998 §3 (cross-check) | A10 | no |
| L12 | Vignéras Ch. III: embedding criterion for quadratic fields into `B` | A10 | partly (Tau Ceti splitting criteria) |
| L13 | González–Rotger 2006 Thm 5.12 | A10 | no |
| L14 | González–Rotger 2006 Prop. 5.6 (for `(f,6) = 1`) | A10 | no |

## 4. Verdict and next steps

- **Done (VERIFIED).** Every finite computation and every elementary lemma of the cluster is a
  Lean theorem. The scripts `form_check.py` (A1, A3), `b1_checks.py` §§A-C, E (A5),
  `branch_check.py` (M7) and `rv-h-cm/check.py` parts A, F (the fibre) are now subsumed by Lean
  proofs, except the type list of M9 and Elkies' constants.
- **Next GLUE-open items, statable now (SPECULATIVE effort: one to three days each):**
  1. Vignéras' local normalizer index at `p = 2, 3` and at split `p`, over `ℍ[ℚ_[p],2,0,−3]` (A3(a)).
  2. The central-idele step A3(b) over `FiniteAdeleRing ℤ ℚ`.
  3. The full M9 type list and the maximality of `ℤ[x]` for discriminants −3, −4, −24.
  4. `[E:ℚ] = |G|` for the kernel field of a finite Galois action (A8).
  5. A Lean statement of Prop. TS over `RatFunc ℚ` (leaf L4).
- **Blocked.** The rest of A3, A5-A8 and A10 needs Shimura curves and abelian surfaces with
  their Tate modules and Néron models in Lean. Until those exist, Part A can enter a
  "theorems from the literature imply H" statement only as one opaque project Prop (the
  modularity half's input, cf. wk-h §4), not as a list of concrete leaves. This holds whatever
  decomposition of Theorem 4.1 is chosen (SPECULATIVE).
