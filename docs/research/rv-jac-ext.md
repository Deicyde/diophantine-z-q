# rv-jac-ext: does the degree-one-divisor extension for Axiom's Jacobians fit Theorem 4.1's bounds?

Task: settle the open question of `docs/research/axiom-bridge.md` §4. Axiom's `Faltings.Jacobian`
(bridged to our layer by `AxiomBridge.ofJacobian`) is constructed only for a
`CurveWithDegreeOneDivisor k`: a smooth projective geometrically integral curve with a divisor of
closed points with `∑ n_x [κ(x):k] = 1`. The QM surface `A` of N5's Theorem 4.1 is geometrically a
genus-2 Jacobian (R3). Over which field does a curve with a degree-one divisor exist, and do the
proof's degree and ramification bounds absorb that field?

## Verdict: ABSORBED

**No constant changes.** `F₀ = 324!`, `D = F₀·3^{256F₀⁴}`, `[L':ℚ] ≤ QM` and `H₆(S;R)` stay as
printed (N5 L388-397). The extension is absorbed at step A5/A8 (h-decomposition G2/G4), and
nothing downstream sees it.

1. **The curve needs no extension.** Let `(A, λ)` be the principally polarized fibre over `K` (A4).
   Then there is a genus-2 curve `C` over `K` itself with `(Jac C, θ_C) ≅ (A, λ)` over `K` (§2,
   N1). Mestre's obstruction (axiom-bridge §4(a)) concerns the field of moduli `ℚ(j) = ℚ` and does
   not arise, because the proof works over `K`. The obstruction is real over `ℚ`: `Aut(C_ℚ̄) = C₂`,
   VERIFIED below.
2. **A degree-one divisor over `K` is not guaranteed** (VERIFIED computation, §3). `G_K` acts on
   `A[2] ≅ 𝒪/2𝒪` through `(𝒪/2𝒪)^* ≅ A₄`, of order 12, and hence on the six Weierstrass points. If
   the image is `V₄` (orbits 2,2,2) or `A₄` (orbit 6), no Weierstrass point has odd degree. The
   other three possible images (1, `C₂`, `C₃`) give an odd orbit, so a degree-one divisor exists
   over `K` in those cases.
3. **The extension (route W′, recommended).** Take `K̃ = K(σA[2] : σ ∈ Gal(K/ℚ))`, the compositum
   of the 2-torsion fields of the conjugates. Then:
   - `K̃/ℚ` is Galois.
   - `K̃` is unramified outside `T`. A6 (good reduction at `v ∤ 3`) and Néron–Ogg–Shafarevich make
     each `σA[2]` unramified away from 6, and `2, 3 ∈ S ⊆ T`.
   - `[K̃:K] ≤ 12^k`, where `k = [K:ℚ]`.
   - `C_{K̃}` has six rational Weierstrass points, so it is a `CurveWithDegreeOneDivisor K̃`.
   - `[K̃:ℚ] ≤ k·12^k ≤ 324·12^324 ≤ 324! = F₀` (VERIFIED: computed, and compiled in Lean as
     `RvJacExt.routeW_finrank`).

   So `A_{K̃}` satisfies every conclusion of A5-A6 (Galois, `[·:ℚ] ≤ F₀`, unramified outside `T`,
   good reduction at `v ∤ 3`, `A[3]` rational) with the same constants. A8 then gives a Hom field
   `L̃` with `[L̃:ℚ] ≤ F₀·3^{256F₀⁴} = D` verbatim, and B3 gives `[L̃':ℚ] ≤ 2m·D ≤ QM` verbatim.
   **Requirement:** `k ≤ 622`. N5 only prints `[K:ℚ] ≤ 324!` (L526), which is too weak. The
   needed `k ≤ 324` follows from A3 (`deg(Y₃→P¹_j) ≤ 324`) and A5 (`J(u)` is not a branch value),
   because `Gal(K/ℚ)` embeds in the group acting freely on the fibre (N4 below). h-b1 M3 gives
   `k | 144` (repository, model-reviewed).
4. **Route L (backup).** Replace the Hom field `L` by `L₂ = L(A[2])`. Then `[L₂:L] ≤ 12`, and `L₂`
   is still Galois, unramified outside `T`, contains `K` and defines every Hom. This needs
   `12·[L:ℚ] ≤ D`, which holds by A8's own bound if `k ≤ 324` (`routeL_degree`). It also holds for
   every `k ≤ F₀` if A8 uses A10's exact rank `r = 4k²` instead of Mumford's `16k²`
   (`routeL_degree_noCM`). That makes route L independent of any refinement of `324!`.
5. **J₁(N): no extension** (§4). `X₁(N)` over `ℚ` has a `ℚ`-rational cusp, so it is a
   `CurveWithDegreeOneDivisor ℚ`, and its base change to `L'` (needed by E1/G17) is one over `L'`.

**What the absorption costs.** One new leaf, N1: a published theorem on genus-2 curves, not
formalized anywhere. Three small glue steps, N2-N4. Their combinatorial and arithmetic cores
compile in `scratch/rv-jac-ext/JacExt.lean`. Their geometric inputs are Mumford's theta
characteristics and Néron–Ogg–Shafarevich, which is already leaf T-NOS (`PkgI2.NeronOggShafarevich`).
The descent alternative (route D, §2.3) would avoid any extension but needs Galois descent of
schemes, which is in neither Mathlib nor Axiom's library. It is not needed.

## 1. The field steps checked (VERIFIED by reading N5 and h-trust)

| Object | Where defined | Bound used downstream | Uses after A8 |
| --- | --- | --- | --- |
| `K` (fibre field) | A5, N5 L524-528; G2 | `[K:ℚ] ≤ F₀` (N5); `∣ 144` (h-b1 M3); `≤ 324` from A3 + free fibre action (N4) | only through `L ⊇ K` and `W₀ = Res_{K/ℚ}A` in A8 |
| `r` (rank of `End(W₀,ℚ̄)`) | A8, N5 L546-549 | `r ≤ 16[K:ℚ]² ≤ 16F₀²` | A8 only |
| `L = EK` (Hom field) | A8, N5 L549-563; G4 | `[L:ℚ] ≤ [K:ℚ]·3^{r²} ≤ F₀·3^{256F₀⁴} = D`; Galois; unramified outside `T`; defines all geometric Homs among conjugates | B1 (N5 L638-640), B3 (`d ≤ D`, L713-716), D (local degree `≤ D`, `A[3]`/`A[5]` field degree `≤ DG₀`, tame for `p > R ≥ D`, L833-852) |
| `L'` | B3, N5 L711-716; G7 | `[L':ℚ] ≤ 2md ≤ 4DR^R M ≤ QM` | E1 (L861-867), E3 (Gaudron–Rémond with `d' = [L':ℚ]`, L873-889) |
| `D` | N5 L390 | only as an upper bound for `d` | everywhere through `d ≤ D` |

After A8, no step uses `K` or `[K:ℚ]` except through `L`. Every bound downstream is a function of
`d ≤ D`, `m`, `T`, `M` and `R`. N5 L828 also has "`e = v_F(2) ≤ D`", which is local, with `F = L_v`.
So any modification of the start that keeps four facts leaves B-F untouched:
1. `K` is Galois over `ℚ`, unramified outside `T`, with `[K:ℚ] ≤ F₀`.
2. `A/K` has good reduction at `v ∤ 3` (all conjugates too).
3. `A[3] ⊂ A(K)`.
4. The QM datum `ι` is defined over `K`.

Base change from `K` to a larger Galois `K̃` preserves 2-4, and does not affect the geometric steps
A7, A9 and A10 or the heights of E-F: the stable Faltings height and `h(j)` do not depend on the
field. Only fact 1 has to be rechecked. For `K̃` that is item 3 of the verdict.

**Fact 1 needs `[K:ℚ] ≤ 324`, not `324!` (glue N4).** `Γ'` acts on `Y₃` over `ℚ` with quotient
`P¹_j` (A3). Over a non-branch value, which `J(u)` is (A5), the effective quotient of `Γ'` acts
simply transitively on the geometric fibre. Fix a fibre point `x`. For `σ ∈ G_ℚ`, write
`σx = γ_σ x`. The stabilizer of `x` fixes every `γx`, because `σ(γx) = γ(σx)`. So `K` is the fixed
field of that stabilizer, and `[K:ℚ] ≤ |Γ'_eff| = deg(Y₃→P¹_j) ≤ 324`. (Elementary.
SPECULATIVE only in that the repository has not written it out. h-b1 M2-M3 contains it with 144.)
G2 currently proves `[K:ℚ] ≤ 324!` in Lean and should output `≤ 324`.

## 2. The extension: exact statements, sources, cost

### 2.1 Statements

- **N1 (leaf; curve over the field of definition).** Let `k` be a field of characteristic 0 and
  `(A, λ)` a principally polarized abelian surface over `k` with `A_k̄` simple. Then there is a
  smooth projective geometrically integral genus-2 curve `C/k` with `(Jac C, θ_C) ≅ (A, λ)` over
  `k`.
  - *Proof outline (STANDARD).* Over `k̄`, `(A, λ)` is the Jacobian of a genus-2 curve or a product
    of elliptic curves with the product polarization (Weil 1957). The second is excluded by
    simplicity: here `End⁰(A_ℚ̄) = B` is a division algebra (A10). Torelli makes
    `Aut(C) → Aut(Jac C, θ)` bijective for hyperelliptic `C`, because `−1` is the hyperelliptic
    involution. So the descent datum of `(A, λ)` lifts uniquely to `C_k̄`. Weil's descent theorem
    then gives `C/k`.
  - *Sources* (all locators UNVERIFIED):
    - Weil, *Zum Beweis des Torellischen Satzes*, Nachr. Akad. Wiss. Göttingen 1957.
    - Milne, *Jacobian varieties*, in Cornell–Silverman (eds.), *Arithmetic Geometry* (1986),
      Thm 12.1 and Cor. 12.2 (Torelli).
    - Weil, *The field of definition of a variety*, Amer. J. Math. 78 (1956).
    - The statement as printed: J.-P. Serre, appendix to K. Lauter, *Geometric methods for
      improving the upper bounds on the number of rational points on algebraic curves over finite
      fields*, J. Algebraic Geom. 10 (2001), 19-36. The appendix proves that a ppav that is
      geometrically a hyperelliptic Jacobian is a Jacobian over the base field; the obstruction it
      describes arises only in the non-hyperelliptic case.
  - *Applied to* `k = K` and the A4 fibre with A10.
- **N2 (glue; Weierstrass points over the 2-torsion field).** For a genus-2 curve `C/k` with
  Weierstrass points `W₁..W₆`, every `σ ∈ G_k` that acts trivially on `Jac(C)[2]` fixes each `W_i`.
  - *Proof (VERIFIED as an argument).* `[W_i + W_j − K_C]` (`i < j`) are 15 distinct classes: two
    distinct effective degree-2 divisors are linearly equivalent only in the `g¹₂`, which would
    force `W_j = ι(W_i) = W_i`. The only effective divisor in the class of `W_i + W_j` is itself
    (`h⁰ = 1`). So `σ` fixes each pair `{W_i, W_j}`, and a permutation of ≥ 3 points fixing every
    pair is the identity: `RvJacExt.perm_eq_one_of_fixes_pairs`, compiled.
- **N3 (glue; the field `K̃`).** With `K`, `A` as in A5-A6 and `k = [K:ℚ]`, let
  `K̃ = K(σA[2] : σ ∈ Gal(K/ℚ))`. Then:
  - (i) `K̃/ℚ` is Galois, since `τ(K(σA[2])) = K((τσ)A[2])`.
  - (ii) `K̃` is unramified outside `T`: by A6 and Néron–Ogg–Shafarevich (Serre–Tate 1968 Thm 1,
    leaf `PkgI2.NeronOggShafarevich`), with `2, 3 ∈ T`.
  - (iii) `[K(σA[2]):K]` divides 12. `G_K` commutes with `σι(𝒪)`, which is defined over `K`. So it
    acts on the free rank-one `𝒪/2𝒪`-module `σA[2]` by right multiplication by units, and §3
    shows there are 12 of them. Hence `[K̃:K] ≤ 12^k` (`RvJacExt.finrank_finset_sup_le`).
  - (iv) `[K̃:ℚ] ≤ F₀` once `k ≤ 324` (`RvJacExt.routeW_finrank`).
  - (v) `C_{K̃}` has a `K̃`-rational point (N2), hence a degree-one divisor.
  - (vi) `A_{K̃} ≅ Jac(C_{K̃})`, which is Axiom's `Faltings.Jacobian` of `C_{K̃}` by uniqueness
    (`nonempty_and_existsUnique_iso`).
- **N4 (glue).** `[K:ℚ] ≤ 324` (§1).

If only `ι` over `L` were available (and not over `K`), (iii) would weaken to `[K(σA[2]):K] ≤ 720`
(`|Sp₄(𝔽₂)|`). Route W′ then needs `k ≤ 235`, so h-b1 M3's 144 rather than 324. A4 gives `ι` over
`K`, since the fibre point is `K`-rational.

### 2.2 Cost

- **Bounds.** None (§1).
- **Text.** One paragraph in A5 ("replace `K` by `K̃`") and the strengthening N4 in G2.
- **Lean.**
  - N2-N4's cores and the degree arithmetic: compiled here (§5).
  - The geometry of N2 (divisors on a curve, the `g¹₂`, `h⁰`) and of N3(iii) (Tate module free
    over `𝒪₂`) needs Riemann–Roch on curves and the Tate module of a Jacobian. Axiom's library has
    the Picard functor but not Riemann–Roch for `h⁰`; medium.
  - N1 is a leaf: large to prove, cheap to state once `PkgI3.AbVar` has polarizations (WP4).
  - Base change `AbVar K → AbVar K̃` is needed to state "`A_{K̃} ≅ ofJacobian J`" and is not in our
    layer (WP4). It is needed anyway for G17 (`A` over `L'`).

### 2.3 Route D (no extension; not needed)

The Jacobian of `C/K` exists without a degree-one divisor and represents `Pic⁰_{C/K}` étale-locally.
This is Milne 1986, Thm 1.1, whose statement assumes no rational point, proved via the case
`C(k) ≠ ∅` and Galois descent; and Bosch–Lütkebohmert–Raynaud, *Néron Models*, §8.1-8.2. Both
UNVERIFIED. In Lean this needs Galois descent of projective schemes with descent data, which
Mathlib does not have, plus uniqueness of `(J, ι)`, which Axiom has. Route W′ makes it
unnecessary.

## 3. Exact computation: Galois orbits of the Weierstrass points (VERIFIED, `weier2.py`)

Set-up (A1, A4).
- `T₂(A)` is a free rank-one left `𝒪₂`-module. `B ⊗ ℚ₂` is a division algebra, so `𝒪₂` is its
  unique maximal order, a noncommutative DVR.
- The Weil pairing is `e₂(x, y) = Trd(μ⁻¹xȳ) mod 2` on `A[2] = 𝒪/2𝒪`. This is the Gram matrix of
  A1, with determinant 1, rechecked.
- `G_K` acts `𝒪`-linearly, hence by right multiplication by `(𝒪/2𝒪)^*`.
- The Weierstrass points correspond `G_K`-equivariantly to the six odd quadratic forms refining
  `e₂` (Mumford, *Theta characteristics of an algebraic curve*, Ann. Sci. ENS 4 (1971); locator
  UNVERIFIED; STANDARD).

Output (`scratch/rv-jac-ext/weier2.output.txt`):
- `|(𝒪/2𝒪)^*| = 12`, with element orders `1, 2³, 3⁸`, so `A₄`. Right multiplication preserves `e₂`.
- There are 6 odd and 10 even forms.
- Orbits on the six Weierstrass points, by image of `G_K`:

| Image of `G_K` | Orbits | Degree-one divisor over `K`? |
| --- | --- | --- |
| 1 | 1,1,1,1,1,1 | yes (rational Weierstrass point) |
| `C₂` (3 conjugates) | 1,1,2,2 | yes |
| `C₃` (4 conjugates) | 3,3 | yes (odd degree 3, plus the degree-2 hyperelliptic fibre) |
| `V₄` | 2,2,2 | not from Weierstrass points |
| `A₄` | 6 | not from Weierstrass points |

So the extension is genuinely needed in general, unless `C` has an odd-degree non-Weierstrass point.
Whether the index of `C/K` is ever 2 here is not decided (SPECULATIVE that it occurs). The minimal
non-Galois fix has degree ≤ 4 over `K` (the fixed field of a `C₃` in `A₄`, or of a `C₂` in `V₄`).
That matches axiom-bridge's "≤ 4", but over `K` and not over `ℚ(j)`. The Galois fix `K(A[2])` has
degree dividing 12.

`autcheck.py`: the only `u ∈ 𝒪` with `μ⁻¹ūμu = 1` are `±1`. Exact argument: the norm `−1` case
needs `2a² + 3b² = 1` with `b ∈ ½ℤ` and `a ∈ b + ℤ`, which is impossible. So
`Aut(A_ℚ̄, λ) = Aut(C_ℚ̄) = C₂` when `End(A_ℚ̄) = 𝒪`. Over the field of moduli `ℚ`, `C` is defined
only where Mestre's conic splits (consistent with Baba–Granath; locator UNVERIFIED). Over `K` this
does not matter (N1).

## 4. J₁(N)

**Confirmed: no extension.**
- `X₁(N)` over `ℚ` (Shimura's model, or the moduli of `(E, P)` with `P` of exact order `N`; the
  two are `ℚ`-isomorphic) is smooth, projective and geometrically connected.
- It has a `ℚ`-rational cusp. In the `(E, P)` model, `(Tate(q^N), q)` is defined over `ℚ((q))`, so
  the cusp it represents is rational. In the `μ_N` model, `(Tate(q), μ_N ⊂ 𝔾_m)` is. Diamond–Im,
  *Modular forms and modular curves* (1995), §9.3, and Diamond–Shurman §9.3: STANDARD, locators
  UNVERIFIED.
- So `X₁(N)` is a `CurveWithDegreeOneDivisor ℚ` (a rational point is a degree-one divisor), and
  `ofJacobian` gives `J₁(N)` with `dim = g`.
- G17 needs `J₁(N)_{L'}`. Either take `ofJacobian` of `X₁(N)_{L'}`, which has the base-changed
  cusp, or base-change the Jacobian. The second needs the small glue "the base change of a Jacobian
  is a Jacobian" (the Picard functor restricted to `L'`-schemes), which is not in Axiom.
- The Hecke action and `G_ℚ`-equivariance (G13) need functoriality of `Jacobian` for
  correspondences, as axiom-bridge §4 already notes. This is unrelated to divisors.

## 5. Lean (`scratch/rv-jac-ext/JacExt.lean`, Mathlib only)

Compiled with `lean` and `LEAN_PATH` set to the package build directories. `lake env` on this
branch tries to fetch `Mordell` and fails offline. No errors. Axioms
`[propext, Classical.choice, Quot.sound]` for every theorem.

| Name | Statement |
| --- | --- |
| `perm_eq_one_of_fixes_pairs` | `3 ≤ card α`, `σ` fixes every `{i, j}` ⇒ `σ = 1` (N2's core) |
| `finrank_finset_sup_le` | intermediate fields of degree `≤ c` ⇒ `finrank (s.sup t) ≤ c ^ s.card` (N3(iii)) |
| `twelve_pow_bound` | `324·12^324 ≤ 324!` (`decide +kernel`) |
| `routeW_degree`, `routeW_finrank` | `[K:ℚ] ≤ 324`, `[M:K] ≤ 12^{[K:ℚ]}` ⇒ `[M:ℚ] ≤ F₀` (tower law) |
| `routeL_degree` | `d ≤ k·3^{(16k²)²}`, `k ≤ 324` ⇒ `12d ≤ D` |
| `routeL_degree_noCM` | `d ≤ k·3^{(4k²)²}`, `1 ≤ k ≤ F₀` ⇒ `12d ≤ D` |

`F0` and `Dconst` are local copies of `heightF0` and N5's `D` (`Height.lean`). The scratch file
cannot import the project.

## 6. Status of claims

- VERIFIED:
  - by reading: §1's table and the downstream dependence on `d ≤ D` only.
  - computed: §3, the bounds in `bounds.py`, and `Aut = ±1`.
  - compiled: §5.
  - as arguments: N2, N4, N3(i)-(iii) given A4/A6, NOS and Mumford's theta characteristics.
- STANDARD, locators UNVERIFIED: N1 (Weil 1957, Torelli, Weil 1956, Serre's appendix to Lauter
  2001), Mumford 1971, the rational cusp of `X₁(N)`, route D (Milne 1986 Thm 1.1, BLR §8.1).
- SPECULATIVE: whether the index of `C/K` is ever 2 for this family. It is not needed.
- Not checked: the instantiation of any of this in Lean beyond the cores above (needs R1/WP4/WP9).
