# pkg-I1: the discriminant-6 Shimura curve as literature leaves

Status: research note (task pkg-I1, 2026-11-11). Package I1 of `docs/research/wk-h.md` §2: steps
A2-A5, A7, A10 and F1 of `docs/research/h-trust.md`. For each literature input: the exact statement
used, the most concrete faithful formulation, the Lean objects it needs and what exists, and a
compiled Lean draft where it can be stated today. Drafts: `scratch/pkg-I1/I1.lean` (compiles, no
`sorry`); scripts `qm_embed.py`, `theta_modular.py`, `igusa_poly.py` in the same directory; log
`scratch/pkg-I1/log.md`. No file under `ZInQKernel/`, `blueprint/` or other notes was edited.

Marks: **VERIFIED** (read in a source, computed, or compiled), **STANDARD** (published, with an
exact reference), **SPECULATIVE**. A locator recalled from memory is marked UNVERIFIED (no
network here). The manuscript `diophantine_zq.tex` is cited as N5 with line numbers.

## Summary

1. **New concrete form of A2 + F1 (VERIFIED numerically, compiled as a Lean Prop).** The
   statement that the proof needs from Lin–Yang, Igusa and Baba–Granath can be written with no
   Shimura curve, no abelian variety and no modular form library at all. It uses only the upper
   half-plane, an explicit `2×2` period matrix `Ω(τ)` of N5's QM datum (computed here), and the ten
   even genus-2 theta constants as `tsum`s over `ℤ²`:

   > `j_θ(τ) = 3779136·∏θ_m(Ω(τ))⁴ / (Σθ_m(Ω(τ))⁸)⁵` is a Hauptmodul of `Γ*\ℍ` (`Γ* = N_B(𝒪)⁺`),
   > its fibres are exactly the `Γ*`-orbits, and it takes the values `0`, `∞`, `−16/27` at the
   > fixed points of `ι(x)` for `x ∈ 𝒪` with `x² = −1`, `x² − x + 1 = 0`, `x² = −6`.

   This is the Lean leaf `QMHauptmodul`. The numerical checks are in `qm_embed.py`. `j_θ` is
   invariant under five generators of `Γ*` and under a non-torsion unit of `𝒪¹`. It vanishes at
   `√2 + i`, has a pole of order 6 in `τ` (simple in the orbifold coordinate) at `i√3`, and equals
   `−16/27` at `i√(9+6√2)` and `81/64` at a disc `−19` point, all to 20-30 digits.
2. **Three leaves compile today** (`I1.lean`, `lake env lean`, no errors):
   `ThetaModularity` (Igusa: `Σθ⁸` and `∏θ²` are Siegel modular of weight 4 and 10;
   signs and weights checked numerically on five generators of `Sp₄(ℤ)`),
   `QMHauptmodul` (Lin–Yang Ex. 30 + Igusa + Baba–Granath, analytic form), and
   `IgusaClebschSeparation` (Clebsch–Bolza–Igusa: Igusa invariants separate `GL₂`-orbits of
   binary sextics with nonzero discriminant). For the last one, explicit `J₂, J₄, J₆, J₁₀` were
   derived as polynomials in the seven coefficients and checked against PARI's `genus2igusa`.
3. **Glue proved in Lean** (no `sorry`): A1's Gram matrix and its determinant; the F1 algebra
   `j·(Σθ⁸)⁵ = 3779136·(∏θ²)²` from the Igusa vector and LNY's conventions; the
   `Sp₄(ℤ)`-invariance of the F1 ratio (from `ThetaModularity`); `G⁶ − 97200F² = H²`; for
   rational `u ∉ 𝒞`, `J(u)` is finite and nonzero, and `J(u) ≠ −16/27` for every rational `u`
   (A5, A7); Elkies' coordinate `1 + 27J/16 = H²/G⁶` and `27J/16 = −3(180F/G³)²` (A10); the CM
   elements `i+j`, `(1+j)/2`, `μ` of `𝒪`; and "two sextics with Igusa vector `∝ lyVec j` are
   equivalent" (A7's algebraic step, from `IgusaClebschSeparation`).
4. **What cannot be stated today (the obstacle).** The canonical model of `Y₃` over `ℚ` as the
   fine moduli scheme of QM surfaces with level-3 structure (A4), and with it the `ℚ`-rationality
   of `j`. Also Shimura reciprocity at CM points with the structure of `CM(𝔬)` (A10 and Lemma NV),
   and Baba–Granath's Jacobian criterion (the `End(Jac C) ⊇ 𝒪` side of the Igusa vector). All of
   these need abelian varieties over a field with endomorphisms, polarizations and level
   structures, and class field theory for CM points. Mathlib has none of these (§3). The analytic
   leaves above are faithful consequences of the published theorems, but alone they do not give
   the proof what it needs: the link "the fibre surface `A/K` over `J(u)` has period matrix
   `Ω(τ)` with `j_θ(τ) = J(u)`" is the canonical-model leaf I1-a.

## 1. What the proof takes from I1

The rest of H's proof (packages I2-I5 and Glazer's arguments) uses the following **output of
I1**. It is stated here once and is not a leaf: it is what the leaves and glue below must yield.

> **(I1-out)** Let `u ∈ ℚ \ 𝒞` and `j₀ = J(u)`. There are a number field `K`, Galois over `ℚ` with
> `[K:ℚ] ≤ 324!`, and a principally polarized abelian surface `(A, λ)/K` with
> `ι: 𝒪 ↪ End_K(A)`, Rosati involution `x ↦ μ⁻¹x̄μ` on `𝒪`, and an `𝒪`-linear isomorphism
> `𝒪/3𝒪 ≅ A[3]` over `K`, such that:
> (i) `K` is unramified outside `T = S ∪ supp M_S(u)` (A5, with Lemma PR(i));
> (ii) every conjugate `σA` (`σ ∈ Gal(K/ℚ)`) is isomorphic to `A` over `ℚ̄` (A7);
> (iii) `End⁰(A_ℚ̄) = B` (A10);
> (iv) for every embedding `K ↪ ℂ` and every period matrix `Ω_A ∈ 𝔥₂` of `(A_ℂ, λ)`,
> `j₀·(Σθ_m(Ω_A)⁸)⁵ = 3779136·(∏θ_m(Ω_A))⁴`, with `Σθ_m(Ω_A)⁸ ≠ 0` (F1).

Step by step, with the class from wk-h §1 (W = well-known theorem, R = repository argument,
B = bookkeeping):

| Step | Class | What I1 must supply | Leaves (§2) | Glue (§4) |
| --- | --- | --- | --- | --- |
| A2 | W | `X₆/W ≅ P¹_j` over `ℚ`, branch values `0, ∞, −16/27` of indices 4, 6, 2 at discs −4, −3, −24 | I1-a (`ℚ`-structure), I1-b `QMHauptmodul` (analytic) | CM elements `cm4`, `cm3`, `cm24` |
| A3 | B | `deg(Y₃ → P¹_j) ≤ 4·72 ≤ 324` | I1-f (local normalizers, Vignéras) | count of `(𝒪/3𝒪)^*` (not in Lean; `form_check.py`) |
| A4 | W | `Y₃` = fine moduli scheme over `ℚ` | I1-a | — |
| A5 | R | inputs to Lemma PR(i): branch data, Shimura reciprocity at the three elliptic points, `W ≅ (ℤ/2)²` | I1-a, I1-e | `Ju_ne_branch` (fibre is étale) |
| A7 | B | conjugates geometrically isomorphic | I1-a (Hecke action), or I1-d + I1-c | `equiv_of_lyVec`, `Ju_ne_zero` |
| A10 | R | NoCM: no CM point lies over `J(u)` | I1-e | `elkies_t`, `elkies_t_sub_one` |
| F1 | W | (iv) above | I1-b, I1-c `ThetaModularity`, I1-a | `f1_algebra`, `f1_constant`, `thetaRatio_invariant` |

## 2. The leaves

### I1-a. The canonical model is the fine moduli scheme (A4, and the `ℚ`-structure of A2) — not statable today

- **Published statements.** Shimura, *Construction of class fields and zeta functions of
  algebraic curves*, Ann. of Math. 85 (1967), 58-159, main theorem; Deligne, *Travaux de Shimura*,
  Sém. Bourbaki 389 (1971), Thm 4.21, Cor. 5.7 and Ex. 5.8, with Prop. 1.15 and §§4.8-4.17;
  Kottwitz, J. Amer. Math. Soc. 5 (1992), §5 and §8 (the `ker¹` count). Locators as adopted in
  h-trust A4 (UNVERIFIED here). Neatness: Mumford, *Abelian varieties*, §21, Thm 5 (UNVERIFIED).
  Uniqueness of the polarization: Rotger, J. reine angew. Math. 561 (2003) (UNVERIFIED), or the
  elementary argument of h-trust A4 item 2.
- **Most concrete faithful formulation.** Let `K₃ = ker(𝒪̂^* → (𝒪/3𝒪)^*)`. The functor on
  `ℚ`-schemes `S ↦ {(A, ι, λ, η)}/≅` is represented by a smooth projective curve `Y₃/ℚ`. Here `A/S`
  is an abelian scheme of relative dimension 2, `ι: 𝒪 → End_S(A)`, and `λ` is a principal
  polarization whose Rosati involution induces `x ↦ μ⁻¹x̄μ` on `𝒪`. `η: (𝒪/3𝒪)_S ≅ A[3]` is an
  `𝒪`-linear isomorphism of `S`-group schemes. Moreover:
  1. (uniformization) `Y₃(ℂ) = B^*\(ℍ^± × B̂^*/K₃)`, with `(A, ι, λ)` at `[τ, 1]` the torus
     `ℂ²/ι(𝒪)(τ,1)ᵀ` with Riemann form `E(ι(x)v, ι(y)v) = Trd(μ⁻¹xȳ)` (§2 of `I1.lean`);
  2. (Hecke action over `ℚ`) the finite group `N/(𝔸_f^*K₃)` acts on `Y₃` over `ℚ` by
     `(A, ι, λ, η) ↦ (A, ι∘Ad(n)⁻¹, λ, η∘n)` for `n ∈ N_B(𝒪)` (same `A`); the quotient is a
     smooth conic `≅ P¹_ℚ`, and there is a coordinate `j` on it, defined over `ℚ`, whose
     pull-back to `ℍ` is the function `f` of I1-b.
- **Lean objects needed.** Abelian schemes over a base with endomorphism actions, polarizations,
  Rosati involutions, finite flat group schemes `A[n]` with level structures, representability of
  a moduli functor, and the complex uniformization (analytification). **What exists:** Mathlib has
  group schemes over a field and the fact that proper geometrically integral ones are commutative
  (`AlgebraicGeometry/Group/Abelian`), and nothing on polarizations, endomorphism algebras,
  `A[n]` or analytification (VERIFIED, grep). Prereq-survey row A4 lists an Anthropic FLT
  development `CerednikDrinfeld.QM.FakeEllipticCurve` with `FullLevel m` (fine moduli of QM
  "fake elliptic curves"), built for `p`-adic uniformization. Whether it gives `Y₃` over `ℚ` with
  its uniformization is not checked; the canonical-model theorem over `ℚ` is not found there.
- **Why this is the obstacle.** I1-b is a statement on `ℍ`. To use it for the surface `A/K` of
  (I1-out) one needs (1) and (2): the algebraic `j` of the `ℚ`-model, evaluated at the moduli point
  of `A`, equals `f(τ_A)`, where `Ω(τ_A)` is a period matrix of `A_ℂ`.

### I1-b. The QM Hauptmodul in theta constants (A2 analytic + F1) — **statable, `QMHauptmodul`**

- **Published statements.** Lin–Yang, *Quaternionic loci in Siegel's modular threefold*, Math. Z.
  295 (2020), Example 30 (divisors of `ψ₄` and `χ₁₀` on the QM curve `X ≅ P¹`: `χ₁₀²/ψ₄⁵` is a
  degree-one function with zero at `P₋₄` and pole at `P₋₃`) and eqs. (13)-(14) (VERIFIED in arXiv
  v1 by task h-v14; journal numbering UNVERIFIED). Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1
  and §3 (the branch data; journal numbering UNVERIFIED). Igusa, Amer. J. Math. 89 (1967), pp.
  833-834 and 848, with Lauter–Naehrig–Yang, J. Number Theory (2015), §2.2 (`ψ₄ = 2⁻²Σθ⁸`,
  `χ₁₀ = −2⁻¹⁴∏θ²`; locators UNVERIFIED). The constant at `P₋₂₄` is also checked independently by
  `scratch/rv-up/theta24.py` and here.
- **Formulation (Lean, `I1.lean` §§2-4, 6).**
  - `B = QuaternionAlgebra ℚ 2 0 (−3)`, `𝒪` = integer span of `1, i, (1+j)/2, (i+ij)/2`.
  - `ι(i) = [[√2,0],[0,−√2]]`, `ι(j) = [[0,−3],[1,0]]`.
  - `Γ* = {ι(x) : x` invertible, normalizing `𝒪`, `det ι(x) > 0}` acting on `ℍ` through Mathlib's
    `GL (Fin 2) ℝ` action.
  - `Ω(τ) = (F₀(τ)P⁻¹)⁻¹E(τ)`, where `E(τ)` has columns `ι(1)(τ,1)ᵀ, ι(i)(τ,1)ᵀ`, `F₀(τ)` has
    columns `ι((1+j)/2)(τ,1)ᵀ, ι((i+ij)/2)(τ,1)ᵀ`, and `P = [[−1,1],[1,−2]]` is the off-diagonal
    block of N5's Gram matrix.
  - `θ_m(Ω) = Σ_{n∈ℤ²} exp(πi(n+a/2)ᵀΩ(n+a/2) + πi(n+a/2)ᵀb)` for `m = (a,b) ∈ ({0,1}²)²`, and
    the ten even `m`.
  - The leaf: there is a continuous `f: ℍ → ℂ ∪ {∞}` with `f = jNum/jDen ∘ Ω` wherever
    `jDen ≠ 0`, with fibres exactly the `Γ*`-orbits, surjective, and with the three CM values.
- **Faithfulness.** `Ω(τ)` is a period matrix of `(ℂ²/Λ_τ, E)`: for the symplectic basis
  `e, f'` one has `E(e_a, f'_b) = δ_ab` by construction, and `F'⁻¹Λ_τ = Ωℤ² + ℤ²`. Symmetry and
  `Im Ω > 0` are VERIFIED numerically; the other normalization `E⁻¹F'` has negative definite
  imaginary part, i.e. it belongs to `−E`. So `τ ↦ Ω(τ)` is the moduli map `ℍ → 𝔥₂` of N5's
  principally polarized QM family, with N5's sign of the Riemann form. `jNum/jDen = 16·144⁵χ₁₀²/ψ₄⁵`
  is a function on `A₂` (I1-c). The leaf is the pull-back of Lin–Yang's degree-one function to
  `ℍ`, with the branch labels of Baba–Granath. It is a consequence of the published statements.
  It is weaker than N5's use, since it says nothing about `ℚ`-structures.
- **Each CM clause is the published one.** Each clause names *all* fixed points of `ι(x)` for
  `x ∈ 𝒪` with the given minimal polynomial. These are the CM points of the maximal orders
  `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]`, and each set is a single `Γ*`-orbit. The argument: the signature of
  `Γ*` is `(0; 2, 4, 6)`. Elements of `𝒪` with `x² = −6` are normalizer elements of reduced norm
  6. The stabilizers of the order-4 and order-6 points contain only elements of reduced norm 1, 2
  and 1, 3 modulo squares, so a fixed point of such an `x` is the unique order-2 point.
  (SPECULATIVE as written; the elliptic-element enumeration is h-b1 M9.)
- **Numerical evidence (VERIFIED, `qm_embed.py`, 30 digits).** Invariance of `j_θ` under `ι(x)`
  for `x = i+j`, `(1+j)/2`, `μ`, `1+i+j` (nrd 2), `j` (nrd 3): errors `≤ 2·10⁻²⁸`. Under the
  non-torsion unit `(−15/2, −11/2, −3/2, 1/2)` of `𝒪¹`: `2·10⁻²¹` (theta series truncated at
  `|n_i| ≤ 30`). Values: `0` at `τ₋₄ = √2+i`; `|j_θ(i√3 + iε)| ≈ 2.05·10⁶, 2.50·10⁹, 1.76·10¹²`
  for `ε = 0.1, 0.03, 0.01` (order-6 pole in `τ`, so simple on the quotient, consistent with
  degree one); `−16/27` at `τ₋₂₄ = i√(9+6√2)`; `81/64` at the disc `−19` point (the value used by
  `igusa_check.py` as a cross-check of Lin–Yang).
- **Lean objects.** All exist: `QuaternionAlgebra`, `Matrix`, `GL (Fin 2) ℝ` acting on
  `UpperHalfPlane`, `tsum`, `OnePoint ℂ`, `Matrix.PosDef`. Defined here: `SiegelH2`,
  `thetaConst`, `evenChars` (`card = 10` by `decide`), `Omega`, `GammaStar`.

### I1-c. Igusa's theta modularity (F1: independence of the theta structure) — **statable, `ThetaModularity`**

- **Published statement.** `ψ₄ = 2⁻²Σ_{m even}θ_m⁸` and `χ₁₀ = −2⁻¹⁴∏_{m even}θ_m²` are Siegel
  modular forms of weight 4 and 10 for `Sp₄(ℤ)` (Igusa, Amer. J. Math. 84 (1962) and 89 (1967);
  theta transformation formula: Igusa, *Theta functions* (1972), Ch. V; all locators UNVERIFIED).
- **Formulation.** For `M = [[A,B],[C,D]] ∈ Matrix.symplecticGroup (Fin 2) ℤ` and `Ω ∈ 𝔥₂`:
  `Σθ⁸(M·Ω) = det(CΩ+D)⁴Σθ⁸(Ω)` and `∏θ²(M·Ω) = det(CΩ+D)¹⁰∏θ²(Ω)`. The exact signs were VERIFIED
  numerically (`theta_modular.py`): for `J`, two translations and two `diag(A, A⁻ᵀ)`, relative
  errors are `≤ 4·10⁻²⁵`, while `−det¹⁰` gives error 2.
- **Use.** Glue `thetaRatio_invariant` (proved): `jNum(MΩ)·jDen(Ω) = jNum(Ω)·jDen(MΩ)`. This is
  N5 L937-938, "permitted changes of theta structure permute coordinates and multiply them by roots
  of unity": the F1 value does not depend on the choice of `Ω_A`.

### I1-d. Baba–Granath / Lin–Yang: the Igusa vector of QM Jacobians (A7, alternative F1 route) — not statable today

- **Published statement.** Baba–Granath 2008, Thm 2.1 and §3, and Lin–Yang 2020, Ex. 30 with eqs.
  (13)-(14) (reading of task h-v14, through `igusa_check.py`). A principally polarized abelian
  surface over `ℚ̄` with N5's QM datum (`𝒪`, Rosati `x ↦ μ⁻¹x̄μ`), not lying over `j ∈ {0, ∞}`, is
  the Jacobian of a genus-2 curve `C` with
  `[J₂:J₄:J₆:J₁₀](C) = [12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]`, where `j` is the image of its
  moduli point in `X₆/W = P¹_j`.
- **Concrete part (statable, done).** Igusa invariants of sextics as explicit polynomials
  (`J2`, `J4`, `J6`, `J10` in `I1.lean` §9; 4, 18, 53 and 246 terms). The weighted vector
  `lyVec j` is defined there. The leaf `IgusaClebschSeparation` (I1-g) and the glue
  `equiv_of_lyVec` are proved from it.
- **Not statable:** "`End(Jac C) ⊇ 𝒪`" needs Jacobians of curves and their endomorphisms (absent).
- **Explicit genus-2 model over the curve: not obtained.** I tried a family recalled from
  Baba–Granath (`y² = (−4+3s)x⁶ + 6tx⁵ + 3t(28+9s)x⁴ − 40t²x³ + 3t²(28−9s)x² + 6t³x − t³(4+3s)`).
  Its exact Igusa invariants (computed with the `igusa_poly.py` polynomials; recorded in the log) meet Lin–Yang's vector only
  on the degenerate locus `J₂ = 0`. So the recollection is wrong (UNVERIFIED, not used). An explicit
  model would come from Mestre's algorithm over `ℚ(j)`, with a conic obstruction. It would make
  I1-d "Jac(C_j) has QM by `𝒪`", which is still not statable.
- **Note.** With I1-a, A7 does not need I1-d. The Hecke action in I1-a(2) fixes `A`, and the
  conjugates of `A` are the fibres over the `Gal`-conjugate points of one `Γ'`-orbit (h-trust A7,
  Remark). Likewise F1 follows from I1-a + I1-b + I1-c without Lin–Yang's Igusa vector. The
  vector enters only through `f1_algebra`, which is the arithmetic behind the constant
  `3779136`, and is not needed once I1-b is stated with `jNum/jDen`.

### I1-e. CM points: Shimura reciprocity, the structure of `CM(𝔬)`, Elkies' model (A10; A5's Lemma NV) — not statable today

- **Published statements** (as used in h-cm 4.1.3-4.1.4 and h-b1 Lemma NV):
  - (S) Shimura 1967, Main Theorem I: for a CM point `x ∈ X₆` with `End_𝒪(A_x) = 𝔬`, the order of
    conductor `f` in `K`, `K·ℚ(x) = K(f)` (the ring class field), and `σx = [𝔞_σ]⋆x` for
    `σ ∈ Gal(ℚ̄/K)`.
  - (JGR) Jordan, Harvard thesis 1981, §3; González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12
    and Prop. 5.6 (numbers of arXiv:math/0612732, VERIFIED by rv-h-cm; journal numbering
    UNVERIFIED): `|CM(𝔬)| = 2^b h(𝔬)`, and `W' × Pic(𝔬)` acts simply transitively.
  - (E) Elkies, ANTS-III, LNCS 1423 (1998), §3: `ℚ(X₆) = ℚ(t)(√−t, √(3(t−1)))`, `t = 1 + 27j/16`.
  - (Emb) Vignéras LNM 800, Ch. II §1, Ch. III §5; (RCF) Cox, §9.
- **Statable parts.** (Emb) and the optimal-embedding side of (JGR) are about orders in `B` and in
  imaginary quadratic fields; they can be stated with Mathlib's `QuaternionAlgebra` and
  `ClassGroup`. The CM points on `ℍ` are fixed points of `ι(x)`, as in I1-b. (S) and the
  `ℚ`-structure in (E) need the canonical model (I1-a) and class field theory (ring class fields,
  the Artin map), which Mathlib lacks.
- **Glue proved now:** `elkies_t` (`t(u) = H²/G⁶`), `elkies_t_sub_one` (`t(u) − 1 = −3(180F/G³)²`).
  Hence the fibre of `X₆ → X₆/W` over `t(u)` consists of `(±iH/G³, ±540iF/G³)` (h-cm Step 1).

### I1-f. Local normalizers (A3) — statable, not drafted

- **Published statement.** Vignéras LNM 800, Ch. II (locator UNVERIFIED): in the division
  quaternion algebra `B_p` over `ℚ_p`, `𝒪_p = {x : nrd x ∈ ℤ_p}` is the unique maximal order, so
  `N(𝒪_p) = B_p^*`, and `B_p^*/ℚ_p^*𝒪_p^*` has order 2 (generated by a uniformizer). At split `p`,
  `N_{GL₂(ℚ_p)}(M₂(ℤ_p)) = ℚ_p^*GL₂(ℤ_p)`.
- **Lean shape.** Over `QuaternionAlgebra ℚ_[p] 2 0 (−3)` for `p = 2, 3`, with `𝒪_p` given by
  coordinate conditions as in `InO`: "every invertible `x` normalizes `𝒪_p`, and
  `x ∈ ℚ_p^*𝒪_p^* ∪ ℚ_p^*π𝒪_p^*`". All objects exist (`Padic`, `QuaternionAlgebra`). It was not
  drafted, because A3 only needs the bound `|N/(𝔸_f^*K₀)| ≤ 4`, a citation of B-class bookkeeping.
  The count `|(𝒪/3𝒪)^*| = 72` is in `form_check.py` (h-trust A3).

### I1-g. Clebsch–Bolza–Igusa separation — **statable, `IgusaClebschSeparation`**

- **Published statement.** Over an algebraically closed field of characteristic 0, binary sextics
  `f, g` with nonzero discriminant are `GL₂ × 𝔾_m`-equivalent iff
  `J_{2k}(g) = r^k J_{2k}(f)` (`k = 1, 2, 3, 5`) for some `r ≠ 0`. Equivalently, two genus-2
  curves are isomorphic iff their Igusa invariants agree in `P(1,2,3,5)`. Igusa, Ann. of Math. 72
  (1960) §§1-2; Mestre 1991 (locators UNVERIFIED). STANDARD.
- **Formulation.** `I1.lean` §9: `J2 … J10 : (Fin 7 → K) → K` explicit; `sexticAct f M e` is
  `e·(cx+d)⁶f((ax+b)/(cx+d))` as a coefficient vector, through Mathlib's `Polynomial`.
  - Checks: interpolation on isobaric monomials agrees with PARI `genus2igusa` on 10 fresh random
    sextics; `J₁₀ = 2⁸·disc(f)`; the transformation law `J_{2k}(e·f|M) = (e·det³M)^{2k}J_{2k}(f)`
    holds on a sample (VERIFIED, `igusa_poly.py`).
  - `J10` is given in Lean as a list of its 246 monomials (a single 246-term expression hits
    the elaborator's recursion limit). Lean spot checks reproduce PARI's values for `x⁵ − 1`,
    `x⁶ + x + 1` and `x⁶ − 2x⁵ + x⁴ + 3x² − x + 2`: `norm_num` for `J₂, J₄, J₆`, and
    `decide +kernel` for `J₁₀`.
- **Use.** `equiv_of_lyVec` (proved): two sextics whose Igusa vectors are weighted multiples of
  `lyVec j`, `j ≠ 0`, are equivalent. This is A7's algebraic step, used together with I1-d.

## 3. Lean objects: what exists (VERIFIED by grep of `.lake/packages/mathlib`)

| Object | Mathlib v4.35.0 | Used in |
| --- | --- | --- |
| quaternion algebras `QuaternionAlgebra R c₁ c₂ c₃` (`i² = c₁ + c₂i`, `j² = c₃`) | yes, `Algebra/Quaternion` | §1, I1-b |
| `GL (Fin 2) ℝ` acting on `ℍ` | yes, `UpperHalfPlane.glAction` (`Analysis/Complex/UpperHalfPlane/MoebiusAction`) | I1-b |
| `Matrix.symplecticGroup`, block decomposition `toBlocks₁₁…` | yes | I1-c |
| `tsum`, `Complex.exp`, `Matrix.PosDef`, `OnePoint ℂ` | yes | I1-b, I1-c |
| `Polynomial.discr`, `resultant` | yes, `RingTheory/Polynomial/Resultant/Basic` | (not needed: `J10` explicit) |
| Siegel upper half-space, genus-2 theta constants, Siegel modular forms | no (defined here) | I1-b, I1-c |
| Igusa(–Clebsch) invariants, hyperelliptic curves, Jacobians | no (invariants defined here) | I1-d, I1-g |
| abelian varieties with `End`, polarizations, Rosati, `A[n]`, level structures | no | I1-a, I1-d |
| Shimura curves, canonical models, moduli of QM surfaces | no (Anthropic FLT: QM fake elliptic curves, unchecked) | I1-a |
| ring class fields, Artin map, Shimura reciprocity | no | I1-e |
| local quaternion orders over `ℚ_p` | definable (`Padic` + `QuaternionAlgebra`) | I1-f |

## 4. Glue in `I1.lean` (all proved; no `sorry`)

`#print axioms` for `gram_det`, `thetaRatio_invariant`, `f1_algebra`, `Ju_ne_branch`,
`elkies_t_sub_one` and `equiv_of_lyVec` gives `propext, Classical.choice, Quot.sound` (VERIFIED).
The whole file checks in about 20 s with `lake env lean`.

| Lean name | Statement | Step |
| --- | --- | --- |
| `gram_eq`, `gram_det` | `Trd(μ⁻¹ b_r b̄_s)` is N5's Gram matrix; det 1 | A1 |
| `mu_sq`, `mu_mul_muInv` | `μ² = −6`, `μ·(−μ/6) = 1` | A1 |
| `cm4`, `cm3`, `cm24` | `i+j`, `(1+j)/2`, `μ ∈ 𝒪` with `x² = −1`, `x² − x + 1 = 0`, `x² = −6` | A2 (non-vacuity of I1-b) |
| `card_evenChars` | ten even characteristics | F1 |
| `thetaRatio_invariant` | `ThetaModularity →` `Sp₄(ℤ)`-invariance of `jNum/jDen` | F1 |
| `f1_algebra`, `f1_constant` | Igusa vector + LNY conventions `⇒ j·Σ⁵ = 3779136·Π²` | F1 |
| `G6_sub_F2` | `G⁶ − 97200F² = H²` | A5 |
| `Gu_ne_zero`, `Ju_ne_zero` | `J(u)` finite, and nonzero for `u ∉ 𝒞` | A7 |
| `quad_ne_zero`, `Hu_ne_zero`, `Ju_add`, `Ju_ne_branch` | `J + 16/27 = 16H²/(27G⁶)`, `H(u) ≠ 0`, so `J(u) ≠ −16/27` | A5, A7 |
| `elkies_t`, `elkies_t_sub_one` | `1 + 27J/16 = H²/G⁶`, `27J/16 = −3(180F/G³)²` | A10 |
| `equiv_of_lyVec` | `IgusaClebschSeparation →` sextics with Igusa vector `∝ lyVec j` are equivalent | A7 |

Glue that is **not** provable today, because it is stated over I1-a's objects: A7 from the Hecke
action; F1 for the surface `A` (I1-a + I1-b + I1-c give (I1-out)(iv)); NoCM (h-cm 4.1.4) from
I1-e; Lemma PR(i) (h-b1) from I1-a, I1-e and SGA 1, a cluster of glue-descent.

## 5. Assessment

- **Leaves statable today and faithful:** I1-b (`QMHauptmodul`), I1-c (`ThetaModularity`), I1-g
  (`IgusaClebschSeparation`); I1-f could be added. These are concrete. A crowd-sourced
  formalization of I1-c and I1-g is classical analysis and invariant theory (SPECULATIVE
  estimate: I1-c needs the theta transformation formula in genus 2, a few thousand lines; I1-g
  needs the first fundamental theorem for binary sextics, a large but finite computation).
- **I1-b is the most valuable new leaf.** It pins down Baba–Granath's `j` and the F1 constant by a
  checkable statement about explicit holomorphic functions on `ℍ`. Its proof from the literature
  is Lin–Yang's divisor computation, which uses Hashimoto's or Rotger's modular embedding and the
  structure of Humbert surfaces. Formalizing it from scratch would be very large (SPECULATIVE).
- **The biggest obstacle is I1-a.** The rest of H's proof needs the surface `A/K` and its
  arithmetic (field of definition, level-3 structure, Galois conjugates). Only the canonical
  model, as a moduli scheme over `ℚ` with its complex uniformization, connects that surface to
  I1-b. Stating I1-a needs abelian schemes with PEL structure, the same missing objects that
  block I2-I5 (wk-h §5). Once those exist, I1-a(1)-(2) is the single further theorem. I1-b and
  I1-c then make F1 a short glue argument, and A7 follows from I1-a(2) without I1-d.
- **Alternative (SPECULATIVE).** Replace the Shimura curve by an explicit genus-2 family over a
  cover of `P¹_j` (Baba–Granath, Hashimoto–Murabayashi). I1-a then becomes "Jac(C_j) has QM by
  `𝒪`" plus a direct computation of the field of definition of `C_j` and of `Jac(C_j)[3]`. It
  redesigns A5-A6 (good reduction from a discriminant instead of from the level-3 moduli), and it
  still needs Jacobians with endomorphisms. It is not a leaf formulation of N5's argument.
