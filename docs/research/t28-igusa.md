# t28-igusa: textbook leaf T28 (Clebsch–Bolza–Igusa separation), plan and first half

Status: research note (task t28-igusa, 2026-11-12). Lean: `scratch/t28-igusa/Igusa.lean` and
`scratch/t28-igusa/SO3.lean` (each self-contained, `import Mathlib` only; check with
`lake env lean scratch/t28-igusa/<file>.lean`). Results log: `scratch/t28-igusa/log.md`.
Computer algebra: `scratch/t28-igusa/mestre_check.py`, `gen.py`, `so3_coeffs.py`.
No file under `ZInQKernel/`, `blueprint/` or another task's notes was edited.

Marks: **VERIFIED** (compiled, computed, or read in a named source), **STANDARD** (published,
reference given), **SPECULATIVE**; theorem numbers given from memory are **UNVERIFIED**.

## 0. Result

The leaf `PkgI1.IgusaClebschSeparation` (copied verbatim, with `J2 J4 J6 j10Data J10
sexticAct`, from `scratch/h-decomposition/Leaves.lean` L423-784) is an `↔`. This task

1. **proves the `⇒` direction** (the transformation law) in Lean, over every field of
   characteristic 0, sorry-free (`PkgI1.igusa_forward`, with
   `J{2,4,6,10}_sexticAct : J_{2k}(sexticAct f M e) = (e·det M³)^{2k}·J_{2k}(f)` for `det M ≠ 0`);
2. **proves** `IgusaClebschSeparation ↔ IgusaSeparationEq` (`PkgI1.igusaClebschSeparation_iff`),
   where `IgusaSeparationEq` is the `⇐` content alone with the weighted scaling removed: sextics
   over an algebraically closed field of characteristic 0 with `J10 ≠ 0` and **equal**
   `J2, J4, J6, J10` are `GL₂ × 𝔾_m`-equivalent. So T28 can be replaced in the leaf list by the
   strictly smaller `IgusaSeparationEq`;
3. **chooses Mestre's reconstruction as the route for `⇐`** (§2), checks its polynomial
   identities by computer algebra (§3: the conic and the cubic identity hold with constant
   exactly 1 on random sextics; the leaf's `J`'s in terms of Clebsch's `A, B, C, D`), and
   **proves in Lean its one geometric step**, `T28SO3.so3` (`SO(3) = PGL(2)` for binary
   quadratics: two bases of binary quadratics with the same Gram matrix for the discriminant
   pairing differ by one invertible substitution), sorry-free;
4. lists what remains (§4): the generic case `det G ≠ 0` needs the quadratic covariants
   `y₁, y₂, y₃` as Lean polynomials, their covariance (same technique as item 1), and the
   expression of the Gram matrix `G_ij` and of `a_ijk` through `J2..J10` (computer algebra
   finds them; verifying them in Lean is the bulk); the special case `det G = 0` (curves with an
   extra involution, Bolza; Cardona–Quer) is a separate, case-heavy argument.

T28 is **not** closed. Verdict: the `⇒` half and the scaling are done; the `⇐` half is a
substantial but elementary formalization (no geometric invariant theory needed on Mestre's route).

## 1. What compiles (VERIFIED, `lake env lean`)

`scratch/t28-igusa/Igusa.lean` (namespace `PkgI1`; definitions verbatim):

| Lean name | Statement |
| --- | --- |
| `J2R J4R J6R J10R` (`J10R0..J10R9`) | the same polynomials over any `CommRing` (`J10R` split in 10 chunks: one 246-term expression times out in elaboration) |
| `J2_eq … J6_eq` (`rfl`), `J10_eq` | `J10 a = J10R a` (unfolds the 246-entry list) |
| `actC`, `sexticAct_eq` | explicit coefficients of `e·(cx+d)⁶ f((ax+b)/(cx+d))`; `sexticAct f M e = actC f M₀₀ M₀₁ M₁₀ M₁₁ e` |
| `actC_actC` | cocycle: acting by `M` then `N` is acting by `M·N` (factor `e·e'`) |
| `trP`, `trP_d0..d6`, `trP_eval` | the coefficients of `f(x + t)` as polynomials in `t`, `d/dt Tᵢ = (i+1)Tᵢ₊₁` |
| `JnR_map` | ring homomorphisms commute with `JnR` |
| `JnR_homog`, `JnR_diag`, `JnR_swap` | `J(e·v) = eⁿJ(v)`; `J(v(s x)·t⁶…) = (st)^{3n}J(v)`; `J(x⁶v(1/x)) = J(v)` (`ring`) |
| `JnR_deriv` | for `t : Fin 7 → K[X]` with `tᵢ' = (i+1)tᵢ₊₁`: `(J t)' = 0` (`ring` after the chain rule) |
| `JnR_trans` | `J(v(x+b)) = J(v)` in characteristic 0 (from `JnR_deriv`, `eq_C_of_derivative_eq_zero`) |
| `IsInv`, `Good`, `Good.mul`, `IsInv.good` | Bruhat decomposition: every invertible `M` is a product of `diag`, `[[0,1],[1,0]]`, `[[1,u],[0,1]]` |
| `IsInv.sexticAct`, `J{2,4,6,10}_sexticAct` | the transformation law for `det M ≠ 0` |
| `igusa_forward` | the `⇒` direction of the leaf |
| `IgusaSeparationEq`, `igusaClebschSeparation_iff` | the leaf is equivalent to its exact-equality `⇐` form |

`scratch/t28-igusa/SO3.lean` (namespace `T28SO3`): `qAct`, `pair` (polar form of `−disc`),
`pair_qAct` (`pair` scales by `det²`), `null_sq` (a null vector is a square), `frame` (a
hyperbolic frame `u, z, v` is the image of `1, x, x²`), `so3`.

The proof of the translation law is the classical infinitesimal argument made algebraic: for
`T(t) =` coefficients of `f(x+t)`, `d/dt J(T(t)) = (DJ)(T(t))` with
`D = Σ (i+1) aᵢ₊₁ ∂/∂aᵢ`, and `DJ = 0` is a `ring` identity of degree `n` with no product of
sums (for `J10`: about 1700 monomials). Directly expanding `J10(f(x+1))` is out of reach for
`ring` (246 products of ten 7-term sums).

## 2. Route for `⇐`: comparison

| Route | Inputs to formalize | Assessment |
| --- | --- | --- |
| Igusa 1960 (GIT) | Reynolds operator for `SL₂` (Cayley Ω-process), Hilbert–Mumford: disc ≠ 0 ⇒ stable ⇒ closed orbit, separation of closed orbits by invariants (Nullstellensatz), and generation of the invariant ring by `J2..J10, J15` (Clebsch–Gordan, Hilbert series) | longest: the generation statement alone is a large computation, and `SL₂` reductivity is not in Mathlib |
| Rosenhain / Galois | normal form `x(x−1)(x−λ)(x−μ)(x−ν)`, then the fibres of `(λ,μ,ν) ↦ [J]` are the `S₆`-orbits (degree 720) | the pointwise fibre statement needs elimination of degree 720; not practical |
| **Mestre 1991 + Cardona–Quer 2005** | Clebsch quadratic covariants `y₁, y₂, y₃`; Gram `G_ij = (y_i,y_j)₂` and `a_ijk = (f, y_iy_jy_k)₆` as polynomials in the invariants; reconstruction `det(G)³f = Σ a_ijk (adj G·y)_i(adj G·y)_j(adj G·y)_k`; the `SO(3)` lemma; the locus `det G = 0` (extra involution) separately | **chosen**: constructive, every step is an explicit identity or linear algebra; the identities are checkable by computer algebra |

Mestre's argument for `det G(f) ≠ 0` (generic case), in the form proved here piecewise:
(i) after scaling (item 2 of §0) `f` and `g` have equal `J`'s, hence equal `G` and `a`
(identities M3 below); (ii) `y(f)` and `y(g)` are bases of binary quadratics with equal Gram
matrices, so `so3` gives `M` with `y_i(g) = y_i(f)|M`, and by covariance `y_i(f)|M = c·y_i(f|M)`;
(iii) the reconstruction identity writes `f|M` and `g` by the same cubic formula in their `y`'s
and the common invariants, so `g ∝ f|M`. Step (iii) has a short conceptual proof that avoids
expanding a degree-90 identity: `f(t) ∝ (f, ℓ_t⁶)₆` for `ℓ_t = x − t`, `ℓ_t⁶ = (ℓ_t²)³`,
`ℓ_t² = Σ (G⁻¹Y)_i y_i` with `Y_j = (ℓ_t², y_j)₂ ∝ y_j(t)`, and multilinearity of transvectants.

## 3. Computer algebra (VERIFIED by running `mestre_check.py`, exact arithmetic)

Transvectants `(φ,ψ)_k = (m−k)!(n−k)!/(m!n!) Σ_j (−1)^j C(k,j) ∂^kφ/∂x^{k−j}∂z^j · ∂^kψ/∂x^j∂z^{k−j}`;
`i = (f,f)₄`, `Δ = (i,i)₂`, `y₁ = (f,i)₄`, `y₂ = (i,y₁)₂`, `y₃ = (i,y₂)₂`;
`A = (f,f)₆`, `B = (i,i)₄`, `C = (i,Δ)₄`, `D = (y₃,y₁)₂`.

- Conic identity `Σ adj(G)_ij y_i y_j ≡ 0` and reconstruction identity
  `det(G)³·f ≡ Σ_{i,j,k} a_ijk (adj G·y)_i (adj G·y)_j (adj G·y)_k` (constant exactly 1): 8 random
  integer sextics.
- `A, B, C, D`, every `G_ij` and `a_ijk` scale by a power of `det M` under `f ↦ f∘M` (weights of
  `A..D`: 6, 12, 18, 30 in `det`): one random `M`.
- The leaf's normalization (PARI `genus2igusa`): `J2 = −240A`, `J4 = 4320A² − 18000B`,
  `J6 = 34560A³ − 432000AB − 1440000C`,
  `J10 = −15925248A⁵ + 248832000A³B + 414720000A²C − 777600000AB² − 1555200000BC − 1166400000D`
  (interpolated on 30 sextics, checked on 10 fresh ones). The system is triangular, so equal
  `J`'s give equal `A, B, C, D`.
- `so3_coeffs.py`: the `linear_combination` certificates used in `T28SO3.frame`.

## 4. What remains for `IgusaSeparationEq` (unproved)

M1. Transvectants on coefficient vectors; `y₁, y₂, y₃`, `G_ij`, `a_ijk` as explicit Lean
    polynomials (generated by `gen.py`-style scripts; `y₃` has degree 7 in `a₀..a₆`).
M2. Covariance `y_i(f|M) = det(M)^{w_i}·(y_i(f))|M` and invariance of `G_ij`, `a_ijk`: the
    generator technique of `Igusa.lean` (`IsInv`) extends to covariants; the translation step
    needs the `D`-equivariance identity of each `y_i` (`ring`, moderate size).
M3. `G_ij` and `a_ijk` as polynomials in `A, B, C, D` (equivalently in `J2..J10`; all have even
    degree, up to 22 for `a₃₃₃`). Computer algebra finds them (Mestre's paper lists them,
    UNVERIFIED). In Lean, direct `ring` in seven variables is likely too large; a workable plan is
    to check both sides (invariants of equal weight) on the normal form
    `x(x−1)(x³+px²+qx+r)` (three variables) and transport by M2 and `J10 ≠ 0`.
M4. The reconstruction identity via the conceptual proof of §2(iii): small transvectant
    identities `(φ, ℓ_t^n)_n ∝ φ(t)`, bilinearity, and `G⁻¹`.
M5. The case `det G = 0`: Bolza's characterization (`det G = 0` iff the curve has an involution
    besides the hyperelliptic one), the normal forms `x⁶ + ax⁴ + bx² + 1` (and the `D₄`, `D₆`,
    `x⁵ − x`, `x⁵ − 1` loci), and the invariants of each normal form (Cardona–Quer 2005,
    UNVERIFIED locator). This is the least explored piece; its hard direction
    (`det G = 0` ⇒ extra involution) has no short proof known to this task.

References (STANDARD; locators UNVERIFIED, no network): J.-I. Igusa, *Arithmetic variety of
moduli for genus two*, Ann. of Math. 72 (1960) 612-649; J.-F. Mestre, *Construction de courbes
de genre 2 à partir de leurs modules*, in *Effective methods in algebraic geometry*, Progr. Math.
94 (1991) 313-334; G. Cardona, J. Quer, *Field of moduli and field of definition for curves of
genus 2*, in *Computational aspects of algebraic curves* (2005) 71-83; O. Bolza, *On binary
sextics with linear transformations into themselves*, Amer. J. Math. 10 (1888) 47-70.
