# t28-igusa: textbook leaf T28 (Clebsch–Bolza–Igusa separation): the `⇒` half, and `⇐` reduced to M3 and the special locus

Status: research note (task t28-igusa, 2026-11-12). Lean: `scratch/t28-igusa/Igusa.lean`
(everything; self-contained, `import Mathlib` only; check with
`lake env lean scratch/t28-igusa/Igusa.lean`, about 10 minutes, most of it the `ring` proofs of
M3); `Forward.lean` and `SO3.lean` are its first two parts as separately compiled drafts.
Results log: `scratch/t28-igusa/log.md`. Computer algebra (`~/pyenv/bin/python -I`, from the repo
root): `mestre_check.py`, `m3_interp.py` (writes `m3_polys.txt`), `special_check.py`,
`pairing_check.py`, `so3_coeffs.py`; Lean generators `gen.py`, `gen_m3.py`, `gen_m3proofs.py`.
No file under `ZInQKernel/`, `blueprint/` or another task's notes was edited.

Marks: **VERIFIED** (compiled, computed, or read in a named source), **STANDARD** (published,
reference given), **SPECULATIVE**; theorem numbers given from memory are **UNVERIFIED**.

## 0. Result

The leaf `PkgI1.IgusaClebschSeparation` (copied verbatim, with `J2 J4 J6 j10Data J10
sexticAct`, from `scratch/h-decomposition/Leaves.lean` L423-784) is an `↔`. In
`scratch/t28-igusa/Igusa.lean` (sorry-free; `#print axioms` gives only `propext`,
`Classical.choice`, `Quot.sound` for every theorem below) this task proves:

1. **the `⇒` direction** (the transformation law), over every field of characteristic 0:
   `PkgI1.igusa_forward`, from `J{2,4,6,10}_sexticAct :
   J_{2k}(sexticAct f M e) = (e·det M³)^{2k}·J_{2k}(f)` for `det M ≠ 0`;
2. **`igusaClebschSeparation_iff : IgusaClebschSeparation ↔ IgusaSeparationEq`**, where
   `IgusaSeparationEq` is the `⇐` content with the weighted scaling removed (`J10 ≠ 0` and
   **equal** `J2, J4, J6, J10` ⇒ equivalent);
3. **the `SO(3) = PGL(2)` lemma** `T28SO3.so3`: two bases of binary quadratics with the same
   Gram matrix for the discriminant pairing differ by one invertible substitution;
4. **Mestre's separation step in abstract form** `PkgI1.mestre_abstract`: if sextics `f, g`
   admit bases `(yᵢ)`, `(y'ᵢ)` of binary quadratics with equal Gram matrices and
   `p6 g (y'ᵢy'ⱼy'ₖ) = p6 f (yᵢyⱼyₖ)` for all `i, j, k` (`p6` the invariant pairing of sextics),
   then `g ≅ f`. The proof needs no reconstruction identity: `so3` gives the substitution, and
   products of three basis quadratics span the sextics, on which `p6` is nondegenerate;
5. **the generic case of `⇐`** `PkgI1.separation_generic`, from one explicit, computer-checked
   Prop `M3Identities` (half of it proved in Lean, see below) (the Gram matrix of Clebsch's quadratic covariants
   `y₁, y₂, y₃` and the ten numbers `p6 f (yᵢyⱼyₖ)` are fixed polynomials in `J₂, J₄, J₆, J₁₀`,
   written out in Lean as `gramJ`, `cubJ`): when `det (yv f) ≠ 0`, equal invariants give
   equivalent sextics;
6. **`igusaClebschSeparation_of : M3Identities → SeparationSpecial → IgusaClebschSeparation`**,
   where `SeparationSpecial` is the `⇐` statement restricted to `det (yv f) = 0` (Clebsch's
   `R = 0`: the curves with an involution besides the hyperelliptic one).

So **T28 is reduced to two concrete statements over genuine definitions**: `M3Identities`
(sixteen polynomial identities in `a₀..a₆`, degrees 6 to 22; true by computer algebra: found by
interpolation on 45 random sextics and checked on 15 fresh ones, and spot-checked in Lean by
`norm_num` for the two largest entries on one sextic; **eight of the sixteen are
proved in Lean by `ring`**: all six Gram entries `G₁₁ G₁₂ G₁₃ G₂₂ G₂₃ G₃₃` and `a₁₁₁`, `a₁₁₂`) and `SeparationSpecial` (Bolza 1888,
Cardona–Quer 2005; unproved, the hard part being "`R = 0` ⇒ extra involution"). Neither is a
literature leaf in the project's sense: M3 is glue (a finite computation) and
`SeparationSpecial` is a special case of T28 itself. Verdict: T28 is **not closed**; its `⇒`
half, the scaling, the geometric step and the generic case are done modulo M3.

## 1. What compiles (VERIFIED, `lake env lean`, full file 8m47 with no errors)

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

Namespace `T28SO3` (also `SO3.lean`): `qAct`, `pair` (polar form of `−disc`), `pair_qAct`
(`pair` scales by `det²`), `null_sq` (a null vector is a square), `frame` (a hyperbolic frame
`u, z, v` is the image of `1, x, x²`), `so3`.

Mestre part (namespace `PkgI1`):

| Lean name | Statement |
| --- | --- |
| `p6`, `p6_actC` | invariant pairing of sextics, `p6(f\|M, g\|M) = det⁶·p6(f, g)` (`ring`) |
| `cub`, `cub_qAct` | product of three quadratics; equivariant |
| `p6_cub_lin`, `eq_zero_of_p6_cub` | trilinearity; `p6 h (yᵢyⱼyₖ) = 0 ∀ i j k` with `(yᵢ)` a basis ⇒ `h = 0` |
| `det_ne_zero_of_gram` | equal Gram matrices: one basis ⇒ the other is a basis (`det Pm = 4`) |
| `mestre_abstract` | item 4 of §0 |
| `y1c0 … y3c2`, `yv` | Clebsch's `y₁, y₂, y₃` as explicit polynomials (8, 29-31, 86 terms per coefficient) |
| `m3G11 … m3a333`, `gramJ`, `cubJ` | the M3 polynomials in `J₂, J₄, J₆, J₁₀` |
| `M3Identities`, `separation_generic` | item 5 |
| `SeparationSpecial`, `igusaClebschSeparation_of` | item 6 |
| `spot_J` and two `example`s | M3 for `G₃₃` and `a₃₃₃` on `2 − x + 3x² + x⁴ − 2x⁵ + x⁶` (`norm_num`) |
| `m3_G11` … | the M3 identities proved by `ring` (all six Gram entries `G₁₁ G₁₂ G₁₃ G₂₂ G₂₃ G₃₃` and `a₁₁₁`, `a₁₁₂`) |

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

Mestre's argument for the generic case, in the form proved here (`mestre_abstract`): after
scaling, `f` and `g` have equal `J`'s, hence (M3) the Gram matrices of `y(f)` and `y(g)` agree
and `p6 g (yᵢyⱼyₖ(g)) = p6 f (yᵢyⱼyₖ(f))`; `so3` gives `M` with `yᵢ(g) = yᵢ(f)|M`; then
`h = g − det(M)⁻⁶·(f|M)` pairs to zero with every `yᵢyⱼyₖ(g)`, these span the sextics, and `p6` is
nondegenerate, so `h = 0`. Mestre's conic and cubic (the reconstruction identity checked in §3)
are not needed for separation; they matter only for constructing a curve from given invariants.

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

## 4. What remains (unproved)

R1. **`M3Identities`** (glue, a finite computation). Sixteen polynomial identities in
    `a₀..a₆` of degrees 6 (`G₁₁`) to 22 (`a₃₃₃`); eight are proved by `ring`
    (all six Gram entries `G₁₁ G₁₂ G₁₃ G₂₂ G₂₃ G₃₃` and `a₁₁₁`, `a₁₁₂`). A batch adding `a₁₁₃` and `a₁₂₂` did not finish within 10 minutes, and `a₁₁₃` alone reached 27 GB after 11 minutes (stopped). The eight left are `a₁₁₃ a₁₂₂ a₁₂₃ a₁₃₃ a₂₂₂ a₂₂₃ a₂₃₃ a₃₃₃`. Direct `ring` in seven variables does not scale to the top
    degrees (`a₃₃₃` expands to about `7·86³ ≈ 4.5·10⁶` monomial products). Workable plans: (a) prove covariance of `yv` by the generator
    technique of the `⇒` part (`IsInv`: diagonal and swap by `ring`, translations by the
    derivation trick with the `D`-equivariance identity of each `yᵢ`), so that both sides are
    invariants of the same weight, then check on the normal form `x(x−1)(x³+px²+qx+r)` (three
    variables) and transport using `J10 ≠ 0`; or (b) a verified sparse-polynomial normalizer
    run by the kernel. Either is mechanical. The coefficients are in `m3_polys.txt`.
R2. **`SeparationSpecial`** (the curves with an extra involution). Ingredients: Bolza's
    characterization `R = 0` ⇔ an involution besides the hyperelliptic one (this task checked
    by computer algebra that `det yv = 0` on `x⁶ + px⁴ + qx² + 1` and on `x⁵ + px³ + qx`, the
    easy direction); the hard direction `det yv = 0` ⇒ `f ≅` an even sextic has no short proof
    known to this task (classically via Clebsch's `R = ∏` over the 15 factorizations `f = q₁q₂q₃`
    of `det(q₁,q₂,q₃)`); then separation inside the 2-parameter family by the dihedral
    invariants and the strata `D₄`, `D₆`, `x⁵ − x`, `x⁶ − 1`, `x⁵ − 1` (Cardona–Quer 2005,
    UNVERIFIED locator). This is the least explored piece and the main open part of T28.

Recommendation for the crowd-sourcing list: replace T28 by `SeparationSpecial` (the `⇐` half
of the published theorem restricted to the locus `det yv = 0`, hence a consequence of it) plus
the glue item `M3Identities` (eight identities left). Any proof of `SeparationSpecial` will do;
Bolza's characterization is only the classical route.

References (STANDARD; locators UNVERIFIED, no network): J.-I. Igusa, *Arithmetic variety of
moduli for genus two*, Ann. of Math. 72 (1960) 612-649; J.-F. Mestre, *Construction de courbes
de genre 2 à partir de leurs modules*, in *Effective methods in algebraic geometry*, Progr. Math.
94 (1991) 313-334; G. Cardona, J. Quer, *Field of moduli and field of definition for curves of
genus 2*, in *Computational aspects of algebraic curves* (2005) 71-83; O. Bolza, *On binary
sextics with linear transformations into themselves*, Amer. J. Math. 10 (1888) 47-70.
