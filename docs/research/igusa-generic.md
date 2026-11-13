# igusa-generic: textbook leaf T28 on the generic locus (Mestre's separation), proved

Status: research note (task igusa-generic, 2026-11-13). Lean: three new files under
`ZInQKernel/Contrib/T28/` (`Generic.lean`, `Covariance.lean`, `Mestre.lean`). Results log:
`scratch/igusa-generic/log.md`. No existing file was edited.

Marks: **VERIFIED** (compiled, computed, or read in a named source), **STANDARD** (published,
reference given), **SPECULATIVE**. Theorem numbers given from memory are **UNVERIFIED**.

## 0. Main result (VERIFIED: `lake build ZInQKernel.Contrib.T28.Mestre`, no errors)

```lean
-- ZInQKernel/Contrib/T28/Generic.lean
def T28.GenericLocus {L : Type*} [Field L] (f : Fin 7 → L) : Prop :=
  (Matrix.of (yv f)).det ≠ 0
def T28.SeparationGeneric : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharZero L] (f g : Fin 7 → L),
    J10 f ≠ 0 → J10 g ≠ 0 → GenericLocus f →
      J2 g = J2 f → J4 g = J4 f → J6 g = J6 f → J10 g = J10 f →
        ∃ M : Matrix (Fin 2) (Fin 2) L, M.det ≠ 0 ∧ ∃ e : L, e ≠ 0 ∧ g = sexticAct f M e

-- ZInQKernel/Contrib/T28/Mestre.lean
theorem T28.separationGeneric : T28.SeparationGeneric
theorem T28.igusaClebschSeparation_of_bothSpecial (hS : SeparationBothSpecial) :
    IgusaClebschSeparation
theorem T28.igusaClebschSeparation_of_specialLocus (hS : SeparationSpecialLocus) :
    IgusaClebschSeparation
```

`yv f` are Clebsch's quadratic covariants `y₁ = (f,i)₄`, `y₂ = (i,y₁)₂`, `y₃ = (i,y₂)₂`,
`i = (f,f)₄` (`PkgI1.yv`, task t28-igusa); `IgusaClebschSeparation` is the leaf T28 verbatim
(`PkgI1.IgusaClebschSeparation`). So **T28 is now reduced to the special locus alone**:
`SeparationSpecialLocus` (equal invariants, `J₁₀ ≠ 0`, `det (yv f) = 0` ⇒ equivalent), or
equivalently (`T28.separationBothSpecial_iff`, proved) `SeparationBothSpecial` (both
`det (yv f) = 0` and `det (yv g) = 0`), which task igusa-special proves.

`#print axioms` (`scratch/igusa-generic/axioms.lean`, output in `axioms.out`), VERIFIED:

```
'T28.separationGeneric' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28.m3Identities_of_J10' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28.igusaClebschSeparation_of_specialLocus' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28.igusaClebschSeparation_of_bothSpecial' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28.yvCovariance' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28.det_yv_sexticAct' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28.igusaSeparationEq_of_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28.igusaSeparationEq_of_generic_bothSpecial' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28.genericLocus_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28.separationBothSpecial_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 1. Declarations (all VERIFIED compiled)

`Generic.lean` (statements and the split, agreed with igusa-special by message, 2026-11-13):

| Lean name | Statement |
| --- | --- |
| `GenericLocus f` | `det (Matrix.of (yv f)) ≠ 0` |
| `SeparationGeneric` | §0 |
| `SeparationSpecialLocus` | as `SeparationGeneric` with `¬ GenericLocus f`; `separationSpecialLocus_iff : … ↔ PkgI1.SeparationSpecial` |
| `SeparationBothSpecial` | igusa-special's form: `J10 f ≠ 0 → J10 g ≠ 0 → det (yv f) = 0 → det (yv g) = 0 → J2 g = J2 f → J4 g = J4 f → J6 g = J6 f → J10 g = J10 f → ∃ M, M.det ≠ 0 ∧ ∃ e, e ≠ 0 ∧ g = sexticAct f M e` |
| `sexticAct_symm` | `g = sexticAct f M e` (`det M ≠ 0`, `e ≠ 0`) ⇒ `f = sexticAct g M' e'` |
| `igusaSeparationEq_of_split`, `igusaSeparationEq_of_generic_bothSpecial` | the halves give `PkgI1.IgusaSeparationEq` |
| `igusaClebschSeparation_of_split`, `…_of_generic_bothSpecial` | the halves give the leaf T28 |
| `YvCovariance` | `∀ L [Field L] [CharZero L] f a b c d e, a*d - b*c ≠ 0 → ∀ i, yv (actC f a b c d e) i = fun l => e ^ (![3,5,7] i) * (a*d - b*c) ^ (![8,14,20] i) * qAct (yv f i) a b c d l` |

`Covariance.lean`:

| Lean name | Statement / proof |
| --- | --- |
| `z{n}c{k}` | integer-coefficient copies `Nₙ·yₙcₖ` over any `CommRing` (`N = 2250, 168750, 12656250`) |
| `y{n}c{k}_eq` | `y{n}c{k} a = z{n}c{k} a / Nₙ` (`ring`) |
| `z{n}c{k}_map`, `z{n}c{k}_deriv` | ring homs commute; with `tᵢ' = (i+1)tᵢ₊₁`: `(zₙc₀ t)' = zₙc₁ t`, `(zₙc₁ t)' = 2 zₙc₂ t`, `(zₙc₂ t)' = 0` |
| `ode3` | `P₀' = P₁, P₁' = 2P₂, P₂' = 0` ⇒ `P(b)` is the translate of `P(0)` (char 0) |
| `z{n}_trans`, `yv_trans` | `yv (actC v 1 b 0 1 1) i = qAct (yv v i) 1 b 0 1` |
| `yv_swap`, `yv_diag`, `yv_homog` | swap, diagonal matrices, scaling (`ring`) |
| `CovGood`, `CovGood.mul`, `covGood` | Bruhat decomposition, as `PkgI1.IsInv.good` |
| `yv_actC`, **`yvCovariance : YvCovariance`** | covariance for every invertible matrix and `e` |
| `det_yv_actC`, `det_yv_sexticAct` | `det (yv (sexticAct f M e)) = e^15 · det M^45 · det (yv f)` |

`Mestre.lean`:

| Lean name | Statement / proof |
| --- | --- |
| `nf p q r s` | `![s, r, q, p, 0, 1, 0]` = `x⁵ + px³ + qx² + rx + s` |
| `yv_nf0..2`, `J2_nf … J10_nf` | explicit values on the normal form |
| `nf_G11 … nf_G33`, `nf_a111 … nf_a333` | the 16 identities M3 on the normal form (`ring` in `p,q,r,s`) |
| `M3At f` | the identities M3 at `f` (Gram matrix = `gramJ (J f)`, `p6 f (yᵢyⱼyₖ) = cubJ (J f)`) |
| `m3At_nf` | `M3At (nf p q r s)` |
| `m3At_of_trans`, `m3At_of_swap`, `m3At_of_scale` | `M3At` descends along translations, `x ↦ 1/x`, scalings |
| `gramJ_homog`, `cubJ_homog` | weighted homogeneity of the M3 polynomials |
| `J10_of_top` | `f 5 = 0 → f 6 = 0 → J10 f = 0` |
| `m3At_of_top`, `m3At_of_J10` | `J10 f ≠ 0 ⇒ M3At f` over an algebraically closed field of char 0 |
| `m3Identities_of_J10` | the conclusion of `PkgI1.M3Identities` at every `f` with `J10 f ≠ 0`, `L` algebraically closed |
| **`separationGeneric`** | §0, from `m3At_of_J10` and `PkgI1.mestre_abstract` |
| `genericLocus_iff_gramJ` | `J10 f ≠ 0 ⇒ (GenericLocus f ↔ det gramJ(J₂ f, …, J₁₀ f) ≠ 0)` (the locus is cut out by the invariants) |
| `genericLocus_congr`, `separationBothSpecial_iff` | equal invariants ⇒ both generic or both special; hence `SeparationBothSpecial ↔ SeparationSpecialLocus` |

## 2. Proof

Mestre's step (`PkgI1.mestre_abstract`, t28-igusa): if `f, g` have quadratic covariant bases with
the same Gram matrix and the same numbers `p6 (yᵢyⱼyₖ)`, then `g ≅ f` (`SO(3) = PGL(2)` and
nondegeneracy of `p6` on the span of the `yᵢyⱼyₖ`). What was missing were the identities M3:
these numbers are fixed polynomials in `J₂, J₄, J₆, J₁₀`. Eight of the sixteen were proved by
`ring` in 7 variables in task t28-igusa; the others (degree up to 22) do not fit `ring` there.

Here M3 is proved for every `f` with `J₁₀ f ≠ 0` over an algebraically closed field `L` of
characteristic 0 by reduction to a normal form:

1. **Covariance of `yv`** under translations by the derivation trick: with `D = Σ (i+1)aᵢ₊₁∂/∂aᵢ`
   one has `D yₙc₀ = yₙc₁`, `D yₙc₁ = 2yₙc₂`, `D yₙc₂ = 0` (degree ≤ 7, `ring`); over `L[X]`
   the coefficients of `yₙ(f(x+X))` solve the same ODE as those of `yₙ(f)(x+X)`. The
   `y`'s are defined over fields, so integer copies `zₙcₖ` over any commutative ring are used.
   Swap and scaling are direct `ring` identities.
2. **Invariance of M3**: by `pair_qAct`, `cub_qAct`, `p6_actC` and the transformation of
   `J₂…J₁₀`, `M3At (actC f 1 b 0 1 1) → M3At f`, `M3At (actC f 0 1 1 0 1) → M3At f`, and
   `M3At (e·f) → M3At f` (`e ≠ 0`, weighted homogeneity of the M3 polynomials).
3. **Normal form**: if `f₆ ≠ 0` take a root `α` of `f` (`IsAlgClosed.exists_root`), translate by
   `α` and swap, so `f₆ = 0`; then `f₅ ≠ 0` (`J10_of_top`), translate by `−f₄/(5f₅)` to kill
   `f₄`, scale by `f₅⁻¹`: the result is `nf p q r s`.
4. **M3 on the normal form**: in 4 variables the covariants are tiny (`y₃` has ≤ 11 terms per
   coefficient, `a₃₃₃` 134 terms against 86-term coefficients in 7 variables), and all 16
   identities close by `ring` in under a minute together.

## 3. Computations (VERIFIED, pure python3, exact rationals)

The host has no sympy/PARI (`~/pyenv` does not exist), so `scratch/igusa-generic/poly.py` is a
small sparse-polynomial library that parses the Lean definitions of `yₙcₖ`, `J₂…J₁₀` and the
M3 polynomials. `cov_check.py`: covariance of `yv` on 5 random `(f, M, e)`. `nf_check.py`: the
D-identities (7 variables, symbolic), translation invariance of `J₂…J₁₀`, the 16 M3 identities
on the normal form (symbolic), the denominators `Nₙ`. Generators: `gen_cov.py`, `gen_cov2.py`
(Covariance.lean), `gen_nf.py` (Mestre.lean).

## 4. What remains for T28: nothing (with igusa-special)

Task igusa-special proved `T28Special.separationBothSpecial : T28.SeparationBothSpecial`
(`ZInQKernel/Contrib/T28/Special.lean`, branch wip/igusa-special, merged here). Independent check
(VERIFIED, `scratch/igusa-generic/t28_check.lean`):

```lean
theorem t28_check : PkgI1.IgusaClebschSeparation :=
  T28.igusaClebschSeparation_of_bothSpecial T28Special.separationBothSpecial
-- 't28_check' depends on axioms: [propext, Classical.choice, Quot.sound]
```

So **textbook leaf T28 is proved**. The official assembly theorem is
`T28.igusaClebschSeparation_proved` in `ZInQKernel/Contrib/T28/Assemble.lean` (owned by
igusa-special). Before that, the special half was the open piece:
 `T28.SeparationSpecialLocus` (equivalently `T28.SeparationBothSpecial`),
the `⇐` direction of T28 on `det (yv f) = 0`. On that locus the curve has an automorphism
besides the hyperelliptic involution (Bolza 1888, STANDARD; locator UNVERIFIED). Task
igusa-special works on it. `T28.igusaClebschSeparation_of_bothSpecial` turns its result into
the leaf.

The name "generic stabilizer" in the task was turned into the explicit, invariant-defined
condition `det (yv f) ≠ 0` (`genericLocus_iff_gramJ`). Its equivalence with "no extra
automorphism" is Bolza's theorem and is **not** formalized or needed: the split is exhaustive
by `by_cases`.

References (STANDARD; locators UNVERIFIED, no network): J.-F. Mestre, *Construction de courbes
de genre 2 à partir de leurs modules*, in *Effective methods in algebraic geometry*, Progr.
Math. 94 (1991) 313-334; O. Bolza, *On binary sextics with linear transformations into
themselves*, Amer. J. Math. 10 (1888) 47-70; J.-I. Igusa, *Arithmetic variety of moduli for
genus two*, Ann. of Math. 72 (1960) 612-649.
