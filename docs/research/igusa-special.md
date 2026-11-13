# igusa-special: the special locus of T28, and T28 assembled

Status: research note (task igusa-special, 2026-11-13). Marks: **VERIFIED** (compiled, computed,
or read in a named source), **STANDARD** (published, reference given), **SPECULATIVE**; theorem
numbers / locators given from memory are **UNVERIFIED** (no network on this host).

## 0. Main result

**Textbook leaf T28 is proved** (VERIFIED: `lake build ZInQKernel.Contrib.T28.Assemble`
succeeds; `#print axioms` below). With task igusa-generic (generic locus, `T28.separationGeneric`):

```lean
-- ZInQKernel/Contrib/T28/Assemble.lean
theorem T28.igusaClebschSeparation_proved : PkgI1.IgusaClebschSeparation
theorem T28.igusaSeparationEq_proved : PkgI1.IgusaSeparationEq
theorem T28.separationSpecial_proved : PkgI1.SeparationSpecial

-- ZInQKernel/Contrib/T28/Special.lean (this task's half)
theorem T28Special.separationBothSpecial : T28.SeparationBothSpecial
```

where (`ZInQKernel/Contrib/T28/Generic.lean`, task igusa-generic, statement agreed between the
two tasks)

```lean
def T28.SeparationBothSpecial : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharZero L] (f g : Fin 7 → L),
    J10 f ≠ 0 → J10 g ≠ 0 → (Matrix.of (yv f)).det = 0 → (Matrix.of (yv g)).det = 0 →
      J2 g = J2 f → J4 g = J4 f → J6 g = J6 f → J10 g = J10 f →
        ∃ M : Matrix (Fin 2) (Fin 2) L, M.det ≠ 0 ∧ ∃ e : L, e ≠ 0 ∧ g = sexticAct f M e
```

and `PkgI1.IgusaClebschSeparation` is the leaf exactly as stated in
`ZInQKernel/HDecomp/Textbook/Igusa/Forward.lean` (copied verbatim from
`scratch/h-decomposition/Leaves.lean`). The assembly is
`T28.igusaClebschSeparation_of_bothSpecial T28Special.separationBothSpecial`
(`ZInQKernel/Contrib/T28/Mestre.lean`, igusa-generic: generic case by Mestre's method, case
"`g` generic" by symmetry, case "both special" by this task).

`#print axioms` (VERIFIED, `lake env lean scratch/igusa-special/Axioms.lean`):

```
'T28.igusaClebschSeparation_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28.igusaSeparationEq_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28.separationSpecial_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28Special.separationBothSpecial' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28Special.special_to_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28Special.special_Nr' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28Special.det_yv_Nr' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28Special.exists_Nr' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28Special.E_sep' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28Special.fam_alg' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28Special.E_D4' depends on axioms: [propext, Classical.choice, Quot.sound]
'T28Special.even_to_E' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Proposal for the leaf list: **remove T28** (the leaf's Prop is the type of a closed theorem with
the standard axioms). No statement change is needed.

## 1. Files (all new, under `ZInQKernel/Contrib/T28/`; no existing file edited)

| File | Content | Compile (VERIFIED) |
| --- | --- | --- |
| `Special/Family.lean` | `Eqv` (equivalence via `actC`: refl/symm/trans, `Eqv.J`, `Eqv.sexticAct`), the family `E a b = x⁶+ax⁴+bx²+1`, `J*_E`, `fam_alg`, `E_rot`, `E_swap`, `E_orbit`, `E_D4`, `E_sep` | ~10 s |
| `Special/Bolza.lean` | `Ne`, `Nr`, `T1..T4`, `y?c?_Ne`, `det_yv_Ne`, `D1..D4`, `cls?_odd?`, `T?_Nr`, `det_yv_Nr`, `J10_Ne`, `J10_Nr`, `Nr_distinct`, `J10_zero_56`, `J10_zero_01`, `even_to_E`, `inv_E`, `cls?_E`, `perm_E`, `special_Nr` | ~3 min |
| `Special/NormalForm.lean` | `root2..root6`, `cubic_split`, `step_inf`, `step_zero`, `step_one`, `exists_Nr` | ~7 s |
| `Special.lean` | `Eqv.det_yv`, `special_to_E`, `separationBothSpecial` | ~5 s |
| `Assemble.lean` | `igusaClebschSeparation_proved`, `igusaSeparationEq_proved`, `separationSpecial_proved` | ~2 s |

Dependencies from igusa-generic (merged from `wip/igusa-generic`): `T28.SeparationBothSpecial`
(`Generic.lean`), `T28.det_yv_actC` (`Covariance.lean`: `det yv (actC f a b c d e) =
e¹⁵ (ad-bc)⁴⁵ det yv f`), `T28.separationGeneric`, `T28.igusaClebschSeparation_of_bothSpecial`
(`Mestre.lean`).

## 2. The proof of the special half

Notation: `Eqv f g` iff `g = actC f a b c d e` with `ad - bc ≠ 0`, `e ≠ 0` (`actC` = the
coefficients of `e·(cx+d)⁶ f((ax+b)/(cx+d))`, equal to `sexticAct f !![a,b;c,d] e`).

**Step 1 (root normal form, `exists_Nr`).** If `J10 f ≠ 0`, then `Eqv f (Nr l m n)` with
`Nr l m n = x(x-1)(x-l)(x-m)(x-n)` (as a sextic: roots `∞,0,1,l,m,n`). A root is sent to `∞`
(`x ↦ (rx+1)/x`), a second to `0` (translation), a third to `1` (scaling), the leading coefficient
to `1`, and the remaining cubic is split. `J10` vanishes identically when `a₅ = a₆ = 0` or
`a₀ = a₁ = 0` (`J10_zero_56`, `J10_zero_01`: every monomial of `j10Data` contains `a₅` or `a₆`,
and `a₀` or `a₁`; VERIFIED by `t10.py` and by `ring`), which excludes double roots at `∞`, `0`.

**Step 2 (Bolza's criterion on the normal form, `special_Nr`).** VERIFIED identity
(`det_yv_Nr`, `ring`; found by `t2.py`/`t4.py`):

`det yv (Nr l m n) = (1/384433593750) · ∏_{s} D_s`,

the product over the fifteen synthemes `s = {{p₁,q₁},{p₂,q₂},{p₃,q₃}}` of `{∞,0,1,l,m,n}`, with
`D_s = det` of the coefficient vectors of `(x-p_i)(x-q_i)` (`(x-p)·z` for `q = ∞`). Under
permutations of `l, m, n` the synthemes form four orbits, with representatives
`D1 = mn - l` for `(∞0)(1l)(mn)`, `D2 = l - m - n + mn` for `(∞1)(0l)(mn)`,
`D3 = l - lm - ln + mn` for `(∞l)(01)(mn)`, `D4 = lm - l - ln + n` for `(∞l)(0m)(1n)`; orbit
products are polynomials `T1..T4` in the elementary symmetric functions (6, 9, 9, 41 terms), and
`det yv (Ne e₁ e₂ e₃) = C·T1·T2·T3·T4` is proved by `ring` after computing the nine entries
`yᵢcⱼ(Ne e₁ e₂ e₃)` (11/33/73 terms). `D_s = 0` means the three quadratics lie in a pencil: the
involution `x ↦ p + k/(x - p)` with `(p, k) = (0, l)`, `(1, 1-l)`, `(l, l(l-1))`, `(l, l(l-m))`
swaps the pairs. With `σ² = k`, the substitution `x = (( σ-p)X + (p+σ))/(1 - X)` (determinant
`2σ ≠ 0`; `k ≠ 0` by `J10_Nr = 256·∏(differences)²`) makes the sextic even: its odd
coefficients are `q₁·(σ² - k) + q₂·D` (`cls?_odd?`, certificates from `t9.py`). An even sextic
with `J10 ≠ 0` has `c₀c₆ ≠ 0` and `x ↦ κx`, `κ⁶ = c₀/c₆`, gives `E a b` (`even_to_E`).
Covariance of `det yv` (igusa-generic) transports `det yv f = 0` to the normal form, so
`special_to_E`: `J10 f ≠ 0 → det yv f = 0 → ∃ a b, Eqv f (E a b)`.

**Step 3 (separation inside the family, `E_sep`).** VERIFIED (`t5.py`, `t6.py`, `t8.py`, and the
Lean proofs): with `u = ab`, `v = a³ + b³`,
`J2(E a b) = -32u - 480`, `J4 = -128v + 32u² + 2624u + 5280`, `J6 = 128·J4 - 131072(3u + 5)`,
`J10 = -262144(v² - 2u³) + 131072u²v - 16384u⁴ + 2359296uv - 1114112u³ - 3538944v - 4423680u²
+ 15925248u - 11943936`. Suppose `J_{2k}(E a' b') = r^k J_{2k}(E a b)`, `r ≠ 0`. Then
`u' + 15 = r(u + 15)` and `128(1 - r)·E3 = (J6-eq) - 128(J4-eq) - 12288(J2-eq)` with
`E3 = r²J4(u,v) - 1024(3r(u+15)(1+r) - 40(1+r+r²))`.
* `r = 1`: `(u', v') = (u, v)`, so `{a'³, b'³} = {a³, b³}` and `(a', b')` is in the orbit of
  `(a, b)` under `x ↦ ωx` (`ω³ = 1`, `E_rot`) and `x ↦ 1/x` (`E_swap`): `E_orbit`.
* `r ≠ 1`: eliminating `u', v', v`, the `J10` equation becomes
  `(128r²)²·(J10-eq) - q₃·E3 = -2³⁸ r⁴ (1-r)³ (r²u² - 2r(16+r)u + (16-r)²)` (`fam_alg`). With
  `ρ² = r`: `ru = (4 ∓ ρ)²`; choosing the sign, `u = t²`, `v = 2t³` (from `E3`), `u' = t'²`,
  `v' = 2t'³` with `t = 4/ρ - 1`, `t' = 4ρ - 1`. So `E a b ≅ E t t`, `E a' b' ≅ E t' t'` (orbits),
  and `E t t ≅ E t' t'` by `x = (1+X)/(1-X)`:
  `(1-X)⁶ E(t,t)((1+X)/(1-X)) = 2(1+t)·E(t',t')` (`E_D4`). This is the `D₄` stratum (reduced
  automorphism group `⊇ V₄`): its two non-conjugate involution classes give two normal forms with
  different `(u, v)` and the same invariants; the larger strata (`D₆`, `x⁵ - x`, `x⁶ - 1`) need no
  separate treatment, because the elimination above covers every solution of the equations.

**Assembly** (`separationBothSpecial`): `f ≅ E a b`, `g ≅ E a' b'`, `J(E a b) = ρ^{2k} J(f)`,
`J(E a' b') = ρ'^{2k} J(g)`, so `E_sep` with `r = (ρ'/ρ)²`.

## 3. Relation to the literature

The classical route (Bolza, *On binary sextics with linear transformations into themselves*,
Amer. J. Math. 10 (1888); Cardona–Quer, *Field of moduli and field of definition for curves of
genus 2*, 2005 — STANDARD, locators UNVERIFIED) characterizes `R = 0` (Clebsch's skew invariant,
`R = ∏` over the 15 factorizations `f = q₁q₂q₃` of `det(q₁,q₂,q₃)`) as the locus of an extra
involution and separates it with the dihedral invariants `u, v` of `x⁶ + ax⁴ + bx² + 1`. Here the
identity `det yv = c·R` is replaced by the direct root-form identity `det_yv_Nr` (constant
`1/384433593750`), and the failure of `(u, v)` to separate on the `D₄` stratum is found and
handled by the elimination of §2 rather than by a case list of automorphism groups.

## 4. Computer algebra

No sympy/PARI on this host (`~/pyenv` absent, no network). `scratch/igusa-special/poly.py` is a
pure-python sparse polynomial library over `ℚ` that parses the Lean definitions (`y?c?`, `J2`,
`J4`, `J6`, `j10Data`); scripts `t2.py … t14.py` (run as `python3 -I scratch/igusa-special/tN.py`
from that directory) and generators `gen_*.py` produced every identity and certificate used.
Results log: `scratch/igusa-special/log.md`.
