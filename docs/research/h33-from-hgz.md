# h33-from-hgz: can `hGZ` replace `h33`?

Task h33-from-hgz, 2026-11-16. Base `c0f3d085` (leaf-fold33b). Scratch: `scratch/h33-from-hgz/` (log `log.md`).
Target: remove the `frozenTarget` binder `h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` by deriving it from
`hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd` and what main already proves (target −1).

## 1. Verdict

**No. `GrossZagierAlgOptCd`, with everything main proves, does not imply `TYZThm33`, not even at the instances that
`frozenTarget` uses.** `h33` stays. No contribution file, no fold, no `#discharges` (nothing was discharged), no new
leaf. Count change: 0.

The gap is TYZ Theorem 3.3 itself. TYZ prove it (Period7.tex L1865–2040, VERIFIED read) from three literature inputs
that `hGZ` does not contain and cannot reach:

* (a) Yuan–Zhang–Zhang's Gross–Zagier formula **with a ring-class (genus) character** `χ_{d₀,d₁}` of `Cl_n`. TYZ use
  its explicit form, their Theorem EGZ (appendix, L3062; TYZ write that its deduction is "almost the same" as for
  another theorem and omit it). For `n ≡ 5 (mod 8)` they need it **without the Heegner hypothesis**, because 2 ramifies
  in `K_n` and the level is 32.
* (b) Kolyvagin: `E(K_{d₀})^- ⊗ ℚ` is one-dimensional when `L'(A_{d₀},1) ≠ 0` (L1995–1996, L2011–2013).
* (c) Tunnell–Saito / the YZZ remark after their Thm 1.2, for the first clause (`P_χ` is torsion when the root number
  of `L(A_{K_n},χ,s)` is `+1`; L1907–1909).

The best smallest named Prop for the gap is the existing printed-form leaf of h33-dict, `H33Dict.TYZThm33Printed`
(`origin/wip/h33-dict`, `ZInQKernel/Contrib/OneProof/TYZThm33.lean`, `tyzThm33_of_printed : ShimuraMainCM →
TYZThm33Printed → TYZThm33`). It is rated **printed form** there and is not yet folded. Splitting it into (a)+(b)+(c)
would give three leaves in place of one. Input (a) cannot be stated over genuine Lean definitions today: it needs
automorphic representations, Gross–Prasad test vectors and Petersson norms on quaternion Shimura curves. Its explicit
form is printed only with the proof omitted. So that split would not be an improvement. **Recommendation: fold
h33-dict's `TYZThm33Printed` in place of `h33` (rating GLUE → LEAF printed form, count unchanged).**

## 2. Why `hGZ` cannot give `TYZThm33`

What each statement says (VERIFIED read):

* `hGZ` (`Contrib/OneProof/GrossZagierAlgebraic.lean` L110–142). It covers curves `E'` with `aₙ(E') = aₙ(C_d)`,
  `d ≡ 5 (mod 8)` squarefree, a strong Weil parametrization `X₀(N) → E'`, and the **trivial** character. The field is
  `K = ℚ(√D)` with `D` an **odd** fundamental discriminant that satisfies `HeegnerHyp N D`. The conclusion is
  `L'(E'/K,1) = (FG)'(1) = κ·ĥ(y)` with `κ > 0`, for `y` a multiple of the Heegner trace `y_K` on `X₀(N)`.
* `h33` (`OneProof/TYZSplit.lean` L157–176). It quantifies over every squarefree `n ≡ 5, 7 (mod 8)` and every
  quadratic `χ` of `Cl_n`. It concerns the Heegner points `z_n` on `X₀(32) ≅ A` over `H_n ⊃ K_n = ℚ(√−n)`. Its
  conclusion is `m(d₀)·P_χ ≡ ε·2^{h₂(n)}·ℓ(d₁)·Q(d₀)` modulo torsion, where `ℓ(d₁)² = 𝓛(d₁)²` is a **central value**
  of `L(C_{d₁}, s)` (`lcalSq`), and `Q(d₀)` is torsion when `ord_{s=1} L(C_{d₀},s) ≥ 2`.

The obstructions are independent; any one of them blocks the derivation:

1. **Wrong field for `n ≡ 5`.** For `n ≡ 5 (mod 8)` the discriminant of `K_n` is `−4n`. Neither `−4n` nor `−n` is an
   odd fundamental discriminant, so `hGZ` never applies over `K_n` (Lean: `not_oddDisc_Kn_of_five`, compiled). Main
   uses `h33` exactly for `n = d ≡ 5`: reading A is the statement "`ord L(C_d,s) ≥ 2` ⇒ `T5a(d)`, `T5b(d)` even" for
   `d ≡ 5`.
2. **Wrong L-function.** The height of `P_{χ_{d₀,d₁}}` is governed by `L'(A_{K_n},χ,1) = L'(A_{d₀},1)·L(A_{d₁},1)`
   (L1991). `hGZ` for a curve `E' ∼ C_{d₀}` gives `L'(C_{d₀},1)·L(C_{d₀} ⊗ χ_D,1)` with `D` coprime to the level. The
   level is divisible by every prime of `d₀`, since a prime dividing both the level and `D` breaks the Heegner
   hypothesis (Lean: `not_heegnerHyp_of_common_prime`, compiled). So `C_{d₀} ⊗ χ_D` still has additive reduction at
   every `p ∣ d₀ > 1`, while `C_{d₁}` has good reduction there. The two are not isogenous, and the two L-functions
   differ (STANDARD: conductor of the twist). The factor `ℓ(d₁)`, a central value of the `d₁`-twist, occurs nowhere
   in `hGZ`. Supplying it needs the character version (a) or a Waldspurger-type formula. The curve case `d₀ ≡ 7` and
   the curve `A ∼ C_1` (`d₁ = n`, `d₀ = 1` does not occur, but `A` itself is the curve of `X₀(32)`) are outside `hGZ`'s
   `d ≡ 5` in any case.
3. **Wrong Heegner points.** `hGZ` gives `ĥ(y) = 0` (or `≠ 0`) for its own `y_K` on `X₀(N_{E'})` over an auxiliary
   `K`. `h33` is about `z_n` on `X₀(32)` over `H_n`. No theorem in main relates the two families. Main's Heegner32 and
   GZConj only produce, from `hGZ`, the rank conclusion `GrossZagierHeegnerCd` (`ord = 1` and `L(C_d⊗χ_D,1) ≠ 0` ⇒ a
   non-torsion point). In general the two families are not comparable: they live over different fields, and the
   heights are those of points on different curves.
4. **Height ⇒ vector needs Kolyvagin.** Even with the right height formula, the existential `Q(d₀)` has to serve all
   `d₁` at once. That needs `rank A(K_{d₀})^- ≤ 1`, which is input (b) and is not in main.
5. **First clause needs (c).** The vanishing of `P_χ` for the other characters comes from root numbers and
   Saito–Tunnell (or YZZ Thm 1.2), not from a Gross–Zagier formula for the trivial character.

So no instance of `h33` that main reads (all `n ≡ 5, 7` through `TYZThm33Pinned`, all decompositions `n = d₀d₁`)
follows from `hGZ`.

## 3. Glue status of TYZ's proof of 3.3 (for a future project proof of `TYZThm33Printed` from (a)–(c))

| step (Period7.tex) | content | status |
|---|---|---|
| L1865–1893 Lemma char' | characters with root number −1 and trivial 2-component are the `χ_{d₀,d₁}` | glue (genus theory; the kernel already has the `χ_T` ↔ `K_n(√e)` dictionary, TYZSplit §3) |
| L1907–1909 | `P_χ` torsion if the root number is +1 | LEAF (c), Tunnell–Saito / YZZ |
| L1910–1913 | `P_χ` torsion unless `χ_2 = 1` (n ≡ 5) | glue from TYZ Prop. "choice" (`K_2^×`-invariance of `f_n` up to torsion) |
| L1922–1980 Lemma multiples1 | `4P(d₀,d₁) ∈ A(ℚ(√∓d₀))^-` | glue (Galois action, TYZ Thm 3.6(1), which the kernel has as `tyzThm36ConjFive_of` for n ≡ 5) |
| L1990–1996 | the two sides are proportional | LEAF (a) for vanishing; LEAF (b) Kolyvagin for proportionality |
| L1998–2026 | equality of heights | LEAF (a), explicit form (TYZ Thm EGZ), plus TYZ's period computations |

## 4. Files

* `scratch/h33-from-hgz/Scope.lean`: compiled with `lake env lean` (exit 0, no messages). It uses Mathlib only, with
  verbatim copies of `IsOddImagFundDisc` and `HeegnerHyp` from `Contrib/GZDecomp/Decomp.lean`; that module could not be
  imported because the worktree's upstream `lean/` package is not built. It proves `not_oddDisc_Kn_of_five` and
  `not_heegnerHyp_of_common_prime`.
* `scratch/h33-from-hgz/autofold.json`: records "no fold" (`discharged: []`, `new_leaves: []`).
* No file under `ZInQKernel/` was created or edited. There is no `FoldCheck.lean`, since there is no fold.

Claims: readings of Period7.tex and of the Lean statements are VERIFIED (read). The non-isogeny of
`C_{d₀} ⊗ χ_D` and `C_{d₁}` is STANDARD (reduction types). TYZ's theorem labels are from arXiv v1. YZZ "Thm 1.2" is
cited as TYZ cite it (UNVERIFIED in YZZ).
