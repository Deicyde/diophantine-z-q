# p0-local: Proposition 0, files 1–4 (coverings, squares in ℚ_p, real place, odd p ∣ d)

Plan: `docs/research/nt-prop0.md` §4.1 files 1–4. Namespace `ZInQ.RouteK.Selmer`. Root module
`ZInQKernel/RouteK/SelmerLocal.lean`, imported from `ZInQKernel.lean`.

`lake build ZInQKernel` succeeds. There is no `sorry`. `#print axioms` on `certifiedRank_of_sel`,
`loc_padic_dvd_iff`, `loc_iff_kummer`, `cov_iff_loc`, `loc_real_iff`, `isSquare_padic_iff`,
`isSquare_two_adic_iff` and both rational tests shows only `propext`, `Classical.choice` and
`Quot.sound`.

## Leaves

| Article (nt-prop0 section) | Lean name | Status |
| --- | --- | --- |
| §1.1 x-form `Loc_K(a,b)` | `Loc` (`Selmer/Covering.lean`) | proved (definition) |
| §2 (Inv) | `loc_congr_sq`, `loc_mul_sq_iff` | proved |
| §2 (Tor) | `loc_torsion` | proved |
| §1.1 projective covering `D_{a,b}` and its x-form | `Cov`, `cov_iff_loc` | proved |
| §1.2 Kummer map and Lemma 1.2 | `kummer`, `loc_iff_kummer` | proved |
| §1.3 `Sel₂(d)` | `Sel2` | definition |
| §1.4 CR₃^Sel | `CertifiedRankSel` (docstring = trust statement) | definition (hypothesis) |
| §2.7 Proposition 0, as used by §1.4 | `Prop0Statement` | definition (to be proved by file 9) |
| §1.4 steps 1–5 | `certifiedRank_of_sel : CertifiedRankSel → Prop0Statement → CertifiedRank` | proved |
| §2.1 Lemma SQ(a), (c) | `isSquare_padic_iff` (`Selmer/PadicSquare.lean`) | proved |
| §2.1 Lemma SQ(b), (c) | `isSquare_two_adic_iff` | proved |
| §2.1 (P) | `sqEq_add_of_norm_lt` (odd `p`), `sqEq_add_of_norm_le_two_adic` (`p = 2`), `sqEq_add_of_norm_lt_two_sq` (all `p`) | proved |
| §2.1 (RT) | `isSquare_ratCast_of_residue`, `isSquare_intCast_div_of_residue`, `isSquare_intCast_of_residue` (odd `p`); `isSquare_ratCast_two_adic`, `isSquare_intCast_div_two_adic` (`p = 2`) | proved |
| §2.2 Lemma ∞ | `loc_real_iff` (`Selmer/Real.lean`), plus `loc_real_iff_int` | proved |
| §2.4 Lemma B | `loc_padic_dvd_iff` (`Selmer/BadOdd.lean`) | proved |

## Statement choices and corrections

- **`Loc` is generic over the field.** It is `Loc (K) [Field K] (d a b : K)`. The integer and
  natural-number arguments in `Sel2` and in `loc_padic_dvd_iff` are casts, so `Loc ℚ_[p] d a b` with
  `d : ℕ`, `a b : ℤ` elaborates exactly as in §4.4. `loc_real_iff` is stated for `d a b : ℝ` with
  `0 < d`, `a, b ≠ 0`. `loc_real_iff_int` is the form for `d : ℕ`, `a b : ℤ`.
  The hypotheses `a, b ≠ 0` are needed: with `a = 0`, `x/a = 0` is always a square.
- **Square classes.** `SqEq u v := ∃ s ≠ 0, u = v s²` is `u ≡ v` in `K*/K*²`. Its algebra is
  `symm`, `trans`, `mul`, `isSquare_mul`, `sqEq_iff_isSquare_mul`, `sqEq_of_mul_sqEq` (from `ab ≡ c`
  and `b ≡ e`, get `a ≡ ce`) and `SqEq.of_mul_sq`.
- **(Tor)** needs `2 ≠ 0` and `d ≠ 0` in `K`, because the three torsion abscissae must be distinct.
  It returns the torsion classes as `SqEq a (−1) ∧ SqEq b (−d)` and so on. In the generic case it
  returns `x, x ∓ d ≠ 0`, `x ≡ a`, `x − d ≡ b`, `x + d ≡ ab` and `x(x − d)(x + d)` square.
- **Kummer map.** `kummer d : (shortCurve (−d²)).toAffine.Point → K × K` (Mathlib points, the repo's
  `ZInQ.shortCurve`), with the values of §1.2. `loc_iff_kummer` needs `2 ≠ 0`, `d ≠ 0` and
  `a, b ≠ 0`. The point built in (⇒) is shown nonsingular from `Δ = 64 d⁶ ≠ 0`.
- **`Sel2`** is as in §1.4:
  `{ab | Squarefree ab.1 ∧ Squarefree ab.2 ∧ Loc ℝ d ab.1 ab.2 ∧ ∀ (p : ℕ) [Fact p.Prime], Loc ℚ_[p] d ab.1 ab.2}`.
- **`CertifiedRankSel`** is word for word the statement of §1.4, with no change. Its docstring gives
  the reading in the literature's terms (`dim Sel₂ = 3` plus the shape `|a| ≡ 7` gives `Ш[2] = 0`,
  equivalently `rank ≥ 1`) and both source routes, as in `ZInQ.CertifiedRank`. I made one wording
  correction against `ZInQ.CertifiedRank`: there, `d ≥ 21` (Kriz's `f₀ ≥ 4`) is visible because
  `a ∣ d` is a hypothesis. In CR₃^Sel it follows only through Proposition 0, since a Selmer `a` with
  `|a| ≡ 7` is a signed divisor of `d`. The docstring says so.
- **`Prop0Statement`** (the note left it unspecified). For squarefree `d ≡ 5 (mod 8)`:
  `(∀ σ, (natConfig d _).IsSol σ ↔ selPair d σ ∈ Sel2 d) ∧ Sel2 d ⊆ Set.range (selPair d)`.
  Here `selPair d σ = (classInt d a₀ a₁ u, classInt d b₀ b₁ v)` and
  `classInt d e₀ e₁ w = (−1)^{e₀} 2^{e₁} Π_{p ∣ d} p^{w_p}`. The second conjunct is the "onto" half
  of the §2.7 corollary, which needs Lemma G1. The injectivity half is proved here
  (`selPair_injective`) and is not part of the hypothesis. So `(Sel2 d).ncard = sols.card` is
  derived inside `certifiedRank_of_sel`.
- **`loc_padic_dvd_iff`** has exactly the statement of §4.4. No adjustment was needed.

## Lemmas added beyond the leaves

- Covering: `SqEq` and its algebra (above), `isSquare_mul_sq_iff`, `isSquare_div_sq_iff`,
  `SqEq.isSquare_iff`, `loc_of_sqEq_torsion` (sufficiency for the four torsion classes
  `(d^i(−1)^j, 2^i(−d)^j)` over any field; Lemma T can reuse it), `zmod2_cases`,
  `classInt_prod_pos`, `classInt_pos_iff`, `prime_dvd_classInt_iff`, `two_dvd_classInt_iff`,
  `selPair_injective`, `classInt_natClass` (step 2: `natClass d a` stands for `a`),
  `eq_one_of_squarefree_of_isSquare`, `exists_point_of_loc` (steps 3–5).
- PadicSquare:
  - `isSquare_of_norm_sub_one_lt`: `‖u − 1‖ < ‖2‖²` implies `u` is a square, for every `p`. This
    single Hensel application gives SQ(a), SQ(b), (P) and (RT) for both odd `p` and `p = 2`.
  - `padic_norm_two`, `two_adic_norm_two`, `padic_norm_two_le_one`;
  - `unitPart` (`x = p^{v(x)} · unitPart x`, `unitPart_spec`, `norm_unitPart`, `isUnit_unitPart`);
  - `isSquare_iff_even_valuation` (SQ(c)), `isSquare_coe_iff_toZMod` (SQ(a) for units),
    `isSquare_coe_iff_toZModPow_two` (SQ(b) for units);
  - `even_valuation_of_isSquare`, `exists_padicInt_sq_of_isSquare`,
    `norm_lt_one_of_toZMod_eq_zero`, `padic_norm_intCast_eq_one`.
- BadOdd: `padic_norm_natCast_of_squarefree` (`‖d‖ = p⁻¹`), `padic_norm_ne_zpow_odd` (the norm of a
  nonzero square is not an odd power of `p`).

All names were grepped against `ZInQKernel/` and are new. They live in the new namespace
`ZInQ.RouteK.Selmer`.

## Cost figures for extrapolation (§4.4 criterion)

| File | Lines |
| --- | --- |
| `Selmer/Covering.lean` | 565 (about 230 for Loc/Cov/Kummer, the rest Sel2, CR₃^Sel and the reduction) |
| `Selmer/PadicSquare.lean` | 298 |
| `Selmer/Real.lean` | 52 |
| `Selmer/BadOdd.lean` | 167 |
| files 2 + 4 | **465** (criterion: about 600) |

- **Speed.** I compiled each file with `-DElab.async=false -Dprofiler=true -Dprofiler.threshold=100`.
  No profiler entry reached 100 ms in any file. Wall time per file, without the 3.2 s import, is
  Covering 5 s, PadicSquare 4 s, BadOdd 2.5 s and Real 2 s. The slowest declarations are therefore
  well under 1 s, against a criterion of 30 s.
- **No sorry.** Every leaf compiled after one to four edit–compile rounds.
- **Proof of Lemma B.** Comparing `‖x‖` with `‖d‖ = p⁻¹` replaced the case split on `v_p(x)`. There
  are three cases (`<`, `=`, `>`), and the `=` case splits on `‖t ∓ 1‖ < 1`. Each case is 10–15
  lines of `SqEq` algebra over (P). Valuations enter only through `padic_norm_ne_zpow_odd`.
- **Lemma T.** It has the same shape with `sqEq_add_of_norm_le_two_adic` and residues mod 8, so
  about 400–600 lines looks realistic. The eight witnesses of the §2.5 table go through
  `loc_congr_sq` and the 2-adic rational test `isSquare_ratCast_two_adic` (or
  `isSquare_intCast_div_two_adic`).

## Problems

None blocking.
- Build setup: the worktree had no `.lake`. I copied it from the main clone, which is at the same
  base commit, with `cp --reflink`; this also needed `lean/.lake`. Building then took only the new
  modules.
- Mathlib 4.35: `if_pos`/`if_neg` are deprecated in favour of `ite_eq_left`/`ite_eq_right`, and
  `Prime.dvd_finset_prod_iff` in favour of `Prime.dvd_finsetProd_iff`. The `ℚ_[p]` norm lemmas are
  `Padic.norm_int_le_one`, `Padic.norm_intCast_lt_one_iff` and `Padic.nonarchimedean`, not
  `padicNormE.*`; use plain `norm_mul`.

## Suggestions for the next agent

- **File 5 (`Two.lean`, Lemma T).** For (⇐), reuse `loc_of_sqEq_torsion` for the four torsion
  classes. The four non-torsion witnesses then need only `loc_congr_sq` and
  `isSquare_ratCast_two_adic`. For (⇒), use `loc_torsion` and then compare `‖x‖` with `1` and with
  powers of `2`. `sqEq_add_of_norm_le_two_adic` is (P) at 2. `unitPart` and
  `isSquare_coe_iff_toZModPow_two` turn "unit ≡ 1 mod 8" into squares.
- **File 7 (`Good.lean`).** G2's lift is `isSquare_intCast_of_residue` (integer `x` with residue
  `ξ`). G1 is a norm argument like BadOdd's, with `‖d‖ = 1`; use `padic_norm_intCast_eq_one`.
- **File 9 (`Prop0.lean`).** It must prove `Prop0Statement` exactly as defined in `Covering.lean`
  (iff, plus `Sel2 d ⊆ Set.range (selPair d)`). `certifiedRank_of_sel` then gives
  `CertifiedRankSel → CertifiedRank`. Useful facts: `prime_dvd_classInt_iff`,
  `two_dvd_classInt_iff` and `classInt_pos_iff` read the unknowns off `classInt`, and
  `loc_real_iff_int` gives row `(R)` directly.
- **`Sel2` uses an instance binder** `∀ (p : ℕ) [Fact p.Prime]`. To use it at a given prime,
  `haveI := Fact.mk hp` and apply.
