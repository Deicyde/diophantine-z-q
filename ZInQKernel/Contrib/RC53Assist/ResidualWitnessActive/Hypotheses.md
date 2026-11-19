# Active residual witness: hypothesis inventory


## Scope of the after-t witness (independent review, 2026-11-18)

The after-t part is a valid nonzero model-level fixture, not a genuine t-deformation: the smaller-support model is the residual cone extended to F_2[[t]] (not built from a global character) and the original-support model is a split extension. The constructor `residualRankCounts_afterT` compares the models only through graded ranks, degreewise equivalences and a homotopy equivalence between supplied models, so it also accepts models with all differentials erased; and its counts sum over degrees 0, 1, 2 although the models live in degrees 0 to 3 (the degree-three term of the before-inverting-t model is positive). The F_2 witnesses of `residualRankCounts_genuine` and `residualRankCounts_actual` are not affected.

## Update (2026-11-18)

The module `ZInQKernel.Contrib.CloudB3RC53.GenuineInst.ResidualAfterT` is now part of the integration branch, so `Witness.lean` imports it and calls `ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_afterT` directly; the former copied section `AfterTCopy` described below has been removed. The copied local Kummer section is unchanged.

The targets are the constructors `ZInQ.Contrib.CloudB3RC53.Mattuck.residualRankCounts_genuine`
and `ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_actual` (manuscript Lemma
`ex:limits-residual-bound`, tex 4453–4648), and the transfer-after-inverting-`t` constructor
`ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_afterT` (tex 4598–4647). All three are
applied in `Witness.lean` to the instance below (`activeGenuineCounts`, `activeActualCounts`,
`activeAfterTCounts`). This file marks every input of the two constructors
as GENUINE (the hypothesis carries content at this instance: its premises are realized, or its
data are nonzero genuine objects) or VACUOUS/TRIVIAL (it holds for a degenerate reason), with the
theorem of `Witness.lean` that shows it.

## The instance

* Field `K = ℚ(i)`, radicand `k = −1` with `α = i`, `A = 0`, one complex place.
* Curve `E₁₁ : y² = x(x − 11)(x + 33)`; at every finite place the integral equation
  `y² = x³ + 22x² − 363x` (discriminant `2304 · 11⁶`), whose generic fibre is the base change of
  `E₁₁`; all four points killed by `2` are rational over every completion.
* `N = 66`, moving prime `r = 5`, derivative primes `D = {7}`, active prime `13`.
  The charged primes are `{2, 3, 5, 7, 11}` (`actCharged_eq`).
* Supports: `S₀ = Sloc = S` = places above `{2, 3, 5, 7, 11}`; `S'` = places above
  `{2, 3, 5, 7, 11, 13}`; `S' − S` is nonempty (`newPlaces_nonempty`).
* Coefficients: the actual residual module `𝔽₂ ⊗ M₁` of `E₁₁` over `S`, coefficient index `j = 0`,
  trivial character (at `j = 0` the coefficient ring `A₁ = 𝔽₂` has only the trivial unit).
* Labels (`actCond`): relaxed derivative above `7`; old Kummer above `2, 3, 11`; full above `5`.
* Local conditions (`actΔ`), genuine complexes with cochain maps into `C^•(G_{K_v}, M)`:
  the Kummer complex above `2, 3, 11` (`actΔ_U_oldKummer`), `τ≤1 C^•(G_{K_v}, M)` above `7`
  (`actΔ_U_derivRelaxed`), the full local complex above `5` (`actΔ_U_full`); at the active places the
  unramified condition `C^•(G_q/I_q, M)` of the support change.
* Residual model `Dsel = actSel`: the cohomology of the global complex, of each condition and of
  each local complex, with the induced maps (`formalData`); degrees `s = {0, 1, 2}`; bounds
  `a = 0`, `b = 3`.
* Original-support data `Dfull = actFull`: the old conditions, and at the active places the
  unramified condition thickened by the cone of its identity; quotient `W = actW`.
* Minimal model `L = actL`: the cohomology of the residual cone, with zero differential.

## The inputs of `residualRankCounts_genuine`

| Input | Value at the instance | Status | Evidence |
|---|---|---|---|
| `K`, `Ew`, `hEw` | `ℚ(i)`, integral equation of `E₁₁` at every place | GENUINE | `smallLocal_elliptic`, `local_models_are_baseChanges` |
| `h410`, `h51`, `h28`, `h23`, `h788` | printed inputs (Milne I.4.10, I.5.1, I.2.8, I.2.3; Nekovář 7.8.8(ii)) | explicit hypotheses, unchanged | — |
| `k`, `α`, `hα`, `hK` | `−1`, `i` | GENUINE | `smallAlpha_radicand`, `smallK_complex` |
| `N`, `hN` | `66` (support parameter) | GENUINE | — |
| `A`, `hA` | `0`; `ω(1) = 0 ≤ 0` | TRIVIAL (`k = −1` has no prime factor) | `by simp` |
| `r`, `hr` | `5` | GENUINE | — |
| `D`, `hD`, `hDodd` | `{7}`, prime and odd | GENUINE (nonempty) | `actD_prime`, `actD_odd` |
| `cond` | `actCond` | GENUINE | `exists_derivative_place`, `exists_oldKummer_place` |
| `hcondD` | relaxed derivative only above `7` | GENUINE: the premise is realized at the place above `7` | `actCond_derivative`, `exists_derivative_place` |
| `hfull` | four rational `2`-torsion points at old-Kummer places | GENUINE: the premise is realized at the places above `2, 3, 11` | `actCond_full_torsion`, `exists_oldKummer_place` |
| `w`, `hw` | a complex place | GENUINE | `smallInfinitePlace_complex` |
| `Sloc` | `S` | GENUINE | — |
| `Dsel` | residual model of the genuine Selmer data with Kummer, derivative and full conditions; nonzero `U`, `L` | GENUINE | `formalData`, `act_U_positive`, `act_L_positive` |
| finiteness of `Dsel.G`, `Dsel.U`, `Dsel.L` | from the printed global and local finiteness | GENUINE | `actSel_G_finite`, `actSel_U_finite`, `actSel_L_finite` |
| `s`, `hs` | `{0, 1, 2}` | GENUINE | — |
| `eG` | `Gⁿ ≅ Hⁿ(G_{K,S₀}, 𝔽₂²)`, `n = 0, 1, 2` | GENUINE | `actEG` |
| `hUm` | condition part vs. genuine condition dimensions | GENUINE: left side `≥ 2`; holds **with equality**, the old Kummer rows by Mattuck's exact dimension | `act_hUm`, `act_hUm_eq`, `act_U_positive`, `oldKummer_places_exact` |
| `hLm` | local part vs. genuine local dimensions | GENUINE: left side `≥ 2`, `Σ (h⁰ + h¹) ≤ Σ (h⁰ + h¹ + h²)` | `act_hLm`, `act_L_positive` |
| `S`, `S'`, `hSS'`, `hS'` | `S ⊊ S'`, both finite | GENUINE: nonempty active support | `smallS_sub`, `smallS'_finite`, `newPlaces_nonempty` |
| `pr`, `hset` | `2`, the finite Nekovář setting | GENUINE | `smallSetting` |
| `M` and its instances | the actual residual module | GENUINE | `smallM_facts` |
| `ψ`, `hψ` | the factorizations of the localizations at the new places through `G_q/I_q` | GENUINE (index set nonempty; factorization proved in the repository) | `urFactor`, `urFactor_spec`, `newPlaces_nonempty` |
| `Δ` | Kummer / relaxed derivative / full conditions | GENUINE | `actΔ_U_oldKummer`, `actΔ_U_derivRelaxed`, `actΔ_U_full` |
| `Dfull`, `W`, `f`, `g` | thickened active conditions; `W = Cone(id)` of the active unramified conditions | GENUINE as data: `f` is not the identity and `W ≠ 0`; the thickening is formal (see below) | `actFull`, `actW_nontrivial` |
| `hDp` | restriction of `Dfull` along `f` is the Nekovář data | GENUINE | `act_hDp` |
| `hfg`, `hinj`, `hsurj`, `hex` | `0 → U_ur → U_ur ⊕ Cone(id) → Cone(id) → 0` exact | GENUINE | `act_fg`, `act_inj`, `act_surj`, `act_ex` |
| `hW` | `Cone(id)` acyclic | holds, but NOT the text's case (see below) | `act_hW`, `active_full_change_not_acyclic` |
| `a`, `b` and the bounds of the residual cone | `[0, 3]` | GENUINE | `actP_ge`, `actP_le` |
| `pP`, `QuasiIso pP` | actual quasi-isomorphism onto the genuine smaller-support Selmer complex with Kummer, derivative and full conditions | GENUINE (the old-Kummer case) | `actPP`, `actPP_quasiIso`, `formalMap_quasiIso` |
| `L`, bounds, finiteness, `hLmin` | cohomology of the residual cone, zero differential | GENUINE | `actL_ge`, `actL_le`, `actL_finite`, `actL_minimal` |
| `pL`, `QuasiIso pL` | through the genuine support change (new places) and the change of condition | GENUINE: the transfer is exercised, `2 ≤ genericRank < rankTot` | `actPL_quasiIso`, `activeGenuineCounts_strict`, `two_le_genericRank` |

## The extra inputs of `residualRankCounts_actual`

| Input | Value | Status | Evidence |
|---|---|---|---|
| `E`, `j`, `χ₀` | `E₁₁`, `0`, trivial (forced at `j = 0`) | GENUINE | — |
| `hT₀`, `hM₀`, `h2₀`, `htriv₀` | full rational `2`-torsion, trivial action on it | GENUINE | `smallTorsion` |
| `eGact` | `Gⁿ ≅ Hⁿ(G_{K,S₀}, 𝔽₂ ⊗ M₁)` | GENUINE | `actEGact` |
| `χ` and the two instances | trivial character over `S` | GENUINE | — |

All other inputs are those of the table above; `activeActualCounts_strict` and
`two_le_genericRank` give `2 ≤ genericRank < rankTot` for this constructor as well.

## The inputs of `residualRankCounts_afterT` (transfer after inverting `t`)

The constructor `ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_afterT` (on the branch
that adds `GenuineInst/ResidualAfterT.lean`; applied here through a verbatim copy, section
`AfterTCopy`) shares the arithmetic, residual-model, `eG`, `hUm` and `hLm` inputs above, all with
the same values (`activeAfterTCounts`). It has no support-change or change-of-condition input and
does not use Nekovář 7.8.8(ii). Its transfer inputs at this instance:

| Input | Value at the instance | Status | Evidence |
|---|---|---|---|
| `P` (free over `𝔽₂[[t]]`) | the residual cone extended to `𝔽₂[[t]]` | GENUINE as a model: free, finite, its reduction modulo `t` has the ranks of the residual cone; the constant extension (see below) | `afterP`, `afterP_free`, `afterP_finite` |
| `hred` | ranks of `P` = ranks of the residual cone | GENUINE | `afterP_hred` |
| `P'`, `hbc` | the base change of `P` to `𝔽₂((t))`; `hbc` is the identity | GENUINE | `afterP'` |
| `a`, `b` and the bounds of `P'`, `L` | `[0, 3]` | GENUINE | `afterP'_ge`, `afterP'_le`, `afterL_ge`, `afterL_le` |
| `L`, `hLmin` | the cohomology of the generic original-support model `Q'`, zero differential | GENUINE: `2 ≤ Σ dim L` | `afterL`, `afterL_minimal`, `two_le_afterT_genericRank` |
| `e : L ≃ P'` | through `Q'`: representatives `L → Q'` and the inclusion `P' → Q'` | GENUINE: the inclusion is a quasi-isomorphism because the active comparison blocks above `13` are acyclic after inverting `t`, and they are not acyclic over `𝔽₂[[t]]` | `afterE`, `afterIncl_quasiIso`, `activeW'_acyclic`, `activeW_not_acyclic`, `afterT_active_case` |

The active comparison block at a place above `13` is `[𝔽₂[[t]]² --((1+t)^e − 1)--> 𝔽₂[[t]]²]` in
degrees `1, 2` (the text's reduction of (4.4), `C = 0`, `A = D = ((1+t)^e − 1) I₂`), with `e = 1` at
a chosen place and `e = −1` at the other places above `13`. Its entry vanishes modulo `t` (so the
reduction of the block is the non-acyclic `𝔽₂` quotient) and is `t` times a unit. The integral
original-support model is `Q = P ⊕ W`, its base change `Q'`, and `0 → P' → Q' → W' → 0` is the
generic change of condition. Result: `2 ≤ genericRank ≤ rankTot`, `genericRank ≤ 294`.

## What remains vacuous, trivial or formal, and why

1. **Over `𝔽₂` the text's change of condition at active primes does not exist.** At a place above
   `13`, `h¹` of the unramified condition is `2` and `h¹` of the full local complex is `4`, so no
   injection with acyclic cokernel exists (`active_unramified_not_full`,
   `active_full_change_not_acyclic`). For `residualRankCounts_genuine` and `residualRankCounts_actual`
   (coefficients `𝔽₂`) the witness thickens the unramified conditions at the active places by the
   contractible cone of their identity; `hW` holds for it but is not the text's case. The text's
   case is witnessed through `residualRankCounts_afterT` (previous section).
2. **The `𝔽₂[[t]]`-models are model-level.** The smaller-support model over `𝔽₂[[t]]` is the
   constant extension of the residual cone. The global character with Frobenius `(1+t)^e` at the
   active places (which produces the entries of the active blocks) is not constructed: it needs class
   field theory. The active blocks are the text's explicit reduction of (4.4), not computed from
   Galois cochains with `𝔽₂[[t]]` coefficients (which, with the inner limit, are not formalized).
   The integral original-support model is the split extension `P ⊕ W`; the connecting map of the
   text's extension is not modelled (after inverting `t` any gluing gives the same result, since
   `W'` is acyclic).
3. **`hA` is trivial**: `k = −1` has no prime factor, so `ω(k) = 0 ≤ A = 0`. This is forced by
   `K = ℚ(i)`, which the manuscript excludes from its final companion choices; the target types
   accept it.
4. **The Kummer coefficient map** `ι_v : E₁₁(K̄_v)[2] ≅ M` is an `𝔽₂`-linear isomorphism between two
   modules with trivial Galois action (`Tv_trivial`, `smallM_facts`), chosen abstractly; it is not
   the comparison along a decomposition embedding `K_S → K̄_v`. The Kummer complex built from it has
   exactly Mattuck's dimensions (`oldKummer_places_exact`).
5. **The moving prime** `5` carries the full condition; its finite character is invisible at the
   residue field (tex 4600: "reduction modulo `t` kills that character").
6. `N = 66` is a support parameter; no equality with the conductor of `E₁₁` is asserted.

No other input of the three constructors is vacuous at this instance.

## Printed inputs, unchanged

Milne, *Arithmetic Duality Theorems*, 2nd ed. (2006), Ch. I: Theorem 4.10(c) (pp. 56–57),
Theorem 5.1 (p. 67), Theorem 2.8 (p. 31), Corollary 2.3 (p. 28); Nekovář, *Selmer complexes*,
Astérisque 310 (2006), Proposition 7.8.8(ii) (pp. 186–187). They are explicit hypotheses of the
statements; the locators are those of the repository's statements of these propositions.

Note (independent review, 2026-11-18): the input `hM0` of the constructors holds trivially at this instance and should be read as TRIVIAL in the tables below. `Axioms.txt` was regenerated so that declaration names containing an apostrophe are printed in full.
