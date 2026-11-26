# igusa-gal: `igusaGL2DS` from Diamond–Shurman Thm 7.6.3 on `Gal(ℚ(j, E_j[N])/ℚ(j))`

Task igusa-gal (2026-11-17). Scratch: `scratch/igusa-gal/` (log `log.md`). Lean:
`ZInQKernel/Contrib/OneProof/IgusaGL2DSGal.lean`.

## 1. Result

**The review's gap is closed.** Review queue14 (rater and skeptic, 11-17) rated the research leaf
`X1Igusa.IgusaGL2DS` GLUE: Diamond–Shurman's Theorem 7.6.3 is about the group `H_ℚ = Gal(ℚ(j, E_j[N])/ℚ(j))`,
while the leaf quantifies over `Aut(\overline{ℚ(j)}/ℚ(j))`, and getting from one to the other is an extension
theorem. This task:

1. states the print's form as the new leaf `X1Igusa.IgusaGL2DSGal`. Here `σ₀` ranges over
   `Gal(L_N/ℚ(j))`, with `L_N = X1Igusa.LDS N = ℚ(j, E_j[N])`: the intermediate field of
   `\overline{ℚ(j)} = AlgebraicClosure (RatFunc ℚ)` that `IntermediateField.adjoin` generates from the `x`- and
   `y`-coordinates of the `N`-torsion points of `EDSBar`. `σ₀` acts on `E_j[N] ⊆ E_j(L_N)` through
   `Affine.Point.map`. The leaf assumes `1 < N`; everything else is as in `IgusaGL2DS`;
2. proves `X1Igusa.igusaGL2DS_of_igusaGL2DSGal : IgusaGL2DSGal → IgusaGL2DS` with no other hypothesis
   (VERIFIED: compiled, standard axioms). The proof follows NeronOggShafarevichSep.lean:181-195:
   `σ = σ₀.liftNormal \overline{ℚ(j)}`, where normality comes from `IsAlgClosure.normal` and
   `AlgEquiv.liftNormal_commutes` makes `σ` agree with `σ₀` on `L_N`. Every point of `E_j[N]` is an `L_N`-point
   (`exists_LDS_point`, using `subset_adjoin` and `baseChange_nonsingular`). `Affine.Point.map_map` turns the
   field identity into the identity on points. `N = 1` is proved directly with `σ = id`;
3. checks the statement against Diamond–Shurman, by theorem and section (section 3). Every answer is favourable. The only
   adjustment is `1 < N` (the standing assumption of §7.5), which the new leaf adopts;
4. writes the autofold spec `scratch/igusa-gal/autofold.json`. Its dry run gives
   **strict 9/25 → 10/24, strictest 9/25 → 10/24** (VERIFIED), so `igusaGL2DS` becomes a LEAF/LEAF row and there
   is one GLUE fewer.

No consumer of `IgusaGL2DS` loses anything (VERIFIED by reading every use). Each one takes `IgusaGL2DS` as a
hypothesis, and the new implication is unconditional:
* `X1Igusa.x1PointsConjugate_of_igusaGL2DS`;
* `AfTateLam.r16CoreY_of_picZero_igusaDS` (AfTateLambda.lean:857);
* `AfTateOr.r16CoreY_of_dsOr_igusaDS`;
* R16CoreYSatDet;
* R16CoreYDS965 (used by the TailZ66 conversion);
* the bundle field in TailZ66–71.

## 2. Lean (`ZInQKernel/Contrib/OneProof/IgusaGL2DSGal.lean`, imports only `ZInQKernel.Contrib.OneProof.X1Igusa`)

| declaration | content |
| --- | --- |
| `coordsDS N : Set Kbar` | coordinates `x, y` of the nonzero points of `nTors EDSBar N` |
| `LDS N : IntermediateField Qj Kbar` | `IntermediateField.adjoin Qj (coordsDS N)`, DS's `ℚ(j, E_j[N])` |
| `incDS N`, `galPtL σ₀` | `Affine.Point.map` along `(LDS N).val`, along `σ₀` |
| `IgusaGL2DSGal : Prop` | **new LEAF** (below) |
| `exists_LDS_point` | every `Q ∈ E_j[N]` is `incDS N P` for an `L_N`-point `P` |
| `galPtDS_liftNormal_inc` | `galPtDS (σ₀.liftNormal Kbar) (incDS N P) = incDS N (galPtL σ₀ P)` |
| `igusaGL2DS_of_igusaGL2DSGal` | `IgusaGL2DSGal → IgusaGL2DS` |

```lean
def IgusaGL2DSGal : Prop :=
  ∀ N : ℕ, 1 < N → ∀ (e : (ZMod N × ZMod N) ≃+ nTors EDSBar N) (g : GL (Fin 2) (ZMod N)),
    ∃ σ₀ : LDS N ≃ₐ[Qj] LDS N, ∀ (v : ZMod N × ZMod N) (P : (EDS.baseChange (LDS N)).toAffine.Point),
      incDS N P = (e v : EDSBar.toAffine.Point) →
        incDS N (galPtL σ₀ P) = (e (matAct (g : Matrix (Fin 2) (Fin 2) (ZMod N)) v) : EDSBar.toAffine.Point)
```

The premise `incDS N P = e v` cannot make the leaf vacuous. By `exists_LDS_point` every `e v` has such a `P`,
and `P` is unique because `incDS` is injective (`Affine.Point.map_injective`).

Checks run (VERIFIED):
* `lake env lean` on the file gives no errors and no warnings;
* `lake build +ZInQKernel.Contrib.OneProof.IgusaGL2DSGal` succeeds;
* `#discharges` output is in section 5.

## 3. Statement check (Diamond–Shurman, GTM 228; AI reading, located by theorem and section)

| question | answer | locator |
| --- | --- | --- |
| Theorem 7.6.3 | `H_ℚ` = Galois group of `ℚ(j, E_j[N])/ℚ(j)`; "there is an isomorphism ρ : H_ℚ → GL₂(ℤ/Nℤ)", plus the `K ∩ \bar ℚ = ℚ` part (not used) | Thm 7.6.3 |
| is ρ the action map on `E_j[N]`? | yes: ρ describes how `H_ℚ` permutes `E_j[N]`. It is defined in §7.6 "as before" in the ordered basis `(P_τ, Q_τ)` of (7.11), with `(P^σ, Q^σ)ᵀ = ρ(σ)(P, Q)ᵀ` | §7.6, (7.11) |
| ρ "as before" | Corollary 7.5.3 over `ℂ`: the basis `(P_τ, Q_τ)` gives an injective representation ρ | Cor. 7.5.3 |
| any basis allowed? | the print fixes one basis, `(P_τ, Q_τ)`, canonical up to sign. Any other basis conjugates the image by a fixed element of `GL₂(ℤ/N)`; going from the print's row convention to `σ(e v) = e(g v)` is a transpose; both are bijections of `GL₂(ℤ/N)`. So the every-basis form is a consequence, by elementary group theory (reading note (1) of the leaf) | §7.6 |
| which `N` | §7.5 opens with "where N > 1", and §7.6 continues in that setting. The new leaf assumes `1 < N`; `N = 1` is proved in Lean | §7.5, §7.6 |
| the curve | (7.12) `E_j : y² = 4x³ − (27j/(j−1728)) x − 27j/(j−1728)`, the "universal elliptic curve" | (7.12), §7.5 |
| how DS define `ℚ(j)` | analytically `j` is the modular invariant. The algebraic view, which is the one §7.6 uses: "view j as a transcendental element" and `E_j` as an elliptic curve over `ℂ(j)`; `ℚ(j) ⊂ ℂ(j)`. So `ℚ(j) = RatFunc ℚ` | §7.5, §7.6 |
| where `E_j[N]` lives | over `ℚ(j)`: points are pairs from the algebraic closure of `ℚ(j)` (opening of §7.6). Over `ℂ`: pairs from the algebraic closure of `ℂ(j)` (§7.5) | §7.6; §7.5 |
| `ℚ(j, E_j[N])` | the field generated by `x(E_j[N]) ∪ y(E_j[N])`. The definition is given over `ℂ` and carried to `ℚ` in §7.6, which shows `μ_N ⊂ ℚ(j, E_j[N])` | §7.5; §7.6 |
| group law | geometric: the chord–tangent law with origin `0_E = [0, 1, 0]`, given by the rational formulas (7.3) (§7.1) | (7.3), §7.1 |

Consequences for the statement:
* `LDS N` is DS's `ℚ(j, E_j[N])`.
  - DS work inside `\overline{ℂ(j)}`; the leaf works inside `AlgebraicClosure (RatFunc ℚ)`. The two algebraic
    closures of `ℚ(j)` are `ℚ(j)`-isomorphic, and the statement is invariant under such isomorphisms.
  - `x(E_j[N])` in the print means the coordinates of the nonzero points, which is what `coordsDS` collects.
* Mathlib's group law on `Affine.Point` is the same chord–tangent law with origin at infinity.
* Mathlib's normal form `EDS` is the print's `E_j` after `y = 2y'`. This is reading note (2) of the original leaf
  and unchanged.

## 4. Kind and flag of the new leaf, and the autofold row

**`igusaGL2DSGal`: published, printed form.** It is DS Theorem 7.6.3 (surjectivity of ρ) over genuine
definitions:
* Mathlib's `IntermediateField.adjoin`, `AlgEquiv`, `Affine.Point.map`;
* the tree's `EDS`, `nTors` and `matAct`.

It differs from the print in three ways, none of them a strengthening:
* (a) it drops injectivity, so it is weaker;
* (b) it states the result in every basis instead of `(P_τ, Q_τ)`, which follows by conjugation and transpose;
* (c) it is stated on the normalized model, the same curve as the print's.

Point (b) is the one step a strict rater could call "consequence", so it is now proved in Lean. The helper file
`ZInQKernel/Contrib/OneProof/IgusaGL2DSGalSome.lean` states the one-basis form `IgusaGL2DSGalSome`
(`∀ N > 1, ∃ e, ∀ g, ∃ σ₀, …`). It proves `igusaGL2DSGal_of_some : IgusaGL2DSGalSome → IgusaGL2DSGal` by
conjugation in `GL₂(ℤ/N)`: `glOf` turns an additive automorphism of `(ℤ/N)²` into a matrix, using `matAct_matOf`
and `matAct_mul`. It also proves `igusaGL2DS_of_igusaGL2DSGalSome` (VERIFIED: compiled, standard axioms).
`IgusaGL2DSGalSome` is the print with nothing added except dropping injectivity. The row convention becomes the
column convention through `g = ρ(σ)ᵀ`, which the `∀ g` absorbs. The alternative spec
`scratch/igusa-gal/autofold-some.json` folds it instead; its dry run gives the same counts, 9/25 → 10/24.
**Recommendation: fold the `Some` spec**, since it removes reading note (1). The primary spec, folding
`IgusaGL2DSGal`, is the one the task asked for. The print's
`(P_τ, Q_τ)` is defined analytically by (7.11), with `℘_τ`, so the print's exact basis cannot be named in Lean
over `RatFunc ℚ`. The `∃ e` form is the closest algebraic statement.

Exact kinds row: `scratch/igusa-gal/kinds-row.tsv`, the row `autofold.py` builds from the spec. Its columns are:

| column | value |
| --- | --- |
| bundle | `research` |
| field | `igusaGL2DSGal` |
| kind | `published` |
| flag | "unread: new printed leaf (no human reading); AI page check (igusa-gal, 11-17) …"; full text in the spec and the row file |
| strict / strictest | `LEAF` / `LEAF` |
| source | Diamond–Shurman, GTM 228, Theorem 7.6.3, ρ as in §7.6, (7.12); Igusa 1959 (unread) |
| rated_by | `igusa-gal-fold; pending review` |
| packet / label / tier | empty, inherited from the `igusaGL2DS` row |
| flag_class | `unread` |
| area_issue | `elliotglazer/diophantine-z-q#37`, inherited |

Dry run: `python3 scripts/one_proof/autofold.py scratch/igusa-gal/autofold.json --dry-run` exits 0 and prints
`strict count: 9/25 on 34 -> 10/24 on 34; strictest 9/25 -> 10/24`. The generated module is in
`scratch/igusa-gal/autofold-dryrun.txt`. It contains `OpenResearchLeaves46`, with the field
`igusaGL2DSGal : _root_.X1Igusa.IgusaGL2DSGal`, and the conversion
`igusaGL2DS := _root_.X1Igusa.igusaGL2DS_of_igusaGL2DSGal n.igusaGL2DSGal`.

No page answer was unfavourable, so the kind stays published and the leaf counts LEAF/LEAF. If a reviewer
nevertheless treats the every-basis step as a reading step, the kind becomes consequence (GLUE/GLUE) with the
flag "consequence step: one basis → every basis (conjugation in GL₂(ℤ/N))". In that case, fold
`IgusaGL2DSGalSome` instead (its proof compiles; see above).

## 5. Checks (all VERIFIED on this host, 11-17)

* `lake env lean ZInQKernel/Contrib/OneProof/IgusaGL2DSGal.lean` gives no errors and no warnings.
  `lake build +ZInQKernel.Contrib.OneProof.IgusaGL2DSGal` and `+…IgusaGL2DSGalSome` succeed.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` succeeds (16093 jobs), with
  `frozenTarget` on the standard axioms. The first attempt failed with a missing `.olean` in two
  CloudB3W16Torsion vendor modules, left by an interrupted earlier build; the rebuild was clean.
* `#discharges` (`scratch/igusa-gal/Discharges.lean`; output in `Discharges-output.txt`):
  ```
  DISCHARGES [OpenResearchLeaves45.igusaGL2DS] by X1Igusa.igusaGL2DS_of_igusaGL2DSGal
    still assumes: [X1Igusa.IgusaGL2DSGal]
    axioms: [propext, Classical.choice, Quot.sound]
  DISCHARGES [OpenResearchLeaves45.igusaGL2DS] by X1Igusa.igusaGL2DS_of_igusaGL2DSGalSome
    still assumes: [X1Igusa.IgusaGL2DSGalSome]
    axioms: [propext, Classical.choice, Quot.sound]
  ```
* The autofold dry run for `autofold.json` gives strict 9/25 → 10/24 and strictest 9/25 → 10/24. The generated
  module, with its first line removed (`scratch/igusa-gal/DryRunFold.lean`), compiles:
  `HDec.HSyn.sixContactMin_of_open65` uses only the standard axioms.
* The dry run for `autofold-some.json` gives the same counts.

## 6. Leaves rated

| leaf | kind | printed form? | reason |
| --- | --- | --- | --- |
| `X1Igusa.IgusaGL2DSGalSome` | published | yes | DS Thm 7.6.3 (surjectivity of ρ) for one basis, on `Gal(ℚ(j, E_j[N])/ℚ(j))` with `ℚ(j, E_j[N])` as DS define it, `N > 1`; only injectivity is dropped |
| `X1Igusa.IgusaGL2DSGal` | published | yes, up to the every-basis step | as above, for every basis; the step from one basis is elementary and proved in Lean (`igusaGL2DSGal_of_some`) |
