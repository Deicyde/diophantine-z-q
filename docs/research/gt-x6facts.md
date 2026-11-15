# gt-x6facts: `babaGranathRationalAb` reduced to the existence of the three CM pairs; `gonzalezRotgerX6Ab` stays a leaf

Task gt-x6facts, 2026-11-14. Base a454ad64 (leaf-fold16, top module `TailZ26`, 61 H fields). Lean:
`ZInQKernel/Contrib/OneProof/X6Facts.lean` (the contribution); `scratch/gt-x6facts/` (log, `#discharges` check,
autofold spec and dry-run, arithmetic checks). No other file under `ZInQKernel/` or `blueprint/` was edited.
This is model work with no human review.

Marks: **VERIFIED** means compiled, computed, or read in a file. **STANDARD** means published, with a reference.
**SPECULATIVE** means a judgement. **UNVERIFIED** means a theorem number or locator recalled without a source
(this host has no network).

## 1. Main result

**`babaGranathRationalAb` is a theorem from the bundle field `elkiesEquationsX6Ab` and one new witness-free
leaf, `QMPairsCMExist`.** The new leaf says that over `ℚ̄` there are QM pairs with CM by `ℤ[i]`, by `ℤ[ζ₃]` and
by `ℤ[√−6]`. The new leaf is **strictly weaker** than the field it replaces: it follows from
`BabaGranathRationalAb` alone. So under Elkies' leaf the two statements are equivalent. VERIFIED: compiled, and
every theorem uses only `[propext, Classical.choice, Quot.sound]`.

```lean
namespace HDec.QMSplit.Moduli.X6Facts

def QMPairsCMExist : Prop :=
  (∃ P : QMPair Qbar, HasCM4 P.q) ∧ (∃ P : QMPair Qbar, HasCM3 P.q) ∧ (∃ P : QMPair Qbar, HasCM24 P.q)

theorem babaGranathRationalAb_of_elkies (hE : ElkiesEquationsX6Ab) (hC : QMPairsCMExist) :
    BabaGranathRationalAb
theorem qmPairsCMExist_of_babaGranath (h : BabaGranathRationalAb) : QMPairsCMExist
theorem babaGranathRationalAb_iff (hE : ElkiesEquationsX6Ab) : BabaGranathRationalAb ↔ QMPairsCMExist
theorem cmExists_iff (X) (Ψ) : CMExists X Ψ ↔ QMPairsCMExist

-- the printed setting over ℂ
def QMPairsCMExistC : Prop :=
  (∃ P : QMPair ℂ, HasCM4 P.q) ∧ (∃ P : QMPair ℂ, HasCM3 P.q) ∧ (∃ P : QMPair ℂ, HasCM24 P.q)
theorem qmPairsCMExist_of_C (hC : QMPairsCMExistC) (hST : …QMSplitSTQM.ShimuraTaniyamaQbar) : QMPairsCMExist
theorem babaGranathRationalAb_of_printed (hE : ElkiesEquationsX6Ab) (hST : …ShimuraTaniyamaQbar)
    (hC : QMPairsCMExistC) : BabaGranathRationalAb
```

**`#discharges`** (VERIFIED; `scratch/gt-x6facts/Discharges.lean`, output in `discharges.out`, run after
`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.X6Facts`):

```
DISCHARGES [OpenResearchLeaves16.babaGranathRationalAb] by HDec.QMSplit.Moduli.X6Facts.babaGranathRationalAb_of_elkies
  still assumes: [HDec.QMSplit.Moduli.ElkiesEquationsX6Ab, HDec.QMSplit.Moduli.X6Facts.QMPairsCMExist]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves16.babaGranathRationalAb] by HDec.QMSplit.Moduli.X6Facts.babaGranathRationalAb_of_printed
  still assumes: [HDec.QMSplit.Moduli.ElkiesEquationsX6Ab,
 HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar,
 HDec.QMSplit.Moduli.X6Facts.QMPairsCMExistC]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 67 open hypotheses, 502 theorems checked, 2 discharge one
```

`ElkiesEquationsX6Ab` is a field of `OpenResearchLeaves16`. `ShimuraTaniyamaQbar` is a field of
`OpenAddedLeaves14`. The only new statements are `QMPairsCMExist` (ℚ̄ form) and `QMPairsCMExistC` (ℂ form).

**`gonzalezRotgerX6Ab` is not reduced.** It is a published leaf (González–Rotger Thm 5.12, audit YES), and its
content (residue fields of all CM points of conductor prime to 6) is used in that generality by NoCM. It is
consistent with Elkies' model at the three elliptic CM points (§3).

## 2. `babaGranathRationalAb`

### 2.1 The proof

The proof takes Elkies' witness `(Y, Φ, X, Ψ, fY, t)` and sets `π = t` and
`(t₄, t₃, t₂₄) = (1, ∞, 0) ∈ P¹(ℚ)`.

* **Distinctness.** The three values are distinct: `coe_ne_infty` and `1 ≠ 0`.
* **Fibre clause.** This is Elkies' fibre clause verbatim.
* **Forward CM clauses.** CM4 gives `t = 1`, CM3 gives `t = ∞` and CM24 gives `t = 0`. These are Elkies' value
  clauses.
* **Converse CM clauses.** Take a point `x` with `t(x) = 1`.
  * Pick a pair `P₄` with CM by `ℤ[i]` (from `QMPairsCMExist`), and set `x₄ = Ψ⁻¹[P₄]`; Elkies gives `t(x₄) = 1`.
  * Elkies' fibre clause then gives `α` with `P₄.twist α ≅ P` as QM pairs.
  * `HasCM4` is invariant under twists (`hasCM4_twist`) and under isomorphisms (`HasCM4.of_iso`), so `P` has CM
    by `ℤ[i]`. This is the chain's `cm_of_val` argument.
  * The cases `∞` and `0` are the same.

### 2.2 The converse, so the new leaf is strictly weaker

`qmPairsCMExist_of_babaGranath` derives the new leaf from Baba–Granath's leaf alone:
* the chain's `ShimuraSplit.surj_of_fibre` (finite twist classes plus the proved `CurveSurj`) makes `π` onto
  `P¹(ℚ̄)`;
* a point over `t₄` carries a pair with CM by `ℤ[i]`, by Baba–Granath's converse clause (and the same for `t₃`
  and `t₂₄`).

In the chain, Baba–Granath's leaf was in effect the source of `CMExists`, the existence of the three CM points
(`cmExists_of_iff`). `cmExists_iff` shows that `QMPairsCMExist` is exactly the witness-free form of the chain's
`CMExists X Ψ`.

### 2.3 The ℂ form

`qmPairsCMExist_of_C` descends a CM pair from `ℂ` to `ℚ̄`. The descent glue is proved; it reuses the chain's
declarations and copies none.
* **Model over `ℚ̄`.** The bundle field `shimuraTaniyamaQbar` (through the chain's `stQM_lf7`) gives
  `A ≅ A₀ ×_{ℚ̄,ιe} ℂ`.
* **Endomorphisms descend.** T11(b) (`AVB2.t11b_of_exists t11bExists_lf8`, proved in the chain) makes `endBCe`
  bijective (`LeafQCheck.endBCe_bijective`). Conjugating by the isomorphism (`LeafQCheck.conjE`) then gives an
  injective ring map `κ : End A → End A₀`.
* **The pair over `ℚ̄`.** `κ ∘ ι` is a QM structure on `A₀`, and `A₀` has dimension 2 by
  `LeafQCheck.dim_eq_of_iso`.
* **CM descends.** `κ` maps the commutant into the commutant (`map_mem_com`) and preserves the three CM
  equations.

### 2.4 Leaf table

| statement | kind | source (locators UNVERIFIED) | strict |
|---|---|---|---|
| `QMPairsCMExist` (ℚ̄) | published, a consequence | see the five points below | LEAF |
| `QMPairsCMExistC` (ℂ) | published, printed setting | Shimura 1967 §§1-3 (the source of the bundle's `QMCentralizerCMC`); Eichler / Vignéras embeddings | LEAF |

Why `QMPairsCMExist` holds:
* The orders `ℤ[i]`, `ℤ[ζ₃]` and `ℤ[√−6]` embed in `𝒪`, by the elements `i + j`, `(1 + j)/2` and `2j + k`.
  VERIFIED by hand: `(i + j)² = 2 − 3 = −1` and `(2j + k)² = −12 + 6 = −6` in `(2, −3)`. Their embedding is
  optimal by Eichler's theorem (Vignéras, LNM 800, Ch. III §5).
* Shimura 1967 §§1-3: the surface `A_τ = ℂ²/ι(𝒪)(τ,1)ᵀ`, at the fixed point of the embedded order, has
  `End_𝒪(A_τ) = Φ_τ(k) ∩ 𝒪`.
* Shimura–Taniyama descends it to `ℚ̄`.
* Independently, González–Rotger 2006 Prop. 5.6 gives `#CM(R) = 2^b h(R) = 2 > 0` on `X₀(6,1)` for each of the
  three orders.
* It is also a consequence of Baba–Granath's leaf (§2.2).

**Counts.** In the ℚ̄ form the fold replaces one LEAF by one LEAF, so the strict count is unchanged at 47/14 on
61 (autofold's own count, VERIFIED by `--dry-run`). What changes:
* The UNVERIFIED reading of Baba–Granath's §3.1 table (the CM assignment) leaves the chain. The CM assignment now
  comes from Elkies' value clauses, whose `0/∞` orientation was already an UNVERIFIED reading of the chain.
* A moduli-theoretic leaf (a coordinate on `X₆/W` with three rational branch values) is replaced by the bare
  existence of three abelian surfaces, which needs no moduli space. That statement is a candidate for a direct
  Lean construction once Jacobians or `E × E` exist as `PkgI3.AbVar` (SPECULATIVE).
* Trade-off (SPECULATIVE): after the fold, the fibre clause and the CM values of `t` rest on Elkies' leaf alone.
  Before the fold, Baba–Granath's leaf also asserted them. Elkies' leaf is flagged GLUE in `kinds.tsv` ("pending
  reading: the fibre clause combines Elkies with the moduli meaning of W"), so the chain then depends more on
  that flagged leaf.

### 2.5 Fold

`scratch/gt-x6facts/autofold-spec.json` (ℚ̄ form) discharges `babaGranathRationalAb` by
`babaGranathRationalAb_of_elkies {n}.elkiesEquationsX6Ab {n}.qmPairsCMExist`, with the leaf `qmPairsCMExist` added
to the research bundle.
* `python3 scripts/one_proof/autofold.py … --dry-run` (nothing written) reports `strict count: 47/14 on 61 ->
  47/14 on 61`.
* Its generated module, `scratch/gt-x6facts/FoldDryRun.lean` (`OpenResearchLeaves17`, `sixContactMin_of_open21`),
  compiles with standard axioms (VERIFIED).

The ℂ form needs `shimuraTaniyamaQbar` from the *added* bundle inside the research bundle's conversion theorem.
autofold's `{n}` covers only the field's own bundle, so that fold would be written by hand.

## 3. `gonzalezRotgerX6Ab`

* **Status.** It stays a published LEAF: González–Rotger, J. Math. Soc. Japan 58 (2006) Thm 5.12, read by the
  locator audit. It is stated on one coarse witness `X₆` of the fine moduli scheme.
* **Not reducible here.** Its consumer, NoCM (`FibreComTrivial`, TailA), uses the residue-field degree for an
  *arbitrary* CM order of conductor prime to 6: it rules out every CM order at a point over `J(u)`, whose residue
  field is `ℚ(i)`. So the leaf cannot be replaced by finitely many computed instances. A weaker form would not
  discharge the field (CONTRIBUTING: the type must match).
* **No proof from the bundle.** None was found:
  * `GonzalezRotgerCountX6Ab` assumes existence;
  * `RayClassCMAb` bounds the residue field from above only;
  * `QMCentralizerCMC` gives the shape of `End_𝒪`, not the residue field.
* **Statement checks (VERIFIED by reading `R5ptProps`, Leaves.lean L191):**
  * `R = ℤ` is excluded, since `conductor ℤ = 0` and `Nat.Coprime 0 6` is false.
  * `inertCount6` and `Pic R` are invariants of the ring isomorphism `com P.q ≃+* R`, so the abstract-isomorphism
    reading is harmless.
* **Consistency with Elkies' model at the three elliptic CM points** (VERIFIED, computed by
  `scratch/gt-x6facts/cm_check.py` with PARI):

| order | `h` | 2, 3 in `k` | `b` | GR: `[ℚ(x):ℚ]`, `k ⊆ ℚ(x)` | Elkies' points (`Y²+3X²+3Z²=0`, `t=−X²/Z²`) | count `2^b h` |
|---|---|---|---|---|---|---|
| `ℤ[i]` | 1 | 2 ram., 3 inert | 1 | 2, yes | `t = 1`: `X/Z = ±i`, `ℚ(i)` | 2 = 2 points |
| `ℤ[ζ₃]` | 1 | 2 inert, 3 ram. | 1 | 2, yes | `t = ∞`: `Y/X = ±√−3`, `ℚ(√−3)` | 2 = 2 points |
| `ℤ[√−6]` | 2 | both ram. | 0 | 2, no requirement | `t = 0`: `Y/Z = ±√−3`, `ℚ(√−3) ∌ √−6` | 2 = 2 points |

  The Möbius map `j = 16(t − 1)/27` sends `t = 1, ∞, 0` to the chain's normalization `0, ∞, −16/27` (computed).
  The residue fields do not distinguish `t = 0` from `t = ∞`: both are `ℚ(√−3)`. This agrees with Elkies'
  docstring, where the `0/∞` orientation rests on the text.

## 4. What remains

* `QMPairsCMExist` (or `QMPairsCMExistC`) is a published leaf. A Lean proof needs an abelian surface object with an
  `𝒪`-action. Possible constructions:
  * `E × E` for a CM elliptic curve `E`, with `𝒪 ↪ M₂(End E)`;
  * a Jacobian of one of Baba–Granath's genus-2 curves.

  Neither exists as `PkgI3.AbVar` in the chain or in Mathlib 4.35 today. Igusa invariants and genus-2 equations
  (the igusa-alg route) do not reach these statements: none of the two targets mentions a curve equation.
* `gonzalezRotgerX6Ab`: remains a published leaf (§3).

## 5. Files

| file | content | check |
|---|---|---|
| `ZInQKernel/Contrib/OneProof/X6Facts.lean` | the contribution (11.6 KB), imports `TailZ22` only | `lake build` OK, standard axioms |
| `scratch/gt-x6facts/Discharges.lean`, `discharges.out` | `#discharges` | output in §1 |
| `scratch/gt-x6facts/autofold-spec.json`, `FoldDryRun.lean` | fold spec; dry-run module | compiles, standard axioms |
| `scratch/gt-x6facts/Statements.lean` | verbatim copies of the targets and their clause lists (reference, not compiled) | — |
| `scratch/gt-x6facts/cm_check.py` | class numbers, splitting, conic residue fields, Möbius values | run with `~/pyenv/bin/python -I` |
| `scratch/gt-x6facts/log.md` | results log | — |
