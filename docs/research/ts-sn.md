# ts-sn: `SNSpecialize` proved, so `SpecNonMeeting` is a theorem

Task ts-sn, 2026-11-13. The targets were the two open Props under `SpecNonMeeting` in Proposition
TS, from `scratch/prop-ts-glue/PropTSGlue.lean` (docs/research/prop-ts-glue.md; merged from
origin/wip/prop-ts-glue):

- `PropTSGlue.VerticalResidueSeparable`;
- `PropTSGlue.SNSpecialize`.

Model work only; no human has reviewed it. **VERIFIED** means compiled, computed, or read in a
named source. **STANDARD** means a published result with its reference. Locators given from memory
are marked **UNVERIFIED**.

## 1. Main result

**Both Props are theorems, with no hypotheses. Neither statement was changed.** (VERIFIED)

- **`PropTSGlue.snSpecialize : SNSpecialize`** is new. It is a complete Lean proof.
- **`PropTSGlue.verticalResidueSeparable : VerticalResidueSeparable`** was already proved before
  this task started, in prop-ts-glue's step 13 (`verticalResidueSeparable_of_degree
  verticalResidueDegree`). Here it is only restated as a named theorem.
- It follows that **`PropTSGlue.specNonMeeting : SpecNonMeeting`** holds with no hypotheses.
  `SpecNonMeeting` is one of the three glue Props under Proposition TS.
- Proposition TS now rests on fewer open Props. The new composite is
  `PropTSGlue.propTSAll_final'`, which proves `PropTSAll` from:
  - the bundle leaves T2 (`PkgI2.AbhyankarDVR`) and `R1R2fp`;
  - the kernel glue `MobiusGlue`;
  - 12 open glue Props:
    - seven Kummer pieces: `KummerCompositum`, `KummerAbhyankarFinGlue`, `KummerOtherBranchFin`,
      `KummerVerticalFin`, and the three `…Inf` pieces;
    - five Hecke pieces: `HeckeIrreducible`, `HeckeNormalizationIrr`, `HeckeDegree`,
      `HeckeBranch`, `HeckeNoVertRam`.

  Before this task there were 13 open glue Props; `SNSpecialize` is the one removed.

**What compiles** (VERIFIED, output in `scratch/ts-sn/compile_out.txt`):

- `lake env lean scratch/ts-sn/TSSN.lean` takes about 110 s and gives 0 errors and no `sorry`.
  The 71 warnings are linter warnings only.
- All 69 `#print axioms` lines read `[propext, Classical.choice, Quot.sound]`.
- `python3 scratch/ts-sn/check_prefix.py` prints `PREFIX IDENTICAL`: `TSSN.lean` begins with
  `scratch/prop-ts-glue/PropTSGlue.lean` byte for byte. So the statements and all their
  dependencies are verbatim; that file in turn begins with `scratch/prop-ts/PropTS.lean`
  verbatim.
- Before compiling, the imported modules `ZInQKernel.HDecomp.QM.Pin` and
  `ZInQKernel.HDecomp.Descent.B2Glue` were built with `lake build`.

| File | Contents |
|---|---|
| `scratch/ts-sn/TSSN.lean` | the deliverable: verbatim prefix plus the ts-sn appendix (4210 lines) |
| `scratch/ts-sn/Abstract.lean` | development file for the abstract criterion (compiled on its own) |
| `scratch/ts-sn/Concrete.part`, `assemble.sh` | development pieces of the appendix |
| `scratch/ts-sn/check_prefix.py`, `compile_out.txt`, `log.md` | the prefix check, the compiler output, the results log |

## 2. The statement of `SNSpecialize`

**Setting.**

| Symbol | Meaning |
|---|---|
| `E/ℚ(X)` | finite |
| `p` | a prime |
| `s₀ = a/d` | `p`-integral |
| `m ⊂ ℤ[X]` | maximal, containing `p` and `dX − a` |
| `R` | `ℤ[X]_m` |
| `S` | the integral closure of `R` in `E` |
| `B` | the integral closure of `ℚ[X]` in `E` |
| `𝔓` | a prime of `B` over `(X − s₀)` |
| `φ : B/𝔓 → ℚ̄` | any ring map |
| `L` | `ℚ(φ(B/𝔓))` |

**Statement.** If `R → S` is étale, then `L` is finite over `ℚ` and `UnramifiedAt L p`: every prime
of `𝓞_L` over `p` has Mathlib's ramification index 1.

The statement is not vacuous. Étaleness is a genuine hypothesis, and in `SpecNonMeeting` it is
supplied by purity. The proof uses it, through formal unramifiedness.

## 3. The proof (all in Lean)

### 3.1 Abstract criterion: `unramifiedAt_of_subring`

Let `L ⊂ ℚ̄` be finite over `ℚ`, and let `A ⊆ L` be a subring with these properties:

- `A` is Noetherian, and its fraction field is `L`;
- the integers prime to `p` are units in `A`;
- for each `y ∈ A`, some integer `n` prime to `p` makes `n·y` integral over `ℤ`;
- every maximal ideal of `A` contains `p`;
- for every prime `q ∋ p` of `A`, the maximal ideal of `A_q` is `(p)`.

Then `UnramifiedAt L p`. The proof:

1. Each `A_q` is a DVR, by `IsDiscreteValuationRing.TFAE`: the maximal ideal is principal.
2. So `A` is integrally closed (`IsIntegrallyClosed.of_localization_maximal`).
3. Hence `𝓞_L ⊆ A`, and `A` is the localization of `𝓞_L` at the integers prime to `p`.
4. For a prime `Q ∋ p` of `𝓞_L`, `(𝓞_L)_Q ≅ A_{QA}`
   (`isLocalization_isLocalization_atPrime_isLocalization`). So `(p)` is the maximal ideal of
   `(𝓞_L)_Q`.
5. That is exactly `ramificationIdx = 1` in Mathlib's length definition. The length-one unfolding
   is taken from Mathlib's `Ideal.ramificationIdx_eq_one`.

### 3.2 The concrete ring: `snSpecialize_aux`

Let `C` be the integral closure of `ℤ[X]` in `E`.

**The maps.**

- `ρ : C → B/𝔓 → L` sends `g ∈ ℤ[X]` to `g(s₀)`. Proof: `f − f(s₀) ∈ (X − s₀) = 𝔓 ∩ ℚ[X]`, and a
  ring map out of `ℚ` is unique.
- `S = C_m`, by `IsLocalization.integralClosure`, as in prop-ts-glue.
- `ψ : S → L` extends `ρ`. This works because `g ∉ m` implies `g(s₀) ≠ 0`.
- `A := ψ(S)`.

**The arithmetic: `homog_data`.** For `g ∈ ℤ[X]` there are `k` and an integer `n₀ = d^k g(s₀)`
with `g ∈ m ⟺ p ∣ n₀`. It is built on prop-ts-glue's `homog_mem` and `C_notMem`.

**`L` is finite over `ℚ`.** `L` is equal to `φ(B/𝔓)`, which is a `ℚ`-subalgebra of `ℚ̄`. It is
spanned over `ℚ` by the images of finitely many `ℚ[X]`-generators of `B`, because
`φ(f·b) = f(s₀)·φ(b)`.

**The hypotheses of the criterion:**

- **Noetherian:** `A` is finite over `R`.
- **Units:** if `p ∤ n`, then `C n ∉ m`.
- **Maximal ideals contain `p`:** `A` is integral over the local ring `R`.
- **Maximal ideal of `A_q` is `(p)`:**
  - `R → A_q` is formally unramified: `R → S` is étale, `S → A` is surjective
    (`FormallyUnramified.of_surjective`), and `A → A_q` is a localization.
  - `A_q` is essentially of finite type over `R`, and `R → A_q` is a local map.
  - So `Algebra.FormallyUnramified.map_maximalIdeal` gives `max(A_q) = m·A_q`.
  - `homog_data` sends `m` into `pA`.
- **Fraction field:** an integer multiple of each element of `B` lies in `C`
  (`exists_multiple_integral_of_isLocalization` along `ℤ[X] → ℚ[X]`).
- **Integrality:** for `c ∈ C`, `ρ(c)` is integral over `ℤ[1/d]`, via `Localization.Away d`. So
  `d^j ρ(c)` is integral over `ℤ`. Combining with `y·g(s₀) = ρ(c)` and `n₀ = d^k g(s₀)` gives
  `(n₀ d^j)·y` integral over `ℤ`.

This is the route prop-ts-glue §6 suggested: étale over `ℤ_(p)` after specialization, then
unramified. It is carried out without forming `S/(dX − a)S`: formal unramifiedness passes to the
quotient `A`, and the DVR property of `A_q` is derived directly.

## 4. Leaves and glue

No new leaf is used. `SNSpecialize` was glue, and it is now proved glue. Nothing under
`SpecNonMeeting` remains open.

## 5. What remains

Nothing remains for this task. Under Proposition TS, the open glue is now:

- the seven Kummer pieces;
- the five Hecke pieces.

These are listed in docs/research/prop-ts-glue.md §3–4. Integration note: the appendix of
`TSSN.lean` depends only on prop-ts-glue's file, so it can be pasted after that file's content.
