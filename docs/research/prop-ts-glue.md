# prop-ts-glue: the three glue Props under Proposition TS, reduced and partly proved in Lean

Task prop-ts-glue, 2026-11-13. The objects are `PropTSRed.SpecNonMeeting`,
`PropTSRed.KummerMeetGlue` and `PropTSRed.CoverModelOfHecke` from `scratch/prop-ts/PropTS.lean`
(docs/research/prop-ts.md; merged from origin/wip/prop-ts). They are the glue under
Proposition TS in prop-ts's `propTSAll_of_bundle_meet`.

| File | Contents |
|---|---|
| `scratch/prop-ts-glue/PropTSGlue.lean` | the Lean file (3329 lines) |
| `scratch/prop-ts-glue/log.md` | results log |
| `scratch/prop-ts-glue/compile_out.txt` | compiler output |
| `LocalData.lean`, `HorizTransfer.lean` | development files, Mathlib-only, compiled; their results are pasted into the main file |

Model work only; no human has reviewed it. Marks: **VERIFIED** means compiled, computed or read
in a named source. **STANDARD** means a published result with its reference. **PROVED HERE**
means an argument written here and not reviewed. **SPECULATIVE** means an assessment. Locators
from memory are **UNVERIFIED** (no network).

## 1. Main result

**None of the three statements is false, vacuous or inert, and none was changed. Each is reduced
in Lean to smaller named Props, and four of the new pieces are proved.** The proved pieces are:

- `SNLocalData`;
- `SNHorizontalTransfer`;
- `SNVertical`, modulo the one-line field-theory glue `VerticalResidueSeparable`;
- purity, through an inlined copy of t-purity3's proof.

All of the `p`-adic and Gauss-lemma bookkeeping is also proved.

**What is VERIFIED:**

- `lake env lean scratch/prop-ts-glue/PropTSGlue.lean` (about 25 s) gives 0 errors. The 37
  warnings are linter warnings only.
- All 32 new `#print axioms` lines read `[propext, Classical.choice, Quot.sound]`.
- `check_identical.py` prints `PREFIX IDENTICAL`: the first 906 lines are
  `scratch/prop-ts/PropTS.lean` byte for byte, so the three statements and their dependencies are
  verbatim.
- It also prints `PURITY COPY CONTAINED`: t-purity3's `PurityDim2.lean` (origin/wip/t-purity3,
  7e4d4dd0) is included verbatim, minus its import and `#print` lines.

**The final composite** is `PropTSGlue.propTSAll_of_pieces''`. Its hypotheses are:

- **Leaves:**
  - T2 (`PkgI2.AbhyankarDVR`);
  - `R1R2fp`.
- **Kernel glue:**
  - `MobiusGlue`.
- **Open glue (14 Props), for `SpecNonMeeting`:**
  - `VerticalResidueSeparable`;
  - `SNSpecialize`.
- **Open glue, for `KummerMeetGlue`:**
  - `KummerCompositum`;
  - `KummerAbhyankarFinGlue`, `KummerOtherBranchFin`, `KummerVerticalFin`;
  - `KummerAbhyankarInfGlue`, `KummerOtherBranchInf`, `KummerVerticalInf`.
- **Open glue, for `CoverModelOfHecke`:**
  - `HeckeIrreducible`, `HeckeNormalizationIrr` (together they give `HeckeNormalization`);
  - `HeckeDegree`, `HeckeBranch`, `HeckeNoVertRam`.

T2 enters only through the two Abhyankar steps. No new literature leaf is needed.

| Prop of the task | reduction (compiled) | proved along the way |
|---|---|---|
| `SpecNonMeeting` | `specNonMeeting_of_pieces4 : PurityGlobalDim2 → VerticalResidueSeparable → SNSpecialize → SpecNonMeeting`. `PurityGlobalDim2` is a theorem in the file (`purityGlobalDim2`, t-purity3's proof inlined) | `snLocalData`, `snHorizontalTransfer`, `snVertical_of_sep`, `snHeightOne_of_pieces`; the Gauss-lemma arithmetic (`exists_int_multiple`, `homog_mem`, `notMem_of_val_zero`); `isFractionRing_zx`; `exists_secIdeal`; `regular_dim2_intPoly` |
| `KummerMeetGlue` | `kummerMeetGlue_of_pieces'`, seven pieces | the case split; all of prop-ts §4.2's arithmetic in both cases (`kummerMeetFin_of_pieces`, `kummerMeetInf_of_pieces`) |
| `CoverModelOfHecke` | `coverModelOfHecke_of_pieces` (four pieces) and `heckeNormalization_of_irr` | `coverModelOfHecke_of_witness : MobiusGlue → R1R2fp → CoverModelWitness → CoverModelOfHecke`, so one triple suffices (`functionFieldModel_transfer`, `coverModel_transfer`) |

## 2. `SpecNonMeeting`

**Setting.** `E/ℚ(X)` is finite, `p` is prime, `[E:ℚ(X)] < p` and `NoVerticalRam E p`. The point
`s₀ = a/d` is `p`-integral and meets no branch point mod `p` (`NonMeeting`).

| Symbol | Meaning |
|---|---|
| `m` | the maximal ideal `(p, dX − a)` of `ℤ[X]`, constructed as `ker(ℤ[X] → 𝔽_p, X ↦ a/d)` (`exists_secIdeal`) |
| `R` | `ℤ[X]_m` |
| `S` | the integral closure of `R` in `E` |
| `C` | the integral closure of `ℤ[X]` in `E` |
| `B` | the integral closure of `ℚ[X]` in `E` |

The proof follows prop-ts §4.1: `R` is regular local of dimension 2, `S` is étale over `R` by
purity, and the result follows by specialization.

| Prop | status | content / proof |
|---|---|---|
| `PurityGlobalDim2` | **theorem** (t-purity3's proof, inlined) | Zariski–Nagata purity over a 2-dimensional regular local base |
| `SNLocalData` | **theorem** `snLocalData` | `S` is normal, `R`-finite, and `R ↪ S`. Uses `isFractionRing_zx`, `IsIntegralClosure.finite`, `integralClosure.isIntegrallyClosedOfFiniteExtension`, `isIntegrallyClosed_of_isLocalization` |
| `SNHeightOne` | **theorem** from the next two (`snHeightOne_of_pieces`) | the horizontal case also uses `NonMeeting`: (1) `N f = F ∈ ℤ[X]` with `p ∤ N`; (2) `d^k F ≡ Σ c_i a^i d^{k−i}` mod `dX − a`; (3) so `F ∉ m`, and `F` is a unit of `R` |
| `SNHorizontalTransfer` | **theorem** `snHorizontalTransfer` | see the steps below the table |
| `SNVertical` | **theorem** from `VerticalResidueSeparable` (`snVertical_of_sep`) | see the steps below the table |
| `VerticalResidueSeparable` | **open glue** (field theory, STANDARD) | `[E:ℚ(X)] < p ⇒ Algebra.HasSeparableResidueFieldsAt ℤ[X] C (pℤ[X])`. Proof: `f ≤ [E:ℚ(X)] < p`, and an extension of degree `< p` in characteristic `p` is separable (`Polynomial.separable_or`) |
| `SNSpecialize` | **open glue** (STANDARD) | `R → S` étale ⇒ every residue field `B/𝔓` over `X − s₀`, embedded in `ℚ̄`, is a number field unramified at `p`. Proof: base change along `R → R/(dX − a) = ℤ_(p)`; then étale over a DVR ⇒ unramified |

**Proof of `SNHorizontalTransfer`:**

1. `S` and `B` are localizations of `C`: `IsLocalization.integralClosure`, using that a field is
   its own localization.
2. So `S_{Q'}` and `B_Q` are both `C_𝔮`, where `𝔮 = Q' ∩ C`, and they are `C`-isomorphic
   (`IsLocalization.algEquiv`). Since `P ∩ ℤ = 0` (`int_notMem`), `𝔮B` is prime.
3. If `e(Q) = 1`, then `ℚ[X] → B_Q` is formally unramified (`Ideal.ramificationIdx_eq_one_iff`;
   the residue fields have characteristic 0).
4. Then `ℤ[X] → B_Q` is formally unramified, hence `ℤ[X] → S_{Q'}`, hence `R → S_{Q'}`
   (`FormallyUnramified.of_restrictScalars`).

**Proof of `SNVertical`:**

1. `P = pR`: compare heights (`IsLocalization.height_under`).
2. `𝔮 = Q' ∩ C` lies over `pℤ[X]`, so `NoVerticalRam` gives `e(𝔮) = 1`.
3. Separable residue fields (`VerticalResidueSeparable`) then make `ℤ[X] → C_𝔮` formally
   unramified.
4. `C_𝔮 ≅ S_{Q'}`, so `R → S_{Q'}` is formally unramified.

## 3. `KummerMeetGlue`

`KummerShape E E' ι r` says that `ι : E → E'` sends `X` to `r ∈ ℚ(s)` and that `E'` is generated
by `ι(E)` and `s`, i.e. `E' = E(s)`. The two substitutions are:

- `rFin b c n`: `X = b + s^n/c`, i.e. `s^n = c (X − b)`;
- `rInf c n`: `X = c/s^n`.

| Prop | kind | content |
|---|---|---|
| `KummerCompositum` | glue (algebra, STANDARD) | Hypothesis: `r = P/Q` non-constant, regular at `s₀`, with `r(s₀) = t`. Conclusion: there is `E' = E(s)` with `[E':ℚ(s)] ≤ [E:ℚ(X)]`, and a prime over `s − s₀` whose residue field contains `ℚ(φ(B/𝔓))` |
| `KummerAbhyankarFin(Glue)` | glue from T2 | if every prime over `X = b` has `e ∣ n`, then `E'/ℚ(s)` is unramified over `s = 0` |
| `KummerOtherBranchFin` | glue (composita) | a ramified prime of `E'` lies over `s = 0` or contains `s^n − c(b' − b)` for some `b' ∈ S ∖ {b}` |
| `KummerVerticalFin` | glue (Gauss valuation) | Hypotheses: `0 < n < p`, `c` a `p`-unit, `b` `p`-integral, `[E:ℚ(X)] < p`. Conclusion: `NoVerticalRam E p ⇒ NoVerticalRam E' p` |
| `…Inf` (three Props) | the same at `∞` | the meeting polynomial is `b' s^n − c`, with `b' ∈ S ∖ {0}` |

**Proved: all the bookkeeping of prop-ts §4.2.**

- **Finite case:** `t − b = p^M u`, `c = u^{n−1}`, `s₀ = p^{M/n} u`, and `s₀^n = c (t − b)`.
- **Case at `∞`:** `t = p^{−M} u`, `c = u^{1−n}`, `s₀ = p^{M/n}/u`, and `t s₀^n = c`.
- **`NonMeeting E' p s₀`** (both cases):
  - the meeting polynomial has `p`-integral coefficients;
  - its value at `s₀` is `c(t − b')`, respectively `c(b' − t)/t`, which is nonzero and a `p`-unit.

## 4. `CoverModelOfHecke`

The pieces quantify over the triples `(Y, Φ, π)` with R1fp, R1hecke and R2fp, and over the
fields `E` that carry prop-ts's `NormalizationModel Y π E`. `NormalizationModel` determines `E`
up to isomorphism (Jacobson; confirmed by the reviewer), so the "∀ E" pieces are properties of
the cover.

| Prop | content | source |
|---|---|---|
| `HeckeIrreducible` | `Y` is irreducible | **SPECULATIVE**. `π₀(Y₃) = (ℤ/3)^×`, and its two points should be swapped by `Gal(ℚ(√−3)/ℚ)` (Deligne's reciprocity on `π₀`) |
| `HeckeNormalizationIrr` | for irreducible `Y`: there is a finite Galois `E/ℚ(X)` with `NormalizationModel Y π E` | h-b1 M1, M2, M8 |
| `HeckeDegree` | `[E:ℚ(X)] ≤ 324` (it divides `\|Γ'\| = 144`) | h-b1 M3 |
| `HeckeBranch` | `BranchData E {0, −16/27} (4, 2) 6` | h-b1 M4 (Baba–Granath §3.1) |
| `HeckeNoVertRam` | `NoVerticalRam E p` for every prime `p > 324` | h-b1 §3, Lemma NV |

If `HeckeIrreducible` failed, `HeckeNormalization` would be false. The safe form is then
`CoverModelWitness`: a cover model for one triple, with `FunctionFieldModel`. It suffices, by
`coverModelOfHecke_of_witness`.

## 5. Independent review (read-only model agent, no Lean)

**Verdict:** no false, vacuous or trivial Prop. Every open glue Prop is true as stated in Lean.
The reviewer checked, in particular:

- the junk values and the ramification conventions;
- `KummerCompositum`'s degree bound and the existence of the prime over `s − s₀`;
- `KummerOtherBranchInf` when `0 ∈ S`;
- `SNSpecialize`'s identification of residue fields;
- that the Hecke "∀ E" forms are properties of the cover.

The one unverified input it found is the `ℚ`-irreducibility of `Y₃`. That input is now its own
Prop, `HeckeIrreducible`. The truth arguments for `SNHorizontalTransfer` and `SNVertical` are now
Lean proofs (§2).

## 6. What remains

Open glue, all STANDARD commutative algebra or curve theory; no new literature leaf:

1. **`VerticalResidueSeparable`.** Two steps:
   - the residue degree at a vertical prime is at most `[E:ℚ(X)]` (localize at `pℤ[X]`: a DVR,
     with the integral closure free of rank `[E:ℚ(X)]`);
   - degree `< p` ⇒ separable (`Polynomial.separable_or`).
2. **`SNSpecialize`.** Étale base change to `ℤ_(p)`, then a finite étale domain over `ℤ_(p)` is
   unramified at `p`, phrased through the repository's `UnramifiedAt`.
3. **The seven Kummer pieces.** `KummerCompositum` (a factor of `E ⊗ ℚ(s)` with a place over a
   given place), Abhyankar via T2, and ramification in composita.
4. **The Hecke pieces.**
   - `HeckeNoVertRam` is h-b1's Lemma NV (inputs: R1rec and Abhyankar).
   - `HeckeIrreducible` is a reciprocity statement on `π₀` that should be checked against
     Deligne or Milne.

The Lean pitfalls met along the way are in the log (step 7).
