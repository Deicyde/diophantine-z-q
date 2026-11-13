# prop-ts-glue: the three glue Props under Proposition TS, reduced in Lean

Task prop-ts-glue, 2026-11-13. Objects: `PropTSRed.SpecNonMeeting`, `PropTSRed.KummerMeetGlue`
and `PropTSRed.CoverModelOfHecke` from `scratch/prop-ts/PropTS.lean` (docs/research/prop-ts.md;
merged from origin/wip/prop-ts). These are the glue under Proposition TS in prop-ts's
`propTSAll_of_bundle_meet`. Lean file: `scratch/prop-ts-glue/PropTSGlue.lean`. Results log:
`scratch/prop-ts-glue/log.md`. Compiler output: `scratch/prop-ts-glue/compile_out.txt`.

Model work only; no human has reviewed it. Marks: **VERIFIED** means compiled, computed, or read
in a named source. **STANDARD** means a published result with its reference. **PROVED HERE**
means an argument written here and not reviewed. **SPECULATIVE** means an assessment. Locators
given from memory are **UNVERIFIED** (no network).

## 1. Main result

**None of the three statements is false, vacuous or inert, and none was changed. Each is reduced
in Lean to strictly smaller named Props. Two pieces are proved outright, and so is all the
`p`-adic and Gauss-lemma bookkeeping.** VERIFIED:

- `lake env lean scratch/prop-ts-glue/PropTSGlue.lean` gives 0 errors.
- All 24 new `#print axioms` lines read `[propext, Classical.choice, Quot.sound]`.
- The first 906 lines are `scratch/prop-ts/PropTS.lean` byte for byte. `check_identical.py`
  prints `PREFIX IDENTICAL`, so the three statements and everything they depend on are verbatim.

**The composite** (`PropTSGlue.propTSAll_of_pieces`): `PropTSAll` follows from the hypotheses
below.

- **Leaves:**
  - T2 (`PkgI2.AbhyankarDVR`);
  - `R1R2fp`.
- **Proved elsewhere:**
  - `PurityGlobalDim2`, proved by t-purity3 (`TPurity3.purityGlobalDim2`). It is copied here
    verbatim and enters as a hypothesis only because scratch files cannot import each other.
- **Kernel glue:**
  - `MobiusGlue`.
- **Glue left open by this task (13 Props):**
  - for `SpecNonMeeting`: `SNVertical`, `SNHorizontalTransfer`, `SNSpecialize`;
  - for `KummerMeetGlue`: `KummerCompositum`, `KummerAbhyankarFinGlue`,
    `KummerOtherBranchFin`, `KummerVerticalFin`, `KummerAbhyankarInfGlue`,
    `KummerOtherBranchInf`, `KummerVerticalInf`;
  - for `CoverModelOfHecke`: `HeckeNormalization`, `HeckeDegree`, `HeckeBranch`,
    `HeckeNoVertRam`.

In this list, T2 enters only through the two Abhyankar steps.

| Prop of the task | reduction (compiled) | proved along the way |
|---|---|---|
| `SpecNonMeeting` | `specNonMeeting_of_pieces'' : PurityGlobalDim2 → SNVertical → SNHorizontalTransfer → SNSpecialize → SpecNonMeeting` | `SNLocalData` (**theorem** `snLocalData`); `isFractionRing_zx`; the horizontal case of codimension-one unramifiedness, i.e. the Gauss-lemma argument (`snHeightOne_of_pieces` with `exists_int_multiple`, `homog_mem`, `notMem_of_val_zero`); `exists_secIdeal`; `regular_dim2_intPoly` (copied from prop-ts) |
| `KummerMeetGlue` | `kummerMeetGlue_of_pieces'` (seven pieces; T2 enters only through `KummerAbhyankarFinGlue`, `KummerAbhyankarInfGlue`) | the case split (`kummerMeet_of_cases`); all of prop-ts §4.2's arithmetic in both cases (`kummerMeetFin_of_pieces`, `kummerMeetInf_of_pieces`) |
| `CoverModelOfHecke` | `coverModelOfHecke_of_pieces : HeckeNormalization → HeckeDegree → HeckeBranch → HeckeNoVertRam → CoverModelOfHecke` | `coverModelOfHecke_of_witness : MobiusGlue → R1R2fp → CoverModelWitness → CoverModelOfHecke` (one triple suffices; `functionFieldModel_transfer`, `coverModel_transfer`) |

## 2. `SpecNonMeeting`

Setting. `E/ℚ(X)` is finite, `p` is prime, `[E : ℚ(X)] < p` and `NoVerticalRam E p`. The point
`s₀ = a/d` is `p`-integral and `NonMeeting`. Let `m` be the maximal ideal of `ℤ[X]` containing
`p` and `dX − a`; it is constructed as the kernel of `ℤ[X] → 𝔽_p`, `X ↦ a d⁻¹`
(`exists_secIdeal`). Let `R = ℤ[X]_m`, and let `S` be the integral closure of `R` in `E`, with
`R → E` given by `locAlg`.

| Prop | kind | content | status |
|---|---|---|---|
| `PurityGlobalDim2` | proved theorem (t-purity3) | regular local `R` of dimension 2, `S` a normal domain, finite and injective over `R`, unramified over the height-one primes ⇒ `R → S` étale | proved in `scratch/t-purity3/PurityDim2.lean`; copied statement |
| `SNLocalData` | glue | `S` is integrally closed, `R`-finite, and `R → S` is injective | **proved** (`snLocalData`) |
| `SNHeightOne` | glue | every height-one prime of `R` is unramified in `S` | **reduced** to the next two (`snHeightOne_of_pieces`) |
| `SNVertical` | glue (STANDARD) | the height-one prime `pR` is unramified in `S`. Reason: `NoVerticalRam` gives `e = 1`; `[E:ℚ(X)] < p` gives separable residue fields | open |
| `SNHorizontalTransfer` | glue (localization, char 0) | a ramified height-one `P ∌ p` comes from a prime `Q` of `B` with `e(Q) ≠ 1` and `ℤ[X] ∩ Q ⊆ P` | open |
| `SNSpecialize` | glue (STANDARD) | `R → S` étale ⇒ every `B/𝔓` over `X − s₀`, embedded in `ℚ̄`, is a number field unramified at `p` (base change to `R/(dX−a) = ℤ_(p)`) | open |

**What is proved for the horizontal case** (VERIFIED). prop-ts §4.1 used Gauss's lemma; the Lean
proof gets the same conclusion without it.

1. `NonMeeting` gives `f ∈ Q ∩ ℚ[X]` with `p`-integral coefficients and `f(s₀)` a `p`-unit.
2. `exists_int_multiple` gives `N f = F ∈ ℤ[X]` with `p ∤ N`.
3. `homog_mem`: modulo any ideal containing `dX − a`, `d^k F ≡ n₀ = Σ c_i a^i d^{k−i}`.
4. Since `n₀ = d^k N f(s₀)` is a `p`-unit, `notMem_of_val_zero` gives `F ∉ m`. So `F` is a unit
   of `R`.
5. `SNHorizontalTransfer` puts `F` in the proper ideal `P`, a contradiction.

**`SNLocalData` is a theorem** (VERIFIED). Ingredients:

- `ℚ(X)` is the fraction field of `ℤ[X]` (`isFractionRing_zx`, via
  `IsLocalization.integerNormalization_spec`), hence also of `ℤ[X]_m`
  (`IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`).
- Normality: `isIntegrallyClosed_of_isLocalization` for `R`, and
  `integralClosure.isIntegrallyClosedOfFiniteExtension` for `S`.
- Finiteness: `IsIntegralClosure.finite`.

## 3. `KummerMeetGlue`

**The pieces.** `KummerShape E E' ι r` says that `ι : E → E'` sends `X` to `r ∈ ℚ(s)` and that
`E'` is generated by `ι(E)` and `s`, i.e. `E' = E(s)`. The two substitutions are:

- `rFin b c n`: `X = b + s^n/c`, i.e. `s^n = c (X − b)`;
- `rInf c n`: `X = c/s^n`.

| Prop | kind | content |
|---|---|---|
| `KummerCompositum` | glue (algebra, STANDARD) | for `r = P/Q` non-constant, regular at `s₀` with `r(s₀) = t`: there is `E' = E(s)` with `[E':ℚ(s)] ≤ [E:ℚ(X)]` and a prime over `s − s₀` whose residue field contains the given `ℚ(φ(B/𝔓))` |
| `KummerAbhyankarFin(Glue)` | glue from T2 | `e(Q) ∣ n` over `X = b` ⇒ `E'/ℚ(s)` unramified over `s = 0` |
| `KummerOtherBranchFin` | glue (composita) | ramified primes of `E'` lie over `s = 0` or contain `s^n − c(b' − b)`, `b' ∈ S ∖ {b}` |
| `KummerVerticalFin` | glue (Gauss valuation) | `0 < n < p`, `c` a `p`-unit, `b` `p`-integral, `[E:ℚ(X)] < p`: `NoVerticalRam E p ⇒ NoVerticalRam E' p` |
| `KummerAbhyankarInf(Glue)`, `KummerOtherBranchInf`, `KummerVerticalInf` | the same at `∞` | the meeting polynomial is `b' s^n − c`, `b' ∈ S ∖ {0}` |

**What is proved** (VERIFIED). Everything in prop-ts §4.2 except these pieces is proved:

- the choice `t − b = p^M u`, `c = u^{n−1}`, `s₀ = p^{M/n} u`, with `s₀^n = c (t − b)`;
- at `∞`: `t = p^{−M} u`, `c = u^{1−n}`, `s₀ = p^{M/n}/u`, with `t s₀^n = c`;
- the `p`-integrality of `s₀`;
- `NonMeeting E' p s₀`:
  - `p`-integral coefficients of the meeting polynomial;
  - `f(s₀) = c(t − b')`, respectively `c(b' − t)/t`, is nonzero and a `p`-unit, via
    `padicValRat.add_eq_of_lt`;
- the degree and residue-field bookkeeping.

## 4. `CoverModelOfHecke`

All four pieces quantify over the triples `(Y, Φ, π)` with R1fp, R1hecke and R2fp, and over the
fields `E` that carry prop-ts's `NormalizationModel Y π E`.

`NormalizationModel` determines `E` up to isomorphism. The image of the open immersion
`Spec B → Y` contains every closed point of `π⁻¹(𝔸¹)`, so (Jacobson) it is `π⁻¹(𝔸¹)`. Then
`B = Γ(π⁻¹(𝔸¹))` and `E = Frac B` (PROVED HERE, not in Lean). So the last three pieces are
properties of the cover.

| Prop | content | source |
|---|---|---|
| `HeckeNormalization` | there is a finite Galois `E/ℚ(X)` with `NormalizationModel Y π E` | h-b1 M1, M2, M8 |
| `HeckeDegree` | `[E : ℚ(X)] ≤ 324` (divides `\|Γ'\| = 144`) | h-b1 M3 |
| `HeckeBranch` | `BranchData E {0, −16/27} (4, 2) 6` | h-b1 M4 (Baba–Granath §3.1) |
| `HeckeNoVertRam` | `NoVerticalRam E p` for every prime `p > 324` | h-b1 §3, Lemma NV |

`HeckeNormalization` needs `Y₃` to be `ℚ`-irreducible. Its two geometric components
(`π₀ = ℤ̂^×/nrd(K₃) ≅ (ℤ/3)^×`) are conjugate over `ℚ(√−3)`. This is SPECULATIVE: it is my
reading of Deligne's reciprocity law on `π₀`, as in prop-ts's `NormalizationModel` docstring.
If it failed, `HeckeNormalization` would be false while `CoverModelOfHecke` could still hold. In
that case `CoverModelWitness` with `FunctionFieldModel` is the safe form.

**The witness form** (VERIFIED). `FunctionFieldModel` and `CoverModel` transfer along the
kernel's `Pin.SameTripleMor`. Hence `coverModelOfHecke_of_witness`: with `MobiusGlue` and
`R1R2fp`, a cover model for one triple gives `CoverModelOfHecke`.

## 5. Truth of the statements

- The three task Props: the arguments of prop-ts §4.1-4.2 and h-b1 hold for the Lean readings
  (PROVED HERE, reviewed below). Lean conventions checked:
  - `Ideal.ramificationIdx` is the localized length and equals 1 at `⊥` (Mathlib
    `ramificationIdx_bot_eq_one`), so `BranchData.1` and `NonMeeting` impose nothing at the
    generic point;
  - `padicValRat p 0 = 0` is excluded by the explicit `f(s₀) ≠ 0`.
- New Props: see §6 for the independent review.

## 6. Independent review

See the log (step 6) for the review of the open Props by a separate model agent (read-only, no
Lean).

## 7. What remains

Open glue, all STANDARD commutative algebra or curve theory, no new literature leaf:

- `SNVertical`, `SNHorizontalTransfer`, `SNSpecialize`;
- the seven Kummer pieces;
- the four Hecke pieces. `HeckeNoVertRam` is Lemma NV, whose inputs are R1rec (bundle) and
  Abhyankar.

Suggested order:

1. `SNHorizontalTransfer` and `SNVertical`: localizations of primes, plus Mathlib's
   `Ideal.ramificationIdx_eq_one_iff`.
2. `SNSpecialize`: étale base change, and étale over a DVR ⇒ unramified.
3. `KummerCompositum`.

`PurityGlobalDim2` could be inlined from t-purity3 (948 lines, Mathlib only) to remove that
hypothesis.
