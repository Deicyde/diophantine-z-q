# prop-ts: Proposition TS (Beckmann's specialization inertia theorem) for the fibre cover

Task prop-ts, 2026-11-13. Object: `G0ModField.PropTS` and `G0ModField.PropTSAll` from
`scratch/fibre-cover/FibreCover.lean`. They are the large open item of fibre-cover
(`docs/research/fibre-cover.md` §5). Both are copied into `scratch/prop-ts/PropTS.lean`, and
`scratch/prop-ts/check_identical.py` confirms the copies are character-identical to the originals,
docstrings included (VERIFIED). Nothing upstream was edited. Log: `scratch/prop-ts/log.md`.
Compiler output: `scratch/prop-ts/compile_out.txt`.

This is model work only; no human has reviewed it. Marks: **VERIFIED** means compiled, computed
or read in a named source. **STANDARD** means a published theorem with its reference. **PROVED
HERE** means an argument written in this note and not reviewed. **SPECULATIVE** means an
assessment. There is no network, so locators given from memory are **UNVERIFIED**.

## 1. Main result

**`PropTSAll` is reduced in Lean to two leaves already in the bundles plus named glue. No new
literature leaf is needed.** Beckmann's theorem now appears only as an optional leaf.

VERIFIED: `lake env lean scratch/prop-ts/PropTS.lean` (about 900 lines) gives 0 errors and 0
warnings. All 24 `#print axioms` lines list only `[propext, Classical.choice, Quot.sound]`.

**The final form** (`PropTSRed.propTSAll_of_bundle_meet`):

```
PkgI2.AbhyankarDVR.{0}   -- bundle leaf T2 (Abhyankar's lemma, DVR form; TextbookLeaves.t2)
→ R1R2fp                 -- bundle leaf (R1 and R2 clause lists on Y₃, X₆)
→ KummerMeetGlue         -- glue: T2 → the Kummer reduction of the meeting case
→ SpecNonMeeting         -- glue from purity (t-purity3's purityGlobalDim2', proved)
→ MobiusGlue             -- kernel glue (ZInQKernel/HDecomp/QM/Pin.lean), already named
→ CoverModelOfHecke      -- glue: function field, branch data and Lemma NV of Y₃ → P¹_j
→ PropTSAll
```

**The normalization variant** (`propTSAll_of_bundle_N`) has the same inputs, except that
`CoverModelOfHeckeN` replaces `CoverModelOfHecke`. In it, `FunctionFieldModel` is replaced by the
scheme statement `NormalizationModel`: an open immersion `Spec B → Y` onto the points with finite
`π`, along which `π = X`. `FunctionFieldModel` is then proved
(`functionFieldModel_of_normalization`).

**The form with Beckmann as a leaf** (`propTSAll_of_leaves`):
`BeckmannSIT → R1R2fp → MobiusGlue → CoverModelOfHecke → PropTSAll`.

**On one cover** (`propTS_of_coverModel`, `propTS_of_coverModel_tame`):
`BeckmannSIT → CoverModel Y π → PropTS Y π`. The same holds with `BeckmannSITTame` in place of
`BeckmannSIT`.

Combined with fibre-cover's `fibreCoverExists_of_propTSAll`, this gives G2's `FibreCoverExists`
from these inputs: T5, `InnerTwistCount`, `UnramifiedConjugates` and the inputs listed above.

What is proved on the way (all VERIFIED):

1. **The valuation bookkeeping of Prop. TS.** Beckmann's hypotheses (a) and (b) and the
   inertia-order conditions are instantiated at `S = {0, −16/27}`, `n = 4, 2` and `n_∞ = 6`.
   For `p > 324`, `v_p(16/27) = 0` (`padicValRat_16_27`).
2. **Only the leaf's own triple needs a cover model.** The proof has three steps.
   - Let `g : Y' → Y` satisfy `Φ' = Φ ∘ g` on `K`-points for every field `K`. Then `g` preserves
     residue fields of `ℚ̄`-points: `ℚ(g ∘ y') = ℚ(y')` (`residueImage_comp_eq_of_pt`). The
     reason is that composing with `g` is a bijection on `K`-points, so `y'` factors through
     `ℚ(g ∘ y')`.
   - So Prop. TS transfers along the kernel's `Pin.SameTripleMor` (`propTS_transfer`). This
     improves on fibre-cover, which needed an isomorphism (`CurvePinned`).
   - With the kernel's `MobiusGlue` and the CM objects from `R1R2fp`, Prop. TS for one triple
     gives `PropTSAll` (`propTSAll_of_witness`).
3. **Beckmann's theorem (tame form) is glue.** `beckmannSITTame_of_glue` derives it from three
   pieces: `KummerStep`, `SpecNonMeeting` and `UnramifiedMono`.
4. **`UnramifiedMono` is a theorem** (`unramifiedMono`): a subfield of a number field unramified
   at `p` is unramified at `p`. The proof uses Mathlib's `Ideal.ramificationIdx_below_dvd` for the
   flat extension `𝓞 L → 𝓞 L'` and lying-over.
5. **The non-meeting case of `KummerStep` is proved** (`kummerStep_of_meet`). Take `E' = E` and
   `s₀ = t`. `BranchData` puts every ramified prime over some `X − b`, and `f = X − b` is
   `p`-integral with `f(t)` a unit. Only the meeting case, `KummerMeet`, remains glue.
6. **Residue fields of points of affine and open subschemes.**
   - `residueImage_specMap`: the `ℚ̄`-point `Spec ψ` of `Spec B` has residue field `ℚ(ψ(B))`.
   - `residueImage_comp_openImmersion`: open immersions preserve residue fields of
     `ℚ̄`-points.
   - These give `functionFieldModel_of_normalization : NormalizationModel → FunctionFieldModel`.
7. **`PropTS` is refuted for some cover** (`not_propTS_cyclotomic`).

**PropTS is a property of the cover, not a tautology (VERIFIED, `not_propTS_cyclotomic`).** It
is false for some `(Y₀, π₀)`.

- Take `Y₀ = Spec ℚ(ζ₃₃₁)` and `π₀ ≡ 1`, with charts `U = V = ⊤` and `f = g = 1`
  (`constOne`).
- Every hypothesis holds at `t = 1` and `p = 331`, because `v₃₃₁(1) = v₃₃₁(43/27) = 0`.
- But 331 is totally ramified in `ℚ(ζ₃₃₁)`, with `e = 330` (Mathlib
  `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime`).

So `PropTS` is neither inert nor vacuous. It has to be proved on the genuine cover, which is what
`CoverModel` and `CoverModelOfHecke` do.

## 2. The named Props

All are `def … : Prop` in `scratch/prop-ts/PropTS.lean`, each with a docstring. Notation:

- `B = integralClosure ℚ[X] E`;
- `ℚ[1/X]` is `InfCoord`, a copy of `ℚ[s]` with `s ↦ X⁻¹`;
- `C = integralClosure ℤ[X] E`;
- `e(Q)` is Mathlib's `Ideal.ramificationIdx`, which is localized (the length of
  `B_Q / 𝔭 B_Q`).

| Prop | kind | content | source | status |
|---|---|---|---|---|
| `PkgI2.AbhyankarDVR.{0}` | textbook leaf (bundle T2) | Abhyankar's lemma, DVR form | SGA 1 X 3.6 (UNVERIFIED number), as in the kernel docstring | leaf, `TextbookLeaves.t2` |
| `R1R2fp` | research leaf bundle | R1/R2 clause lists | the kernel `QM/Leaves.lean` | leaf |
| `BeckmannSIT` | **optional** literature leaf | `E/ℚ(X)` finite Galois; branch points in `S ∪ {∞}` with indices dividing `n_b`, `n_∞`; (a) `[E:ℚ(X)] < p`; (b) `S` is `p`-integral and pairwise distinct mod `p`; (d) `NoVerticalRam E p`; `t ∉ S` with `n_b ∣ v_p(t−b)⁺` and `n_∞ ∣ (−v_p t)⁺`. Conclusion: every residue field `B/𝔓` over `X − t`, embedded in `ℚ̄`, is unramified at `p` | Beckmann, J. reine angew. Math. 419 (1991), Prop. 4.2; Legrand's "Specialization Inertia Theorem" (UNVERIFIED locators) | not needed by the final form |
| `BeckmannSITTame` | glue | `BeckmannSIT` with the extra hypotheses `0 < n_b < p` and `0 < n_∞ < p` | — | **proved** from the next three |
| `SpecNonMeeting` | glue from purity | `E/ℚ(X)` finite, `[E:ℚ(X)] < p`, `NoVerticalRam`, `s₀` `p`-integral and meeting no branch point mod `p` (`NonMeeting`). Conclusion: every `B/𝔓` over `X − s₀` is a number field unramified at `p` | SGA 1 X; t-purity3 `purityGlobalDim2'` (proved) | open (§4.1) |
| `KummerStep` | glue | the meeting case of Prop. TS reduces to the non-meeting case for some `E'/ℚ(s)` and `s₀ ∈ ℚ` | h-b1 §1.2, Kummer coordinate | **proved** from `KummerMeet` |
| `KummerMeet`, `KummerMeetGlue` | glue from T2 | `KummerStep` when `t` meets a branch point (`v_p t < 0`, or `v_p(t−b) > 0` for some `b`); `KummerMeetGlue := AbhyankarDVR → KummerMeet` | §4.2 | open |
| `UnramifiedMono` | textbook | `L ≤ L'`, `L'` finite, `L'` unramified at `p` ⇒ `L` unramified at `p` | multiplicativity of `e` | **proved** |
| `CoverModel Y π` | glue (packaging) | there is a finite Galois `E/ℚ(X)` with `FunctionFieldModel Y π E`, `CoverBranchData E`, and `NoVerticalRam E p` for every `p > 324` | — | open (= the three below) |
| `FunctionFieldModel Y π E` | glue (curve theory) | every `ℚ̄`-point `y` with `π(y) = t ∈ ℚ` has `ℚ(y) = φ(B/𝔓)` for some prime `𝔓` over `X − t` and some `φ` | normalization; h-b1 M2, M8 | open |
| `CoverBranchData E` | glue from leaves | `[E:ℚ(X)] ≤ 324`; `BranchData E {0, −16/27} (4, 2) 6` | h-b1 M3 (`144`), M4 (Baba–Granath elliptic orders) | open |
| `NoVerticalRam E p` | glue (Lemma NV) | every prime of `C` over `p·ℤ[X]` has `e = 1` | h-b1 §3 (Shimura reciprocity via R1rec, Abhyankar, `W`) | open |
| `CoverModelOfHecke` | glue | `R1fp ∧ R1hecke ∧ R2fp ⇒ CoverModel` | h-b1 M1-M10 | open |
| `NormalizationModel Y π E` | glue (scheme theory) | an open immersion `h : Spec B → Y` whose image contains every `ℚ̄`-point with `π ≠ ∞`, with `π(Spec ψ ≫ h) = ψ(X)` | `Y` normal, proper and `ℚ`-irreducible with function field `E`, `π` finite: `π⁻¹(𝔸¹) = Spec B` | open; **implies** `FunctionFieldModel` (proved) |
| `CoverModelN`, `CoverModelOfHeckeN` | glue | as `CoverModel`, `CoverModelOfHecke`, with `NormalizationModel` | — | open; imply the originals (proved) |
| `MobiusGlue` | kernel glue | `π' = π ∘ g` on `ℚ̄`-points | qm-pin §3.4 | open (already named in the kernel) |

## 3. Why the statements are right

**`BeckmannSIT` is a consequence of Beckmann's theorem, never stronger** (the locator is
UNVERIFIED; the content follows h-b1 §1.1).

- Beckmann gives the inertia group at `p` of `E_t` as conjugate to `⟨g_b^{I_p(t,b)}⟩`, of order
  `e_b / gcd(e_b, I_p(t,b))`. Here `I_p(t,b) = v_p(t−b)⁺` for finite `b`, and
  `I_p(t,∞) = (−v_p t)⁺`. When `t` meets no branch point, `E_t` is unramified at `p`.
- Assume `e_b ∣ n_b` (BranchData) and `n_b ∣ I_p(t,b)`. Then every inertia order is 1.
- Each hypothesis of the leaf is the published one or stronger:
  - (a) is `[E:ℚ(X)] < p`, which implies `p ∤ |G|`. It is stated this way so that every version
    of the theorem implies the leaf.
  - (b) is "no two branch points meet mod `p`", written out with `∞` kept separate.
  - (c) holds automatically, because the branch points are rational.
  - (d) is no vertical ramification, read through Mathlib's localized ramification index on `C`.
  - Let `Q` be a prime of `C` with `Q ∩ ℤ[X] = pℤ[X]`. Then `Q` has height one, and `C_Q` is
    the DVR of the integral closure of `ℤ[X]_(p)` (Krull–Akizuki). So `e(Q)` is the vertical
    ramification index.
- The leaf allows `E` with constant field bigger than `ℚ`. This is needed because `Y₃` has two
  geometric components (see the Remark below). Beckmann allows it (h-b1 §1.1), and the SGA 1
  proof of h-b1 §1.2 works for any finite Galois `M/ℚ(j)`. If the constant field were ramified
  at `p`, the extension would be vertically ramified, so (d) excludes that case.
- **The h-b1 counterexample is excluded.** For `y² = p·j(27j+16)`, the Gauss valuation of
  `p·j(27j+16)` is odd, so `NoVerticalRam` fails and the leaf does not apply. This is the cover
  that showed Beckmann's (d) cannot be dropped.
- **The binders are satisfiable**: `example (h : BeckmannSIT) := h (RatFunc ℚ)` elaborates.

**`SpecNonMeeting` (PROVED HERE, from STANDARD inputs).** See §4.1. It needs no Galois hypothesis
and no distinctness of branch points. Residue separability at the vertical primes follows from
`[E:ℚ(X)] < p`, because the inseparable degree is a power of `p` dividing `f ≤ [E:ℚ(X)]`.

**`NonMeeting` encodes "`s₀` meets no branch point mod `p`."** For every ramified `Q` it asks for
a `p`-integral `f ∈ Q ∩ ℚ[X]` with `f(s₀) ≠ 0` and `v_p(f(s₀)) = 0`.

- The condition `f(s₀) ≠ 0` is explicit because `padicValRat p 0 = 0`.
- It is equivalent to "the closure of the branch point in `P¹_{ℤ_(p)}` misses the section `s₀`
  on the special fibre". If `β ≡ s₀` at a prime above `p`, then `f(s₀) ≡ f(β) = 0`. If `β` is not
  integral, it meets `∞` and cannot meet the integral `s₀`.

**`KummerMeet` (PROVED HERE; uses T2).** See §4.2.

**Independent review.** A second model agent read the file without running Lean and found no
false, vacuous or junk-value-exploitable statement. Its checks:

- `BeckmannSIT`: junk values (`padicValRat p 0 = 0`, `toNat`, `n_b = 0`, `Q = ⊥`), the `∞`
  chart, and the vertical index on the 2-dimensional ring `C`;
- the truth of `SpecNonMeeting` and `KummerMeet`, including the arithmetic of the Kummer
  coordinates.

It asked for four docstring fixes, all applied:

1. derive the non-regular case of `BeckmannSIT` from the regular case over the constant field
   `k'` (see below);
2. "residue extensions separable" needs `[E:ℚ(X)] < p`, not `p ∤ n`;
3. hypothesis (a) is the *stronger* hypothesis, so the leaf is weaker;
4. `FunctionFieldModel` needs `π` to be `Γ'`-invariant and non-constant on components, which
   holds for `Y₃`.

**Non-regular `E` in `BeckmannSIT`** (from the review; PROVED HERE).

- Restatements such as Legrand's assume `E/k(X)` regular, so the non-regular case has to be
  derived.
- Apply the regular theorem over the constant field `k'` to `E/k'(X)`. Its group is a subgroup
  of `G`, and it has the same rational branch points.
- `NoVerticalRam E p` forces `k'` to be unramified at `p`: `e` is multiplicative in
  `ℤ[X] ⊆ 𝒪_{k'}[X] ⊆ C`.
- The field `B/𝔓 ⊇ k'` is the specialization of `E/k'(X)` at `t`, and `(X − t)` stays prime in
  `k'[X]`.

**Remark on `CoverModelOfHecke`.** It follows h-b1 M1-M10.

- `Γ'` acts on `Y₃` over `ℚ` by R1hecke. Let `Y^{(1)}` be a `ℚ`-component. Its function field is
  Galois over `ℚ(j)` with group a subquotient of `Γ'`, of order dividing 144 (M2, M3). This
  gives `[E:ℚ(j)] ≤ 324`.
- The branch points are `0, ∞, −16/27`, with indices `4, 6, 2` (M4).
- `Y₃` is the normalization of `P¹` in `E` over `𝔸¹`. All points of a fibre have conjugate
  residue fields (M2, M8). This gives `FunctionFieldModel`.
- Lemma NV gives `NoVerticalRam` for `p ≥ 5` (h-b1 §3).

## 4. Proofs of the open glue (not compiled)

### 4.1 `SpecNonMeeting` from purity (PROVED HERE)

Let `s₀ = a/d` with `p ∤ d`, and let `m = (p, dX − a) ⊂ ℤ[X]`. Write `R = ℤ[X]_m`, a regular
local ring of dimension 2. Let `C_m` be the integral closure of `R` in `E`. It is a normal
domain, finite over `R` (separable extension of a Noetherian normal domain), and torsion-free.

Step 1: the height-one primes of `R` are unramified in `C_m`.

- **`(p)`.** `e = 1` by `NoVerticalRam`. The residue extension is separable because
  `[E:ℚ(X)] < p`.
- **`(g)`, with `g` primitive irreducible and `p ∣ g(s₀)`.**
  - Suppose some prime over `(g)` is ramified. Its prime `Q` of `B` lies over `gℚ[X]` and has
    `e(Q) ≠ 1`, since the local rings agree.
  - `NonMeeting` gives a `p`-integral `f ∈ gℚ[X]` with `f(s₀)` a unit.
  - By Gauss's lemma, `f = g·h` with `h ∈ ℤ_(p)[X]`. So `p ∣ f(s₀)`, a contradiction.

Step 2: by purity over a 2-dimensional regular local base (t-purity3 `purityGlobalDim2'`,
proved), `C_m` is étale over `R`.

Step 3: specialize.

- Base change along `R → R/(dX − a) = ℤ_(p)` gives an étale `ℤ_(p)`-algebra `A`.
- `A` is normal, so it is a product of unramified extensions of DVRs. For `𝔓 ∋ X − s₀`,
  `B/𝔓 = Frac` of a factor of `A`.
- So `B/𝔓` is a number field unramified at `p`. Its embedded image `adjoin ℚ (range φ)` is
  isomorphic to it, so the same holds for the image.

Lean ingredients still missing (one is now done):

- regularity of `ℤ[X]_m` with dimension 2: **proved** in `scratch/prop-ts/ZXRegular.lean`
  (`regular_dim2_intPoly`, VERIFIED). It uses Mathlib's `IsRegularRing ℤ[X]` instances and
  `Polynomial.height_eq_height_add_one`;
- finiteness of the integral closure (Mathlib has `IsIntegralClosure.finite`);
- base change of étale algebras;
- "étale over a DVR ⇒ `UnramifiedAt`".

### 4.2 `KummerMeet` from Abhyankar (PROVED HERE)

**Case `t` meets `b ∈ S`.** Let `m = v_p(t−b) > 0` with `n = n_b ∣ m`, and write
`t − b = p^m u` with `v_p(u) = 0`. Set `c = u^{n−1}` and adjoin `s` with `s^n = c(X − b)`.
Then `s₀ = p^{m/n} u ∈ ℚ` satisfies `s₀^n = c(t − b)`. Let `E'` be the factor of `E ⊗ ℚ(s)`
that carries a prime over both `𝔓` and `(s − s₀)`. Such a factor exists: `ℚ[s]` is free over
`ℚ[X]`, and `κ(𝔓) ⊗ ℚ ≠ 0`.

1. **`E'/ℚ(s)` is unramified over `s = 0`.** Apply T2 to the DVR `ℚ[X]_(X−b)` with uniformizer
   `c(X − b)`, using `e(Q) ∣ n`. Every prime of `E'` over `X = b` then has `e = n`, and
   `ℚ(s)/ℚ(X)` is totally ramified of degree `n` there.
2. **`NonMeeting E' p s₀`.**
   - The other finite branch points of `E'/ℚ(s)` lie over `b' ≠ b`. They are roots of monic
     factors `f` of `s^n − c(b' − b)`.
   - These `f` are `p`-integral, and `f(s₀)` divides `s₀^n − c(b'−b) = c(t − b')`, which is a
     `p`-unit because `t ≡ b ≢ b'`.
   - `ℚ(s)/ℚ(X)` is ramified only over `b` and `∞`.
3. **`NoVerticalRam E' p`.** Substituting `X = s^n/c + b` preserves the Gauss valuation, because
   `c` is a unit, `b` is integral, and the reduction is injective. The residue extension
   `F_p(s)/F_p(X̄)` is separable of degree `n < p`. So `E(s)/E` is unramified at the vertical
   primes.
4. **Degree and residue field.** `[E':ℚ(s)] ≤ [E:ℚ(X)] < p`. The residue field of `E` at `𝔓`
   embeds in that of `E'` at `𝔓'`.

**Case `v_p(t) = −m < 0`, `n = n_∞ ∣ m`.** Use `s^n = c/X` with `c = u^{1−n}`, where
`t = p^{−m}u`. Then `s₀ = p^{m/n}/u`. T2 applies at the DVR of `∞`, and the same checks go
through. The point `b' = 0` goes to `s = ∞`, outside the chart.

## 5. Lean outcomes (`scratch/prop-ts/PropTS.lean`)

Imports: `ZInQKernel.HDecomp.QM.Pin` and `ZInQKernel.HDecomp.Descent.B2Glue`. Build those first
with `lake build` (about 5 min). After that, `lake env lean` takes about 1.5 min.

- **Part 1, definitions:** `InfCoord` (with `CommRing` and `Algebra … (RatFunc ℚ)` instances),
  `infUnif`, `infAlg`, `intPolyAlg`, `vertPrime`, `BranchData`, `NoVerticalRam`.
- **Part 2, the leaf:** `BeckmannSIT`.
- **Part 3, the cover glue:** `FunctionFieldModel`, `nY3`, `CoverBranchData`, `CoverModel`.
- **Part 4, theorems:** `padicValRat_16_27`, `propTS_of_coverModel`, `propTSAll_of_coverModel`.
- **Part 5, theorems:**
  - copied from fibre-cover with their proofs: `spec_to_specQ_eq`,
    `exists_factor_of_residueImage_le`, `residueImage_le_aux`, `residueImage_comp_le_self_aux`;
  - new: `residueImage_comp_eq_of_pt`, `propTS_transfer`, `propTSAll_of_witness`,
    `propTSAll_of_leaves`;
  - definition: `CoverModelOfHecke`.
- **Part 6:** the sanity `example`.
- **Part 8:** `exists_factor_scheme`, `residueImage_specMap`,
  `residueImage_comp_openImmersion`, `NormalizationModel`,
  `functionFieldModel_of_normalization`, `CoverModelN`, `coverModel_of_N`,
  `CoverModelOfHeckeN`, `propTSAll_of_bundle_N`.
- **Part 9:** `constOne`, `constOne_val`, `exists_primitive_331`, `padicValRat_43_27`,
  `not_propTS_cyclotomic`.
- **Part 7:**
  - definitions: `NonMeeting`, `SpecNonMeeting`, `KummerStep`, `KummerGlue`, `KummerMeet`,
    `KummerMeetGlue`, `UnramifiedMono`, `BeckmannSITTame`;
  - theorems: `padicValRat_sub_nonneg`, `kummerStep_of_meet`, `beckmannSITTame_of`,
    `beckmannSITTame_of_glue`, `propTS_of_coverModel_tame`, `propTSAll_of_bundle`,
    `unramifiedMono`, `propTSAll_of_bundle'`, `propTSAll_of_bundle_meet`.

Lean notes:

- `Ideal.ramificationIdx` in Mathlib v4.35 is the localized length, so the vertical ramification
  index can be stated directly on `integralClosure ℤ[X] E` (a 2-dimensional ring) without a DVR.
- `𝓞 L → 𝓞 L'` for intermediate fields `L ≤ L'` of `ℚ̄`: set `Algebra L L'` from
  `IntermediateField.inclusion`. Mathlib's instances then supply `Algebra (𝓞 L) (𝓞 L')`,
  `Algebra.IsIntegral` and `Module.Flat` (Dedekind base, torsion-free module).

## 6. Integration

The names live in `G0ModField` (copied) and `PropTSRed` (new). With fibre-cover's file in the same
module, `fibreCoverExists_of_propTSAll t5 hW (propTSAll_of_bundle_meet …) hU` gives
`FibreCoverExists`.

For h-decomposition G2, "Prop. TS from T1-T2 or Beckmann" becomes:

- T1 is no longer used as a leaf: its case is t-purity3's theorem, consumed inside
  `SpecNonMeeting`;
- T2 is consumed by `KummerMeetGlue`;
- the remaining glue is `SpecNonMeeting`, `KummerMeet`, `CoverModelOfHecke` and the kernel's
  `MobiusGlue`.

## 7. What remains

- `SpecNonMeeting`: the purity argument of §4.1 in Lean. This is the largest piece.
- `KummerMeet`: the Kummer construction of §4.2 and its use of T2.
- `CoverModelOfHecke` (or `CoverModelOfHeckeN`):
  - `NormalizationModel`: `π⁻¹(𝔸¹) = Spec B` for `Y₃`. The step from it to
    `FunctionFieldModel` is proved;
  - `CoverBranchData`: the elliptic orders and `|Γ'|`;
  - `NoVerticalRam`: h-b1's Lemma NV, which needs inertia groups of `E/ℚ(j)` and Shimura
    reciprocity at the CM points through R1rec.
- `MobiusGlue`: already in the kernel, owned by qm-pin.
- Locators: Beckmann Prop. 4.2, SGA 1 X 3.1/3.6, Legrand §2. All are UNVERIFIED.
