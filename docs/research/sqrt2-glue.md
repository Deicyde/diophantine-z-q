# sqrt2-glue: `SqrtTwoNotInHHprime` (√2 ∉ ℍ'_n) is proved in Lean, so TYZ Lemma 3.18 (`Lemma318Literal HHprime`) holds with no hypotheses

Task sqrt2-glue, 2026-11-14. Lean: `scratch/sqrt2-glue/Sqrt2Glue.lean` (1573 lines) and
`scratch/sqrt2-glue/Combined.lean`. Log: `scratch/sqrt2-glue/log.md`.

## 1. Result

The glue Prop that tyz-318 left under `Lemma318Literal HHprime` is now a theorem. It needs no hypotheses
and no leaves:

```lean
-- scratch/sqrt2-glue/Sqrt2Glue.lean, namespace ZInQ.Contrib.TYZGenus.Sqrt2Glue
theorem sqrtTwoNotInHHprime : SqrtTwoNotInHHprime   -- ∀ n, n % 8 = 5 → Squarefree n → ∀ s ∈ HHprime n, s ^ 2 ≠ 2
theorem sigmaLift : SigmaLift                       -- tyz-318's stronger class-field form, also proved

-- scratch/sqrt2-glue/Combined.lean (tyz-318's file followed by this one)
theorem lemma318Literal_HHprime : T318.Lemma318Literal HHprime          -- TYZ Lemma `torsion2`, verbatim
theorem package_lemma318Literal_HHprime : Package.Lemma318Literal HHprime
theorem tyzThm35ReadingA_of_cmLeaves_ringClassD_no318 ... : ZInQ.Literature.TYZThm35ReadingA
  -- the kernel's RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD with h318 discharged
```

* **Copies.** `SqrtTwoNotInHHprime` and `SigmaLift` are byte-identical to the definitions in
  `scratch/tyz-318/Lemma318.lean`. tyz-318's proof of `SigmaLift → SqrtTwoNotInHHprime` is copied
  unchanged. VERIFIED by a textual comparison. In the combined file, `T318.SqrtTwoNotInHHprime = SqrtTwoNotInHHprime`
  is checked by `rfl`.
* **Checks.** VERIFIED, compiled: `lake env lean scratch/sqrt2-glue/Sqrt2Glue.lean` takes about 40 s and
  `Combined.lean` about 37 s. Both report 0 errors and contain no `sorry` and no `axiom`. `#print axioms`
  gives `[propext, Classical.choice, Quot.sound]` for `sqrtTwoNotInHHprime`, `sigmaLift`,
  `frobNormLaw`, `lemma318Literal_HHprime`, `package_lemma318Literal_HHprime` and
  `tyzThm35ReadingA_of_cmLeaves_ringClassD_no318`.
* **No statement was changed.** The statement was not found to be false, vacuous or inert.
* **Effect.** cm-bridge's hypothesis `h318 : Lemma318Literal HHprime` is gone. tyz-318 had already reduced
  it to this one glue Prop, so TYZ Lemma 3.18 is now proved outright for every squarefree `n ≡ 5 (mod 8)`.
* **Remaining caveat.** The HUMAN CHECK that tyz-318 flagged, "is `SqrtTwoNotInHHprime` TYZ's Step 3?",
  no longer matters for correctness: what is proved is `Lemma318Literal HHprime` itself. The fidelity of
  `Lemma318Literal` and `HHprime` to TYZ's text is outside this task. It was reviewed in cm-bridge and tyz-318.

## 2. The proof

This is Route A of `docs/research/tyz-318.md` §3.2 in a lighter form. Write `F = L_n(i) = Lni n` and `K_d = ℚ(√−d)`.
For each prime `q ∣ n` put `q* = ±q ≡ 1 (mod 4)`, and set

`β = i ∏_{q ∣ n} (1 + √q*)/2` and `α = 1 + 2β ∈ 𝓞_F`.

The proof uses **no Chebotarev density and no class field of `F`.** Instead of a single prime of `F` in
the class of `α` (tyz-318's step 2), it multiplies the Frobenius elements at the prime factors of `α𝓞_F`.
The Artin map is multiplicative on ideals, so the product acts on each `H_{d₀,4}` as the Artin symbol of
`N_{F/K_{d₀}}(α𝓞_F)`.

| Prop (§ of the file) | statement | kind | status |
|---|---|---|---|
| `FrobNormLaw` (§2) | Let `F ⊂ ℚ̄` be a number field, normal over ℚ, `D` a finite set, and `P ∌ 2` a nonzero prime of `𝓞_F`. Some `h ∈ Gal(ℚ̄/F)` acts on `H̄_{d,4}` as `artin4 d (classOf (N_{F/K_d} P))` for every `d ∈ D` with `K_d ⊂ F`. | GLUE (norm functoriality of ring-class reciprocity at primes) | **PROVED**: `frobNormLaw` (§5–§7) |
| `NormSigma` (§2) | Some `α ∈ 𝓞_{L_n(i)}`, `α ≠ 0` and coprime to 2, has `classOf (N_{L_n(i)/K_{d₀}}(α𝓞)) = sigmaClass d₀` for all `d₀ ∣ n`, `d₀ ≡ 5 (mod 8)`. | GLUE (Route A, step 1) | **PROVED**: `normSigma` (§8, §13) |
| `NormCongr` (§8) | the same `α` has `N_{L_n(i)/K_{d₀}}(α𝓞) = (1 + 2ε√−d₀ + 4γ)𝓞_{K_{d₀}}` with `ε = ±1` and `γ ∈ 𝓞_{K_{d₀}}` | GLUE, the explicit computation | **PROVED**: `normCongr` (§9–§13) |
| `SigmaLift` (tyz-318) | one `h` that fixes `L_n(i)` and acts as `σ_{1+2ϖ}` on every `H̄_{d₀,4}` | stronger than the target | **PROVED**: `sigmaLift = sigmaLift_of frobNormLaw normSigma` |

Each piece in detail:

* **Definitions (§1).**
  * `kEmb d : K_d → ℚ̄` is `embed d` restricted to `K_d`, the embedding used for `H̄_{d,4}`.
  * `relNormK F d P` is Mathlib's `Ideal.relNorm (𝓞 K_d) P`, for the `K_d`-algebra structure on `F` given
    by `kEmb`. It is `⊥` if `kEmb d (K_d) ⊄ F`.
  * `classOf J` is the `Pic(ℤ + 4𝓞_{K_d})` class of an ideal prime to the conductor.
  * `sigmaClass d = classOf (span {3 + 2√−d})` holds by `rfl`.
* **Assembly (§4, `sigmaLift_of`).** The proof is an induction over `normalizedFactors (α𝓞_F)`.
  * `h` is the product of the Frobenius elements `h_P`.
  * Each `h_P` acts on `H̄_{d₀,4}` by `artin4 (classOf (N P))`.
  * `relNorm` and `classOf` are multiplicative on ideals coprime to 2. An ideal of odd absolute norm is
    coprime to 2, and the converse follows from Cauchy's theorem in `𝓞/J`. Mathlib's `absNorm_relNorm`
    carries this through the relative norm.
  * At the end `∏ P = α𝓞_F` (Mathlib `prod_normalizedFactors_eq_self`) and `NormSigma` apply.
* **`frobNormLaw` (§5–§7).**
  * `M = F ⊔ ⨆_{d ∈ D} H̄_{d,4}` is finite and Galois over ℚ, hence over `F`.
  * Mathlib's `IsArithFrobAt.exists_of_isInvariant` supplies a Frobenius `σ ∈ Gal(M/F)` over `𝓞_F` at a
    prime `𝔔 ∣ P`. `liftNormal` lifts it to `h ∈ Gal(ℚ̄/ℚ)`.
  * `frob_on_H4` transports `h` to `τ ∈ Gal(H_{d,4}/K_d)` through `embed d`. Then `τ` acts as
    `x ↦ x^{N P}` modulo `Q' = 𝔔 ∩ 𝓞_{H_{d,4}}`.
  * Put `𝔭 = Q' ∩ 𝓞_{K_d} = P ∩ 𝓞_{K_d}`. Then `N P = (N 𝔭)^f` (Mathlib `cardQuot_pow_inertiaDeg`) and
    `N_{F/K_d}(P) = 𝔭^f` (Mathlib `relNorm_eq_pow_of_isMaximal`).
  * `eq_pow_of_congr` (§5) shows that an automorphism acting as `x ↦ x^{(N𝔭)^f}` modulo an unramified
    `Q'` equals `Art(𝔭)^f`. The proof applies Tau Ceti's uniqueness `isArithFrobAt_eq_of_isUnramifiedAt`
    to `φ·(τ⁻¹φ^f)`, where `φ = Art(𝔭)`.
  * Tau Ceti supplies the inputs: `isArithFrobAt_ringClassArtinEquiv_picClass` and
    `isUnramifiedAt_ringClassField` (`𝔭 ∤ 4`).
* **`normCongr` (§9–§13).**
  * *Norm and trace.* `norm_one_add_two_mul` gives `N_{F/K}(1 + 2β) = 1 + 2 Tr_{F/K}(β) + 4γ` with `γ`
    integral. The proof uses Mathlib's `Algebra.norm_eq_prod_embeddings`, `trace_eq_sum_embeddings` and
    `∏(1 + 2x_i) = 1 + 2Σx_i + 4Z`.
  * *Expanding `β`.* `β = 2^{−r} Σ_{S ⊆ primes(n)} x_S` with `x_S = i∏_{q∈S}√q*` and `x_S² ∈ ℚ`.
  * *The trace.* `trace_sum_sq` with `trace_eq_zero_of_sq` (`Tr(x) = 0` if `x² ∈ K`, `x ∉ K`; via minpoly
    `X² − c`) gives `Tr_{F/K_{d₀}}(β) = 2^{−r}[F : K_{d₀}] x_{D₀}`. Here `x_{D₀} = ±√−d₀`, because
    `∏_{q ∣ d₀} q* = d₀` for `d₀ ≡ 1 (mod 4)`.
  * *Which `x_S` lie in `K_{d₀}`.* `kEmb_ne_xS` shows `x_S ∉ K_{d₀}` unless `S = primes(d₀)`. The argument:
    `p · r` with `p ∤ r` is not a rational square, and `√−d₀ ∉ ℚ`.
  * *The degree.* `[F : ℚ] ≤ 2^{r+1}` holds because `F ⊂ ℚ(i, √q)` and adjoining square roots at most
    doubles the degree. So `[F : K_{d₀}] ≤ 2^r`. Write `c = [F : K_{d₀}]/2^r`. Since `Tr(β) = c·(±√−d₀)` is
    integral, `c²d₀ ∈ ℤ`; as `d₀` is odd, `2^r ∣ [F : K_{d₀}]`. Hence `[F : K_{d₀}] = 2^r` and
    `Tr(β) = ±√−d₀`. This avoids proving the multiquadratic degree, i.e. Kummer independence, directly.
  * *Relative norm.* Mathlib's `relNorm_singleton` and `algebraMap_intNorm` give
    `N_{F/K}(α𝓞) = (1 + 2ε√−d₀ + 4γ)𝓞_K`.
* **`classOf_span_congr` (§8).**
  * `(1 + 2ε√−d + 4γ)(3 − 2ε√−d) ∈ ℤ + 4𝓞_K`.
  * `3 + 2√−d` has class `σ` by definition, and `(3 − 2√−d)(3 + 2√−d) = 9 + 4d`. Together with `σ² = 1`
    (ring-class `sigmaClass_sq`), this gives class `σ` for both signs `ε`.

Inputs used:
* the kernel's `ZInQKernel/Contrib/TYZGenus/` (ring-class, cm-bridge objects: `Lni`, `HHprime`, `H4`,
  `artin4`, `sigmaClass`, `embed`, `normal_Lni`, `normal_H4bar`, `Lni_le_Hprimebar`,
  `natCast_mul_mem_conductor`, `sigmaClass_sq`);
* vendored Tau Ceti (`ringClassArtinEquiv`, `isArithFrobAt_ringClassArtinEquiv_picClass`,
  `isUnramifiedAt_ringClassField`, `isArithFrobAt_eq_of_isUnramifiedAt`, `picClass_eq_one_iff`,
  `mem_integralIdealsPrimeTo_conductorModulus_iff`);
* Mathlib (relative norms, Frobenius elements, embeddings, minpoly).

## 3. Checks

* VERIFIED, compiled: both files are listed in §1. They import only
  `ZInQKernel.Contrib.TYZGenus.RingClassBridge` and `RingClassTwo`. The combined file adds tyz-318's
  imports, Tau Ceti `TorsionReduction` and Mathlib `PrimesInAP`. They were built here from tyz-318's
  `.lake/build`, with 6 changed Tau Ceti modules rebuilt.
* VERIFIED, computed earlier by tyz-318 (`scratch/tyz-318/trace_check.py`): the same `α` gives
  `Tr(β) = √−d₀` and `N(α) ≡ 1 + 2√−d₀ (mod 4)` for 8 values of `n`. The Lean proof now covers every `n`.
* **Lean pitfall** (VERIFIED, compiled): `artin4 d c = ringClassArtinEquiv (O4 d) c := rfl` hits the
  maximum recursion depth, because the instance paths differ. `artin4 d = ringClassArtinEquiv (O4 d) := rfl`
  is fine. Rewrite with the second before applying Tau Ceti lemmas to `artin4`.

## 4. What remains / integration

* Nothing remains for this glue.
* `Sqrt2Glue.lean` can become a Contrib module as is. The combined file can serve as the integration of
  tyz-318 and sqrt2-glue: it proves `Package.Lemma318Literal HHprime`, so `h318` can be dropped from
  cm-bridge's final theorems and from `RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD`.
* The remaining hypotheses of that bridge are `TYZThm11Integral`, `TYZLcalOne`, `TYZLemma29Mod2`,
  `CMFieldOfDefinition ringClassFieldD`, `TYZSigmaFixesZn` and `GenusPointLeafCM`. They belong to other
  tasks and are untouched here.
