# T2: exact tame DVR Abhyankar lemma

## Status and exact contract

Contributor proof work against baseline
`a5937595cde3e3db00975b81e5171cdef92c801a`, Lean **4.35.0**, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

The requested closed type is **`PkgI2.AbhyankarDVR.{0}`**, defined in
`ZInQKernel/HDecomp/Objects.lean`, lines 988–1003. The proposed extraction in
PR 41, revision `2757349fbd8ca613340b679bbd149f78c2baba6b`, is an
unregistered, unreviewed statement reference, not a proof supplier. It is not
imported by this contribution.

**Closed general-form proof:**
`ZInQ.Contrib.Abhyankar.abhyankarDVR : PkgI2.AbhyankarDVR.{0}` is supplied in
`ZInQKernel/Contrib/Abhyankar/General.lean`, lines 109–158. Its raw elaborated
type is exactly that constant, with **no outer binders and no universe
parameters**. All 18 contribution modules compiled cleanly, and all 227
serialized contribution declarations passed scoped kernel replay, with none
skipped. The axiom union is exactly `{propext, Classical.choice, Quot.sound}`.
The full original-prime composition is proved, not inferred from component
compilation. Parent candidate audit and independent/Astra acceptance remain
separate and pending.

The baseline quantifies over an exact DVR `R`, its specified fraction field `K`,
a finite separable extension `L/K`, and a specified field `M = L(t)`. It assumes
an irreducible uniformizer `π`, a positive unit exponent `n`, and, at **every**
prime `q` of `integralClosure R L` above the maximal ideal of `R`, a unit index
`e(q)`, divisibility `e(q) ∣ n`, and a separable residue extension. Its conclusion
is, at **every** prime `Q` of the actual `integralClosure R M` above that ideal,
`Q.ramificationIdx R = n` and separability of its residue extension. No
completeness, henselianity, or perfect-residue assumption is part of that type.

## Source-first comparison

### Stacks

The advertised [0EYG](https://stacks.math.columbia.edu/tag/0EYG) is Lemma
58.31.5, the regular-divisor, scheme-theoretic local normal-form result. Its
proof invokes the actual DVR lemma
[0BRM](https://stacks.math.columbia.edu/tag/0BRM), Lemma 15.116.4.

The primary TeX source examined is `more-algebra.tex` at Stacks revision
`a04446e57ec1fbc252a871afcec7752fb2807b14`, SHA-256
`0106554339e8966fe04411b2ae9f9cd856b165849feef0c7bc37634819064708`.
The DVR assertion and proof are at lines 34036–34135. The root-of-uniformizer
normalization lemma [09EV](https://stacks.math.columbia.edu/tag/09EV) is at
lines 33953–34003. That source states `n ≥ 2`; the contribution treats `n = 1`
separately instead of dropping its endpoint restriction.

In 0BRM, `A ⊂ B` are DVRs, the ramification index is prime to the residue
characteristic, the residue extension is separable, and the index divides the
ramification of the chosen base-change local factor. The conclusion covers
**all** primes over that factor. The proof uses the root of the unit
`θ / π_B`, not its inverse; the primary source incorporates the correction of
that ratio. The tensor-product formulation includes all field factors.
Here the model is built inside the *specified* field `M`, and its equality with
the integral closure is proved, so a tensor factor is not assumed.

Stacks identifies its document license as GNU FDL. No Stacks text or TeX proof
is vendored by the contribution; the argument and source comparison are recorded
here, and mathematical conclusions are supplied by Lean proofs.

### Tau Ceti

The actual source snapshot examined is
[TauCeti `30f41378f0cb1d569f51d8a4d0cb74aea8a80e44`](https://github.com/TauCetiProject/TauCeti/tree/30f41378f0cb1d569f51d8a4d0cb74aea8a80e44).
Its root `LICENSE` and relevant source headers identify **Apache-2.0**. Its
`lean-toolchain` is **4.36.0-rc2**, and its Mathlib dependency is
`2ddf59c8f14245864e6c0ed227a2dab76b9efea2`, not this project's pin.

`TauCeti/FieldTheory/FunctionField/Place/Extension/Abhyankar.lean`, lines
139–185, gives `TauCeti.Place.ramificationIdx_restrict_sup` with an
`IsFunctionField` input and **`PerfectField` on the lower residue field**.
The Galois version, lines 79–122, requires a finite Galois ambient extension
with separable residue extension. Neither signature is a direct match for
arbitrary, potentially imperfect-residue DVRs. A name match or an `lcm` formula
cannot discharge the missing field/prime coverage and residue hypotheses.

The more suitable sources are the newer DVR `AbhyankarModel/Basic.lean`
and `AbhyankarModel/Unramified.lean`, together with `DiscreteValuationRing/Kummer.lean`.
They study `(B[y]/(y^e-u))[t]/(t^d-ϖy)`, where `n = e*d`. The local computation
requires a DVR, a uniformizer, a unit `u`, a unit `e`, and positive `d`; it does
not require completeness or residue perfection. This contribution takes the
actual subalgebra `B[y,t] ⊂ M` and proves its normality and fraction-field
identity. Consequently its identification with `integralClosure B M` is a
proved field-factor bridge.

Minimal source ports are attributed in their headers: ramification transport,
denominator clearing, the forward standard-etale presentation, reduced
principal-divisor localization, and the binomial root-ring argument. The large
function-field library and its perfect-residue theorem are not imported.
The coefficient-prime normalization and original-field comparison arguments
use the pinned Mathlib primitives directly.

The separately developed monogenicity route was also inspected. Its general
separable-residue version still requires a **finite** local algebra extension.
Finiteness of the semilocal integral closure over `R` does not silently imply
finiteness of `R → S_q` at one of several primes. That existence proof is not
used here, nor is a uniformizer power basis assumed.

## Direct proof inventory and connecting arguments

1. **Baseline field/scalar checks — `Field.lean`, `Primes.lean`.**
   The missing scalar tower `R → L → M`, integrality of the root, finiteness and
   separability of `M/K`, faithful embeddings, and the DVR localization at
   each actual integral-closure prime are derived. Uniformizer nonvanishing is
   checked through those embeddings. No chosen place replaces the prime family.

2. **Actual index normalization — `Local.lean`, `Builder.lean`.**
   `Ideal.ramificationIdx` is the localization-length definition. The mapped
   maximal ideal is shown to be the corresponding maximal-ideal power, and a
   uniformizer's valuation is identified with that same index. Divisibility
   constructs `d`, and `y = t^d/ϖ` is proved to satisfy `y^e = u` and `t^d = ϖy`.
   The index is positive and its cast is a unit in the actual localized ring.

3. **Normalized model — `Etale.lean`, `ReducedLocal.lean`, `Model.lean`.**
   The unit-root algebra is etale because its monic polynomial is separable.
   The model modulo `t` is an actual quotient of that algebra; over the residue
   field it is reduced, without perfection. Every maximal model prime is minimal
   over the root divisor. Its localization is a DVR with uniformizer `t`.
   The subalgebra is finite over `B`, its fraction field is the specified `M`,
   and normality follows at all maximal ideals. Thus
   `integralClosure_eq_tameRootModel` proves equality with the actual integral
   closure. `tameRootModel_at_every_prime` gives index `d` and separable residue
   at every prime over the maximal ideal of `B`.

4. **Field-factor and localization maps — `Fraction.lean`, `LocalField.lean`,
   `Frame.lean`, `Normalization.lean`.**
   Denominators are cleared to identify the fraction field of an adjoin. The
   canonical localization embeddings into `L` and `M` are shown compatible by
   localization extensionality. The closure of the closure is compared with
   the original closure through the given field embedding. Normalization
   commutes with coefficient localization, with a proved bijection of the
   complete lying-over prime families and coefficient-compatible local algebra
   equivalences. This is not an assumption that the rings or primes are equal.

5. **Consumer index/residue comparisons and full composition — `Transport.lean`,
   `Comparison.lean`, `General.lean`.**
   `normalization_ramificationIdx` compares the original and extended prime's
   actual indices over `R`; `normalization_residueSeparable_iff` compares their
   actual residue algebras over `R/maximalIdeal R`. Maximal-ideal transport is
   proved before either comparison is applied. Tower multiplicativity is used
   after proving torsion-freeness and flatness over the localized Dedekind base.
   The quotient scalar tower is checked on quotient classes of the original
   coefficients. The entire composition is proved by `abhyankarDVR`, not only
   its components.

   For clarity, its exact chain is: put `S = integralClosure R L` and
   `C = integralClosure S M`; use the proved `R`-algebra equivalence
   `C ≃ integralClosure R M`. Pull back **every** final prime to `Q0` in `C`,
   put `q = Q0.under S`, and prove `q` lies over the original maximal ideal.
   Let `B = S_q` with the canonical, compatible maps into `L` and `M`.
   Extend `Q0` to its specified prime `P` of `U = integralClosure B M`.
   The constructed model gives `e(P/B) = d`, where `n = e(q/R)*d`.
   Flat tower multiplicativity and localization invariance give `e(P/R) = n`.
   The given separability at `q` and the model's separability at `P` compose
   through `κ(R) → κ(B) → U/P`. The verified original/normalized comparisons
   return the exact index and residue assertion for `Q0`, and then for the
   original final prime. Compatible field-map and lying-over inputs exposed
   by the local helper are **constructed in the closed proof**, not assumptions
   of the final theorem.

   A bounded locating search was scoped to the 26 baseline HDecomp modules;
   it is not a whole-proof or source-inventory coverage acceptance. The other
   current representation located is `ObjBridge.AbhyankarDVR`
   (`Objects.lean`, lines 1481–1496), with the existing
   `ObjBridge.abhyankarDVR_iff` at line 1498. Its actual full assertion was read
   and matches `PkgI2.AbhyankarDVR.{0}` definitionally. Those baseline files,
   the proposed target, and their existing records were not edited. There is
   no claim that H, the manuscript, or any release was assembled or accepted.

6. **Useful closed partial scopes — `One.lean`, `Kummer.lean`, `DvrInclusion.lean`.**
   `baseline_iff_all_exponents` checks the exact baseline type.
   `atExponent_one` proves its exponent-one specialization.
   `pureKummer_at_every_prime` proves the full conclusion when `M = K(t)`, even
   without exponent invertibility, by proving the root-ring DVR and actual
   normalization. `trivialExtension_at_every_prime` handles an arbitrary
   presentation with surjective `K → L`. A local valuation-ring inclusion with
   a common fraction field is proved bijective; the target need not itself be
   a DVR. These are not substituted for the general tame-compositum statement.

## Hypotheses, exceptional cases, and scope

- `π` is irreducible in the *actual* DVR, so it is nonzero and generates its
  maximal ideal; its image remains nonzero in the constructed localizations.
- Positive exponents exclude `n = 0`; the unit-index hypothesis excludes index
  zero. The constructed quotient exponent is positive. The binomial proof
  treats `n = 1` and the trivial field extension explicitly.
- The unit casts are in the specified rings, not merely nonzero in a fraction
  field. Unit-root separability works in arbitrary residue characteristic.
- Multiple primes are retained. Prime restriction, extension, contraction and
  the inverse family correspondence are proved. A complete/henselian case
  with a unique prime is not used to claim the general conclusion.
- Only contribution modules and this focused research note are changed. Pins,
  baseline definitions, registry, root, checkers, policy and manuscript are
  unchanged. There is no manuscript/release promotion or assembled-proof
  acceptance claim.

## Nine application checks (author reconstruction)

These are source-to-consumer checks for this contributed proof, not an
independent inventory-coverage or Astra decision.

1. **Source hypotheses:** the supplying type is the unchanged baseline
   `PkgI2.AbhyankarDVR.{0}`. Its DVR, fraction-field, finite-separable, tame,
   unit/divisibility, root and generation inputs are the proof's actual inputs.
   The restricted place theorem is explicitly not used.
2. **Constructed objects:** `S`, `C`, `B`, `U`, their primes and the root model
   are the concrete integral closures, localization and subalgebra described
   in the full chain above; `Frame.lean` and `LocalField.lean` fix their maps.
3. **Domain/index coverage:** an arbitrary original final prime is pulled
   back by the actual algebra equivalence. Its restricted prime is proved
   prime and lies over the original maximal ideal. Extension/contraction and
   the complete inverse prime-family correspondence are proved in
   `Normalization.lean`; no single chosen complete-field place supplies all.
4. **Transition maps:** the natural field embedding, integral-closure map,
   canonical coefficient localizations and quotient maps commute. The local
   and residue comparisons preserve the original `R` coefficients, with
   quotient-class formulas in `Comparison.lean` and `General.lean`.
5. **Consumed-object identity:** the field-factor model is proved equal to
   `integralClosure B M`. The iterated closure is compared to the literal
   `integralClosure R M`, and the final quotient concerns the original prime.
6. **Normalization conventions:** the proof uses the baseline's localization-
   length `Ideal.ramificationIdx`. `Local.lean` identifies it with the DVR
   uniformizer exponent; the final tower computes equality with `n`, not an
   unspecified proportionality or just an `lcm` analogy.
7. **Local conditions:** the DVR localization, normal model, fraction fields,
   faithful embeddings and flatness are proved. Finiteness is used over the
   actual rings where established; `R → S_q` is not falsely asserted finite.
8. **Exceptional cases:** `n = 1`, trivial intermediate extension, arbitrary
   residue characteristic, unit casts, nonzero denominators and multiple
   primes are addressed by the closed proof and the explicit component lemmas.
   No complete/henselian/perfect-residue hypothesis is added.
9. **Downstream consumption:** the returned type is exactly the closed
   baseline proposition. The actual shared-layer repetition and its existing
   iff were compared. Root/registry/manuscript/release integration and required
   non-author acceptance are not supplied by this contribution.

## Frozen contribution source binding

SHA-256 of the actual UTF-8 Lean source files checked (all paths are relative
to `ZInQKernel/Contrib/Abhyankar/`):

```text
Audit.lean        40b1397ff5a26a9962c42fc6bbe365034b7192093d20cd1974a2a59d26629355
Builder.lean      a0dc896d4df69016dae094db0023d8cbcff2865f8a2e94776bb63e89bad9a8f5
Comparison.lean   614f72b505cae7a2c41f1647b89cb7ff0871154c35ff44cd2d9fb8f49835a032
DvrInclusion.lean 828530fb8848515248fba0b91b3c9e7dd20f1b49de933f8f244eafa8684e9bd4
Etale.lean        ee75110c63719900bba1972faffb02f8fb7ed156c3957213b8db05239b9f5d6a
Field.lean        71431dfef83d67c0f4169f330d6dbb8a0fb5a0803871f4d68cba70d5b179e96b
Fraction.lean     427353329f0a7aaf3596d5a5da479cd0a73822e40a0b6a2e5e1a70cb64bd253b
Frame.lean        7cae8227bf4c4047efbf2ff8afc47238f4960d137664f9a17baf242d0ea4cd07
General.lean      6cf14b4852ac0b2d5d589cc24170aa709cb42679720d7e96e8017244d9254026
Kummer.lean       c2e2b02e5b4b0121e76c2ee51954f7f7d951951aa5672158df86d16ecbd6a58d
LocalField.lean   d4ccb4c57dad35f9040ec0d80f35b41c9915c4062c6a74f8b548595ac24053db
Local.lean        a2531ee1b3986321263b3209b4fa032fceefc20af714bdb15b6c31ed194a0720
Model.lean        6d844b55b2e6ac2ba9db01f276714a73d4e101468abe427b0b48dd9ecfe7e911
Normalization.lean 50c0ee12fec458ccf05fb991b03c9dd404d03999968ed9e19a311b8e0085a73c
One.lean          65b504b8607da08365243dabdc1b53ff8bb510003ef3c61891e05d82b4e1e47f
Primes.lean       e318c632a1b13141c14122414b9737b509b951f16815b3d0a4a67a5844021b66
ReducedLocal.lean 2e5d1dfcad8944cd4c994756dc4cdc66304a8b4adc209010391e54392aa98b75
Transport.lean    dbd4dda5714ac510d1b899af9b02b8a5bb0a285a96e90a6517356156a0c099b5
```

The unchanged baseline `ZInQKernel/HDecomp/Objects.lean` has SHA-256
`60178cdd4a2cbaaf44c18676b9677b85721ccc8efc04fdfe6ec0cf4a3a1fec1d`.

## Verification and review

The scoped modules were compiled on the pinned toolchain with
`LEAN_NUM_THREADS=2`, at most two compiler processes, and a resource gate
preserving their compiler arguments and exit statuses. No Mathlib source or
shared cache was changed. A portable underlying command is:

```sh
for m in Field Transport Local Primes Fraction Etale ReducedLocal Model Builder \
  Normalization LocalField Frame Comparison Kummer One DvrInclusion General Audit
do
  LEAN_NUM_THREADS=2 lake env lean \
    -o ".lake/build/lib/lean/ZInQKernel/Contrib/Abhyankar/$m.olean" \
    "ZInQKernel/Contrib/Abhyankar/$m.lean" || exit "$?"
done
```

`Audit.lean` is the tracked scoped type/axiom reproduction entry point. It prints
`ZInQ.Contrib.Abhyankar.abhyankarDVR : PkgI2.AbhyankarDVR.{0}`, with no extra
explicit, implicit, typeclass or section hypotheses. Both this provider and
every reported component use only `propext`, `Classical.choice`, and `Quot.sound`.

The final scoped replay used Lean 4.35.0's
`Lean.Kernel.Environment.replay` on **all 227 serialized declarations from
all 18 contribution modules**, including auxiliary declarations. It rejected
owned axioms, unsafe/partial declarations, duplicate declarations, missing
modules and declarations already in the external base. Before replay it checked
the provider's raw elaborated type and empty universe-parameter list. No owned
declaration was skipped. Traversal of **37,550 dependency declarations** gave
exactly the three standard axioms above. The baseline objects and pinned
external libraries were the external base; protected parent candidate audit
and independent/Astra review are distinct, not claimed here. Source-token and
import checks found no forbidden proof mechanism or unproved scratch-leaf import;
Git checks found no tracked baseline, pin, registry or policy changes.

AI contribution: Metamate and a separately scoped helper agent implemented the
proofs and connecting arguments. **Serving model identity is unknown. Astra
review is pending.** The work is a contributor proposal, not independent
protocol acceptance. No commit, push, pull request, merge, human outreach, or
controller acceptance was performed.
