# Global Kronecker–Weber support: exact objects, closed reductions, conditional conductor assembly

## Scope

This is an additive **partial support contribution**, not an unrestricted global Kronecker–Weber theorem (T17), a local KW theorem (T16), an accepted registered provider, or a new official manuscript record. The frozen proof slice consists of thirteen `ZInQKernel/Contrib/KroneckerWeber/Global*.lean` modules and the nine-module `GlobalDifferentTransport.FixedFieldPrimeInvariants` source closure. It excludes the older eight KW modules, all subsequent compositum/completed-inertia consumers, and the completed-field and LocalKW supplier packets.

The publication is prepared on main `8799c581c8c327fca153ef31b8042f1dc053c62d`. Its 22 proof files are byte-identical to the earlier immutable source/review slice at `a5937595cde3e3db00975b81e5171cdef92c801a`. The intervening PR30 manuscript/release changes are preserved, not reverted or absorbed into a proof-acceptance claim. Lean, dependency pins, frozen root, target statements, registry, checker and controller policy are not changed.

The nine GDT sources are exact public dependencies already present in proposals [PR56](https://github.com/elliotglazer/diophantine-z-q/pull/56), head `fcc6b75d4aecdd112ca15e1ba8eed237fb2b34bf`, and [PR58](https://github.com/elliotglazer/diophantine-z-q/pull/58), head `11a2303f0a707553465613c75f3124de298c89d0`. Their bytes agree at both heads. In particular, `FixedFieldPrimeInvariants.lean` has SHA-256 `bc7a6f4d625577997a5b0f372165bca00b0cbed9d2d70e410ed82855bab0c60e`. Its changed application is reviewed anew; another proposal's CI or acceptance is not borrowed.

## Closed reductions

- `GlobalCyclic`: fixed fields of coordinate kernels give cyclic intermediate fields generating the **original** finite abelian number field. The native Mathlib `IsAbelianGalois ℚ L` class is used, not an exponent-two predicate.
- `GlobalCyclotomic`: normality and minimal-polynomial equality put branch images in the same actual cyclotomic layer of `AlgebraicClosure ℚ`; a finite family yields one positive common level, including the empty-family case. The final algebra map consumes the original field, not a substitute isomorphic model.
- `GlobalUnramified`: global unramifiedness over **ℚ** at every integer maximal ideal implies degree one by the pinned number-field discriminant/Minkowski result. No Galois hypothesis is added to that degree-one theorem.
- `GlobalInertia`: the actual inertia groups at nonzero primes generate `Gal(M/ℚ)` for every finite Galois number field. For their fixed field, the imported fixed-field index/intersection identity and the same integer-ring tower show ramification index one. Every fixed-field maximal prime is lifted to an original prime. The degree-one result and Galois correspondence then give the full group. Abelianity and local KW are not premises here.
- `GlobalDegree` and `GlobalInertiaFinite`: finite subgroup generation yields a product cardinality/degree bound, using actual inertia and the same Galois group.
- `GlobalRationalInertia` and `GlobalRationalDiscriminant`: primes over the same rational prime have equal actual inertia subgroups in an abelian extension; inertia is trivial outside the actual rational discriminant prime set. These are not merely cardinality comparisons or a set of model primes.
- `GlobalConductor`: the prime-power product is positive and its totient is the product of the local totients. The boundary cases include `p = 2`, exponent zero, an empty prime set, and level one.

## Conditional endpoint and the remaining arithmetic

`GlobalMilne` fixes one genuine rational closure embedding `φ : L →ₐ[ℚ] AlgebraicClosure ℚ` and constructs

`E_n = φ.fieldRange ⊔ cyclotomicLayer n`.

The number-field and abelian-Galois structures of this **same compositum** are derived from the actual factors. Finite inertia coverage, bounds and a product equal to `n.totient` imply that `E_n` is the actual cyclotomic layer, hence provide an algebra embedding of the original `L` into `CyclotomicField n ℚ`.

`GlobalPrimePowerAssembly.nonempty_embedding_at_primePowerConductor_of_arithmetic` constructs the positive level `n = ∏ p ∈ S, p ^ r p`, proves finite rational-prime coverage and the totient product, and retains two explicit arithmetic premises:

1. `hU`: for every prime `p ∉ S`, every actual integer prime `Q` of **E_n** containing `p` is unramified over **ℤ**.
2. `hB`: for every `p ∈ S` and every such actual `Q`, the cardinality of its inertia subgroup in **Gal(E_n/ℚ)** is at most `(p ^ r p).totient`.

The theorem quantifies over an **arbitrary finite prime set S**. Choosing `S = rationalRamificationSet L` is a downstream application, not an already-proved condition in this frozen theorem. Suitable exponents and both arithmetic premises must be supplied and separately checked for that original-set application. Neither a numeral example, unramifiedness over a cyclotomic base, bounds on an unrelated completion, nor a different embedding/conductor silently replaces them. The cyclic-input reduction likewise keeps its explicit input.

Thus the frozen support proves the reductions as stated; **full T17 remains open in this contribution**. Subsequent source that may discharge part of `hU` or compare completed inertia is outside this publication's frozen review scope.

## Evidence and limits

The preliminary independent source-first review reconstructed its statements before reading producer notes. Its immutable INITIAL SHA-256 is `3ef082b8b56d2e49d5d048e593315b70912e04f7e21fc192d2dec17f69f7a3f7`.

For this exact 22-module slice, that reviewer compiled all modules, checked 45 independent whole-type expectations plus six defining equalities, walked the axiom closure, and replayed all 132 owned declarations twice with actual bodies. The axiom closure was exactly `propext`, `Classical.choice`, and `Quot.sound`. Seven whole-type comparisons differed only in the elaborated `SupSet` instance path and were kernel-checked definitionally equal. All 113 inventoried passages were covered within the stated partial scope. The review's imported Mathlib/Lean-core dependencies were not themselves freshly replayed there; the parent full-normal gate is a separate result.

Retained qualifications include arbitrary-S scope, the unconsumed GDT lint warning, whole-package overlay shadowing, stale self-import behavior, the imported trusted-base limit, and later out-of-scope live-source drift. Earlier failed/tool-infrastructure attempts and overwritten-log limitations remain recorded; they are not relabeled as passes.

The reviewer was a non-author, but the review was preliminary and nonblind with unknown serving identity: **not designated Astra acceptance**, final assembled-proof acceptance, or manuscript incorporation. The PR supplies its own exact-head normal/control and public-CI evidence separately; this note does not forecast those results.

## Reproduction

Use the unchanged Lean 4.35.0 toolchain and the repository's pinned dependencies. Run the stock full gate, without skipping the root build:

```sh
python3 -B scripts/check_kernel.py --output ../kw-support-audit
```

Run the original kernel rejection and contract tests as well. A result is attached to its actual source head, base, compiler/pins, full module inventory and terminal logs. Do not import stale `Contrib` objects as source evidence, silently refresh frozen bindings after edits, count compilation as a raw replay, or count ordinary CI as the protected `Protocol / independent agent audit` check.
