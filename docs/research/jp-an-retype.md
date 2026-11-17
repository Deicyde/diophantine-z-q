# jp-an-retype: Javanpeykar Thm 1.1.1 + §2.3 over the analytic stable height

Task jp-an-retype, 2026-11-17. Base `wip/leaf-fold33b` bf691da22 with `wip/semistab-assembly` 418304785 merged.
Lean: `ZInQKernel/Contrib/OneProof/JavanpeykarAnRetype.lean` (namespace `JavanpeykarAnRetype`). Scratch:
`scratch/jp-an-retype/` (log, autofold spec, `#discharges` file and output, dry-run output).

## 1. Result

The research field `javanpeykarThm111 : JavanpeykarDirect.JavanpeykarThm111` is **retyped onto the analytic stable
height**: the new leaf `JavanpeykarAnRetype.JavanpeykarThm111An` is `JavanpeykarThm111` verbatim with the height
predicate `IsStableHeightBar` (built on height-fix's `IsPrintedStableHeight`) replaced by `IsStableHeightBarAn`
(built on semistab-assembly's `IsAnStableHeightSS`: r3-residual's `IsAnStableHeight` with semistability as printed).
VERIFIED (compiled, standard axioms only):

* `javanpeykarThm111_of_an (h : JavanpeykarThm111An) (hMT : AvSplit.MumfordTorsionAlgClosed) : JavanpeykarThm111`
  (T35 filled by `uniformizationLeafAll_proof` through `AvSplit.Final.h38`, as r3-residual did for
  `javanpeykarPrintedMap_of_an_min`);
* `javanpeykarThm111An_of_thm111 (h : JavanpeykarThm111) (hT35 : UniformizationExists) : JavanpeykarThm111An`
  (the converse: the new leaf is not stronger than the row it replaces);
* `isStableHeightBarAn_iff (hT35) : IsStableHeightBarAn W x ↔ IsStableHeightBar W x`.

So the deciding step of the row is now exactly R3' (the `IsHolChart` atlas is the complex structure of
`A(ℂ)^an`), the same single step that `bostLowerBoundAnSS` and `gaudronRemondThm14AnSS` sit behind.

**By-product (VERIFIED, compiled):** semistab-assembly's printed semistability is *equivalent* to the old clause:
`isSemistableRes_of_printed : IsSemistablePrinted 𝒩 → IsSemistableRes 𝒩` (an open subgroup `U` whose image is the
connected component of the unit is connected: an open immersion is an embedding, and a connected component is
connected), hence `isAnStableHeightSS_iff : IsAnStableHeightSS A x ↔ IsAnStableHeight A x` with no hypothesis.
semistab-assembly proved only `→`; with this, `BostLowerBoundAnSS ↔ BostLowerBoundAn` and
`GaudronRemondThm14AnSS ↔ GaudronRemondThm14An` as well (one-line consequences; not stated as theorems here).

## 2. The leaf and its rating

`JavanpeykarThm111An` (docstring in the Lean file) states, for any algebraic closure `ℚ̄` of `ℚ`, any smooth proper
geometrically connected integral projective curve `X/ℚ̄` of genus `g = genusK X ≥ 1`, any Jacobian `W` (representing
`Pic⁰_{X/ℚ̄}` with the tensor group law), any proof `hB` that a Belyi map exists, and any `x` with
`IsStableHeightBarAn W x` (the analytic stable height of a model of `W` over a number field `L ⊆ ℚ̄`):
`x ≤ 13·10⁶ · g · deg_B(X)⁵`, with `deg_B(X) = belyiDegree X hB` the least Belyi degree.

Shape (task item 4). The manuscript cites the print at diophantine_zq.tex L870 as "Theorem 1.1.1 and Section 2.3"
of Javanpeykar, applied to `J = J₁(N)`, and notes that the normalization is the original stable Faltings height of
the Jacobian (L874-875, VERIFIED read). The docstring keeps both cited statements and the line:
* Thm 1.1.1 (ANT 8 (2014) p. 90; arXiv:1403.6404v1 p. 1): `h_Fal(X) ≤ 13·10⁶ g deg_B(X)⁵` for `X/ℚ̄` smooth
  projective connected of genus `g ≥ 1`;
* §2.3 (ANT p. 98; arXiv p. 9): `h_Fal(X) = h_Fal(Jac X)`, the stable Faltings height of the Jacobian.
(Locators as recorded by the locator audit, docs/research/locators.md row R18; I have not read the paper here.)
The leaf is their composite and assumes nothing else. It is general in `X` (the manuscript's application to
`X₁(N)` is a specialization, made downstream by the existing glue).

**Rating: consequence, GLUE (count-neutral), not printed form as a whole**, for two reasons, both in the flag:
1. R3' remains inside the height predicate (IsAnMetricSq reads densities in the `IsHolChart` atlas; that this is
   the complex structure of `A_τ(ℂ)^an` is R3', being proved by a separate worker). Once R3' is a theorem, the
   height predicate is the print's.
2. The Section 2.3 composite: `h_Fal(X)` of a curve (Arakelov-metrized determinant of cohomology) is not defined
   in Lean, so the leaf is stated with `h_Fal(Jac X)`, i.e. Thm 1.1.1 composed with §2.3. Each conjunct is printed;
   the composite is a consequence of the two, never stronger. **Lead's ruling wanted** on whether the composite of
   two printed statements counts as printed form.
Other clauses are as in javanpeykar-direct (definition-level: `IsStableHeightBar` as Faltings' stable height of an
abelian variety over `ℚ̄` via a model, `IsBelyiMap` via ramification indices). Semistability is the print's (both
readings of SGA 7 IX 3.4 at once, equivalent to `IsSemistableRes` by §1).

## 3. Checks

* `lake env lean ZInQKernel/Contrib/OneProof/JavanpeykarAnRetype.lean`: VERIFIED, no errors, no warnings.
* `#discharges`: see §4 (scratch/jp-an-retype/discharges-output.txt).
* Autofold spec `scratch/jp-an-retype/autofold.json`: field `javanpeykarThm111` discharged by
  `JavanpeykarAnRetype.javanpeykarThm111_of_an {n}.javanpeykarThm111An {t}.mumfordTorsionAlgClosed`; new leaf
  `javanpeykarThm111An`, kind consequence, flag class `reading-risk` (flag names R3' and the §2.3 composite; no
  unread/pending/UNVERIFIED wording). `autofold.py --dry-run`: VERIFIED exit 0,
  "strict count: 4/27 on 31 -> 4/27 on 31; strictest 4/27 -> 4/27" (count effect 0, as expected).

## 4. #discharges

`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.JavanpeykarAnRetype`:
VERIFIED "Build completed successfully (16217 jobs)". `lake env lean scratch/jp-an-retype/Discharges.lean`
(output scratch/jp-an-retype/discharges-output.txt), VERIFIED:

```
DISCHARGES [OpenResearchLeaves48.javanpeykarThm111] by JavanpeykarAnRetype.javanpeykarThm111_of_an
  still assumes: [JavanpeykarAnRetype.JavanpeykarThm111An, AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
```

(`AvSplit.MumfordTorsionAlgClosed` is the existing textbook field `{t}.mumfordTorsionAlgClosed`, as in
r3-residual's discharges.) `#print axioms` of `isSemistableRes_of_printed`, `isAnStableHeightSS_iff`,
`isStableHeightBarAn_iff`, `javanpeykarThm111_of_an`, `javanpeykarThm111An_of_thm111`: standard three only.

## 5. What remains

* R3' (separate worker). When it lands, `javanpeykarThm111An`, `bostLowerBoundAnSS`, `gaudronRemondThm14AnSS`
  lose their shared step together.
* Lead's ruling on the §2.3 composite (Thm 1.1.1 ∘ §2.3 stated with `h_Fal(Jac X)`).
* No ON THE SPOT arguments were used: every proof step is an equivalence of Lean definitions.
