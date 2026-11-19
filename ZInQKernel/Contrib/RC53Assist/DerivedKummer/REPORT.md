# Derived Kummer: local duality and the remaining comparison interface


## Correction after independent review (2026-11-18)

The premise `hred` of `actualCup_divisible_of_print` and `kummerTruncIsotropy_from_print` is, as typed, equivalent to pointwise vanishing of the integral function it is applied to, once the printed local duality is supplied (`reductionPremise_iff_zero` in `Circularity.lean`). It therefore restates the trace-vanishing goal and is not an independent reduction-identification input: these two declarations are conditional wrappers around the still-open trace-vanishing statement. What is needed instead is a set of fixed, genuine finite-level coefficient, cochain and class reduction maps, their Kummer-image identifications and the cup-invariant compatibility for those maps, from which the displayed equality is derived. The finite-duality results (the exact Kummer annihilator, the mod-two comparisons, the degree-zero identification) and the comparison algebra are unaffected. The `MANIFEST.json` and standalone audit sources mentioned below are not shipped with this edition.

## Result and scope

The three production modules compile individually. They prove the exact Kummer annihilator assertion, the actual quotient-to-dual comparison over F₂, its degree-two component dual to the retained rational two-torsion, and the canonical degree-zero torsion identification. They also supply a torsion-preserving comparison for a presented derived reduction and the comparison-cone algebra needed by derived Nakayama.

This is **not a completed instantiation of the actual integral local Selmer-condition comparison**. The remaining identifications are listed below as explicit hypotheses, not converted into new printed leaves. In particular, no contraction of the actual local comparison cone has been asserted without constructing that map and its cycle-class identifications.

The source boundary is two named Prop inputs from the manuscript's cited Milne source. They have no unconditional inhabitant in these files. The axiom audit records kernel dependencies; it does not discharge these Prop inputs or the explicit identification hypotheses.

`THEOREMS.md` contains the exact Lean statement and verbatim `#print axioms` result for every new theorem. `MANIFEST.json` records SHA-256 and byte size for the delivered sources and receipts. Each audit source is a standalone copy of its production source followed by audit commands; do not import an audit copy alongside the corresponding production module.

## The manuscript statement actually used

The supplied manuscript passage says, at lines 3442–3445, that the local finite dualities make

- the Kummer map `B(F)/2^a B(F) → H¹(F,B[2^a])`, and
- the projection `H¹(F,B[2^a]) → H¹(F,B)[2^a]`

adjoint. Kummer exactness identifies the kernel of the latter map with the Kummer image. Nondegeneracy of local Tate duality therefore makes that image its exact right annihilator.

Lines 3452–3453 require a derived mod-two comparison, **including the degree-zero torsion**, before derived Nakayama can be applied. At the cohomology level the two nonzero comparison components are

```
H¹(F,B[2]) / im(δ)  ≃  Hom_F₂(B(F)/2B(F), F₂),
H²(F,B[2])         ≃  Hom_F₂(B(F)[2], F₂).
```

The degree-zero condition map must be the canonical identification `B(F)[2] ≃ H⁰(F,B[2])`. Omitting this torsion or proving only the degree-one component would not prove the derived comparison.

There is no condition that the residue characteristic be odd. The printed local inputs here require characteristic zero of **F itself**. Consequently they cover both nondyadic and dyadic nonarchimedean places, with arbitrary reduction of the elliptic curve. `twoPower_isUnit` proves the relevant invertibility in the field, not in its residue field.

## The new printed leaves and their actual print locators

The bibliography entry `milne` is Milne, *Arithmetic Duality Theorems*, second edition, 2006, Chapter I:

https://www.jmilne.org/math/Books/ADTnot.pdf

The PDF read for this work has 347 pages, 2,136,045 bytes, and SHA-256

```
2c6195ec76a974f3f336c77cb71cc3845b018aad2d43136716b3477a3bc5fb31
```

The quotes below are mathematical transcriptions of the actual print. The elliptic curve is specialized along its canonical principal polarization. The Lean leaves record the underlying additive isomorphisms, not formalized compact/discrete topologies. The point-side dual is the finite-order character group; such characters are continuous because their kernels contain `nB(F)`, which is open by Lemma I.3.3.

### `MilneLocalDualityPrint`

**Corollary I.3.4, printed page 43, PDF page 51:**

> If K has characteristic zero, then there is a canonical pairing
> H^r(K,A^t) × H^{1-r}(K,A) → Q/Z,
> which induces an isomorphism of compact groups A^t(K) → H^1(K,A)^* (case r = 0) and an isomorphism of discrete groups of cofinite-type H^1(K,A^t) → A(K)^* (case r = 1).

**The commuting diagram in the proof of Theorem I.3.2, printed page 42, PDF page 50:**

> if we take α^r(G,A_n) to be the map α^r(G,A_n(K^s)) of §2, then it is clear that the diagram commutes.

**Remark I.3.5, printed page 44, PDF page 52:**

> It is possible to show that these pairings agree with those in (3.4) (up to sign) by checking that each is compatible with the pairings
> H^r(K,A^t_n) × H^{2-r}(K,A_n) → H^2(K,G_m)
> defined by the e_n-pairing.

The common sign is absorbed in the choice of the full Tate pairing. The leaf states existence of a `MilneCompatiblePairings B`: the two full Tate-duality isomorphisms and the commuting Kummer diagram for every finite level. **It does not contain the Kummer annihilator assertion or the quotient comparison as a field.**

### `MilneFiniteLocalDualityPrint`

**Corollary I.2.3, printed page 28, PDF page 36:**

> Let M be a finitely generated G-module whose torsion subgroup has order prime to char(K). Then cup-product defines isomorphisms
> H^r(G,M^D) → H^{2-r}(G,M)^*
> for all r ≥ 1, and an isomorphism (of compact groups)
> H^0(G,M^D)^∧ → H^2(G,M)^*.
> The groups H^1(G,M) and H^1(G,M^D) are finite.

The finite coefficient module is the actual `B[n]`, identified with its dual through the Weil pairing. The recorded components are the perfect degree-one pairing and the degree-two comparison to the dual of rational torsion, with the actual cup/invariant evaluation rule. Completion in degree zero is unnecessary for the finite coefficient module.

**Remark I.3.7 is not the dyadic input.** It concerns archimedean local fields, printed page 46, PDF page 54, and uses Tate cohomology of `Gal(C/R)`. No archimedean local-duality claim is made here.

## What the new proofs establish

### `LocalDuality.lean`

1. `MilneCompatiblePairings.toRC53` discharges the existing finite local-duality interface from the full printed pairing and its commuting diagram.
2. `kummer_exact_annihilator_of_print` proves membership in the actual Kummer range iff orthogonality to that range under the actual Weil-cup/local-invariant pairing.
3. `kummerQuotientComparison_bijective` proves the finite quotient-to-dual comparison for every invertible finite level. Its surjectivity follows from the full Tate duality and the surjective Kummer projection, not from an assumption that isotropy implies maximal isotropy.
4. `kummer_modTwo_linear_comparison_of_print` proves the coefficient-valued F₂-linear comparison, with the precise normalization
   `toRatAddCircle 2 (e [y] [p]) = localTatePairing (δ p) y`.
5. `kummer_modTwo_torsion_comparison_of_print` supplies the degree-two component dual to all of `B(F)[2]`.
6. `derived_modTwo_comparisons_of_print` transports both components through the existing `kerReduction_equiv` and `cokerReduction_equiv`, displaying the actual-completion identifications `η₀` and `η₁` explicitly.
7. `actualCup_divisible_of_print` discharges finite divisibility from actual Kummer isotropy when the explicit integral-to-finite trace compatibility is supplied. `kummerTruncIsotropy_from_print` then constructs the existing zero truncated isotropy homotopy.

### `DegreeZero.lean`

`torsionH0Equiv` identifies the actual rational n-torsion with the invariant part of the actual torsion coefficient module. Its evaluation rules are the actual `baseTorsionCoeff` and `basePointCoeff` maps. This needs no local-duality print and is valid over a general field.

### `ComparisonAlgebra.lean`

The file proves that a based chain map bijective on its identified cohomology has exact cone. Over a field the cone has a contraction by the existing `exists_contraction` theorem. It also proves coefficient-change transport from F₂ to the residue field of Z₂.

`nakayama_comparison_of_modTwo_models` derives an **integral** cone contraction from two bijective F₂ cohomology comparisons, explicit cycle-class models, and their commuting squares with the reduced chain map. Its statement has **no reduced-cone-contraction hypothesis**. This supplies the comparison algebra for the manuscript's Nakayama step, once the actual map identifications are supplied. It gives existence of a contraction, not an arithmetic bound on its entries.

## The exact RC53 interfaces targeted

All five requested modules already contain proved algebraic declarations, not unfinished tactic holes.

### The local Tate input, in the imported local-Kummer dependency

`ZInQ.Contrib.CloudB3RC53.Duality.MilneLocalTateDualityKummer.out` is the precise local arithmetic placeholder. It requests

```
∃ tate : B(F) →+ H¹(F,B) →+ Q/Z,
  (∀ p y, localTatePairing (δ p) y = tate p (kummerProj y)) ∧
  (∀ y, n • y = 0 → (∀ p, tate p y = 0) → y = 0).
```

`kummerAnnihilatorNode_proof` already proves the annihilator implication from that interface. The new `toRC53` theorem supplies that interface from the stronger, accurately located full Milne print. The new global leaf is restricted to characteristic zero, unlike the older unconstrained nonarchimedean-local-field interface.

### The requested Duality algebra

- `derivedKummerStep_trunc`: `he` is injectivity of the degree-two trace on cocycles; `hiso` is divisibility of every restricted cup value by every `2^a`.
- `kerReduction_equiv` and `cokerReduction_equiv`: the hypotheses are the exact presentation `g.comp f = 0`, injectivity of `f` where needed, surjectivity of `g`, lifting of `ker g` to `im f`, and regularity of the scalar on `P₀`. These are algebraic presentation hypotheses, not local Tate duality.
- `kummerTruncIsotropy`: `hker` says the trace kernel on degree-two cocycles consists of boundaries; `hcup` is finite trace isotropy.
- `kummerTruncIsotropy_two`: `htrv` kills boundaries; `hker` is the trace-isomorphism kernel statement; `hdiv` is finite divisibility. `LocalTruncIsotropy.isotropy₂` and `.isotropy₃` are the output homotopy identities, not arithmetic printed inputs.

### The requested Torsion algebra

- `nakayama_contraction` takes `hbar : Contraction (C.map (IsLocalRing.residue R))`.
- `nakayama_comparison` takes
  `hbar : Contraction (BasedCx.coneR (f.map (IsLocalRing.residue R)))`.

These hypotheses represent the already-perfect reduced comparison at chain level. Milne does not print a contraction of an arbitrary supplied based cone. The new comparison algebra proves that contraction from cohomology models and the actual comparison maps instead of treating it as another printed leaf.

## Precisely what remains open

### 1. Actual completion/presentation identification

For the actual `M = B(F)^∧₂` and its selected free presentation, instantiate the existing presentation hypotheses and construct

```
η₀ : torsionN (2 : Z₂) M ≃+ B(F)[2],
η₁ : (M / nSub (2 : Z₂) M) ≃+ B(F)/2B(F).
```

The generic reduction algebra is proved, and both transported dual comparisons are proved **conditional on these displayed identifications**. No new identification of an arbitrary `M` with the actual completion has been postulated.

### 2. Actual integral trace and finite-reduction compatibility

Instantiate the existing two-term bounds and the trace hypotheses `htrv` and `hker` for the actual local target. In addition, prove the explicit `hred` equality in `kummerTruncIsotropy_from_print`: for each `a,u,v`, the canonical mod-`2^a` invariant of the integral restricted cup trace equals the actual finite local pairing of two Kummer classes. This is the remaining cochain/reduction identification; the vanishing of those actual finite pairings is proved.

The result constructs a **truncated** isotropy homotopy. No stronger untruncated homotopy has been inferred from trace isotropy.

### 3. Actual based chain comparison and its class maps

Supply the actual bounded based complexes `C,D` and their actual chain map `f` for the local quotient-to-dual comparison. On their reductions modulo two, construct the two `CohomologyModel` records:

- even and odd cycle-class maps;
- surjectivity of each class map;
- kernels exactly equal to boundaries.

Identify the source classes with `H²(F,B[2])` and `H¹(F,B[2])/im δ`, and the target classes with the F₂ duals of `B(F)[2]` and `B(F)/2B(F)`. Prove the two `commE` and `commO` squares for the actual reduced chain map using the supplied cup evaluation rules. In the local quotient cone this includes showing that the degree-zero condition map agrees with the canonical `torsionToH0`; the canonical fixed-torsion identification itself is now proved.

The new `nakayama_comparison_of_modTwo_models` then proves the required integral cone contraction. These actual model records and commuting squares have not been instantiated in the delivered files. Thus the complete actual derived-orthogonality assertion, and its application to the actual integral Selmer-cone comparison, remain open.

## Worktree discipline

The supplied baseline was `6ea158a404343c90a445c129cd0d1f3a0d4b8ddc`. Existing source files were only read. All authored sources and receipts are confined to the requested contribution directory. No Git operation, commit, checkout, repository build, package update, executable build, or message to another person was performed.

Single-file checks started only after the supplied build log reported `Build completed successfully (10643 jobs)`. The required CPU affinity, thread limit, and priority were used. Imported dependency objects were read from the completed build; no missing dependency was built.
