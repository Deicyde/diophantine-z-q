# The abelian variety and coefficient-field action in `AfShimura`

`AfTateLam.afShimura_proof : AfTateLam.AfShimura` is proved outright on
the pinned main base `29bfbc3f6793d98b7c1ac637f9728fe51e701e5b`.
It supplies the finite-dimensional coefficient field, the abelian variety
quotient and the action. A later fold can remove `shimuraThm1Af`, taking the
open-row inventory from 24 to 23. [Lean proof](../../ZInQKernel/Contrib/OneProof/AfShimuraProof.lean)

## Quotient builds

The six serial `lake build` commands ran on Lean 4.35.0 with a 60 GiB memory
cap. Each module built without source repairs.

| Module | Result |
| --- | --- |
| `ShimuraQuotientHecke` | Passed |
| `ShimuraQuotientGeometry` | Passed |
| `AbVarQuotientFinite` | Passed |
| `AbVarQuotientComplement` | Passed |
| `AbVarQuotientConnected` | Passed |
| `ShimuraQuotientImageSum` | Passed |

The source scan of these six files had no matches for `sorry`, `axiom` or an
import of `AbVarQuotientPrint`. [Build log](../../scratch/m1-afshimura/builds.txt)

The quotient audit returned `[propext, Classical.choice, Quot.sound]` for
`imageSum_exists`, `abVarQuotientBySubvarietyExists` and
`kills_iff_kills_imageSum`.
[Kernel output](../../scratch/m1-afshimura/axioms-quotient.txt)

## Construction

The manuscript invokes Shimura's quotient at `diophantine_zq.tex:770`.
The existing reading of Shimura 1973, Theorem 1, identifies the construction
as the quotient by a sum of images of annihilating endomorphisms. Here the
family is the image under `heckeJ` of the kernel of `evF`, as required by
`KillsIf`. [Recorded source reading](r16-thm1b.md)

1. `imageSum_exists` gives the abelian subvariety `C` for this family, and
   `abVarQuotientBySubvarietyExists` gives the genuine quotient `π : J → A`.
   The equivalence `kills_iff_kills_imageSum` transfers its surjectivity,
   annihilation and unique factorization into `IsAfQuotient`.
2. `DSCoeffExt.isNormalizedEigenformDS_of` turns the newform's normalized
   eigenform condition into the input to `eigenformCoeffFieldFinite_proof`,
   giving finite dimension of the coefficient field over ℚ.
3. For a free Hecke element `g`, the composite `π ∘ heckeJ g` kills the
   annihilator family since `evF (g * k) = 0` whenever `evF k = 0`.
   `R16Thm1.exists_rel` supplies the induced endomorphism. Uniqueness and
   the integral composition laws make these endomorphisms a ring
   homomorphism. Its kernel contains the kernel of evaluation, so it
   descends to the integral eigenvalue ring. The prime-square recurrence
   at a Dirichlet prime in each unit residue class puts the diamond values
   in `coeffField f`.
4. The rationalization map from ℚ tensored with the integral eigenvalue
   ring into `coeffField f` is injective by clearing an integer denominator.
   Its image is a subfield because the coefficient field is algebraic over ℚ.
   It contains the prime coefficients and diamond values, hence all
   coefficients by `HeckePin.coeff_mem_genField`. Tensoring the integral
   action and using this isomorphism gives `θ`. The free generators give
   the two clauses of `IsAfAction`.

The action uses the coefficient recurrence and the universal property of
the quotient. The stronger Shimura statement also carries a dimension
clause and uniqueness among triples.

## Axiom audit

The full `AfShimuraProof` module build passed. The axiom audit covers all
46 theorems in the seven added Lean modules, including private lemmas.
Each entry has the same axiom set. [Kernel output](../../scratch/m1-afshimura/axioms.txt)

```text
'AfTateLam.afShimura_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Fold specification

On the pinned main commit, `frozenTarget` receives
`HDec.HSyn.OpenResearchLeaves76` at `ZInQKernel/OneProof/Main.lean:268`.
The live Tail is `ZInQKernel/OneProof/H/TailZ102.lean:75`. Its field
`shimuraThm1Af` is at line 43. The Tail conversions forward it back to
`ZInQKernel/OneProof/H/TailZ91.lean:106`, which enters the NOS chain. The
receiving field is `HDec.HSyn.OpenResearchLeaves59_y3x6NOS.afShimura` at
`ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:4173`.

After the full `NOSNarrowChain` build, Lean checked that this field has type
`AfTateLam.AfShimura` and that `AfTateLam.afShimura_proof` inhabits it.
[Fold check](../../scratch/m1-afshimura/FoldCheck.lean)

| Assignment on main | Module in the import closure of `frozenTarget` | Use on its declaration route |
| --- | --- | --- |
| `ZInQKernel/OneProof/H/CMOpen.lean:342` | Yes | Historical CM copy |
| `ZInQKernel/OneProof/H/Y3Open.lean:342` | Yes | Historical Y₃ copy |
| `ZInQKernel/OneProof/H/TailZ86.lean:79` | Yes | Historical Tail conversion |
| `ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:4421` | Yes | Live NOS conversion entered from `TailZ91` |

Remove `shimuraThm1Af` from the live forwarding bundles and use
`afShimura := _root_.AfTateLam.afShimura_proof` in the live NOS conversion.
This covers `TailZ91.lean` through `TailZ102.lean` and the NOS fields at
`NOSNarrowChain.lean:4143`, `:4659` and `:4780` with their forwarding
assignments. Import `AfShimuraProof` where the NOS assignment consumes it.
A literal reversal of r16-thm1b would restore `heckeJ1DS` and drop
`bShStandardModel`. Keep the existing `bShStandardModel` wiring. The standalone
`R16Thm1b.r16CoreY_of_thm1Af` at
`ZInQKernel/Contrib/OneProof/R16Thm1b.lean:95` also calls the supplier,
with an explicit `ShimuraThm1Af` argument. It has no callers in the tree.

The fold removes the research `consequence` / `GLUE` row at
`docs/one-proof/kinds.tsv:17`, its claim index entry at
`docs/one-proof/OPEN.md:80`, its table row at `docs/one-proof/OPEN.md:143`
and its detail section at `docs/one-proof/OPEN.md:366` and `:368`.
This takes the stated inventory from 24 to 23 with one fewer GLUE row.

The source reading for `hRC`'s κ route, `shimuraEmbeddings` and
`carayolEulerFactors` is still required. The reviewer owns the decision
about the `ShimuraThm1AsPrinted` and `ShimuraRing0` split.

## Known issues

- The earlier source audit records a missing conjugation subscript in
  Shimura 1973, p. 526, in the sentence before clause (iv). The quotient
  construction uses the annihilator family and its universal property.
  [Prior audit](r16-thm1b.md#known-issues-exact-locations)
- The comment describing the integral intertwining relation as weaker in
  `ZInQKernel/Contrib/OneProof/R16Thm1.lean:53` is misleading. In this
  setting the relations are equivalent by clearing denominators and
  torsion-freeness. [Prior audit](shimura-quotient.md#known-issues)
