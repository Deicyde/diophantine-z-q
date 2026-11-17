# Source-to-theorem application map

Application ID: `LBI-V13-20261110`. Author/integrator: Codex `/root`, directed
by Chey Loveday. This is a conditional-interface application record, not a new
acceptance of the manuscript's global arithmetic constructions.

The manuscript authority is `manuscripts/quartic_v13.tex` at upstream commit
`9c0b3aba60d90fdcac82115f0582a6f52f1054f7`, SHA-256
`9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`.
The four Lean source files are unchanged selections from research commit
`33483f751e6dcd3f91fb303969838aca33ad0458`.
[ORIGIN.json](ORIGIN.json) binds their Git blobs, SHA-256 hashes, imports,
dependency pins and manuscript excerpts. Line numbers below refer only to
that manuscript version. No manuscript edits are proposed.

Historical ordinary derivations remain available at immutable source links:
[local transport](https://github.com/CheyLoveday/diophantine-z-q/blob/33483f751e6dcd3f91fb303969838aca33ad0458/research/conjugate-local-transport/DERIVATION.md),
[boundary cup](https://github.com/CheyLoveday/diophantine-z-q/blob/33483f751e6dcd3f91fb303969838aca33ad0458/research/actual-boundary-cup/DERIVATION.md), and
[orthogonal comparison](https://github.com/CheyLoveday/diophantine-z-q/blob/33483f751e6dcd3f91fb303969838aca33ad0458/research/orthogonal-comparison/DERIVATION.md).
They are attribution/context, not additional proof roots or fresh acceptance
of every arithmetic/limiting assertion. Their dated status prose is historical.

## Application table

Names below omit the common `Research.DerivativeSwitch` prefix. Supporting
proof roots and definitions are exhaustively listed in [TARGETS.json](TARGETS.json).

| ID / lower-level premise | Proved interface | Exact manuscript consumer | Remaining arithmetic input |
| --- | --- | --- | --- |
| L1. `LocalData`: normal subgroup, actual twist αT, φ=dτ, T(φ)=T(τ), τ²=1, finite generator φ², tame relation and trivial local actions. | `ConjugateLocalTransport.LocalData.coordinates_rawConjugate` derives u=α(d)⁻¹ and coordinates (u f,u ℓ s); `_of_neg_one` gives (u f,−u s) when (ℓ:R)=−1. The transport equation is not a structure field. | H12, lines 3225–3233; local conjugate carriers and pairing, 2898–2967 and 3431–3508; `ex:limits-derivative-switch`, 5021–5093. | Instantiate all relations on the actual finite representation and a common quotient retaining the cocycles/actions. The tame relation must be exact in the chosen quotient, not merely true for unrelated local lifts. H21 character triviality and the good odd derivative place are arithmetic inputs. |
| L2. Evaluation at trivially acting elements; pullback of the coefficient representation and cocycles. | `h1Evaluation`, `h1Pullback` descend through Mathlib's actual H¹ projection; `LocalData.h1_local_transport` proves the same unit identity on every H¹ class, with original and conjugate carriers distinct. | Continuous finite representatives in H22, 3509–3542; derivative data H20–H21, 3339–3417; retained inner diagrams, `ex:limits-inner-limit`, 4577–4636. | Identify continuous arithmetic classes with the appropriate finite/abstract group-cohomology realization. Retain compatible coordinate maps, units and inverses in the specified limiting diagram. H¹ base change or finite-to-characteristic-zero maps are not supplied by the theorem. |
| B1. Two degreewise cup Leibniz identities; closed l; actual cycle equation `inc u=loc g+dq`. | `ActualBoundaryCup.pure_boundary_correction` proves `l cup inc u = l cup loc g − d(l cup q)`. A trace killing d gives `traced_pure_boundary`; closedness and that same trace give boundary invariance in both slots. | H22 cone, 3509–3542; duality-defined paired functionals, 3842–4012; their use in `ex:limits-derivative-switch`, 5021–5093. | Construct/identify the actual local products, comparison partner, compact-support product and global/local trace square. Use the same trace and coefficient pairing, including J exactly once, for both source functionals. This PR does not prove that these arithmetic objects instantiate `LocalCupData` and the trace hypotheses. |
| O1. Local degreewise chain-map relation for a and inclusion homotopy `inc−inc'a=dh+hd`. | `OrthogonalComparison.fibreComparison_commutes` proves the H22 comparison `(g,u,q) ↦ (g,au,q+hu)`; `fibreComparison_global` preserves g; `fibreComparison_sign_change` translates q to the opposite cone convention. | H22, 3509–3542; orthogonal/conjugate comparison defining the partner, 3842–4012; derivative orthogonal identity, 5351–5373. | Supply the actual local chain maps and homotopy in every relevant degree and assemble the complexes. The degreewise calculation alone is not an existence theorem for an arithmetic quasi-isomorphism. |
| O2. Genuine homological complexes, maps j,k,p,q with `j ≫ q=p`, and a supplied homotopy `k ≫ j ~ id`. Localization is a chain map from the common global complex. | `inverse_preserves_global_homotopy` / `_homology` and their local counterparts prove projection preservation by k, first up to homotopy and then on homology. | The actual partner `j⁻¹c(z)` at 3842–4012 and derivative-place localization at 5351–5373, consumed by the lower-bound route 5095–5379. | Prove existence of the required k and right-inverse homotopy in each permitted arithmetic coefficient/localization regime, and identify it with the source comparison. Do not infer an integral inverse from a generic inverse or invert a nilpotent finite-stage parameter. |

These are three lower-level compatibility deductions, not a proof of the
complete functional-normalization equation. None assumes the desired tensor
ratio or the global boundary-duality adjunction as a renamed premise. The
source occurrence of the lower-level data remains visible in the last column.

## Conventions and source comparison

Let q_H be the H22 local coordinate. Its differential has third component
`loc g − inc u − d q_H`. In the boundary-cup convention put q_N = −q_H;
the third component becomes `−loc g + inc u − d q_N`. A cycle then has
`inc u=loc g+d q_N`, precisely the hypothesis of B1. The comparison sends
q_H to q_H+h u, hence q_N to q_N−h u. These are different coordinate formulas
for the same sign conversion, not contradictory cycle equations.

For closed l, the first Leibniz identity gives
`d(l cup q_N)=−l cup d q_N`. Bilinearity and the cycle equation give B1;
applying a trace that kills d gives its traced version. The other Leibniz
identity proves invariance under a left boundary. The formal hypotheses are
therefore independently meaningful input equations. A global adjunction does
not appear among them.

For O2, composition of the supplied homotopy `k ≫ j ~ id` with q, using
`j ≫ q=p`, gives `k ≫ p ~ q`; postcomposing with localization gives the local
version. This requires a right homotopy inverse, not just an arbitrary chosen
map called an inverse. No finite/singular Selmer-complex isomorphism fixing
the strict complex is used or concluded.

The ordinary cone/cup source is Jan Nekovář, *Selmer complexes*, Astérisque
**310** (2006), §§1.3.1–1.3.4 (mapping-fibre products and homotopies),
§§6.3.1–6.3.3 (compact-support target and trace), and §§7.1.1–7.2.1 (local
conventions), [published edition](https://www.numdam.org/item/AST_2006__310__R1_0/).
These sections identify the source construction to be instantiated; no
unproved use of global Poitou–Tate duality is hidden in the Lean import graph.
Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679` provides
`H1`, `H1π`, `H1π_eq_zero_iff`, `H1_induction_on` in
`RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`, and
`Homotopy.homologyMap_eq` / homotopy composition in
`Algebra/Homology/Homotopy.lean`. Those are actual dependencies, covered by
the native transitive-axiom audit with the declared cache trust.

## Nine application obligations

1. **Source hypotheses:** addressed as explicit formal premises in L1–O2.
   Their arithmetic instantiation is conditional as recorded in the table;
   it is not certified by the module names or earlier review verdicts.
2. **Constructed objects:** L1 constructs the unit; L2 constructs evaluation
   and pullback on actual Mathlib H¹; B1 proves an equality of supplied cup
   expressions; O1 gives a degreewise map and O2 a homotopy from supplied data.
   Continuous Galois/Selmer complexes are not constructed by this selection.
3. **Domain/index coverage:** all cocycles/classes on fixed L1/L2 data; all
   closed directions and partner cycles in B1; any supplied complexes and
   homology index with the required homology instances in O2. Arithmetic
   occurrence for every finite stage, support, retained limit or height-one
   localization is still an external input, not an implicit quantifier.
4. **Transition/comparison maps:** conjugate coefficient pullback is explicit;
   boundary invariance is proved; O1 and O2 keep comparison direction and
   homotopy hypotheses visible. No inverse is inferred merely from localization.
5. **Consumed-object identity:** the source partner is `j⁻¹c(z)`, not an
   independently normalized row. The actual functional is defined at 3873–3891
   with comparison/integral regimes at 3979–3999; 4014–4029 defines the resulting
   class-functional determinant coordinate, not a stored-row matrix construction.
   Identifying these objects with the common-strict matrices and stored rows is
   required before applying a determinant bridge. No such identity is set by fiat.
6. **Coefficients/normalization:** R is a commutative ring in L1/L2/B1;
   no division by two, a vector or a functional occurs. The tame minus-one
   specialization requires its finite-stage congruence. The coefficient J
   belongs in the arithmetic pairing once, not in raw conjugation again.
   An arbitrary rescaling of one functional is not justified by these results.
7. **Local conditions:** the formal relations are explicit. Good reduction,
   odd derivative primes, tame quotients, full/zero/Kummer conditions elsewhere,
   and their orthogonal comparison remain source inputs as indicated above.
8. **Exceptional cases:** zero/divisible coordinates and characteristic two
   do not invalidate the ring-level identities. There is no nonvanishing,
   primitivity, integral inverse or fixed-characteristic-zero minus-one claim.
   Rank-changing finite/singular complexes are not asserted isomorphic.
9. **Downstream use:** the package makes these local interfaces inspectable
   and reusable. The actual paired-functional normalization, strict determinant
   lattice, torsion factors, retained cup/trace compatibility, exceptional-prime
   coverage and universal integral descent remain outside this selection's proof
   and acceptance scope. Existing ordinary source arguments and other research
   packets retain their separate status. The frozen
   conditional foundation and its 39-target evidence are unchanged and are not
   used to certify this selection.

## Review boundary

The exact final source/application bytes are to be assessed by the separately
authored reports in [reviews/](reviews/). Their bindings, limitations and any
findings are recorded separately; this author does not supply their acceptance.
Native Lean checking, finite diagnostic controls, source interpretation and
arithmetic occurrence are distinct evidence layers. The wider research bank
and four-term proposal are neither inputs nor mandatory merge gates here.
