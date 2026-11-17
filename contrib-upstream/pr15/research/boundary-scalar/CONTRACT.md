# Boundary-scalar application contract

**Scope:** an isolated extension of the derivative-switch research packet.
The supplied general matrix theorem is proved in [DERIVATION.md](DERIVATION.md).
The new formal core uses explicit normal-form matrices and closed functionals;
the adapter uses two typed boundary--cup identities. The actual arithmetic
identities remain OPEN. This is a non-release contribution on the research
branch, not a change to the manuscript or its accepted application records.

## Exact input and output

The matrix setting is an arbitrary field K and arbitrary finite index set with
distinct class/complement indices p,q. The remaining indices form the strict
block. The normal forms, cycle coordinate vector, and row-swap matrix are
concrete definitions. For each side retain a square differential D, source
basis matrix B, common target matrix T, cycle z and functional row λ. Supply
the exact equations `D B=T N`, `z=B e_p`, closedness `λ D=0`, and det T≠0.
The theorem derives the full outer-product/cofactor identity. With det B_F=η,
det B_S=δη and the stated nonzero hypotheses, it derives the comparison
`δu_F/u_S=−q_F/q_S`. Nonzero rows give nonzero cross evaluations.

The normal-form equations and basis determinants must be constructed from the
common-strict source data; the construction is proved in ordinary algebra in
the derivation and not claimed to be a Lean construction. The formal unit
criterion must refer to the image of R× under a ring homomorphism, since every
nonzero element of the fraction field is already a field-unit.

The adapter uses `J:F≃S` and the transported pairing
`β(f,s)=εω(f,J.symm s)`. Its hypotheses are lower-level identities for the
actual supplied boundary maps d_F,d_S and functionals λ_F,λ_S, with one common
factor c (or separately displayed c_F,c_S). Alternation then proves the cross
evaluation relation. The determinant equality is never an adapter hypothesis.

## Nine source-facing obligations

| Obligation | Constructed input and derivation | Arithmetic status |
| --- | --- | --- |
| Source hypotheses | The supplied matrix statement fixes n≥2, common D₀, actual nonzero cycles, closed nonzero rows, invertible J and T. The derivation checks rank, cofactor signs, denominators and the δ factor. | Applying the required source duality to the actual Selmer data remains OPEN. |
| Constructed objects | The formal input is explicit field-valued matrices, vectors, rows and finite indices. The ordinary bridge constructs B_F,B_S,T from D₀,A_F,A_S,h_F,h_S,v,x. | A compatible actual integral two-term model, or a determinant-functor replacement with checked conventions, must still be supplied. |
| Domain/index coverage | The formal result is uniform over finite index types with p≠q. The ordinary bridge covers each n≥2. Finite examples range over sizes 2–5 and do not prove uniform arithmetic claims. | Required inner instances, the completed 2-adic DVR and exceptional height-one localizations must be checked separately. |
| Transition/comparison maps | The explicit normal-form equations preserve both actual cycles. The common target determinant cancels only after retaining it on both sides. The adapter uses the correctly typed inverse of J. | Verify actual transfer, conjugation, orthogonal-comparison and boundary--cup maps, including cone/homotopy signs. |
| Consumed object identity | The tensor is the outer product of each supplied cycle and its supplied closed functional, characterized by the full adjugate. The distinct functionals are never identified by a determinant-line map alone. | Show that these are exactly the retained class-functional tensors consumed by the manuscript. |
| Coefficients/normalization | Algebraic identities hold over a field; the integral interpretation uses an R-unit δ. The unit criterion refers to an R-unit image. A common nonunit c may cancel. | Prove the same normalization for the actual functionals, with fixed clearing factors retained. |
| Local conditions | D₀ remains shared, and each quotient adds the appropriate two-dimensional local plane. No strict factor is deleted. | Retain D⁰ and actual orthogonal local conditions at every derivative prime; identify the quotient and target maps. |
| Exceptional cases | p≠q enforces at least two coordinates. det T, η, δ and q_S are nonzero where divided. The counterexample treats primitive classes/functionals; divisible vectors, fractional x and nonunit strict factors remain allowed. | No rank-reducing outer test is substituted for a rank-one inner instance. The actual permitted localizations must preserve the hypotheses. |
| Downstream consumption | This packet proves an algebraic implication and records the remaining premise. The manuscript's switch, uniform lower bound and regularity are consumers to be assessed only after arithmetic instantiation. | `ex:limits-derivative-switch`, `ex:limits-uniform-lower-bound`, (5.5a)/(5.5), and the restricted converse are not newly accepted here. |

## Source and history

The supplied review is pinned to `40d01c5`; its reviewed Lean/Python bytes match
the branch at intake `083344e`. The frozen manuscript SHA-256 is
`9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`.
The paired-functional construction is `ex:arith-paired-functional` (lines
3842 onward); the determinant switch is `ex:limits-derivative-switch` (lines
5020–5092), and the lower-bound consumer starts at line 5095. These are
locations of the relevant objects and claims, not arithmetic acceptance.
The non-author mathematical report records its source lookup and limits.

The impossible identity-on-strict triangle comparison was an auxiliary strategy
from the earlier review, not a triangle isomorphism asserted by the manuscript.
This extension computes the comparison from two separate sequences. Neither
the primitive negative control nor the normal-form theorem refutes the paper.

No manuscript, accepted helper, frozen `ZInQ` target, dependency pin, polynomial
artifact, old receipt or acceptance hash changes. PDF regeneration, release
archive synchronization and whole-manuscript acceptance therefore do not apply
to this bounded research addition. A later arithmetic integration must undergo
its own source/application and downstream review under the repository protocol.
