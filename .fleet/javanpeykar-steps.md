# javanpeykar-steps (2026-11-17)

**Result.** `javanpeykarPrintedMapHF` (GLUE, kind consequence) is now a direct instance of Javanpeykar's
Thm 1.1.1 as printed: `JavanpeykarSteps.javanpeykarPrintedMap_of_thm111 : JavanpeykarThm111 →
JavanpeykarRebase.JavanpeykarPrintedMap`, with no other hypothesis
(`ZInQKernel/Contrib/OneProof/JavanpeykarThm111.lean`, standard axioms).

**The new leaf `JavanpeykarThm111`** is Thm 1.1.1 (ANT 8 (2014) p. 90, arXiv v1 p. 1) together with
p. 9's identification of h_Fal(X) as the stable Faltings height of Jac(X). It quantifies over any
algebraic closure Qbar of Q, any smooth proper integral projective curve over Qbar of genus >= 1, and
any tensor-compatible Pic^0 representative W. It takes the height of a model of W over a number field
(height-fix's printed height) and deg_B as the least degree of a Belyi morphism, where "unramified"
over P^1 minus {0,1,oo} means Mathlib's FormallyUnramified plus LocallyOfFiniteType.
Rated printed form; two dictionary points, the height over Qbar and the degree over the stalk at
beta(eta), are listed for the statement check.

**Steps proved in Lean.**
* (1) X0 x_K Kbar is an instance.
* (2) deg_B <= d, and the bound is monotone in d.
* (3) Ramification index 1 at closed points implies unramified (stalkwise; quasi-finite residue
  extensions, separable in characteristic 0).
* (H2) The printed height is invariant under isomorphism (`isPrintedStableHeight_of_iso`).
* (H3) The printed height has one value (`isPrintedStableHeight_unique`, from T35, Stacks 04KV, N1
  and SS2; checked against height-fix's `isStableFaltingsHeight_of_printed`).

**What compiles.**
* The Contrib file.
* The `#discharges` check: DISCHARGES javanpeykarPrintedMapHF, still assumes only JavanpeykarThm111.
* The autofold dry run of scratch/javanpeykar-steps/autofold.json: GLUE 16 -> 15 (strict and
  strictest); the generated TailZ module compiles with standard axioms.

**Remains.**
* A statement check of the leaf against the print. If Addendum 1 applies, the leaf counts as GLUE
  until reviewed.
* Not attempted: W unique up to isomorphism of abelian varieties, and independence of the Qbar-height
  across number fields (needs descent of isomorphisms, not in Mathlib).

Report: docs/research/javanpeykar-steps.md.
