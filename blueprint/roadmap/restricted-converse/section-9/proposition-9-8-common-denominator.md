---
article_id: af_6a1db53b0369bc5f061f39b2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Wiring.clearingTarget_of_G3Q2, ZInQ.Manuscript.RC.Wiring.ClearingTarget, ZInQ.Manuscript.RC.Determinant.valuation_f0, ZInQ.Manuscript.RC.Determinant.f_pole
---

# Proposition 9.8: a common denominator for the corrected coordinate

Assume:

- height-one regularity, $\widetilde u_x\in\Lambda[1/2]$ at every address of every final family
  (`HeightOneTarget`), which the reduction of Theorem 5.3 proves from the field `PostLeaves.prim_regular`
  and the common coordinate [(4.7)](../section-8/equation-4-7-unused-prime-comparison.md) of [Lemma
  8.10](../section-8/lemma-8-10-common-coordinate.md);
- the field `PostLeaves.clearing_model` of [the remaining hypotheses](../remaining-hypotheses.md)
  (`ClearingInputsG3Q2`): a number field $K$ and constants fixed before the family, and at every final
  family an identification of the remaining complex with the full-condition triangle (5.6) (ELLIOT for
  the cancellation core: the lifted family model with the new local blocks, $B_0=\operatorname{diag}(A_q)$,
  $T_0=0$, the central Smith form and the counts of (5.7); GLUE for the Galois comparisons), the actual
  cycle, closed functional and correction $\eta$ over $\mathscr O[G]$ (data), and the coordinate
  identification `OrigCoordLink3` (ELLIOT): where $\Delta_x\ne0$, $\widetilde u_x$ is $\eta_x$ times the
  determinant coordinate of the cycle and functional in the complex before cancellation.

Then there are $c_{\det}$ and $d_K$ such that for every precision $M$ and every final family of
[(3.9)](../section-7/proposition-7-17-final-family.md) there are $f$ and $d$, given by their
group-basis Laurent coefficients, and $c\le c_{\det}$ with:

- the coefficients of $f$ tending to zero at $-\infty$, so that $f\in\mathscr O[G]$ (no such condition
  is asked of $d$);
- $f_x\widetilde u_x=d_x$ at every sign character $x$, as a convergent convolution of coefficients;
- $f_0\in\Lambda$, $f_0(0)\ne0$ and $v_2f_0(0)=c$;
- $2^M$ divides $[t^i]f_x$ for every $x$ and every $i<-L_T(M)$, where $L_T(M)=16(d_K+5)M$.

The last two clauses are the manuscript's two clearing bounds: with $f_0=2^a\Delta_0^4\in\Lambda$ the
augmentation of $f$,
$$c=v_2f_0(0)\le c_{\det}:=a+4(h_K+2c_E+2t_K),\qquad L_T(M)=16(d_K+5)M,\tag{5.9}$$
where the second means that, modulo $2^M$, no $f_x$ has Laurent terms below degree $-L_T(M)$, uniformly in
the sign character $x$. `ClearingTarget` states both bounds.

The manuscript fixes $f=2^a\Delta^4$ and $d=\eta\Delta Q$ once, with $c_{\det}=a+4(h_K+2c_E+2t_K)$, and bounds
their poles for every $M$; the Lean statement chooses the data for each $M$, leaves $c_{\det}$ existential
and omits the formula $\widetilde u_x=2^{-a}\eta_xQ_x/\Delta_x^3$. In the reduction the paired-functional
exponent is $a=0$. The field $K$ of the hypothesis is existential, and $d_K$, $h_K$, $c_E$ and $t_K$
are free numbers tied only by the counts of the identification; so $c_{\det}$ and $L_T(M)$ are not the
manuscript's constants built from $\dim_{\mathbb F_2}\mathrm{Sel}_2(E/K)$, the torsion lengths of $C_K$
and the constant of the moving character.

Lean proves the two bounds of (5.9) separately, for the central Smith data of the remaining old
complex: blocks $A_i$ whose augmentations over $\Lambda$ have constant terms the diagonal matrices of the
nonzero Smith entries, $\Delta=\prod_i\det A_i$ and $f=2^a\Delta^4$. `valuation_f0` gives $f_0(0)\ne0$, the
exact value $v_2f_0(0)=a+4h_1$, with $h_1$ the sum of the valuations of the Smith entries, and, from the
torsion count $h_1\le h_K+2c_E+2t_K$ of [(5.7)](equation-5-7-fixed-field-budget.md), the first bound.
`f_pole` gives the pole bound at one sign character, for any ring with pole data, from the disk count
$m\le d_K+5$ of (5.7) and the pole bound $4M$ modulo $2^M$ on the sign-evaluated entries of every block,
from [(5.8)](equation-5-8-inverse-blocks.md). The proof of this proposition uses both through
`fixed_field_clearing`, with $a=0$.

The reduction of Theorem 5.3 takes this statement from the theorem. The docstrings of
`ZInQKernel/Contrib/OneProof/RC/Wiring/Leaves.lean` list `clearing_model` among the conclusion-shaped
leaves, close to the proposition itself: its objects are existential witnesses that do not constrain
the actual ones, and the form `ClearingInputsCx` through which the deduction runs follows from a bare
common-denominator statement (`RC/Wiring/ClearingComplex3.lean`). They also record that
`OrigCoordLink3` is the definition of the corrected coordinate only for the actual complex, cycle,
functional, correction and retained basis, whose provenance the existential interface does not
supply, and that the two-place data and the Galois comparisons of the field carry no weight in the
deduction.

**Proof sketch.** From the identification the Lean proof derives the Smith model, the entry poles from
[(5.8)](equation-5-8-inverse-blocks.md) and the counts $m\le d_K+5$ and $h_1\le h_K+2c_E+2t_K$ of
[(5.7)](equation-5-7-fixed-field-budget.md). Cancelling the new local blocks and the Smith blocks
expresses $\widetilde u_x$ through $\Delta_x$ wherever $\Delta_x\ne0$; with $f=\Delta^4$ and $d=\eta\Delta Q$
the identity $f_x\widetilde u_x=d_x$ then holds at every character, also where $\Delta_x=0$. For (5.9): the
constant term of $\Delta_0$ is the product of the Smith entries, so $v_2f_0(0)=a+4h_1$; and $f$ is a
polynomial of degree $4m$ in the entries of the blocks, each of pole at most $4M$ modulo $2^M$ at a sign
character, so a product of $4m$ of them has pole at most $16mM$, and $m\le d_K+5$.

## Depends on

- [The remaining hypotheses](../remaining-hypotheses.md)
- [Proposition 7.17: one family for the two coefficient tests (3.9)](../section-7/proposition-7-17-final-family.md)

## Proof depends on

- [(5.7): the fixed-field budget](equation-5-7-fixed-field-budget.md)
- [(5.8): the inverse new local blocks](equation-5-8-inverse-blocks.md)

## Sources

- [Section 9](../../../sources/manuscript.md#section-9)
