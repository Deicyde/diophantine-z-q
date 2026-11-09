---
article_id: af_a3af10ea27c967ba0a032879
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Mult.multiplication_exact, ZInQ.Mult.multiplication_exact_unique, ZInQ.Mult.multiplication_existsUnique
---

# Correctness of the multiplication template

Assume the minimal height hypothesis, pole completeness and the slope representation.
For all $Y_1,Y_2,Y_3\in\mathbb Q^5$,
$$\mathrm{Rel}_{\mathtt{multiply}}(Y_1,Y_2,Y_3)\iff\exists\,a,b\in\mathbb Z:\quad
(Y_1,Y_2,Y_3)=\bigl(\iota(a),\iota(b),\iota(ab)\bigr),$$
where $\mathrm{Rel}_{\mathtt{multiply}}(Y_1,Y_2,Y_3)$ means that the polynomial of the
multiplication template, which has $15$ parameters and $35{,}134$ witnesses, vanishes at
$(Y_1,Y_2,Y_3)$ and some $w\in\mathbb Q^{35134}$. The inputs are arbitrary rational
$5$-tuples, not assumed to be codes; when the relation holds, $a$ and $b$ are unique.

This is input M of the assembly lemma. The two directions use different hypotheses:

- **soundness** ($\Rightarrow$) uses the six-contact estimate H in its minimal form (through the
  finite-box deduction) and the generator certificate, but not pole completeness
  and not the slope representation;
- **completeness** ($\Leftarrow$) uses pole completeness PC and the slope representation, which
  the prime pattern 22P gives (to build the slope certificates of a true triple), and the
  generator certificate (through the fixed-scalar and guard semantics), but not the
  six-contact estimate.

Neither direction uses the catalogue bound. The Mordell–Weil input of the generator
certificate is proved by the two-isogeny descent, so it is not a hypothesis. No constant of the template ($c_*$, $\ell_0$,
$T$) is evaluated. The template's three parameter points, written $P_0,P_1,P_2$ in the
specification, are written $Y_1,Y_2,Y_3$ in this chapter, since $P_0$ denotes the generator.

**Proof sketch.** Combine soundness of the multiplication template with completeness of the
multiplication template. Uniqueness of $a,b$ is injectivity of $\iota$ (the generator
certificate).

## Depends on

- [The multiplication template](../syntax/templates/template-multiply.md)
- [Point codes](../model/point-codes.md)
- [Semantics of templates and recipes](../syntax/template-semantics.md)
- [The minimal height hypothesis](../main/six-contact-min.md)
- [Pole completeness](../main/pole-completeness.md)
- [The slope representation](completeness/slope-representation.md)

## Proof depends on

- [Soundness of the multiplication template](soundness/soundness.md)
- [Completeness of the multiplication template](completeness/completeness.md)
- [The generator certificate](../model/generator.md)
- [Mordell-Weil for $E/K_0$ from the descent](../model/descent/mordell-weil-from-descent.md)

## Sources

- [Multiplication input M](../../sources/multiplication-locators.md#multiplication-input-m)
- [Section 6 opening](../../sources/multiplication-locators.md#section-6-opening)
- [Conclusion of the multiplication proof](../../sources/multiplication-locators.md#conclusion-of-the-multiplication-proof)
