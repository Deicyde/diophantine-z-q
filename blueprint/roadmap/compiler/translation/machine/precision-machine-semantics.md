---
article_id: af_0d182f0bee3b5fdaeaf60c2a
declaration: theorem
origin: cited
---

# The universal interpreter at the program literal

For every $x\in\mathbb N$,
$$U\text{ accepts }(c_3,x)\iff\mathrm{accepts\_naturals}(\operatorname{decode}_5(x)),$$
and in particular, for every $\mathbf c\in\mathbb N^5$,
$$U\text{ accepts }\bigl(c_3,\operatorname{encode}_5(\mathbf c)\bigr)\iff\mathrm{accepts\_naturals}(\mathbf c).$$
This is the machine half of equation (C.4); it uses no height, restricted-converse or
rational-model premise, and the height expression enters only through the exact computation
of the fixed integer $A^{(0)}_{\rm ht}$ capped at the precision available.

**Proof sketch.** Chain the equivalences: $U$ accepts $(c_3,x)$ iff the decoded program of
$c_3=\operatorname{code}(W(\Pi_{\rm prec}))$ halts on $x$ (interpreter correctness) iff $W(\Pi_{\rm prec})$
halts on $x$ (decoding a program code) iff $\Pi_{\rm prec}$ halts on $\operatorname{decode}_5(x)$ (wrapper
correctness; $\Pi_{\rm prec}$ is in final-halt form) iff $\mathcal R$ accepts $\operatorname{decode}_5(x)$
(lowering correctness) iff $\mathrm{accepts\_naturals}(\operatorname{decode}_5(x))$ (correctness of the
precision program). For $x=\operatorname{encode}_5(\mathbf c)$ use $\operatorname{decode}_5(\operatorname{encode}_5(\mathbf c))=\mathbf c$.

## Depends on

- [The universal interpreter](universal-interpreter.md)
- [The wrapper and the program literal](wrapper.md)
- [The precision predicate](precision-predicate.md)
- [Cantor pairing and unpairing](cantor-unpairing.md)

## Proof depends on

- [Correctness of the universal interpreter](interpreter-correctness.md)
- [Decoding a program code](program-numbering-decode.md)
- [Correctness of the wrapper](wrapper-correctness.md)
- [The lowered machine halts exactly on acceptance](lowering-correctness.md)
- [The precision program computes the precision predicate](ir-correctness.md)

## Sources

- [Section 10.3 specialization](../../../../sources/compiler-translation-locators.md#section-103-specialization)
- [Section 10.3 interpreter](../../../../sources/compiler-translation-locators.md#section-103-interpreter)
- [Section 10.3 lowering](../../../../sources/compiler-translation-locators.md#section-103-lowering)
