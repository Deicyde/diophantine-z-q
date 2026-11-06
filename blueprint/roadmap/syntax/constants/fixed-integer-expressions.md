---
article_id: af_b9719f8201f695d81422c28b
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.FixedExpr, ZInQ.Syntax.FixedExpr.val
---

# Fixed integer expressions

A fixed integer expression is built from

- integer literals;
- references to earlier named fixed constants;
- $\mathrm{add}(e_1,e_2)$, $\mathrm{mul}(e_1,e_2)$, $\mathrm{pow}(e_1,e_2)$;
- $\max(e_1,\dots,e_k)$ with $k\ge1$;
- $\mathrm{factorial}(e)$;
- $\mathrm{catalogue\_product}(e_W,e_k,e_B)$ and $\mathrm{catalogue\_max}(e_W,e_k,e_B)$;
- $\mathrm{least\_formal\_multiple}(e_N)$.

Its value $\mathrm{val}(e)\in\mathbb Z$ is defined recursively: literals are themselves, a
reference is the value of the named constant, $\mathrm{add}$ and $\mathrm{mul}$ are $+$ and
$\times$, $\mathrm{pow}(e_1,e_2)=\mathrm{val}(e_1)^{\mathrm{val}(e_2)}$ (the specification uses only
nonnegative exponents; to make the definition total a negative exponent is replaced by
$0$, so the power is then $1$), $\max$ is the maximum,
$\mathrm{factorial}(e)=\mathrm{val}(e)!$ (with $n!=1$ for $n\le0$), the catalogue operators
are the catalogue product and maximum of the prime catalogue with modulus
$\mathrm{val}(e_W)$, count $\mathrm{val}(e_k)$ and floor $\mathrm{val}(e_B)$, and
$\mathrm{least\_formal\_multiple}(e_N)$ is the least formal multiple of
$\mathrm{val}(e_N)$. Negative arguments of the last three operators do not occur; they are
read through the natural-number truncation.

These expressions produce constants, not quantified witnesses, and none of the
astronomical ones is ever evaluated: every later statement about them is proved
symbolically from these defining equations.

This is a definition.

## Depends on

- [The prime catalogue](prime-catalogue.md)
- [The least formal multiple](least-formal-multiple.md)

## Sources

- [Appendix C.1](../../../sources/syntax-locators.md#appendix-c1-scalar-nodes)
- [Section 2.2](../../../sources/syntax-locators.md#section-22-catalogue-and-formal-multiple)
