---
article_id: af_2124904da9c211bdaff0b2b9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Syntax.Formula.exists_blocks_iff
---

# Private witness blocks

Let $\varphi$ be a formula whose atoms of the form $\langle\cdot\rangle$ are calls
$\langle\tau_i[g_i;w_i]\rangle$, $i=1,\dots,k$, where $\tau_i$ has $p_i$ parameters, $v_i$
variables, $m_i=v_i-p_i$ witnesses and all its variables below $v_i$. Put
$B_i=\{w_i,\dots,w_i+m_i-1\}$ and assume:

- the blocks $B_1,\dots,B_k$ are pairwise disjoint;
- no variable of any $B_i$ occurs in any parameter polynomial $g_j$ or in any atom
  $a\doteq b$ of $\varphi$.

Let $\varphi^\ast(x)$ be the statement obtained from $\varphi$ by replacing each call atom by
$\mathrm{Rel}_{\tau_i}(g_i(x))$ and each atom $a\doteq b$ by $a(x)=b(x)$. Then for every
$x:\mathbb N\to\mathbb Q$,
$$\bigl(\exists\,y:\textstyle\bigcup_iB_i\to\mathbb Q,\ \ \kappa(\varphi)(x[y])=0\bigr)\iff\varphi^\ast(x),$$
where $x[y]$ agrees with $y$ on $\bigcup_iB_i$ and with $x$ elsewhere; both sides depend only
on $x$ outside the blocks. In particular a conjunction of calls with disjoint blocks has a
rational zero exactly when every callee relation holds, a product of calls has one exactly
when some callee relation holds, and the block of an inactive factor may be given
arbitrary values (for instance all zero). Variables occurring in no atom and no block may
likewise take arbitrary values.

**Proof sketch.** By the compilation theorem the left side says that $\varphi$ holds at
$x[y]$ for some $y$. Induct on $\varphi$, proving the statement for every $x$. For an atom
$a\doteq b$ the value does not depend on $y$. For a call atom this is the evaluation of a
call. For a conjunction $\bigwedge\varphi_j$ the blocks used by different conjuncts are
disjoint, so witnesses $y_j$ for the conjuncts glue to one $y$ that restricts to each $y_j$
on its own blocks; conversely a common $y$ restricts to witnesses for each conjunct. For a
disjunction, a witness for the true disjunct extends by arbitrary values (the rational
domain is nonempty) to the blocks of the other disjuncts. Fixed equations inside an active
callee are part of that callee's relation and are not discarded.

## Depends on

- [Formulas and their polynomial compilation](formula-compilation.md)
- [Semantics of templates and recipes](../template-semantics.md)

## Proof depends on

- [Sums of squares and products over the rationals](../sum-of-squares-semantics.md)
- [Evaluation of a template call](call-semantics.md)

## Sources

- [Section 2.1](../../../sources/syntax-locators.md#section-21-literal-operations)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
