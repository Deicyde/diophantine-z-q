---
article_id: af_b8d81f819529166f35f5a6cb
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.translate, ZInQ.Syntax.translate_variableCount
---

# Translation of a natural circuit into a model-evaluation recipe

**Natural circuits.** A natural circuit has $k$ inputs, a list of explicit variables
$(i_0,\kappa_0),(i_1,\kappa_1),\dots$ (variable index and kind, the inputs first with indices
$0,\dots,k-1$), a node list whose nodes are $\mathrm{const}\ c$, $\mathrm{var}\ i$,
$\mathrm{add}\ j\ j'$, $\mathrm{mul}\ j\ j'$ or $\mathrm{call}\ (a,b,c)\ w$ (a call of the power
template on three earlier nodes with a private block of $79$ variables at $w$), and a root
node. The power template is itself a natural circuit with $3$ inputs, $79$ witnesses, no
calls, and explicit variables $0,\dots,81$.

**Translation.** Fix the operation templates $\nu=\mathtt{natural}$, $\alpha=\mathtt{raw\_add}$,
$\mu=\mathtt{multiply}$ with witness counts $140604$, $6$, $35134$. The translation of a
natural circuit with $k$ inputs, in mode $\mathrm{value}$ or $\mathrm{zero}$, with or without
natural constraints on the inputs, and with an optional power recipe $\pi$, is the
model-evaluation recipe with $p=5(k+[\mathrm{value}])$ parameters built by one allocation
counter starting at $p$:

1. the generator indices $g_0,g_1,g_2$ take the next three variables;
2. for each explicit variable in list order: an input $i$ gets the point reference $5i$
   (inside the parameters), any other variable gets a fresh point (five variables); then,
   unless it is an input and inputs are unconstrained, a natural block of $140604$ variables
   is taken; the row records the reference and the natural start (or none);
3. each node $j$ in order gets a point reference $\mathrm{pt}(j)$: $\mathrm{var}\ i$ the reference of $i$;
   $\mathrm{const}\ 0$, $1$, $-1$ the references $-1$, $-2$, $-3$; any other constant $c$ (the
   translation is defined only when every such constant is an integer $c\ge2$, which holds
   for both circuits translated here), at its first occurrence in this circuit, a fresh point followed by a block of $1$, recording
   the constant definition $(S_{\mathrm{integer\_constant}_h},\text{point},\text{start})$ where
   $\mathrm{integer\_constant}_h=c$ (a new index $h$ is created when $c$ has not occurred in
   any earlier translation), and later occurrences reuse that point; $\mathrm{add}\ j_1\ j_2$ and
   $\mathrm{mul}\ j_1\ j_2$ nodes a fresh point followed by a block of $6$ or $35134$, recording the
   operation $(0\text{ or }1,\ \mathrm{pt}(j_1),\ \mathrm{pt}(j_2),\ \text{point},\ \text{start})$; a
   $\mathrm{call}\ (a,b,c)\ w$ a fresh point followed by a block of the witness count of $\pi$,
   recording $(2,\mathrm{pt}(a),\mathrm{pt}(b),\mathrm{pt}(c),\text{point},\text{start})$; the
   source block at $w$ is not used;
4. the root equality is $(\mathrm{pt}(\mathrm{root}),5k)$ in value mode and
   $(\mathrm{pt}(\mathrm{root}),-1)$ in zero mode;
5. the variable count is the final counter.

The polynomial of the result is given by the semantics of model-evaluation recipes: the
three generator constraints, the natural calls, the constant definitions (each a
fixed-scalar template on $(\mathrm{ref}(-2),\text{point})$), the operation calls and the five
root differences, squared and summed.

Equivalently, the translation takes the table of nontrivial constants as an argument, listed
in order of first occurrence across the translations: $(4,2,3)$ for power_value and
$(4,2,3,c_3,1399)$ for precision, a constant $c$ using the fixed-scalar template of its
position in the table.

This is a definition. The arithmetic meaning (every node point is the code of the node's
signed integer value) is the compiler chapter's rational translation statement.

## Depends on

- [Semantics of templates and recipes](../template-semantics.md)
- [Point references](../language/point-references.md)
- [The fixed-scalar templates](../templates/template-fixed-scalar.md)
- [The natural-code template](../templates/template-natural.md)
- [The raw addition template](../template-raw-add.md)
- [The multiplication template](../templates/template-multiply.md)

## Sources

- [Section 10.4](../../../sources/syntax-locators.md#section-10-translation)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Saved specification](../../../sources/syntax-locators.md#saved-specification)
