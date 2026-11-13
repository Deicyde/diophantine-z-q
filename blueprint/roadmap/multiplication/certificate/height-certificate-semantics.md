---
article_id: af_7fccb8cca72f8e3e30cb16ec
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.heightCertificate_rel_iff, ZInQ.Mult.HeightCert
---

# Semantics of the height certificate template

For all $Y_1,Y_2,Y_3\in\mathbb Q^5$,
$\ell\in\mathbb Q$ and $c\in\mathbb Z^4$, the relation
$\mathrm{Rel}_{\mathtt{height\_certificate}}(Y_1,Y_2,Y_3,\ell,\iota(c_0),\iota(c_1),\iota(c_2),\iota(c_3))$
holds if and only if:

1. there are $n_1,n_2,n_3\in\mathbb Z$ with $Y_i=\iota(n_i)$; write
   $x([n_i]P_0)=x_{i0}+x_{i1}s$ with $x_{i0},x_{i1}\in\mathbb Q$, where $x_{i0}=x_{i1}=0$ if
   $n_i=0$ (these are the coordinates $(Y_i)_1,(Y_i)_2$);
2. there are $a_{i0},a_{i1},b_i\in\mathbb Q$ ($i=1,2,3$) with $b_i\ne0$ and
   $b_ix_{ij}=a_{ij}$;
3. for each of the nine quantities
   $(Q_1,\dots,Q_9)=(a_{10},a_{11},b_1,a_{20},a_{21},b_2,a_{30},a_{31},b_3)$ there are
   rationals $t_{k,1},t_{k,2},t_{k,3}$ with $t_{k,1}+t_{k,2}+t_{k,3}=Q_k$ and
   $\mathrm{Slope}(t_{k,l},\ell;c)$ for $l=1,2,3$.

Thus the certificate first forces all three inputs to be members of $2E(K_0)$: membership
is a conjunct inside the certificate, not a precondition, so even untyped rational inputs,
if accepted, have unique indices.

**Proof sketch.** Unfold the conjunction of the $35{,}106$-witness template. The three
membership calls give $Y_i=\iota(n_i)$ by membership and the generator certificate. The atoms
$b_iu_i\doteq1$, $b_i(Y_i)_1\doteq a_{i0}$, $b_i(Y_i)_2\doteq a_{i1}$ are item 2. Each of the nine
sum atoms and twenty-seven slope calls gives item 3 through the slope semantics, the four
shift points being the canonical codes $\iota(c_k)$. The converse chooses the same witnesses.

## Depends on

- [The height certificate template](../../syntax/templates/template-height-certificate.md)
- [The slope predicate](slope-predicate.md)
- [Point codes](../../model/point-codes.md)

## Proof depends on

- [Accepted inputs have unique indices](../../model/membership-indices.md)
- [Semantics of the slope template](slope-semantics.md)
- [Inverse witnesses](../../syntax/nonzero-gadgets.md)
- [Sums of squares and products over the rationals](../../syntax/sum-of-squares-semantics.md)
- [Evaluation of a template call](../../syntax/language/call-semantics.md)
- [Private witness blocks](../../syntax/language/existential-lifting.md)
- [Mordell-Weil for $E/K_0$ from the descent](../../model/descent/mordell-weil-from-descent.md)

## Sources

- [Height certificate](../../../sources/multiplication-locators.md#height-certificate)
- [Section 6 opening](../../../sources/multiplication-locators.md#section-6-opening)
