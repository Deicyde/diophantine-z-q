---
article_id: af_2d303128db416726670b75a8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Assembly.signedEncode_rel_iff
---

# Semantics of the signed encoding

Assume the six-contact estimate, pole completeness and the twenty-two-prime
pattern. Then for all $N,C\in\mathbb Q^5$,
$$\mathrm{Rel}_{\mathtt{value.signed\_encode}}(N,C)\iff\exists\,m\in\mathbb Z:\ N=\iota(m)\ \text{and}\ C=\iota(\operatorname{enc}(m)),$$
equivalently, $C=\iota(c)$ for some $c\in\mathbb N$ and $N=\iota(\operatorname{dec}(c))$.

**Proof sketch.** The template polynomial is the sum of the squares of the three generator
equations and of $\kappa(\varphi)$. By the rational-constant lemma the generator equations force
$(c_1,c_2,c_3)=(1641/8,-15465/4,87483/32)$, so $G=(0,c_1,-145,c_2,c_3)=\iota(1)$; they are
outside the internal disjunction and constrain both branches. By the private-witness
lemma, $\mathrm{Rel}(N,C)$ holds exactly when there are points $Q,Q_2,Q_+$ with
$\mathrm{Rel}_{\mathtt{member}}(N)$, $\mathrm{Rel}_{\mathtt{member}}(C)$, $\mathrm{Rel}_{\mathtt{natural}}(Q)$,
$\mathrm{Rel}_{\mathtt{raw\_add}}(Q,Q,Q_2)$ and one of the branches (i) $N=Q$, $C=Q_2$, or (ii)
$\mathrm{Rel}_{\mathtt{raw\_add}}(Q,G,Q_+)$, $N=\operatorname{neg}(Q_+)$, $\mathrm{Rel}_{\mathtt{raw\_add}}(Q_2,G,C)$.

($\Rightarrow$) The natural-code predicate, with M from the multiplication template, gives
$Q=\iota(q)$ with $q\in\mathbb N$, and raw addition on canonical codes gives $Q_2=\iota(2q)$.
In branch (i), $N=\iota(q)$ and $C=\iota(2q)=\iota(\operatorname{enc}q)$. In branch (ii),
$Q_+=\iota(q+1)$, $N=\operatorname{neg}(\iota(q+1))=\iota(-(q+1))$ and $C=\iota(2q+1)$; since
$-(q+1)<0$, $\operatorname{enc}(-(q+1))=2q+1$.

($\Leftarrow$) For $m\ge0$ take $Q=\iota(m)$, $Q_2=\iota(2m)$ and branch (i). For $m<0$ take
$Q=\iota(-m-1)$, $Q_2=\iota(-2m-2)$, $Q_+=\iota(-m)$ and branch (ii); then
$\operatorname{neg}(Q_+)=\iota(m)$ and the last raw addition gives $\iota(-2m-1)=\iota(\operatorname{enc}m)$. The
membership, natural and raw-addition relations hold by the accepted-indices statement,
the natural-code predicate (with M from the multiplication template) and raw addition; an
inactive branch takes arbitrary witnesses.

## Depends on

- [The signed-encoding template](../../syntax/templates/template-signed-encode.md)
- [Point codes](../../model/point-codes.md)
- [The signed encoding of integers](../../compiler/natural/precision/signed-encoding.md)
- [The six-contact height estimate](../../main/six-contact-estimate.md)
- [Pole completeness](../../main/pole-completeness.md)
- [The twenty-two-prime pattern](../../main/prime-pattern.md)

## Proof depends on

- [The natural-code predicate](../../compiler/translation/natural-code-semantics.md)
- [Correctness of the multiplication template](../../multiplication/multiplication-template.md)
- [Accepted inputs have unique indices](../../model/membership-indices.md)
- [Raw addition](../../model/raw-addition.md)
- [Elementary properties of codes](../../model/field/point-code-properties.md)
- [Rational constants by global equations](../../syntax/language/rational-constants.md)
- [Private witness blocks](../../syntax/language/existential-lifting.md)
- [Template construction from formulas](../../syntax/language/builder-soundness.md)
- [Witness scope of constructed templates and recipes](../../syntax/language/builder-well-formed.md)
- [Mordell-Weil for $E/K_0$ from the descent](../../model/descent/mordell-weil-from-descent.md)

## Sources

- [Section 10 precision predicate](../../../sources/assembly-locators.md#section-10-precision-predicate)
- [Section 10.4 translation](../../../sources/assembly-locators.md#section-104-translation)
- [Section 11.1 approximation](../../../sources/assembly-locators.md#section-111-approximation)
