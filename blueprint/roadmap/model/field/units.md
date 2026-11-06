---
article_id: af_edfe8c6e5dd37a3a609f8e6f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Zs_unit_sqClass, ZInQ.isSquare_of_totallyPositive_unit
---

# Units of $\mathbb Z[\sqrt2]$

1. $\mathbb Z[s]^\times=\{\pm\epsilon^k:k\in\mathbb Z\}$ with $\epsilon=1+s$, and
   $\epsilon^{-1}=s-1$, $\operatorname N(\epsilon)=-1$.
2. The unit squareclasses $\mathbb Z[s]^\times/(\mathbb Z[s]^\times)^2$ are exactly the four
   classes of $1,-1,\epsilon,-\epsilon$, whose sign vectors are $(+,+)$, $(-,-)$, $(+,-)$ and
   $(-,+)$ respectively.
3. Every totally positive unit is the square of a unit.

**Proof sketch.** (1) $(1+s)(s-1)=1$. If $u$ is a unit, replace it by $\pm u$ so that
$\sigma_+(u)>0$, and choose $k$ with $1\le\sigma_+(u\epsilon^{-k})<1+\sqrt2$. A unit
$w=a+bs$ with $1\le\sigma_+(w)<1+\sqrt2$ has $|\sigma_-(w)|=1/\sigma_+(w)\le1$, so
$2a=\sigma_+(w)+\sigma_-(w)\in[0,2+\sqrt2)$ and $2b\sqrt2=\sigma_+(w)-\sigma_-(w)\in[0,2+\sqrt2)$.
Hence $a,b\in\{0,1\}$; of $0,1,s,1+s$ only $1$ and $1+s$ are units, and
$\sigma_+(1+s)=1+\sqrt2$ is excluded, so $w=1$ and $u=\pm\epsilon^k$. (2) By (1) the quotient is generated
by $-1$ and $\epsilon$; $\sigma_+(\epsilon)=1+\sqrt2>0>1-\sqrt2=\sigma_-(\epsilon)$, so the four
sign vectors differ, and squares of units are totally positive, so the four classes are
distinct. (3) A totally positive unit has sign vector $(+,+)$, so lies in the class of $1$.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](quadratic-field.md)

## Proof depends on

- [Explicit identities in $K_0$](explicit-identities.md)

## Sources

- [Class number and units](../../../sources/model-locators.md#class-number-and-units)
