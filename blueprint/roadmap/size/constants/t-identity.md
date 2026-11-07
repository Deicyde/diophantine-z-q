---
article_id: af_042cffb72f4407aa6f13963f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.t_identity
---

# The closed form of $T$

Assume the catalogue bound. Then:

1. $Q=R^{RE_0}=D^{10G_0^2D^3}$;
2. $C_{\rm cm}<2^{50000D^2}<Q^{17}$, so $\max(1,C_{\rm cm},Q^{17})=Q^{17}$;
3. $A_{\rm ht}=2\cdot10^{13}\,D^{170G_0^2D^3}$ and
$$T=(48A_{\rm ht})^{13}=(96\cdot10^{13})^{13}\,D^{2210G_0^2D^3}.$$

**Proof sketch.** By $R=D$ and $E_0=10D^2G_0^2$, $RE_0=10G_0^2D^3$, which is (1). For (2):
$D^2<2^{D^2}$ and $3^{21000D^2}<4^{21000D^2}=2^{42000D^2}$ give $B_{\rm cm}\le2^{42001D^2}$, and
$4096(1028+5D+84000D^2)\le4096\cdot85033\,D^2<2^{29}D^2<2^{42001D^2}$ (using $1\le D\le D^2$), so
$C_{\rm cm}<3\cdot2^{42001D^2}<2^{50000D^2}$. On the other side $D\ge2$ gives
$Q^{17}=D^{170G_0^2D^3}\ge2^{170G_0^2D^3}$, and $170G_0^2D^3>50000D^2$ because $170G_0^2D>50000$
(already $D>300$). Also $Q^{17}\ge1$. For (3), $A_{\rm ht}=2\cdot10^{13}Q^{17}$, so
$48A_{\rm ht}=96\cdot10^{13}Q^{17}$ and $T=(96\cdot10^{13})^{13}Q^{221}$ with
$Q^{221}=D^{221\cdot10G_0^2D^3}=D^{2210G_0^2D^3}$.

The manuscript compares $\log_2Q_D^{17}=170G_0^2D^3\log_2D$ with $50000D^2$; the proof here
uses only $\log_2D\ge1$.

## Depends on

- [The prescribed fixed constants](../../syntax/constants/fixed-constants.md)
- [The catalogue bound](../../main/catalogue-bound.md)

## Proof depends on

- [Closed numerical comparisons](closed-comparisons.md)
- [The parameter $R$ equals $D$](r-equals-d.md)
- [Bounds for $D$](d-bounds.md)

## Sources

- [Proof of Proposition 12.1, cutoff](../../../sources/size-locators.md#proof-of-proposition-121-cutoff)
- [Section 12 opening](../../../sources/size-locators.md#section-12-opening)
- [Section 4 constants](../../../sources/size-locators.md#section-4-constants)
