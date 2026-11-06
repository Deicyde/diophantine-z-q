---
article_id: af_a619b79cc067a2bfa738d415
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.pointCode_injective, ZInQ.iota_add
---

# Elementary properties of codes

1. The map $\operatorname{code}:E(K_0)\to\mathbb Q^5$ is injective. The first coordinate of
   a code is $1$ exactly for $O$ and $0$ for every affine point.
2. For every point $Q$, $\operatorname{code}(-Q)$ is $\operatorname{code}(Q)$ with its last
   two coordinates negated. In particular $\iota(0)=(1,0,0,0,0)$ and, for every
   $n\in\mathbb Z$, $\iota(-n)$ is $\iota(n)$ with its last two coordinates negated.
3. $\iota(1)=\bigl(0,\tfrac{1641}{8},-145,-\tfrac{15465}{4},\tfrac{87483}{32}\bigr)$.
4. For all $a,b\in\mathbb Z$, $\iota(a)$ and $\iota(b)$ are codes of the points $[a]P_0$ and
   $[b]P_0$, whose sum $[a+b]P_0$ has code $\iota(a+b)$.

**Proof sketch.** (1) The components of an element of $K_0$ determine it, so the code
determines $x$ and $y$; the first coordinate separates $O$ from affine points. (2)
$-(x,y)=(x,-y)$ and $-O=O$. (3) Read off the coordinates of $P_0$: $1160/8=145$ and
$123720/32=15465/4$. (4) $[a]P_0+[b]P_0=[a+b]P_0$ in the group $E(K_0)$.

## Depends on

- [Point codes](../point-codes.md)

## Sources

- [Model setup](../../../sources/model-locators.md#model-setup)
- [Point references and fixed point codes](../../../sources/model-locators.md#point-references-and-fixed-point-codes)
