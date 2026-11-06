---
article_id: af_1961627191bb71869253bfda
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Precision.dec_enc, ZInQ.Compiler.Precision.enc_dec, ZInQ.Compiler.Precision.encEquiv
---

# The signed encoding is a bijection

$\operatorname{dec}(\operatorname{enc}(n))=n$ for every $n\in\mathbb Z$ and
$\operatorname{enc}(\operatorname{dec}(c))=c$ for every $c\in\mathbb N$. Moreover
$\operatorname{enc}(n)$ is even exactly when $n\ge0$, and
$|\operatorname{dec}(c)|=\lceil c/2\rceil$.

**Proof sketch.** Case analysis on the sign of $n$ and the parity of $c$: $2n$ is even with
half $n$; $-2n-1$ is odd for $n<0$ and $-((-2n-1)+1)/2=n$; conversely $c=2h$ decodes to
$h\ge0$ and $c=2h+1$ to $-(h+1)<0$, which encodes to $2h+1$.

## Depends on

- [The signed encoding of integers](signed-encoding.md)

## Sources

- [Section 10 signed encoding](../../../../sources/compiler-natural-locators.md#section-10-signed-encoding)
