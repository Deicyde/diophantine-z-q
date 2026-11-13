---
article_id: af_09427e5086bb6b0b3b1c600d
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.JHeight.cert_x, ZInQ.JHeight.cert_y, ZInQ.JHeight.C0, ZInQ.JHeight.dvd_C0
---

# The cancellation in $J(u)$ is bounded

Let $F_h$ and $G_h$ be the binary forms of the Hauptmodul value. For all integers $a,b$,
$$3a^7=(-200a-4800b)F_h(a,b)+(29a^5+3700a^4b+164400a^3b^2+2880000a^2b^3+17280000ab^4)\,G_h(a,b),$$
$$104976000000\,b^7=(-1001a-37650b)F_h(a,b)+(143a^5+20557a^4b+1026600a^3b^2+20691900a^2b^3+133110000ab^4+29160000b^5)\,G_h(a,b),$$
where $104976000000=2^{10}3^85^6$. Put
$$C_0=(57600\cdot3^7)(57600\cdot104976000000^7)=57600^2\cdot3^7\cdot(2^{10}3^85^6)^7.$$
If $a,b$ are coprime integers and an integer $c$ divides both $57600F_h(a,b)^2$ and
$G_h(a,b)^6$, then $c\mid C_0$.

**Proof sketch.** The two identities are polynomial identities, checked by expanding. For all
integers $x,y$,
$$57600(x+y)^7=57600x^2\,(x^5+7x^4y+21x^3y^2+35x^2y^3+35xy^4+21y^5)+y^6\cdot57600(7x+y).$$
With $x=AF_h(a,b)$ and $y=BG_h(a,b)$, the first term is a multiple of $57600F_h(a,b)^2$ and the
second a multiple of $G_h(a,b)^6$, so $c$ divides $57600(AF_h(a,b)+BG_h(a,b))^7$ for all integers
$A,B$. Raising the two identities to the seventh power gives
$c\mid57600\cdot3^7a^{49}$ and $c\mid57600\cdot104976000000^7b^{49}$. Since $a,b$ are coprime, so
are $a^{49},b^{49}$, and there are integers $s,t$ with $sa^{49}+tb^{49}=1$. Then
$$C_0=(57600\cdot104976000000^7s)(57600\cdot3^7a^{49})+(57600\cdot3^7t)(57600\cdot104976000000^7b^{49}),$$
a combination of two multiples of $c$, so $c\mid C_0$.

## Depends on

- [The Hauptmodul value $J(u)$](hauptmodul-value.md)

## Sources

- [Step F4](../../../sources/height-locators.md#step-f4)
