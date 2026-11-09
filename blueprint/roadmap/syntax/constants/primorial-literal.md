---
article_id: af_e439aad5665fe7a483ab4ef0
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Syntax.primorial_324_eq, ZInQ.Syntax.four_mul_primorial_324_eq
---

# Decimal values of the primorial constants

There are exactly $66$ primes $p\le324$, and
$$P_s=\prod_{p\le324}p=19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570,$$
$$W=4P_s=77445546562803292653885700217249280330651590450286255047627849656860049479426548716387789340974722678430125902516592961137599906280 .$$
These are the two decimal literals of the saved specification. In binary, $P_s$ has $433$
digits and $W$ has $435$.

This is a closed decidable statement about explicit natural numbers: compute the
primes up to $324$ and their product.

## Depends on

- [The prescribed fixed constants](fixed-constants.md)

## Sources

- [Saved specification](../../../sources/syntax-locators.md#saved-specification)
- [Section 2.2](../../../sources/syntax-locators.md#section-22-catalogue-and-formal-multiple)
