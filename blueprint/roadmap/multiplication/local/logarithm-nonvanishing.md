---
article_id: af_1fde17c0f717ebc5031205d6
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.log25_z_ne_zero
---

# The truncated logarithm does not vanish on nonzero multiples of $P_0$

For every integer $n\ne0$, the point
$Q=[n]P_0$ is affine with $x(Q)\ne0$ and $y(Q)\ne0$, so $z(Q)=-x(Q)/y(Q)$ and $1/x(Q)$ are
defined and nonzero, and
$$L\bigl(z(Q)\bigr)\ne0 .$$

The manuscript states that all denominators in the tests are guarded; this lemma shows that
the two guards $L(z(H))\ne0$ and $L(z(V_0))\ne0$ of a test group hold automatically once
$H\ne O$ and $V_0\ne O$.

**Proof sketch.** By the torsion theorem $P_0$ has infinite order, so $Q\ne O$ and $Q$
is not of order two; hence $y(Q)\ne0$, and $x(Q)\ne0$ because $x=0$ forces $y=0$. Thus
$z(Q)\ne0$. By the dyadic position of $P_0$, $Q\in E_1(K_{(s)})$ with
$v_s(z(Q))\ge3\ge1$, and the unit form of the truncated logarithm at $(s)$ gives
$L(z(Q))=16575\,z(Q)(1+\eta)$ with $v_s(\eta)\ge2$, which is nonzero.

## Depends on

- [The point $P_0$](../../model/field/generator-point.md)
- [The truncated logarithm template](../../syntax/templates/template-log25.md)

## Proof depends on

- [Nonzero multiples of the generator](../../model/descent/nonzero-multiples.md)
- [The generator lies in the dyadic formal group](dyadic-generator.md)
- [The truncated logarithm is $16575z$ times a unit](truncation-unit.md)

## Sources

- [Twelve tests](../../../sources/multiplication-locators.md#twelve-tests)
