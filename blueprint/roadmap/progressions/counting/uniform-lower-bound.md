---
article_id: af_2bb9d092ac43a2d8ca9d38bb
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.min_le_norm_LFunction_one, ZInQ.Progressions.effectiveLBound_le_norm_LFunction_one
---

# A lower bound for $|L(1,\chi)|$ at every nonprincipal character

Let $q\ge1$, put $M=\log q+3$, and let $\chi$ be a nonprincipal Dirichlet character modulo
$q$. Then
$$|L(1,\chi)|\ge\min\Bigl(\frac1{256\,M^7},\ \frac1{40\,q^{3/2}}\Bigr).$$

**Proof sketch.** If $\chi^2\ne\chi_0$, the lower bound at complex characters gives
$|L(1,\chi)|\ge1/(256M^7)$. If $\chi^2=\chi_0$, the lower bound at real characters gives
$|L(1,\chi)|\ge1/(40q^{3/2})$. In both cases $|L(1,\chi)|$ is at least the minimum.

## Depends on

None.

## Proof depends on

- [A lower bound for $|L(1,\chi)|$ at complex characters](../lseries/complex-lower-bound.md)
- [A lower bound for $L(1,\chi)$ at real characters](../real-characters/real-lower-bound.md)

## Sources

- [Apostol, Chapter 7](../../../sources/progressions-locators.md#apostol-chapter-7)
