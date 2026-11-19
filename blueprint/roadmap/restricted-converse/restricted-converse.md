---
declaration: theorem
origin: cited
---

# Theorem 5.3: the restricted converse

For every positive squarefree $\ell\equiv11\pmod{12}$, the curve $E_\ell:y^2=x(x-\ell)(x+3\ell)$ satisfies
$$\operatorname{corank}_{\mathbb Z_2}\mathrm{Sel}_{2^\infty}(E_\ell/\mathbb Q)=1\quad\Longrightarrow\quad\operatorname{ord}_{s=1}L(E_\ell,s)=1.$$

**Proof sketch.** Fix $\ell$ and assume the corank is one. By the opening reduction the root number of
$E=E_\ell$ is $-1$, so $\operatorname{ord}_{s=1}L(E,s)$ is odd and at least one. The proof then splits into
two branches according to the intrinsic odd limit symbol at the empty configuration.

- If that symbol is a unit, the index $D=1$ is visible at an actual theta stage, with
  $v_2a_{M_\theta}(1)=\delta_o<M_\theta$, and the visibility implication (O.8) gives
  $\operatorname{ord}_{s=1}L(E,s)=1$ directly.
- Otherwise a companion $k<0$ with $L(E^{(k)},1)\ne0$ is fixed and $K=\mathbb Q(\sqrt k)$. Then $E/K$ has
  $2^\infty$-Selmer corank one, and the final contradiction shows $L'(E/K,1)\ne0$. Since
  $L(E/K,s)=L(E,s)L(E^{(k)},s)$ and $L(E^{(k)},1)\ne0$, the zero of $L(E,s)$ at $s=1$ is simple.

## Depends on

None.

## Proof depends on

- [The opening reduction](opening-reduction.md)
- [The branch split and the nonempty seeds](common-family/nonempty-seeds.md)
- [Finite coefficient transfer and the final contradiction](determinant/coefficient-transfer.md)

## Sources

- [The 11/5 manuscript](../../sources/manuscript.md#theorem-52): `hyp:RC` (L1005–1011), restated as (RC) at
  L1771–1775; the two branches at L2584–2594 and L5647–5739, and again at L10862–10935

## Manuscript check

Checked by AI review: the statement at L1771–1775 is the one at L1005–1011, and its hypothesis domain
matches the curves defined at L1761–1764. Both places where the proof becomes a deduction of the theorem
were checked: the first branch (L2584–2594), relative to (O.8), and the closing step (L5734–5738), where
$L'(E/K,1)\ne0$, $L(E^{(k)},1)\ne0$ and the factorization of $L(E/K,s)$ give a simple zero. The outline at
L1816–1823 does not mention the first branch; the opening reduction records this.
