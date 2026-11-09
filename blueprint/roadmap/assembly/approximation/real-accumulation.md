---
article_id: af_db94cccfceea1aba7e4e10bc
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Assembly.exists_multiple_large_unconditional
---

# Multiples of the generator approach the identity at both real places

For every $M\in\mathbb R$ there is an integer $k\ge1$ such that $[k]P_0=(x_k,y_k)$ is affine and
$$\sigma_+(x_k)>M\qquad\text{and}\qquad\sigma_-(x_k)>M .$$
That is, positive multiples of $P_0$ approach the identity simultaneously in the two real
embeddings.

**Proof sketch.** Each real embedding $\sigma_\pm$ maps $E$ to the real curve
$y^2=x^3-e_\pm^2x$ with $e_\pm=\sigma_\pm(d)=75\mp53\sqrt2\ne0$, and induces a group homomorphism
$E(K_0)\to E_{e_\pm}(\mathbb R)$, $(x,y)\mapsto(\sigma_\pm x,\sigma_\pm y)$, $O\mapsto O$ (the
chord-and-tangent formulas are rational and commute with ring homomorphisms). Apply the
compactness statement to the sequence $\sigma_+([k]P_0)$, $k\ge1$, and then to
$\sigma_-([k]P_0)$ along the resulting subsequence: there are $k_1<k_2<\cdots$ and points
$Q_\pm$ with $\sigma_\pm([k_i]P_0)\to Q_\pm$. By continuity of subtraction,
$\sigma_\pm([k_{i+1}-k_i]P_0)=\sigma_\pm([k_{i+1}]P_0)-\sigma_\pm([k_i]P_0)\to O$ in both embeddings.
For $i$ large, $k=k_{i+1}-k_i\ge1$ has both embedded points equal to $O$ or with abscissa
$>M$; since $P_0$ has infinite order, $[k]P_0$ is affine, so both abscissas exceed $M$.

The manuscript's argument (partition the compact closure of the cyclic subgroup into small
neighbourhoods and subtract two close multiples) is the same pigeonhole principle.

## Depends on

- [The point $P_0$](../../model/field/generator-point.md)
- [The field $K_0=\mathbb Q(\sqrt2)$](../../model/field/quadratic-field.md)

## Proof depends on

- [Compactness and continuity of subtraction on a real curve](real-subtraction.md)
- [Nonzero multiples of the generator](../../model/descent/nonzero-multiples.md)

## Sources

- [Section 11.1 approximation](../../../sources/assembly-locators.md#section-111-approximation)
