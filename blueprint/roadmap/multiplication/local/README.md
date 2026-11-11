---
article_id: af_5971f1d401ed5ed61c874681
---

# Local conventions: the formal group and the truncated logarithm

The multiplication certificate reads arithmetic information off points of $2E(K_0)$ at
finite places. This section fixes the local conventions of the manuscript and proves the
local facts that both directions of the multiplication statement use. Throughout,
$E:y^2=x^3-d^2x$ with $d=75-53s$, a point of $E(K_0)$ is regarded as a point over every
completion $K_{\mathfrak p}$ of $K_0$, $z=-x/y$ and $w=1/x$ with $z(O)=w(O)=0$, and
$E_1(K_{\mathfrak p})$ is the set of points with $v_{\mathfrak p}(x)<0$ together with $O$.
For a point $P$ of $E(K_0)$ with $x(P)\ne0$, $P\in E_1(K_{\mathfrak p})$ exactly when
$v_{\mathfrak p}(1/x(P))\ge1$; this is how the inverse-abscissa tests detect the formal group.

## Primes of $K_0$

An odd prime $p$ is unramified in $K_0$; it splits into two conjugate primes when $2$ is a
square modulo $p$ and is inert otherwise. Conjugation exchanges the valuations at
conjugate primes, which is how the conjugated tests of a test group refer to the other
place above $p$.

- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](primes-above-p.md)

## The formal group and its logarithm

For the integral equation $y^2=x^3+Ax$ over a discretely valued field, the points with
$v(x)<0$ form a subgroup on which $z$ is injective, with $v(w)=2v(z)$, filtered by the
subgroups $v(z)\ge k$, so multiplication by an integer never lowers $v(z)$; this part has an
elementary chord-and-tangent proof. Over a complete field, $z$ turns the group law into a
formal group law, whose formal logarithm converges on $v(z)>0$, is a homomorphism, and is an
isometry where $v(z)>e/(p-1)$; at an odd unramified prime this is the whole formal group.
These are classical (Silverman IV and VII.2); here they are background statements, the
formal group law and the logarithm being the deepest inputs of the chapter. The manuscript's remark that identifying the formal neighbourhood with the
reduction kernel of a minimal model needs Silverman VII.2.1-2.2 is not used: every argument
below works with the integral equation of $E$ itself.

- [The formal neighbourhood of $y^2=x^3+Ax$ and its filtration](formal-group.md)
- [The chord estimate in a formal neighbourhood](chord-estimate.md)
- [The formal group law of $y^2=x^3+Ax$](formal-group-law.md)
- [The formal logarithm](formal-logarithm.md)
- [The isometry range of the formal logarithm](logarithm-isometry.md)

For $E$ the invariant differential is $dz/\sqrt{1+4d^2z^4}$, so the logarithm is an explicit
binomial series, and the polynomial $L$ of the truncated logarithm template is $16575$ times
its truncation in degree $25$.

- [The formal logarithm of $E$ is a binomial series](logarithm-series.md)
- [The coefficients of the truncated logarithm](logarithm-coefficients.md)

## The truncated logarithm

At every finite place, $L(z)$ is $16575z$ times a unit as soon as $v(z)\ge1$. At a prime
$p>324$ the truncation is much finer: $L(z)/16575=\log(z)(1+\epsilon_z)$ with
$v(\epsilon_z)\ge28$, because every omitted term has relative valuation at least
$r-1-v_p(r)\ge28$.

- [The truncated logarithm is $16575z$ times a unit](truncation-unit.md)
- [The truncation error at a large prime](truncation-error.md)

## Consequences for multiples of the generator

$P_0$ lies deep in the formal group at the dyadic prime $(s)$, so $L(z(Q))\ne0$ for every
nonzero multiple $Q$ of $P_0$: the two inverse guards of a test group never fail for a
nonidentity base point. At an odd prime, the full logarithms of two multiples of $P_0$ in
the formal group have the rational ratio of their indices.

- [The $2$-adic valuations of the coordinates of $P_0$](generator-dyadic-numerals.md)
- [The generator lies in the dyadic formal group](dyadic-generator.md)
- [The truncated logarithm does not vanish on nonzero multiples of $P_0$](logarithm-nonvanishing.md)
- [Full-logarithm ratios of multiples of $P_0$](logarithm-ratio.md)
