---
article_id: af_7780cbcd8ca0c689a37fef93
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.O12.o12_charZero, ZInQ.Manuscript.RC.Odd.O12_diag, ZInQ.Manuscript.RC.O12.LocalBlocks
---

# (O.12): the inertia identity at a ramified prime

Fix a finite set $U$ and a natural number $p$; the manuscript's $U$ is a set of good primes and
$p\in U$, but neither condition is a hypothesis. Assume a model of the characteristic-zero forms
(`GaloisConstituentModel`, named inputs, not proved), of which the theorem uses $\rho$ and $F_U$:
constituents with two-dimensional Galois representations $\rho_i$ over a characteristic-zero
coefficient field (Carayol's theorem, PRINT, entered as data), and the form $F_U$ as a vector of
constituent coordinates, on which $t(g)$ and $d(g)$ act through the trace and the determinant of
$\rho_i(g)$. Its other fields are unused: `det_orbit` and `two_fresh` (ELLIOT), `stable_t`,
`stable_d`, `kummer` and `finiteIndex` (GLUE), and `chebotarev` (PRINT). Take an inertia element
$\tau$ above $p$ on which the character of $\mathbb Q(\sqrt{p^*})$ is $-1$, and an arithmetic
Frobenius element $\phi$ at the same prime. Assume the local description at $p$ (`LocalBlocks`, named
inputs): sets of active and of ramified constituents, with $F_U$ zero off the active ones
(definitions); an operator $U_p^{(2)}$ on the coordinates that preserves the active ramified part;
$\rho_i(\tau)=1$ on the active unramified constituents; and on each active ramified constituent a
basis with
$$\rho(\tau)=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
\rho(\phi)=\begin{pmatrix}\lambda&0\\0&\mu\end{pmatrix},$$
on which $U_p^{(2)}$ acts by $\lambda$ (`newLine`: on cuspidal constituents PRINT, Casselman and
Carayol as cited in the manuscript, locators unverified; on Eisenstein constituents the parallel
calculation with the pair of characters). Then for every $g\in G_{\mathbb Q}$
$$U_p^{(2)}\{t(g\tau\phi)-t(g\phi)\}F_U=d(\phi)\{t(g\tau)-t(g)\}F_U.\tag{O.12}$$

On a ramified block this is the matrix identity `O12_diag`: for
$\rho(g)=\begin{pmatrix}a&b\\c&e\end{pmatrix}$, $t(g\tau)-t(g)=-2e$ and $t(g\tau\phi)-t(g\phi)=-2e\mu$,
and $d(\phi)=\lambda\mu$. On the old blocks both differences vanish, however $U_p^{(2)}$ acts there. The
identity is stated on the characteristic-zero coordinates of $F_U$; its transfer to the integral trace
module and its use at coefficient one are not part of it.

This theorem is not on the path of the reduction of Theorem 5.3: there (O.12) at coefficient one is a
field of the trace models of `PostLeaves.address` (ELLIOT); see
[Proposition F.5](proposition-f-5-coefficient-rules.md).

**Proof sketch.** Conjugating by the chosen basis does not change traces, so on an active ramified
constituent the identity is `O12_diag` with $\lambda=U_p^{(2)}$. On an active unramified constituent
$\rho(\tau)=1$, so both differences are zero; inactive constituents carry no coordinate of $F_U$.

## Depends on

None.

## Sources

- [Appendix F](../../../sources/manuscript.md#appendix-f)
