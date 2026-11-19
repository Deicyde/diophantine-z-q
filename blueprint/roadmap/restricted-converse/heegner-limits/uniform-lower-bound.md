---
declaration: theorem
origin: cited
---

# Uniform ring lower bound and height-one regularity (5.5)

Fix $E$, $\pi$, the old local types and a bound $A$. For every ring instance satisfying the hypotheses of the
arithmetic calibration (4.6) with $\omega(k)\le A$, the primitive coordinate satisfies
$$v_2u_{\rm prim}\ge-C(E,A),\qquad u_{\rm prim}\in\Lambda[1/2],\tag{5.5}$$
where the valuation is that of $\mathscr O$ and the constant is independent of the active support and the
companion field. Consequently its central specialization and (4.6) give (3.5). The regularity
$u_{\rm prim}\in\Lambda[1/2]$ also holds at the unknown base of corank one; the numerical bound is asserted
only at the known simple zeros.

**Proof sketch.** At a known simple zero the central class is nonzero by (4.5), so the generic kernel of the
two-term model over $\Lambda_{(t)}$ is nonzero, and by semicontinuity it has rank one. Suppose no uniform bound
exists: take instances with $v_2u_j\to-\infty$, bounded minimal models $[\mathscr O_j^n\to\mathscr O_j^n]$ and
primitive kernel vectors $v_j$, and pass to the outer ring, where the kernel has dimension $s\ge1$. If $s>1$,
one derivative prime gives a rank-two localization containing $v_j$; the relaxed image is self-annihilating
and contains the finite plane, hence equals it, and the outer dimension drops to $s-2$. The switch preserves
each inner determinant valuation, and a drop to zero is impossible since the actual class has nonzero generic
localization. After finitely many switches, bounded by (5.1), a nonzero maximal minor $\Delta$ with inner
valuation $b$ gives $u=\pm\alpha\beta/\Delta$ with $\alpha$ integral and $v_2\beta\ge-a$, so $v_2u_j\ge-a-b$, a
contradiction. For regularity at a height-one $\mathfrak p\ne(2)$, the same switches run over the DVR
$\Lambda_{\mathfrak p}$. A quadratic specialization occurs only at $\mathfrak p=(t)$ or $(t+2)$, since
$(1+t)^2-1=t(t+2)$; there the induced representation splits as $W_+\oplus W_-$ by the sign of $\tau$, the
derivative planes split into orthogonal hyperbolic planes (5.5a), and a detection with both signs (5.5b) again
drops the dimension by two. At derivative primes the orthogonal comparison is the identity, so the paired
functional stays integral, and $\Lambda[1/2]=\bigcap_{\mathfrak p\ne(2)}\Lambda_{\mathfrak p}$.

## Depends on

- [The paired functional and the class-functional coordinate](paired-functional.md)
- [Central specialization and arithmetic calibration (4.5), (4.6)](central-calibration.md)

## Proof depends on

- [The reduced generic residual rank bound (5.1)](residual-bound.md)
- [Evaluation and the outer valuation ring (5.2), (5.3)](outer-dvr.md)
- [The common kernel and a rank-two test (5.4)](kernel-detection.md)
- [Derivative local conditions and the determinant-preserving switch](derivative-switch.md)
- [Finite Heegner descent with one multiplier (4.1), (4.2)](finite-heegner.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:limits-uniform-lower-bound` (L4909–5205)

## Manuscript check

Checked line by line by AI review, relative to its inputs, with 18 checks by script: the switch pairing and
determinant symmetry, the Schur formula $u=\pm\alpha\beta/\Delta$ (for every nonzero maximal minor, 3,694
evaluations), the quadratic case with (5.5a) and (5.5b), and the step from (5.5) and (4.6) to (3.5). One gap
was filled: the bound $v_2\beta\ge-a$ after the switches needs the paired functional to stay $2^a$-integral with
the added derivative conditions, which the manuscript proves only in the regularity paragraph (L5161–5189,
where the orthogonal comparison at a derivative prime is the identity). The constant $C(E,A)$ comes from an
ultrafilter contradiction and is not effective; Theorem 5.3 is qualitative, so this suffices. The inputs (5.1)
and the paired functional were checked separately; the inner and outer limit lemmas, the derived Kummer lemma
and the moving character's construction are not yet checked line by line. A TeX comment inside the proof
(L4975) is an editorial note from the file's assembly.
