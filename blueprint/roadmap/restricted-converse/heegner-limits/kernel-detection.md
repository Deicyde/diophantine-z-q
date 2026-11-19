---
declaration: theorem
origin: cited
---

# The common kernel and a rank-two test (5.4)

Use the exact kernel of the sequences acting trivially on the full Tate module, the relevant ring class
fields and the quadratic characters. On the characteristic-zero tests used later, restriction of the
evaluated cohomology to this kernel is injective. When the moving scalar character is nonquadratic, two
independent classes have a rank-two localization at a single element of the kernel. Finite Chebotarev
realizes the required conjugation coset and basis-cochain evaluations, with the exact inner-limit matrix
identity
$$L_j=E_{\sigma_j^2}\tag{5.4}$$
before any denominators of $\mathscr O$-minimal models are applied. At the residual test only scalar-inertia
vanishing, bounded cohomology and finite detecting lists are asserted; the quadratic exception at
characteristic-zero height-one tests is treated in the proof of (5.5).

**Proof sketch.** A cocycle vanishing on the kernel is a coboundary in characteristic zero: $z$ is central
modulo the kernel with $\rho(z)=u^4I$, and $(u^4-1)b(g)=(g-1)b(z)$ can be divided by $u^4-1\ne0$. With a
nonquadratic scalar character, the moving inertia characters $(1+t)^{\pm1}$ are distinct, the induced rank-four
representation is absolutely irreducible, and Goursat's lemma with the matrix span from the finite Heegner
descent gives a joint rank-two image; polarization picks one element. A new prime, with a place above it,
matching all basis-cochain evaluations at a common retained precision $n(i)\to\infty$ realizes it, and the
same inner ultrafilter makes (5.4) an exact equality of $\Lambda$-matrices; only afterwards is it composed with
the inclusion of a minimal model, whose denominators are then irrelevant.

## Depends on

- [Finite free models and the inner limit](inner-limit.md)

## Proof depends on

- [Finite Heegner descent with one multiplier (4.1), (4.2)](finite-heegner.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:limits-kernel-detection` (L4747–4832)

## Manuscript check

Checked by AI review in the line-by-line check of (5.5): the kernel cocycle argument, the rank-two
localization and the polarization identity, the last by script. The use of (5.4) was checked structurally;
the inner-limit lemma it rests on is not yet checked line by line.
