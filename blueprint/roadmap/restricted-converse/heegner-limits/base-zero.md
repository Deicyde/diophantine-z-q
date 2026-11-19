---
declaration: theorem
origin: cited
---

# The unknown base has zero coordinate if its derivative vanishes

Use the base $h_0=1$ of the final construction over $K=\mathbb Q(\sqrt k)$, with $L(E^{(k)},1)\ne0$ and
$2^\infty$-Selmer corank one for $E/K$. If $L'(E/K,1)=0$, then $u_{{\rm prim},0}(0)=\widetilde u_0(0)=0$ for the
same coordinates as before; the primitive coordinate is regular at $(t)$, and so is the corrected relaxed
coordinate. No finiteness of $\mathrm{Sha}$ at the base is needed.

**Proof sketch.** Put $A=\Lambda_{(t)}$, a DVR with residue field $\mathbb Q_2$, and use the finite free
primitive complex with its retained class and functional, integral over $A$ by the paired-functional
proposition. The conductor-one height formula (Theorem 1.1 of Cai–Shu–Tian) makes the Heegner point torsion
when $L'(E/K,1)=0$, so its rational Kummer class vanishes, and the boundary (4.5) makes the specialized cycle
zero. Corank one gives central dimensions $(1,1)$ in degrees one and two. Over $A$ the complex decomposes by
Smith reduction into free summands with zero differential and disks $[A\xrightarrow{t^r}A]$; a disk with $r>0$
adds one central class in each adjacent degree, so by semicontinuity and the Euler characteristic the
generic complex is either acyclic, where $u=0$ by definition, or has dimensions $(1,1)$. In the latter case no
disk with $r>0$ occurs, integral base change identifies the coordinate with that of the central tensor, and
that tensor is zero. The corrected coordinate follows from $\widetilde u_0=\varepsilon_0u_{{\rm prim},0}$ with
$\varepsilon_0\in\Lambda^\times$.

## Depends on

- [The paired functional and the class-functional coordinate](paired-functional.md)
- [Unused-prime comparison and the corrected coordinate (4.7)](common-coordinate.md)

## Proof depends on

- [Central specialization and arithmetic calibration (4.5), (4.6)](central-calibration.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:arith-base-zero` (L4330–4376)

## Manuscript check

Read by AI review. The height formula is used here only in its qualitative form, height zero exactly when
the derivative vanishes, which does not depend on the conductor factor discussed under (3.4). That use
matches the special case of Theorem 1.1 of Cai–Shu–Tian with conductor one, every prime of $N$ split and no
extra units; the theorem's statement is not yet checked against the print.
