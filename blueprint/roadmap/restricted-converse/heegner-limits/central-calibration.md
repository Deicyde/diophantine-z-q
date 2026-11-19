---
declaration: theorem
origin: cited
---

# Central specialization and arithmetic calibration (4.5), (4.6)

Let $K=\mathbb Q(\sqrt k)$ and $h$ satisfy the ring-class hypotheses, with every prime of $h$ split in $K$.
Suppose $L(E^{(h)},s)$ has a simple zero at $s=1$ and $L(E^{(hk)},1)\ne0$. Then the primitive coordinate of the
central class and functional satisfies
$$v_2u_{\rm prim}(0)=2j_{\rm rc}(h,k)-4\omega(h)-s(h)-s(hk)-\sum_{p\mid k}t_p+O_{E,\pi}(1),\tag{4.6}$$
with a bounded term independent of $h$ and $k$, where $0\le t_p\le2$, and $t_p=2$ when $E[2]$ is rational. Only after
$\omega(k)$ is bounded may the companion sum be absorbed.

The central identification behind it: the finite classes satisfy a retained boundary
$$z_i(0)-Lm_i\,j_i(b_h)=dv_i,\qquad m_i=a_{r_i}-2\chi_h(r_i),\tag{4.5}$$
with the same fixed $L$, and for the central Kummer comparison $i$,
$z_0=i(LmP)$ and $(\lambda_z)_0(ix)=\operatorname{PD}_K(x,c_K(LmP))$, where $P$ is the unaveraged ring-class
point and $c_K$ its conjugate-dual transport. On the rank-one Mordell–Weil lattice both free-line
coefficients therefore have valuation $j_{\rm rc}(h,k)+v_2(Lm)$.

**Proof sketch.** The split norm relation gives the finite-stage boundary (4.5), which lifts to the Selmer
cone; the trace bound bounds $v_2(m_i)$ by $c_E$. Over $\Lambda_{(t)}$ the active contraction ($C=-2$) and the
moving-prime contraction (nonzero central Frobenius determinants) commute with specialization, so the full
and Kummer local objects at the changed odd places are rationally acyclic, the comparison $j_0$ factors
through the ordinary Kummer complex, and the paired functional specializes to the Kummer-dual functional of
the same point. For (4.6), at a known simple zero Lemma 5.5 gives rank one and finite $\mathrm{Sha}$. The
torsion and free parts of the ordinary Kummer complex give the Selmer group; the sum and difference
isogenies between the restriction of scalars and $E^{(h)}\times E^{(hk)}$ have lattice indices with $IJ=2$ and
regulator ratio $2/I^2$, and Milne's isogeny ratio (proof of I.7.3) applies with finite $\mathrm{Sha}$, without
the leading-term conjecture. At each active $p\mid h$ the two split places each contribute the length
$\dim E[2]^{\operatorname{Fr}_p}=2$, so $-4\omega(h)$ in all. At $p\mid k$ the component group of the ramified
twist is $E[2]^{\operatorname{Fr}_p}$ (Edixhoven, Theorem 5.3 and Remark 5.4.1), which gives $t_p$.

## Depends on

- [The paired functional and the class-functional coordinate](paired-functional.md)
- [Finite Heegner descent with one multiplier (4.1), (4.2)](finite-heegner.md)

## Proof depends on

- [One moving character for the complete active list](moving-character.md)
- [Local conditions, the derived Kummer condition and duality](local-conditions.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:arith-central-specialization` (L3894–3986)
  and `ex:arith-central-calibration` (L3987–4141)

## Manuscript check

Mapped by AI review. The Euler-factor identities, the regulator ratio and the component-group bookkeeping
were checked. The rest of the length bookkeeping was read for structure and is not yet checked line by line.
The locators of Milne (I.7.3, (7.3.1)) and Edixhoven (Theorem 5.3, Remark 5.4.1) are not yet checked against
the prints; the finiteness of $\mathrm{Sha}$ comes through Lemma 5.5, that is from Kolyvagin's Theorem 1, whose
statement is not yet checked against the print. A TeX comment inside the proof (L3923) is an editorial note
from the file's assembly.
